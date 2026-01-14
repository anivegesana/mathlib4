module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
public import Mathlib.LinearAlgebra.Matrix.Diagonal
public import Mathlib.LinearAlgebra.Matrix.Permutation
public import Mathlib.LinearAlgebra.Matrix.Transvection
public import Mathlib.LinearAlgebra.UnitaryGroup

@[expose] public section

variable {n R : Type*} [Fintype n] [DecidableEq n]

namespace Equiv.Perm.permMatrix

open Units Matrix

def submonoid_of_GL [Semiring R] : Submonoid (GL n R) where
  carrier := {x | ∃ (σ : Perm n), x.val = σ.permMatrix R}
  one_mem' := by
    rw [Set.mem_setOf_eq]
    use 1
    rw [val_one, permMatrix_one]
  mul_mem' ha hb := by
    rw [Set.mem_setOf_eq] at *
    choose π ha using ha
    choose ρ hb using hb
    use ρ * π
    rw [val_mul, ha, hb, permMatrix_mul]

def subgroup_of_GL [CommRing R] : Subgroup (GL n R) where
  carrier := {x | ∃ (σ : Perm n), x.val = σ.permMatrix R}
  one_mem' := by
    rw [Set.mem_setOf_eq]
    use 1
    rw [val_one, permMatrix_one]
  mul_mem' ha hb := by
    rw [Set.mem_setOf_eq] at *
    choose π ha using ha
    choose ρ hb using hb
    use ρ * π
    rw [val_mul, ha, hb, permMatrix_mul]
  inv_mem' hx := by
    rw [Set.mem_setOf_eq] at *
    choose π hx using hx
    use π⁻¹
    rw [coe_units_inv, hx, permMatrix_inv]

end Equiv.Perm.permMatrix

namespace Matrix

theorem permMatrix_mem_orthogonalGroup [CommRing R] (σ : Equiv.Perm n) :
    σ.permMatrix R ∈ orthogonalGroup n R := by
  rw [Matrix.mem_orthogonalGroup_iff, transpose_permMatrix, ← permMatrix_inv,
    Matrix.mul_nonsing_inv]
  rw [det_permutation]
  have h' : σ.sign = 1 ∨ σ.sign = -1 := by
    cases Equiv.Perm.sign_eq_one_or_eq_neg_one σ <;> rename_i h <;> simp [h]
  cases h' <;> rename_i h'
  · have h'' : IsUnit ((1 : ℤˣ) : R) := by
      simp
    rw [← h'] at h''
    exact h''
  have h'' : IsUnit ((-1 : ℤˣ) : R) := by
    simp
  rw [← h'] at h''
  exact h''

end Matrix
