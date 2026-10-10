import OAI.NumberTheory.Ostmann.Characters.FiniteKernelLinearMaps
import OAI.NumberTheory.Ostmann.Supply.LocalSparsePolydisc

namespace OAI

/-! # Finite matrices for the scalar plus centered-residue blocks -/

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

noncomputable def finiteBlockMatrix {p : ℕ} [NeZero p]
    (a : ℂ) (row col : ZMod p → ℂ) (L : (ZMod p → ℂ) →ₗ[ℂ] (ZMod p → ℂ)) :
    Option (ZMod p) → Option (ZMod p) → ℂ
  | none, none => a
  | none, some y => conj (row y)
  | some x, none => col x
  | some x, some y => L (residuePointVector y) x

theorem finiteBlockMatrix_apply_none {p : ℕ} [NeZero p]
    (a : ℂ) (row col : ZMod p → ℂ) (L : (ZMod p → ℂ) →ₗ[ℂ] (ZMod p → ℂ))
    (f : Option (ZMod p) → ℂ) :
    (∑ y, finiteBlockMatrix a row col L none y * f y) =
      a * f none + ∑ y, conj (row y) * f (some y) := by
  rw [Fintype.sum_option]
  rfl

theorem finiteBlockMatrix_apply_some {p : ℕ} [NeZero p]
    (a : ℂ) (row col : ZMod p → ℂ) (L : (ZMod p → ℂ) →ₗ[ℂ] (ZMod p → ℂ))
    (f : Option (ZMod p) → ℂ) (x : ZMod p) :
    (∑ y, finiteBlockMatrix a row col L (some x) y * f y) =
      f none * col x + L (fun y => f (some y)) x := by
  rw [Fintype.sum_option, finiteLinearMap_point_expansion]
  simp only [finiteBlockMatrix]
  ring

theorem finiteBlockMatrix_energy {p : ℕ} [NeZero p]
    (a : ℂ) (row col : ZMod p → ℂ) (L : (ZMod p → ℂ) →ₗ[ℂ] (ZMod p → ℂ))
    (f : Option (ZMod p) → ℂ) :
    (∑ x, ‖∑ y, finiteBlockMatrix a row col L x y * f y‖ ^ 2) =
      ‖a * f none + ∑ y, conj (row y) * f (some y)‖ ^ 2 +
        residueVectorNorm (fun x => f none * col x + L (fun y => f (some y)) x) ^ 2 := by
  rw [Fintype.sum_option, finiteBlockMatrix_apply_none, residueVectorNorm_sq]
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  rw [finiteBlockMatrix_apply_some]

end Ostmann

end OAI
