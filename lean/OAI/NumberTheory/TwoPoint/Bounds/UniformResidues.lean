import OAI.NumberTheory.TwoPoint.Bounds.TraceDesignations
import Mathlib.Data.Fintype.Fin

namespace OAI

/-! Uniform residue coordinates realized on one common finite carrier. -/

namespace TwoPointCorrelations

open Finset

/-- A uniform residue modulo `p`, embedded into `Fin B`. The zero-weight
padding allows different prime moduli to share the same sample type. -/
noncomputable def uniformResidueLaw (B p : ℕ) (hp : 0 < p) (hpB : p ≤ B) :
    FiniteLaw (Fin B) where
  weight x := if x.val < p then (p : ℝ)⁻¹ else 0
  nonneg x := by split_ifs <;> positivity
  total := by
    rw [← sum_filter]
    simp [Fin.card_filter_val_lt, min_eq_right hpB, ne_of_gt hp]

@[simp] lemma uniformResidueLaw_weight (B p : ℕ) (hp : 0 < p) (hpB : p ≤ B)
    (x : Fin B) (hx : x.val < p) :
    (uniformResidueLaw B p hp hpB).weight x = (p : ℝ)⁻¹ := by
  simp [uniformResidueLaw, hx]

lemma uniformResidueLaw_support (B p : ℕ) (hp : 0 < p) (hpB : p ≤ B)
    (x : Fin B) :
    (uniformResidueLaw B p hp hpB).weight x ≠ 0 ↔ x.val < p := by
  simp [uniformResidueLaw, ne_of_gt hp]

@[simp] lemma uniformResidueLaw_castLE (B p : ℕ) (hp : 0 < p) (hpB : p ≤ B)
    (x : Fin p) :
    (uniformResidueLaw B p hp hpB).weight (Fin.castLE hpB x) = (p : ℝ)⁻¹ := by
  exact uniformResidueLaw_weight B p hp hpB _ x.isLt

/-- Every actual residue assignment with nonzero product mass lies below
its coordinate's modulus. This applies to the very same sample used for
the mixed-difference identity. -/
lemma uniformResidueLaw_independent_support {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B : ℕ) (p : ι → ℕ) (hp : ∀ i, 0 < p i) (hpB : ∀ i, p i ≤ B)
    (x : ι → Fin B) :
    (FiniteLaw.independent (fun i => uniformResidueLaw B (p i) (hp i) (hpB i))).weight x ≠ 0 ↔
      ∀ i, (x i).val < p i := by
  simp only [FiniteLaw.independent, prod_ne_zero_iff, mem_univ, true_implies,
    uniformResidueLaw_support]

end TwoPointCorrelations

end OAI
