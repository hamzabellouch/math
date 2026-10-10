import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks

namespace OAI

section

noncomputable section
namespace Pureness
open Set TopologicalSpace MeasureTheory
open scoped NNReal ENNReal

variable {X : Type*} [TopologicalSpace X]

def dimensionCompactCapacity (r : C(X, ℝ≥0) → ℝ≥0∞) (K : Compacts X) : ℝ≥0∞ :=
  ⨅ (f : C(X, ℝ≥0)) (_ : ∀ x ∈ K, 1 ≤ f x), r f

lemma dimensionCompactCapacity_le (r : C(X, ℝ≥0) → ℝ≥0∞) (K : Compacts X)
    (f : C(X, ℝ≥0)) (hf : ∀ x ∈ K, 1 ≤ f x) :
    dimensionCompactCapacity r K ≤ r f := iInf_le_of_le f (iInf_le_of_le hf le_rfl)

lemma dimensionCompactCapacity_mono (r : C(X, ℝ≥0) → ℝ≥0∞) :
    Monotone (dimensionCompactCapacity r) := by
  intro K L hKL
  exact le_iInf₂ fun f hf => dimensionCompactCapacity_le r K f (fun x hx => hf x (hKL hx))

lemma dimensionCompactCapacity_ne_top (r : C(X, ℝ≥0) → ℝ≥0∞)
    (hr : r 1 ≠ ⊤) (K : Compacts X) : dimensionCompactCapacity r K ≠ ⊤ :=
  ne_top_of_le_ne_top hr (dimensionCompactCapacity_le r K 1 (fun _ _ => le_rfl))

lemma dimensionCompactCapacity_empty (r : C(X, ℝ≥0) → ℝ≥0∞) (hr : r 0 = 0) :
    dimensionCompactCapacity r ⊥ = 0 := by
  apply le_antisymm _ bot_le
  exact (dimensionCompactCapacity_le r ⊥ 0 (by intro x hx; exact False.elim hx)).trans hr.le

lemma dimensionCompactCapacity_sup_le (r : C(X, ℝ≥0) → ℝ≥0∞)
    (hsub : ∀ f g, r (f+g) ≤ r f+r g) (K L : Compacts X) :
    dimensionCompactCapacity r (K ⊔ L) ≤ dimensionCompactCapacity r K + dimensionCompactCapacity r L := by
  unfold dimensionCompactCapacity
  rw [ENNReal.iInf_add]
  apply le_iInf
  intro f
  rw [ENNReal.iInf_add]
  apply le_iInf
  intro hf
  rw [ENNReal.add_iInf]
  apply le_iInf
  intro g
  rw [ENNReal.add_iInf]
  apply le_iInf
  intro hg
  apply le_trans (dimensionCompactCapacity_le r (K ⊔ L) (f+g) ?_) (hsub f g)
  intro x hx
  rcases hx with hx | hx
  · exact (hf x hx).trans (le_add_of_nonneg_right bot_le)
  · exact (hg x hx).trans (le_add_of_nonneg_left bot_le)

end Pureness
end
end

end OAI
