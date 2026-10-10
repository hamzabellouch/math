import Mathlib
import OAI.Geometry.HyperbolicGroups.IncidenceTemplate

namespace OAI

section
section


noncomputable section
open scoped BigOperators
namespace HyperbolicObstruction
namespace SparsePattern.Pattern
variable {F R : Type*} [Fintype F] [Fintype R] [DecidableEq F]
  (P : SparsePattern.Pattern F R)

lemma cost_subset (J : Finset R) :
    (∑ r ∈ J, P.cost r) ≤ ∑ r, if P.support r ⊆ J.biUnion P.support then P.cost r else 0 := by
  classical
  calc
    _ = ∑ r ∈ J, if P.support r ⊆ J.biUnion P.support then P.cost r else 0 := by
      apply Finset.sum_congr rfl
      intro r hr
      rw [ite_eq_left (Finset.subset_biUnion_of_mem P.support hr)]
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ J)
      (fun r _ _ => by split_ifs <;> simp [P.nonneg])

/-- Pinning zero or one named field leaves a full unit on any active row overlap. -/
lemma pinned_overlap_margin (supports : ∀ r, 3 ≤ (P.support r).card)
    (budget : ∀ W : Finset F, (min 2 W.card : ℕ) ≤ P.exponent W)
    {J : Finset R} (hJ : J.Nonempty) (I : Finset F) (hI : I.card ≤ 1) :
    1 ≤ ((J.biUnion P.support \ I).card : ℤ) - ∑ r ∈ J, P.cost r := by
  obtain ⟨r,hr⟩ := hJ
  have hc : 3 ≤ (J.biUnion P.support).card :=
    (supports r).trans (Finset.card_le_card (Finset.subset_biUnion_of_mem P.support hr))
  have hb := budget (J.biUnion P.support)
  have hm : min 2 (J.biUnion P.support).card = 2 := by omega
  rw [hm] at hb
  unfold exponent at hb
  have hs := P.cost_subset J
  have hi : (J.biUnion P.support ∩ I).card ≤ I.card := Finset.card_le_card Finset.inter_subset_right
  have he := Finset.card_sdiff_add_card_inter (J.biUnion P.support) I
  omega

end SparsePattern.Pattern

namespace IncidenceTemplate
/-- Exact increases from critical to actual array-entry costs. -/
def rowSurcharge (α β δ : ℝ) : Row → ℝ
  | Sum.inl _ => α
  | Sum.inr (Sum.inl _) => β - 7 * α
  | Sum.inr (Sum.inr _) => δ

/-- Source Equation (sample:eq-costs), with the critical integer cost displayed. -/
def actualRowCost (α β δ : ℝ) (r : Row) : ℝ := rowCost r + rowSurcharge α β δ r

lemma rowSurcharge_nonneg {α β δ : ℝ} (ha : 0 ≤ α) (hb : 7 * α ≤ β) (hd : 0 ≤ δ)
    (r : Row) : 0 ≤ rowSurcharge α β δ r := by
  rcases r with i | (_ | τ)
  · exact ha
  · exact sub_nonneg.mpr hb
  · exact hd

lemma rowSurcharge_sum (α β δ : ℝ) : (∑ r, rowSurcharge α β δ r) = β + 90 * δ := by
  simp [rowSurcharge, Fintype.sum_sum_type, card_twoPaths]
  ring

lemma rowSurcharge_subset {α β δ : ℝ} (ha : 0 ≤ α) (hb : 7 * α ≤ β) (hd : 0 ≤ δ)
    (J : Finset Row) : (∑ r ∈ J, rowSurcharge α β δ r) ≤ β + 90 * δ := by
  rw [← rowSurcharge_sum]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ J)
    (fun r _ _ => rowSurcharge_nonneg ha hb hd r)

lemma actualRowCost_nonneg {α β δ : ℝ} (ha : 0 ≤ α) (hb : 7 * α ≤ β) (hd : 0 ≤ δ)
    (r : Row) : 0 ≤ actualRowCost α β δ r := by
  have hc : (0 : ℝ) ≤ rowCost r := by exact_mod_cast pattern.nonneg r
  exact add_nonneg hc (rowSurcharge_nonneg ha hb hd r)

lemma actual_pinned_overlap {α β δ : ℝ} (ha : 0 ≤ α) (hb : 7 * α ≤ β) (hd : 0 ≤ δ)
    {J : Finset Row} (hJ : J.Nonempty) (I : Finset Field) (hI : I.card ≤ 1) :
    1 - (β + 90 * δ) ≤ ((J.biUnion rowSupport \ I).card : ℝ) -
      ∑ r ∈ J, actualRowCost α β δ r := by
  have hc := pattern.pinned_overlap_margin rowSupport_card
    (fun W => by rw [pattern_exponent]; exact criticalExponent_lower W) hJ I hI
  have hc' : (1 : ℝ) ≤ ((J.biUnion rowSupport \ I).card : ℝ) - ∑ r ∈ J, (rowCost r : ℝ) := by
    exact_mod_cast hc
  have hs := rowSurcharge_subset ha hb hd J
  simp only [actualRowCost, Finset.sum_add_distrib]
  linarith

end IncidenceTemplate
end HyperbolicObstruction
end
end

section

end
end

end OAI
