import Mathlib
import OAI.Geometry.HyperbolicGroups.GenericMoment
import OAI.Geometry.HyperbolicGroups.Pinned
import OAI.Geometry.HyperbolicGroups.LeafMargin

namespace OAI

section
section


noncomputable section
open scoped BigOperators
namespace HyperbolicObstruction
namespace StarModel
variable {F R B : Type*} [Fintype F] [Fintype R] [Fintype B]
  [DecidableEq F] [DecidableEq R] [DecidableEq B] [Nonempty B]

omit [Fintype F] [DecidableEq R] [DecidableEq B] in
lemma sum_array_le (support : R → Finset F) (U : Finset F) (c : R → ℝ)
    (hc : ∀ r, 0 ≤ c r) (J : Finset (Pos (B := B) support U)) :
    (∑ s ∈ J, c (array support U s)) ≤ (Fintype.card B : ℝ) * ∑ r, c r := by
  calc
    _ ≤ ∑ s : Pos (B := B) support U, c (array support U s) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun s _ _ => hc _)
    _ ≤ _ := by
      rw [Fintype.sum_sum_type, Fintype.sum_prod_type]
      change (∑ r : {r : R // support r ⊆ U}, c r.val) +
        (∑ _j : B, ∑ r : {r : R // ¬support r ⊆ U}, c r.val) ≤ _
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      rw [← Fintype.sum_subtype_add_sum_subtype (fun r => support r ⊆ U) c]
      have hn : (1 : ℝ) ≤ Fintype.card B := by exact_mod_cast Fintype.card_pos (α := B)
      have ha : 0 ≤ ∑ r : {r : R // support r ⊆ U}, c r.val := Finset.sum_nonneg (fun _ _ => hc _)
      nlinarith

end StarModel
namespace IncidenceTemplate
variable {B : Type*} [Fintype B] [DecidableEq B] [Nonempty B]

omit [DecidableEq B] in
lemma star_surcharge {α β δ : ℝ} (ha : 0 ≤ α) (hb : 7 * α ≤ β) (hd : 0 ≤ δ)
    (U : Finset Field) (J : Finset (StarModel.Pos (B := B) rowSupport U)) :
    (∑ s ∈ J, rowSurcharge α β δ (StarModel.array rowSupport U s)) ≤
      (Fintype.card B : ℝ) * (β + 90 * δ) := by
  rw [← rowSurcharge_sum]
  exact StarModel.sum_array_le rowSupport U _ (rowSurcharge_nonneg ha hb hd) J

lemma star_leaf_actual_gap {α β δ : ℝ} (ha : 0 ≤ α) (hb : 7 * α ≤ β) (hd : 0 ≤ δ)
    (U : Finset Field) (e : Field) (he : e ∉ U)
    (gap : ∀ W, W.Nonempty → Disjoint U W → 1 ≤ pattern.exponent (U ∪ W) - pattern.exponent U)
    (J : Finset (StarModel.Pos (B := B) rowSupport U)) (hJ : J.Nonempty) :
    1 - (Fintype.card B : ℝ) * (β + 90 * δ) ≤
      (((J.biUnion (StarModel.rowSupport rowSupport U)) \ StarModel.leafPins U e).card : ℝ) -
        ∑ s ∈ J, actualRowCost α β δ (StarModel.array rowSupport U s) := by
  have hcrit := StarModel.leaf_critical_gap pattern U e he
    (fun W => by rw [pattern_exponent]; exact criticalExponent_lower W) rowSupport_card gap J hJ
  have hc : (1 : ℝ) ≤
      (((J.biUnion (StarModel.rowSupport rowSupport U)) \ StarModel.leafPins U e).card : ℝ) -
        ∑ s ∈ J, (rowCost (StarModel.array rowSupport U s) : ℝ) := by
    exact_mod_cast hcrit
  have hs := star_surcharge ha hb hd U J
  simp only [actualRowCost,Finset.sum_add_distrib]
  linarith

end IncidenceTemplate

namespace PinnedAssignments
variable {W F A S I : Type*} [Fintype W] [Fintype F] [Fintype A] [Fintype S] [Fintype I]
  [DecidableEq W] [DecidableEq F] [DecidableEq A] [DecidableEq S] [DecidableEq I] [Nonempty A]

omit [Fintype F] in
/-- The generic variance estimate after pinning named coordinates, with the
cardinality bound produced from fieldwise injectivity. -/
theorem relative_variance (tag : W → F) (P : Finset W) (ξ : W → A)
    (hξ : PinFieldwise tag P ξ) (hN : 4 * Fintype.card W ≤ Fintype.card A)
    (row : (W → A) → S → I) (E : S → Finset W)
    (read : ∀ σ τ s, row σ s = row τ s → ∀ v ∈ E s, σ v = τ v)
    (inj : ∀ σ, Fieldwise tag σ → Function.Injective (row σ))
    (p : I → ℝ) (hp : ∀ i, p i ∈ Set.Icc (0 : ℝ) 1) (c : S → ℝ)
    (prob : ∀ σ s, p (row σ s) = (Fintype.card A : ℝ) ^ (-c s))
    {ε : ℝ} (gap : ∀ J : Finset S, J.Nonempty →
      ε ≤ (((J.biUnion E) \ P).card : ℝ) - ∑ s ∈ J, c s) :
    (FiniteLaw.bernoulliProduct p hp).variance
      (fun w => (BernoulliCandidates.count (fun σ => row (extend P ξ σ)) (candidates tag P ξ) w : ℝ)) ≤
    Fintype.card (BernoulliCandidates.OverlapType S) * 2 ^ Fintype.card (Free P) *
      (Fintype.card A : ℝ) ^ (-ε) *
      ((FiniteLaw.bernoulliProduct p hp).expect
        (fun w => (BernoulliCandidates.count (fun σ => row (extend P ξ σ)) (candidates tag P ξ) w : ℝ))) ^ 2 := by
  apply BernoulliCandidates.relative_variance_power
    (fun σ => row (extend P ξ σ)) (fun s => support P (E s))
    _ p hp (candidates tag P ξ) _ c _ (candidates_lower tag P ξ hξ hN)
  · intro J hJ
    rw [support_biUnion,card_support]
    exact gap J hJ
  · intro σ τ s he v hv
    have hh := read (extend P ξ σ) (extend P ξ τ) s he v.val ((mem_support _ _ _).mp hv)
    simpa only [extend_free] using hh
  · intro σ hσ
    exact inj _ (Finset.mem_filter.mp hσ).2
  · intro σ _ s
    exact prob _ s

end PinnedAssignments
end HyperbolicObstruction
end
end

section

end
end

end OAI
