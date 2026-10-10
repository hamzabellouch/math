import OAI.MeasureTheory.Falconer.Estimates.FinitePopularity
import OAI.MeasureTheory.Falconer.Incidence.FiniteBallBounds

namespace OAI

/-! Averaging local counts over rows proves regularity of popular line
parameters. This is the refinement in Orponen--Shmerkin, Appendix A.7. -/
namespace Falconer

theorem familyDegree_restrict_sum {α β : Type*} [DecidableEq β]
    (J : Finset α) (A : α → Finset β) (S : Finset β) :
    (∑ x ∈ S, familyDegree J A x) = ∑ j ∈ J, ((S ∩ A j).card : ℝ) := by
  have hd := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
    (s := J) (t := S) (fun j x => x ∈ A j)
  have he : (∑ j ∈ J, (S ∩ A j).card) =
      ∑ x ∈ S, (J.filter fun j => x ∈ A j).card := by
    simpa only [Finset.bipartiteAbove,Finset.bipartiteBelow,Finset.filter_mem_eq_inter] using hd
  unfold familyDegree
  exact_mod_cast he.symm

theorem popular_family_regular {α : Type*} (J : Finset α) (hJ : J.Nonempty)
    (A : α → Finset (Space 2)) {δ s K θ C : ℝ} (hδ : 0 ≤ δ) (hK : 0 ≤ K) (hθ : 0 < θ)
    (hA : ∀ j ∈ J, NormalizedFiniteBallBound δ s K (A j))
    (G : Finset (Space 2)) (hsize : ((J.biUnion A).card : ℝ) ≤ C*(G.card : ℝ))
    (hdegree : ∀ x ∈ G, θ*(J.card : ℝ) ≤ familyDegree J A x) :
    NormalizedFiniteBallBound δ s (K*C/θ) G := by
  have hJpos : 0 < (J.card : ℝ) := Nat.cast_pos.mpr (Finset.card_pos.mpr hJ)
  intro z r hdr hr1
  let H := G.filter fun x => dist x z ≤ r
  have hr0 : 0 ≤ r := hδ.trans hdr
  have hb : θ*(J.card : ℝ)*(H.card : ℝ) ≤
      (J.card : ℝ)*(K*r^s*((J.biUnion A).card : ℝ)) := by
    calc
      _ = ∑ _x ∈ H, θ*(J.card : ℝ) := by simp; ring
      _ ≤ ∑ x ∈ H, familyDegree J A x :=
        Finset.sum_le_sum fun x hx => hdegree x (Finset.mem_filter.mp hx).1
      _ = ∑ j ∈ J, ((H ∩ A j).card : ℝ) := familyDegree_restrict_sum J A H
      _ ≤ ∑ j ∈ J, K*r^s*((J.biUnion A).card : ℝ) := by
        apply Finset.sum_le_sum
        intro j hj
        have hsub : H ∩ A j ⊆ (A j).filter (fun x => dist x z ≤ r) := by
          intro x hx
          obtain ⟨hxH,hxA⟩ := Finset.mem_inter.mp hx
          exact Finset.mem_filter.mpr ⟨hxA,(Finset.mem_filter.mp hxH).2⟩
        calc
          _ ≤ (((A j).filter fun x => dist x z ≤ r).card : ℝ) :=
            Nat.cast_le.mpr (Finset.card_le_card hsub)
          _ ≤ K*r^s*((A j).card : ℝ) := hA j hj z r hdr hr1
          _ ≤ _ := mul_le_mul_of_nonneg_left
            (Nat.cast_le.mpr (Finset.card_le_card (Finset.subset_biUnion_of_mem A hj)))
            (mul_nonneg hK (Real.rpow_nonneg hr0 _))
      _ = _ := by simp
  have hb' : θ*(H.card : ℝ) ≤ K*r^s*((J.biUnion A).card : ℝ) := by
    apply (mul_le_mul_iff_right₀ hJpos).1
    convert hb using 1
    ring
  have hc : θ*(H.card : ℝ) ≤ K*C*r^s*(G.card : ℝ) := by
    calc
      _ ≤ K*r^s*((J.biUnion A).card : ℝ) := hb'
      _ ≤ K*r^s*(C*(G.card : ℝ)) :=
        mul_le_mul_of_nonneg_left hsize (mul_nonneg hK (Real.rpow_nonneg hr0 _))
      _ = _ := by ring
  have hd : (H.card : ℝ) ≤ (K*C*r^s*(G.card : ℝ))/θ :=
    (le_div_iff₀ hθ).2 (by simpa only [mul_comm] using hc)
  exact hd.trans_eq (by ring)

end Falconer

end OAI
