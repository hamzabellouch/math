import OAI.MeasureTheory.Falconer.Estimates.PopularRegularity

namespace OAI

/-! A common regular parameter set extracted from a family of regular rows.
The loss is explicit and polynomial in the union-to-row cardinality ratio. -/
namespace Falconer

theorem common_regular_family {α : Type*} (J : Finset α) (hJ : J.Nonempty)
    (A : α → Finset (Space 2)) {δ s K m R : ℝ}
    (hδ : 0 ≤ δ) (hK : 0 ≤ K) (hm : 0 < m) (hR : 0 < R)
    (hsize : ∀ j ∈ J, m ≤ ((A j).card : ℝ))
    (hunion : ((J.biUnion A).card : ℝ) ≤ R*m)
    (hA : ∀ j ∈ J, NormalizedFiniteBallBound δ s K (A j)) :
    ∃ G ⊆ J.biUnion A, m/2 ≤ (G.card : ℝ) ∧
      NormalizedFiniteBallBound δ s (4*R^2*K) G ∧
      m*(J.card : ℝ)/2 ≤ ∑ x ∈ G, familyDegree J A x := by
  obtain ⟨G,hGU,hGcard,hGmass,hdegree⟩ := family_popular_selection J A hJ hm hsize
  have hGpos : 0 < (G.card : ℝ) := (half_pos hm).trans_le hGcard
  have hUpos : 0 < ((J.biUnion A).card : ℝ) :=
    hGpos.trans_le (Nat.cast_le.mpr (Finset.card_le_card hGU))
  have hc : ((J.biUnion A).card : ℝ) ≤ (2*R)*(G.card : ℝ) := by
    nlinarith [mul_le_mul_of_nonneg_left hGcard hR.le]
  have hd (x : Space 2) (hx : x ∈ G) :
      (1/(2*R))*(J.card : ℝ) ≤ familyDegree J A x := by
    have hr : 1/(2*R) ≤ m/(2*((J.biUnion A).card : ℝ)) := by
      apply (div_le_div_iff₀ (by positivity : 0 < 2*R) (by positivity : 0 < 2*((J.biUnion A).card : ℝ))).2
      nlinarith
    have hh := mul_le_mul_of_nonneg_right hr (Nat.cast_nonneg J.card)
    have he : m/(2*((J.biUnion A).card : ℝ))*(J.card : ℝ) =
        m*(J.card : ℝ)/(2*((J.biUnion A).card : ℝ)) := by ring
    rw [he] at hh
    exact hh.trans (hdegree x hx)
  have hreg := popular_family_regular J hJ A hδ hK (by positivity : 0 < 1/(2*R)) hA G hc hd
  have he : K*(2*R)/(1/(2*R)) = 4*R^2*K := by field_simp; ring
  rw [he] at hreg
  exact ⟨G,hGU,hGcard,hreg,hGmass⟩

theorem popular_family_rows {α : Type*} (J : Finset α) (A : α → Finset (Space 2))
    (G : Finset (Space 2)) (hG : G ⊆ J.biUnion A) {m R : ℝ} (hm : 0 < m) (_hR : 0 ≤ R)
    (hunion : ((J.biUnion A).card : ℝ) ≤ R*m)
    (hmass : m*(J.card : ℝ)/2 ≤ ∑ x ∈ G, familyDegree J A x) :
    ∃ Y ⊆ J, (J.card : ℝ) ≤ 4*R*(Y.card : ℝ) ∧
      ∀ j ∈ Y, m/4 ≤ ((G ∩ A j).card : ℝ) := by
  let w := fun j => ((G ∩ A j).card : ℝ)
  have ht : m*(J.card : ℝ)/2 ≤ ∑ j ∈ J, w j := by
    simpa only [familyDegree_restrict_sum,w] using hmass
  have hb := finite_popular_mass J w (show 0 ≤ m/4 by positivity) ht
    (show (m/4)*(J.card : ℝ) ≤ (m*(J.card : ℝ)/2)/2 by nlinarith)
    (fun j _ => (Nat.cast_le.mpr (Finset.card_le_card
      (show G ∩ A j ⊆ J.biUnion A from fun x hx => hG (Finset.mem_inter.mp hx).1))).trans hunion)
  refine ⟨J.filter (fun j => m/4 ≤ w j),Finset.filter_subset _ _,?_,?_⟩
  · have hb' := hb.2
    have hm' := mul_pos hm (show (0 : ℝ) < 1/4 by norm_num)
    nlinarith
  · intro j hj
    exact (Finset.mem_filter.mp hj).2

end Falconer

end OAI
