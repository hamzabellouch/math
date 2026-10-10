import OAI.Probability.SLE.Gauge.RibbonCoordinateGeometry

namespace OAI

/-! The two strips outside the narrow core are in the actual surviving
component. Their connection to the unbounded future excludes filled hulls,
even when the stopped past is not simple. -/

noncomputable section
open Set Filter Metric
open scoped Topology NNReal

namespace SLEExactGauge.RibbonCoordinates

def sideCorridor (a b : ℝ) : Set ℂ :=
  {z | 0 < z.re ∧ z.im ∈ Ioo a b}

theorem sideCorridor_convex (a b : ℝ) : Convex ℝ (sideCorridor a b) := by
  exact (convex_halfSpace_gt Complex.reLm.isLinear 0).inter
    ((convex_Ioo a b).is_linear_preimage Complex.imLm.isLinear)

/-- A strip strictly outside the past's core connects to the free future
and hence is in the unbounded surviving domain. This covers either side. -/
theorem sideCorridor_survives
    (P : ℂ → ℂ) (hP : ContinuousOn P closedRibbon) (hi : InjOn P closedRibbon)
    (hH : ∀ z ∈ closedRibbon, 0 < z.re → P z ∈ upperHalfPlane)
    (γ : ℝ≥0 → ℂ) (T : ℝ≥0) {k ε a b : ℝ} (hk : 0 ≤ k)
    (hab : a < b) (ha : -1 ≤ a) (hb : b ≤ 1)
    (hgap : ∀ x ∈ Ioo a b, ε < |x|)
    (hpast : γ '' Icc 0 T ⊆
      P '' {z ∈ closedRibbon | z.re ≤ k ∧ |z.im| ≤ ε})
    (hunbounded : ¬ Bornology.IsBounded (P '' futureRibbon k)) :
    P '' sideCorridor a b ⊆ survivingDomain γ T := by
  have hsideSub : sideCorridor a b ⊆ closedRibbon := by
    intro z hz
    exact ⟨hz.1.le, (abs_lt.mpr ⟨ha.trans_lt hz.2.1, hz.2.2.trans_le hb⟩).le⟩
  have hfutureSub := futureRibbon_subset_closedRibbon hk
  let S := sideCorridor a b ∪ futureRibbon k
  have hSsub : S ⊆ closedRibbon := union_subset hsideSub hfutureSub
  let z : ℂ := ((k + 1 : ℝ) : ℂ) + (((a + b) / 2 : ℝ) : ℂ) * Complex.I
  have hzre : z.re = k + 1 := by simp [z]
  have hzim : z.im = (a + b) / 2 := by simp [z]
  have hzm : z.im ∈ Ioo a b := by rw [hzim]; constructor <;> linarith
  have hzside : z ∈ sideCorridor a b := ⟨by rw [hzre]; linarith, hzm⟩
  have hzfuture : z ∈ futureRibbon k :=
    ⟨by rw [hzre]; linarith,
      abs_lt.mpr ⟨ha.trans_lt hzm.1, hzm.2.trans_le hb⟩⟩
  have hSconn : IsPreconnected S :=
    (sideCorridor_convex a b).isPreconnected.union z hzside hzfuture
      (futureRibbon_convex k).isPreconnected
  have hfree : P '' S ⊆ upperHalfPlane \ (γ '' Icc 0 T) := by
    rintro y ⟨u, hu, rfl⟩
    have huH : 0 < u.re := by
      rcases hu with hu | hu
      · exact hu.1
      · exact hk.trans_lt hu.1
    refine ⟨hH u (hSsub hu) huH, ?_⟩
    intro hp
    obtain ⟨v, hv, he⟩ := hpast hp
    have hvu := hi hv.1 (hSsub hu) he
    rw [hvu] at hv
    rcases hu with hu | hu
    · exact (not_le_of_gt (hgap u.im hu.2)) hv.2.2
    · exact (not_le_of_gt hu.1) hv.2.1
  have hSunbounded : ¬ Bornology.IsBounded (P '' S) := by
    intro hbound
    exact hunbounded (hbound.subset (image_mono subset_union_right))
  exact (image_mono subset_union_left).trans
    (free_preconnected_subset_surviving γ T (P '' S)
      (hSconn.image P (hP.mono hSsub)) hfree hSunbounded)

end SLEExactGauge.RibbonCoordinates

end

end OAI
