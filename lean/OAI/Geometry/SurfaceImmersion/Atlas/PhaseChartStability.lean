import OAI.Geometry.SurfaceImmersion.Atlas.GoodPhaseC2Stability
import OAI.Geometry.SurfaceImmersion.Atlas.GoodPhaseCover
import OAI.Geometry.SurfaceImmersion.Geometry.CompactRealJetNeighborhood
import OAI.Geometry.Immersion.ClosedSurface.CoordinateBounds
import OAI.Geometry.SurfaceImmersion.Geometry.CompactLocalBounds

namespace OAI

/-! A fixed good phase chart remains admissible throughout a C2 neighborhood. -/
noncomputable section
open Set TopologicalSpace
open scoped ContDiff
namespace ClosedSurfaceR4.RealModes
open SmallModes WeightedEstimates

lemma norm_realTwoJet_le_on {U : Set Base} (hU : IsOpen U) {F : RField 4}
    (hF : ContDiff ℝ ∞ F) {C : ℝ} (hC : 0 ≤ C)
    (hb : WeightedBound U 1 2 C F) {p : Base} (hp : p ∈ U) :
    ‖realTwoJet F p‖ ≤ C := by
  have h1 (v : Base) (hv : ‖v‖ = 1) : WeightedBound U 1 1 C (coordDeriv v F) := by
    change WeightedBound U 1 1 C (fun x => fderiv ℝ F x v)
    simpa only [hv,div_one,one_mul] using hb.directional hU zero_lt_one hF.contDiffOn v
  have h2 (v w : Base) (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) :
      ‖coordDeriv v (coordDeriv w F) p‖ ≤ C := by
    have hd := (h1 w hw).directional hU zero_lt_one (contDiff_real_coordDeriv hF w).contDiffOn v
    simpa only [coordDeriv,hv,div_one,one_mul] using hd.norm_le hp
  have hx : ‖dx‖ = 1 := by simp [dx]
  have hy : ‖dy‖ = 1 := by simp [dy]
  apply (pi_norm_le_iff_of_nonneg hC).mpr
  intro i
  fin_cases i
  · exact (h1 dx hx).norm_le hp
  · exact (h1 dy hy).norm_le hp
  · exact h2 dx dx hx hx
  · exact h2 dx dy hx hy
  · exact h2 dy dy hy hy

theorem compact_twoJet_comp_bound {T : Base → Base} (hT : ContDiff ℝ ∞ T)
    (K : Compacts Base) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ (F : RField 4), ContDiff ℝ ∞ F → ∀ C : ℝ,
      0 ≤ C → WeightedBound univ 1 2 C F →
      ∀ p ∈ (K : Set Base), ‖realTwoJet (F ∘ T) p‖ ≤ D*C := by
  obtain ⟨r,hr⟩ := K.isCompact.isBounded.subset_ball (0 : Base)
  obtain ⟨B,hB,hb⟩ := compact_local_weighted_bound Metric.isOpen_ball isOpen_univ
    (isCompact_closedBall (0 : Base) r) Metric.ball_subset_closedBall (subset_univ _)
    hT.contDiffOn 2
  let D : ℝ := ((2 : ℕ).factorial : ℝ)*B^2
  have hD : 1 ≤ D := by dsimp [D]; nlinarith [sq_nonneg (B-1)]
  refine ⟨D,hD,?_⟩
  intro F hF C hC hFC p hp
  have hcoord (j : ℕ) (_ : 1 ≤ j) (hj : j ≤ 2) (x : Base)
      (hx : x ∈ Metric.ball (0 : Base) r) :
      ‖iteratedFDerivWithin ℝ j T (Metric.ball (0 : Base) r) x‖ ≤ B := by
    simpa only [one_pow,one_mul] using hb 1 zero_le_one le_rfl j hj x hx
  have hc := hFC.comp_coordinates Metric.isOpen_ball.uniqueDiffOn uniqueDiffOn_univ
    zero_lt_one le_rfl hB hC hT.contDiffOn hF.contDiffOn (mapsTo_univ _ _) hcoord
  have hn := norm_realTwoJet_le_on Metric.isOpen_ball (hF.comp hT) (by positivity) hc (hr hp)
  simpa only [D,mul_assoc,mul_left_comm,mul_comm] using hn

end ClosedSurfaceR4.RealModes

namespace ClosedSurfaceR4.PhaseGeometry
open SmallModes RealModes WeightedEstimates

/-- The compact jet neighborhood and radius are fixed before the perturbed
map, using the smooth inverse of the reference map. -/
theorem GoodPhaseChart.uniform_jet_neighborhood {F : RField 4} (hF : ContDiff ℝ ∞ F)
    {φ : Base → ℝ} (c : GoodPhaseChart F φ) :
    ∃ (ρ : ℝ) (Q : Set RealTwoJet), 0 < ρ ∧ IsCompact Q ∧ Q ⊆ admissibleRealJets ∧
      ∀ (G : RField 4), ContDiff ℝ ∞ G → ∀ C : ℝ, 0 ≤ C → C < ρ →
      WeightedBound univ 1 2 C (G-F) →
      MapsTo (realTwoJet (G ∘ c.chart.symm)) c.chart.target Q ∧
        RealModeDomain (G ∘ c.chart.symm) c.chart.target := by
  obtain ⟨ε,Q,hε,hQ,hQa,hclose⟩ := compact_real_jet_neighborhood (hF.comp c.smoothInverse)
    c.targetCompact (fun p hp => c.good.determinant p (c.targetInside hp))
    (fun p hp => c.good.good p (c.targetInside hp))
  obtain ⟨D,hD,hd⟩ := compact_twoJet_comp_bound c.smoothInverse c.targetCompact
  have hDp : 0 < D := zero_lt_one.trans_le hD
  refine ⟨ε/D,Q,div_pos hε hDp,hQ,hQa,?_⟩
  intro G hG C hC hCρ hb
  have hDC : D*C < ε := by
    simpa only [mul_comm] using (lt_div_iff₀ hDp).mp hCρ
  have hsmall (p : Base) (hp : p ∈ (c.targetCompact : Set Base)) :
      ‖realTwoJet (G ∘ c.chart.symm) p - realTwoJet (F ∘ c.chart.symm) p‖ < ε := by
    have hj := hd (G-F) (hG.sub hF) C hC hb p hp
    have he : (G-F) ∘ c.chart.symm = (G ∘ c.chart.symm) - (F ∘ c.chart.symm) := rfl
    rw [he,realTwoJet_sub (hG.comp c.smoothInverse) (hF.comp c.smoothInverse)] at hj
    exact hj.trans_lt hDC
  have hmaps : MapsTo (realTwoJet (G ∘ c.chart.symm)) c.chart.target Q :=
    fun p hp => hclose (G ∘ c.chart.symm) hsmall (c.targetBound hp)
  refine ⟨hmaps,c.chart.open_target,?_,?_⟩
  · intro p hp
    exact (hQa (hmaps hp)).1
  · intro p hp
    exact (hQa (hmaps hp)).2

end ClosedSurfaceR4.PhaseGeometry

end

end OAI
