import OAI.Geometry.RCD.Sobolev.RadialSobolevTimeMeasurable
import OAI.Geometry.RCD.Coordinates.IntervalVectorExtension

namespace OAI

/-! # Continuous L2 values of a locally Lipschitz time cylinder -/

open Set Filter MeasureTheory Metric
open scoped Topology NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) [IsFiniteMeasureOnCompacts μ] (Q : QuadraticCheegerEnergy μ)

include Q in
theorem radial_continuous_L2_time_family (z : X) {r : ℝ} (hr : 0 < r)
    {a b : ℝ} (H : ℝ → X → ℝ) {L : ℝ≥0}
    (hH : LipschitzOnWith L (Function.uncurry H) (Ioo a b ×ˢ closedBall z (2*r))) :
    ∃ g : Ioo a b → Lp ℝ 2 μ, Continuous g ∧
      (∀ t, g t =ᵐ[μ] fun x => radialCutoff z r x*H t x) ∧
      ContinuousOn (intervalVectorExtension g) (Ioo a b) := by
  obtain ⟨W,hW,he⟩ := hH.extend_real
  obtain ⟨A,hA⟩ := (isCompact_Icc.prod (isCompact_closedBall z (2*r))).exists_bound_of_continuousOn
    hW.continuous.continuousOn
  let B : ℝ≥0 := ⟨max A 0,le_max_right _ _⟩
  have hs (t : Ioo a b) : LipschitzOnWith L (H t) (closedBall z (2*r)) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    have hb := hH.dist_le_mul (t,x) ⟨t.property,hx⟩ (t,y) ⟨t.property,hy⟩
    simpa only [Prod.dist_eq,dist_self,max_eq_right dist_nonneg,Function.uncurry] using hb
  have hb (t : Ioo a b) (x : X) (hx : x ∈ closedBall z (2*r)) : |H t x| ≤ B := by
    have hbound := hA ((t:ℝ),x) ⟨Ioo_subset_Icc_self t.property,hx⟩
    have heq := he (show ((t:ℝ),x) ∈ Ioo a b ×ˢ closedBall z (2*r) from ⟨t.property,hx⟩)
    change H t x = W (t,x) at heq
    rw [heq]
    exact (show |W (t,x)| ≤ A by simpa only [Real.norm_eq_abs] using hbound).trans (le_max_left _ _)
  have htime (x : X) (hx : x ∈ closedBall z (2*r)) : Continuous (fun t : Ioo a b => H t x) := by
    have hwc : Continuous (fun t : Ioo a b => W (t,x)) :=
      hW.continuous.comp (continuous_subtype_val.prodMk continuous_const)
    apply hwc.congr
    intro t
    exact (he (show ((t:ℝ),x) ∈ Ioo a b ×ˢ closedBall z (2*r) from ⟨t.property,hx⟩)).symm
  let g := fun t : Ioo a b => SobolevSpace.toLp μ Q (radialLocalSobolev μ Q z hr (hs t) (hb t))
  have hg : Continuous g := radialLocalSobolev_toLp_continuous μ Q z hr
    (fun t : Ioo a b => H t) L B hs hb htime
  refine ⟨g,hg,fun t => radialLocalSobolev_coe μ Q z hr (hs t) (hb t),?_⟩
  apply continuousOn_iff_continuous_domRestrict.mpr
  change Continuous (fun t : Ioo a b => intervalVectorExtension g t)
  simpa only [intervalVectorExtension_eq] using hg

end RegularPointCoordinates

end

end OAI
