import OAI.Geometry.SurfaceImmersion.Geometry.MetricGaussInvariance

namespace OAI

/-! A bound fixed by the prescribed metric before any oscillatory loop is
selected; it applies to every exact local realization of that metric. -/
noncomputable section
open Set Filter
open scoped ContDiff Matrix Topology
namespace ClosedSurfaceR4.RealModes
open SmallModes

private lemma scalar_partial_smooth {f : Base → ℝ} (hf : ContDiff ℝ ∞ f) (v : Base) :
    ContDiff ℝ ∞ (coordDeriv v f) :=
  (hf.fderiv_right (by simp)).clm_apply contDiff_const

private lemma inverseMetricPair_continuousOn {U : Set Base}
    {E F G a b c d : Base → ℝ} (hE : ContinuousOn E U) (hF : ContinuousOn F U)
    (hG : ContinuousOn G U) (ha : ContinuousOn a U) (hb : ContinuousOn b U)
    (hc : ContinuousOn c U) (hd : ContinuousOn d U)
    (hdet : ∀ x ∈ U, E x*G x-(F x)^2 ≠ 0) :
    ContinuousOn (fun x => inverseMetricPair (E x) (F x) (G x) (a x) (b x) (c x) (d x)) U :=
  ((((hG.mul ha).mul hc).sub (hF.mul ((ha.mul hd).add (hb.mul hc)))).add
    ((hE.mul hb).mul hd)).div ((hE.mul hG).sub (hF.pow 2)) hdet

lemma coordinateGauss_continuousOn {U : Set Base} {E F G : Base → ℝ}
    (hE : ContDiff ℝ ∞ E) (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G)
    (hdet : ∀ x ∈ U, E x*G x-(F x)^2 ≠ 0) :
    ContinuousOn (coordinateGauss E F G) U := by
  have he₁ := (scalar_partial_smooth hE dx).continuous.continuousOn (s := U)
  have he₂ := (scalar_partial_smooth hE dy).continuous.continuousOn (s := U)
  have hf₁ := (scalar_partial_smooth hF dx).continuous.continuousOn (s := U)
  have hf₂ := (scalar_partial_smooth hF dy).continuous.continuousOn (s := U)
  have hg₁ := (scalar_partial_smooth hG dx).continuous.continuousOn (s := U)
  have hg₂ := (scalar_partial_smooth hG dy).continuous.continuousOn (s := U)
  have hraw : ContinuousOn (fun p => (2*coordDeriv dx (coordDeriv dy F) p-
      coordDeriv dy (coordDeriv dy E) p-coordDeriv dx (coordDeriv dx G) p)/2) U := by
    exact ((continuousOn_const.mul
      (scalar_partial_smooth (scalar_partial_smooth hF dy) dx).continuous.continuousOn).sub
      (scalar_partial_smooth (scalar_partial_smooth hE dy) dy).continuous.continuousOn |>.sub
      (scalar_partial_smooth (scalar_partial_smooth hG dx) dx).continuous.continuousOn).div_const 2
  exact (hraw.sub (inverseMetricPair_continuousOn hE.continuous.continuousOn
    hF.continuous.continuousOn hG.continuous.continuousOn (he₁.div_const 2)
    (hf₁.sub (he₂.div_const 2)) (hf₂.sub (hg₁.div_const 2)) (hg₂.div_const 2) hdet)).add
    (inverseMetricPair_continuousOn hE.continuous.continuousOn
      hF.continuous.continuousOn hG.continuous.continuousOn (he₂.div_const 2)
      (hg₁.div_const 2) (he₂.div_const 2) (hg₁.div_const 2) hdet)

theorem compact_metric_gauss_bound {C : Set Base} (hC : IsCompact C)
    {E F G : Base → ℝ} (hE : ContDiff ℝ ∞ E) (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G)
    (hdet : ∀ x ∈ C, E x*G x-(F x)^2 ≠ 0) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ H : RField 4, ContDiff ℝ ∞ H → ∀ p ∈ C,
      NormalFrame.gramDet (coordDeriv dx H p) (coordDeriv dy H p) ≠ 0 →
      realMetric H dx dx =ᶠ[𝓝 p] E → realMetric H dx dy =ᶠ[𝓝 p] F →
      realMetric H dy dy =ᶠ[𝓝 p] G →
      |realSecondForm H dx dx p ⬝ᵥ realSecondForm H dy dy p-
        realSecondForm H dx dy p ⬝ᵥ realSecondForm H dx dy p| ≤ K := by
  have hc := coordinateGauss_continuousOn hE hF hG hdet
  obtain ⟨B,hB⟩ := (hC.image_of_continuousOn hc.abs).bddAbove
  refine ⟨max 1 B,le_max_left _ _,?_⟩
  intro H hH p hp hD he hf hg
  rw [gauss_of_metric_germ hH p hD he hf hg]
  exact (hB (mem_image_of_mem _ hp)).trans (le_max_right _ _)

end ClosedSurfaceR4.RealModes

end

end OAI
