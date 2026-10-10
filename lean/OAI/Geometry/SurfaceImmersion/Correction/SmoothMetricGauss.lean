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

private lemma inverseMetricPair_smoothOn {U : Set Base}
    {E F G a b c d : Base → ℝ} (hE : ContDiffOn ℝ ∞ E U) (hF : ContDiffOn ℝ ∞ F U)
    (hG : ContDiffOn ℝ ∞ G U) (ha : ContDiffOn ℝ ∞ a U) (hb : ContDiffOn ℝ ∞ b U)
    (hc : ContDiffOn ℝ ∞ c U) (hd : ContDiffOn ℝ ∞ d U)
    (hdet : ∀ x ∈ U, E x*G x-(F x)^2 ≠ 0) :
    ContDiffOn ℝ ∞ (fun x => inverseMetricPair (E x) (F x) (G x) (a x) (b x) (c x) (d x)) U :=
  ((((hG.mul ha).mul hc).sub (hF.mul ((ha.mul hd).add (hb.mul hc)))).add
    ((hE.mul hb).mul hd)).div ((hE.mul hG).sub (hF.pow 2)) hdet

lemma coordinateGauss_smoothOn {U : Set Base} {E F G : Base → ℝ}
    (hE : ContDiff ℝ ∞ E) (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G)
    (hdet : ∀ x ∈ U, E x*G x-(F x)^2 ≠ 0) :
    ContDiffOn ℝ ∞ (coordinateGauss E F G) U := by
  have he₁ := (scalar_partial_smooth hE dx).contDiffOn (s := U)
  have he₂ := (scalar_partial_smooth hE dy).contDiffOn (s := U)
  have hf₁ := (scalar_partial_smooth hF dx).contDiffOn (s := U)
  have hf₂ := (scalar_partial_smooth hF dy).contDiffOn (s := U)
  have hg₁ := (scalar_partial_smooth hG dx).contDiffOn (s := U)
  have hg₂ := (scalar_partial_smooth hG dy).contDiffOn (s := U)
  have hraw : ContDiffOn ℝ ∞ (fun p => (2*coordDeriv dx (coordDeriv dy F) p-
      coordDeriv dy (coordDeriv dy E) p-coordDeriv dx (coordDeriv dx G) p)/2) U := by
    exact ((contDiffOn_const.mul
      (scalar_partial_smooth (scalar_partial_smooth hF dy) dx).contDiffOn).sub
      (scalar_partial_smooth (scalar_partial_smooth hE dy) dy).contDiffOn |>.sub
      (scalar_partial_smooth (scalar_partial_smooth hG dx) dx).contDiffOn).div_const 2
  exact (hraw.sub (inverseMetricPair_smoothOn hE.contDiffOn
    hF.contDiffOn hG.contDiffOn (he₁.div_const 2)
    (hf₁.sub (he₂.div_const 2)) (hf₂.sub (hg₁.div_const 2)) (hg₂.div_const 2) hdet)).add
    (inverseMetricPair_smoothOn hE.contDiffOn
      hF.contDiffOn hG.contDiffOn (he₂.div_const 2)
      (hg₁.div_const 2) (he₂.div_const 2) (hg₁.div_const 2) hdet)


end ClosedSurfaceR4.RealModes

end

end OAI
