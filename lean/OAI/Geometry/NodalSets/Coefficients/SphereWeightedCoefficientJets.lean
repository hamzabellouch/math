import OAI.Geometry.NodalSets.Coefficients.CorrectionProductBounds
import OAI.Geometry.NodalSets.Coefficients.SphereCoefficientScalarBounds
import OAI.Geometry.NodalSets.Elliptic.RealPartialJetLinearity

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry Yau.Analysis Metric
open scoped ContDiff
noncomputable section

theorem sphere_weighted_coefficient_scalar_jet_bound (J : ℕ)
    (L : CoefficientPoint BaseModel →L[ℝ] ℝ) :
    ∃ C > 0, ∀ (P : Finset Base) (d b : SphereEnergyData),
      ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ d.density → ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ b.density →
      ∀ p ∈ P, ∀ x ∈ closedBall (0 : Yau.Jets.Coord) 1,
      ∀ ds : List (Fin 4), ds.length ≤ J →
      |partialJet (fun y ↦ roundCoordDensity y * L (intrinsicChartCoefficient b.tensor b.density p (seedCoordEquiv y))) ds x-
        partialJet (fun y ↦ roundCoordDensity y * L (intrinsicChartCoefficient d.tensor d.density p (seedCoordEquiv y))) ds x| ≤
        C * sphereCoefficientDistance P J d.tensor d.density b.tensor b.density := by
  obtain ⟨K,hK,hKb⟩ := compact_multiplier_frequency_bound roundCoordDensity roundCoordDensity_smooth
    (isCompact_closedBall (0 : Yau.Jets.Coord) 1) J
  let H := (‖L‖+1) * (max 1 ‖seedCoordEquiv.toContinuousLinearMap‖)^J
  have hH : 0 < H := by dsimp [H]; positivity
  refine ⟨K*H,mul_pos hK hH,?_⟩
  intro P d b hd hb p hp x hx ds hds
  have hdc := intrinsic_coefficient_chart_smooth d.tensor d.smooth d.symm d.pos d.density hd
  have hbc := intrinsic_coefficient_chart_smooth b.tensor b.smooth b.symm b.pos b.density hb
  let D := sphereCoefficientDistance P J d.tensor d.density b.tensor b.density
  have hD : 0 ≤ D := sphereCoefficientDistance_nonneg P J d.tensor b.tensor d.density b.density
    (fun q _ ↦ hdc q) (fun q _ ↦ hbc q)
  let F : Yau.Jets.Coord → ℝ := fun y ↦ L (intrinsicChartCoefficient b.tensor b.density p (seedCoordEquiv y)-
    intrinsicChartCoefficient d.tensor d.density p (seedCoordEquiv y))
  have hF : ContDiff ℝ ∞ F := by
    simpa only [F,Function.comp_def] using
      (ContinuousLinearMap.contDiff L).comp (((hbc p).sub (hdc p)).comp seedCoordEquiv.contDiff)
  have hFb : ∀ k, k ≤ J → ‖iteratedFDeriv ℝ k F x‖ ≤ H*D := by
    intro k hk
    apply (sphereCoefficientDistance_scalar_derivative_bound P J d b hd hb L p hp x hx k hk).trans
    apply mul_le_mul_of_nonneg_right _ hD
    dsimp [H]
    gcongr
    linarith
  have hmult := hKb F hF 1 (H*D) le_rfl (mul_nonneg hH.le hD) 0 x hx
    (fun k hk ↦ by simpa only [one_pow,mul_one] using hFb k hk) ds.length hds
  simp only [one_pow,mul_one] at hmult
  have hsub : (fun y ↦ roundCoordDensity y * L (intrinsicChartCoefficient b.tensor b.density p (seedCoordEquiv y))-
      roundCoordDensity y * L (intrinsicChartCoefficient d.tensor d.density p (seedCoordEquiv y))) =
      fun y ↦ roundCoordDensity y * F y := by
    funext y
    simp only [F,map_sub,mul_sub]
  have hbs : ContDiff ℝ ∞ (fun y ↦ roundCoordDensity y * L (intrinsicChartCoefficient b.tensor b.density p (seedCoordEquiv y))) := by
    simpa only [Function.comp_def] using roundCoordDensity_smooth.mul
      ((ContinuousLinearMap.contDiff L).comp ((hbc p).comp seedCoordEquiv.contDiff))
  have hds : ContDiff ℝ ∞ (fun y ↦ roundCoordDensity y * L (intrinsicChartCoefficient d.tensor d.density p (seedCoordEquiv y))) := by
    simpa only [Function.comp_def] using roundCoordDensity_smooth.mul
      ((ContinuousLinearMap.contDiff L).comp ((hdc p).comp seedCoordEquiv.contDiff))
  rw [← partialJet_sub _ _ hbs hds,hsub]
  exact (partialJet_norm_le_iterated _ (roundCoordDensity_smooth.mul hF) ds x).trans
    (hmult.trans_eq (by dsimp [D]; ring))

end
end Yau.Target

end OAI
