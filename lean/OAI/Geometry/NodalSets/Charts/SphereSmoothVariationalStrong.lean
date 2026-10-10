import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import OAI.Geometry.NodalSets.Charts.SphereChartScalarExtension
import OAI.Geometry.NodalSets.Charts.SphereSmoothGreenLocal
import OAI.Geometry.NodalSets.Spectral.SphereWeakResolvent

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry MeasureTheory
open scoped ContDiff
noncomputable section
local instance sphereSmoothStrongMeasurable : MeasurableSpace Base := borel Base
local instance sphereSmoothStrongBorel : BorelSpace Base := ⟨rfl⟩

theorem sphere_smooth_variational_to_intrinsic
    (d : SphereEnergyData) (u : SphereEnergySmooth d) (lam : ℝ)
    (hweak : ∀ v : SphereEnergyHilbert d,
      sphereCompletedDirichlet d (sphereEnergyToCompletion d u) v =
        lam * inner ℝ (sphereEnergyL2Linear d u) (sphereEnergyL2Map d v)) :
    ∀ p z,
      -intrinsicWeightedChartOperator d.tensor d.density
          (SphereEnergySmooth.toSmooth d u) p z =
        lam * (SphereEnergySmooth.toSmooth d u : Base → ℝ)
          ((extChartAt (𝓡 4) p).symm z) := by
  let f : Base → ℝ := SphereEnergySmooth.toSmooth d u
  have hf : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ f := (SphereEnergySmooth.toSmooth d u).property
  intro p z
  let D := Yau.weightedDiv roundCoordDensity (sphereChartFlux d.tensor f p)
  have hD : Continuous D :=
    (Yau.weightedDiv_smooth roundCoordDensity_smooth (fun x ↦ (roundCoordDensity_pos x).ne')
      (intrinsicRealVector_smooth d.tensor d.smooth d.symm d.pos f hf p)).continuous
  let R : Yau.Jets.Coord → ℝ := fun x ↦ roundCoordDensity x *
    (D x + lam * d.density (sphereChartCoordMap p x) * f (sphereChartCoordMap p x))
  have hR : Continuous R := roundCoordDensity_smooth.continuous.mul
    (hD.add ((continuous_const.mul (d.continuous.comp (sphereChartCoordMap_smooth p).continuous)).mul
      (spherePullback_smooth f hf p).continuous))
  have htest : ∀ phi : Yau.Jets.Coord → ℝ, ContDiff ℝ ∞ phi → HasCompactSupport phi →
      (∫ x, phi x • R x) = 0 := by
    intro phi hphi hc
    obtain ⟨F,hF,_,hval⟩ := sphere_chart_scalar_extension p phi hphi hc
    let v : SphereEnergySmooth d := (⟨F,hF⟩ : sphereSmoothFunctions)
    have hcomp : F ∘ sphereChartCoordMap p = phi := funext hval
    have hgreen := (sphere_smooth_green_compact_chart d.tensor d.smooth d.symm d.pos
      F f hF hf p (hcomp ▸ hc)).2
    have hw := hweak (sphereEnergyToCompletion d v)
    rw [sphereCompletedDirichlet_coe,sphereEnergyL2Map_coe] at hw
    have hi : inner ℝ (sphereEnergyL2Linear d u) (sphereEnergyL2Linear d v) =
        sphereWeightedPairing d.density f F :=
      sphereWeightedToLp_inner d.density d.continuous (fun x ↦ (d.positive x).le) f F
        hf.continuous hF.continuous
    rw [hi] at hw
    change sphereDirichletForm d.tensor f F = _ at hw
    rw [sphereDirichletForm_symm d.tensor d.symm,hgreen] at hw
    simp only [hval] at hw
    rw [sphereWeightedPairing,sphereReferenceMeasure_integral_chart p] at hw
    simp only [roundChartDensity_coord_eq,hval] at hw
    have hI : Integrable (fun x ↦ roundCoordDensity x * phi x * D x) :=
      ((roundCoordDensity_smooth.continuous.mul hphi.continuous).mul hD).integrable_of_hasCompactSupport
        (hc.mul_left.mul_right)
    have hJ : Integrable (fun x ↦ roundCoordDensity x *
        (d.density (sphereChartCoordMap p x) * f (sphereChartCoordMap p x) * phi x)) :=
      (roundCoordDensity_smooth.continuous.mul
        (((d.continuous.comp (sphereChartCoordMap_smooth p).continuous).mul
          (spherePullback_smooth f hf p).continuous).mul hphi.continuous)).integrable_of_hasCompactSupport
            (hc.mul_left.mul_left)
    calc
      _ = ∫ x, (roundCoordDensity x * phi x * D x) +
          lam * (roundCoordDensity x *
            (d.density (sphereChartCoordMap p x) * f (sphereChartCoordMap p x) * phi x)) := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun x ↦ by dsimp [R]; ring)
      _ = (∫ x, roundCoordDensity x * phi x * D x) +
          lam * (∫ x, roundCoordDensity x *
            (d.density (sphereChartCoordMap p x) * f (sphereChartCoordMap p x) * phi x)) := by
        rw [integral_add hI (hJ.const_mul lam),integral_const_mul]
      _ = 0 := by linarith
  have hae := ae_eq_zero_of_integral_contDiff_smul_eq_zero hR.locallyIntegrable htest
  have hzero : R = 0 := Measure.eq_of_ae_eq hae hR continuous_const
  let x := seedCoordEquiv.symm z
  have hx : seedCoordEquiv x = z := seedCoordEquiv.apply_symm_apply z
  have hres : D x + lam * d.density (sphereChartCoordMap p x) * f (sphereChartCoordMap p x) = 0 :=
    (mul_eq_zero.mp (congrFun hzero x)).resolve_left (roundCoordDensity_pos x).ne'
  rw [← hx,intrinsicRealOperator_pullback]
  change -((d.density (sphereChartCoordMap p x))⁻¹ * D x) = lam * f (sphereChartCoordMap p x)
  apply (mul_left_cancel₀ (d.positive (sphereChartCoordMap p x)).ne')
  rw [mul_neg,← mul_assoc,mul_inv_cancel₀ (d.positive (sphereChartCoordMap p x)).ne',one_mul]
  nlinarith

end
end Yau.Target

end OAI
