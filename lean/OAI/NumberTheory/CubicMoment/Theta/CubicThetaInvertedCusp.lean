import OAI.NumberTheory.CubicMoment.Theta.CubicThetaInversionRestriction
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaResidueInversion

namespace OAI

/-! Bounded Fourier observations at the inverted cusp, with their
literal initial values and the now identified full spectral residue. -/
noncomputable section
open Filter Topology MeasureTheory
namespace CubicFirstMoment

def cubicThetaInvertedForcedCusp (s : ℂ) : CubicThetaStripL2 :=
  cubicThetaCuspRestriction (cubicThetaInversionEnergy (cubicThetaContinuedEnergyLift
    (cubicThetaGlobalSpectralParameter s) (cubicThetaForcingL2 s)))

lemma cubicThetaInvertedForcedCusp_meromorphic {s : ℂ} (hs : 1<s.re) :
    MeromorphicAt cubicThetaInvertedForcedCusp s :=
  cubicThetaMeromorphic_clm
    (cubicThetaCuspRestriction.comp cubicThetaInversionEnergy.toContinuousLinearMap)
    (cubicThetaForcedEnergy_meromorphic hs)

lemma cubicThetaInvertedForcedCusp_right {s : ℂ} (hs : 3<s.re) :
    cubicThetaInvertedForcedCusp s=
      cubicThetaInvertedFiniteRestriction (cubicThetaArithmeticFiniteEnergy s hs) := by
  rw [cubicThetaInvertedForcedCusp,←cubicThetaArithmeticEnergy_eq_continued hs,
    ←cubicThetaArithmeticFiniteEnergy_embedding s hs,cubicThetaCuspRestriction_inversion_finite]

lemma cubicThetaInvertedForcedCusp_coe {s : ℂ} (hs : 3<s.re) :
    cubicThetaInvertedForcedCusp s =ᵐ[cubicThetaPointMeasure.restrict (cubicThetaCuspStrip 2)]
      (fun p : CubicThetaPoint => cubicThetaEisenstein
        (cubicThetaMobius (cubicThetaFullComplex cubicThetaFullInversion) p.val) s) := by
  rw [cubicThetaInvertedForcedCusp_right hs]
  have he := (cubicThetaSection_strip_memLp
    (cubicThetaInversionSection (cubicThetaArithmeticFiniteEnergy s hs))
    (cubicThetaInversionSection_memLp _ (cubicThetaArithmeticFiniteEnergy s hs).property.2.1)).coeFn_toLp
  filter_upwards [he,ae_restrict_mem (cubicThetaCuspStrip_measurable 2)] with p hp hstrip
  have hv : (cubicThetaInvertedFiniteRestriction (cubicThetaArithmeticFiniteEnergy s hs)) p=
      cubicThetaArithmeticRemainder
        (cubicThetaMobius (cubicThetaFullComplex cubicThetaFullInversion) p.val) s := hp
  exact hv.trans (cubicThetaArithmeticRemainder_inverted
    (by have h:=hstrip.1; change 2<p.val.2 at h; linarith) s)

theorem cubicThetaInvertedForcedCusp_residue :
    Tendsto (fun s : ℂ => (s-4/3) • cubicThetaInvertedForcedCusp s)
      (𝓝[≠] (4/3:ℂ))
      (𝓝 (cubicThetaCuspRestriction (cubicThetaArithmeticResidueEnergy (4/3)))) := by
  have h := ((cubicThetaCuspRestriction.comp
      cubicThetaInversionEnergy.toContinuousLinearMap).continuous.tendsto _).comp
    (cubicThetaForcedEnergy_residue (σ:=(4/3:ℝ)) (by norm_num) (by norm_num))
  simpa only [Function.comp_def,ContinuousLinearMap.comp_apply,LinearIsometry.coe_toContinuousLinearMap,
    map_smul,Complex.ofReal_div,Complex.ofReal_ofNat,cubicThetaInvertedForcedCusp,
    cubicThetaArithmeticResidueEnergy_inversion] using h

def cubicThetaInvertedCuspObservable (T : CubicThetaStripL2) (s : ℂ) : ℂ :=
  inner ℂ T (cubicThetaInvertedForcedCusp s)

theorem cubicThetaInvertedCuspObservable_meromorphic (T : CubicThetaStripL2)
    {s : ℂ} (hs : 1<s.re) : MeromorphicAt (cubicThetaInvertedCuspObservable T) s :=
  cubicThetaMeromorphic_clm (innerSL ℂ T) (cubicThetaInvertedForcedCusp_meromorphic hs)

theorem cubicThetaInvertedCuspObservable_residue (T : CubicThetaStripL2) :
    Tendsto (fun s : ℂ => (s-4/3)*cubicThetaInvertedCuspObservable T s)
      (𝓝[≠] (4/3:ℂ))
      (𝓝 (inner ℂ T (cubicThetaCuspRestriction (cubicThetaArithmeticResidueEnergy (4/3))))) := by
  have h := ((innerSL ℂ T).continuous.tendsto _).comp cubicThetaInvertedForcedCusp_residue
  simpa only [Function.comp_def,innerSL_apply_apply,inner_smul_right,
    cubicThetaInvertedCuspObservable] using h

end CubicFirstMoment

end

end OAI
