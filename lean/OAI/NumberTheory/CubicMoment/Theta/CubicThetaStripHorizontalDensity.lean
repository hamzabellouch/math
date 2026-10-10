import OAI.NumberTheory.CubicMoment.Theta.CubicThetaStripRepresentative
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

namespace OAI

/-! Compact radial tests recover the horizontal Fourier coefficient
of an arbitrary cusp L2 vector at almost every height. -/
noncomputable section
open MeasureTheory Set
open scoped CompactlySupported ContDiff
namespace CubicFirstMoment

def cubicThetaStripHorizontalDensity (F : CubicThetaStripL2) (h : Eisenstein) (v : ℝ) : ℂ :=
  ∫ z in cubicThetaHorizontalCell,
    star (Real.fourierChar (tracePair z (cubicThetaRowFrequency h)):ℂ)*
      cubicThetaStripRepresentative F (z,v)/(v:ℂ)^3

lemma cubicThetaStripHorizontalDensity_integrable (F : CubicThetaStripL2) (h : Eisenstein) :
    IntegrableOn (cubicThetaStripHorizontalDensity F h) (Ioi (2:ℝ)) := by
  have hi := cubicThetaStripRepresentative_integrable F
  change Integrable (fun y : ℂ × ℝ => cubicThetaStripRepresentative F y/(y.2:ℂ)^3)
    (((volume : Measure ℂ).prod (volume : Measure ℝ)).restrict
      (cubicThetaHorizontalCell ×ˢ Ioi (2:ℝ))) at hi
  rw [←Measure.prod_restrict] at hi
  have hc : Continuous (fun y : ℂ × ℝ =>
      star (Real.fourierChar (tracePair y.1 (cubicThetaRowFrequency h)):ℂ)) := by
    unfold tracePair
    fun_prop
  have hb := hi.bdd_mul hc.aestronglyMeasurable (c:=1)
    (Filter.Eventually.of_forall (fun y => by simp))
  have he := hb.integral_prod_right
  apply he.congr
  filter_upwards with v
  unfold cubicThetaStripHorizontalDensity
  apply integral_congr_ae
  filter_upwards with z
  ring

lemma cubicThetaStripHorizontalDensity_pairing (F : CubicThetaStripL2) (h : Eisenstein)
    (W : C_c(ℝ,ℂ)) :
    inner ℂ (cubicThetaCuspFourierTest h W) F=
      ∫ v in Ioi (2:ℝ),star (W v)*cubicThetaStripHorizontalDensity F h v := by
  rw [cubicThetaStripRepresentative_pairing]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro v _
  dsimp only
  unfold cubicThetaStripHorizontalDensity
  rw [integral_div]
  ring

theorem cubicThetaStripHorizontalDensity_zero (F : CubicThetaStripL2) (h : Eisenstein)
    (hzero : ∀ W : C_c(ℝ,ℂ), (∀ v≤(2:ℝ),W v=0) →
      inner ℂ (cubicThetaCuspFourierTest h W) F=0) :
    ∀ᵐ v ∂volume, v∈Ioi (2:ℝ) → cubicThetaStripHorizontalDensity F h v=0 := by
  apply isOpen_Ioi.ae_eq_zero_of_integral_contDiff_smul_eq_zero
    (cubicThetaStripHorizontalDensity_integrable F h).locallyIntegrableOn
  intro g hg hgs hs
  let W : C_c(ℝ,ℂ) :=
    ⟨⟨fun v => (g v:ℂ),Complex.continuous_ofReal.comp hg.continuous⟩,
      hgs.comp_left Complex.ofReal_zero⟩
  have hW (v : ℝ) (hv : v≤2) : W v=0 := by
    have hz : g v=0 := image_eq_zero_of_notMem_tsupport
      (fun hv' => (not_lt_of_ge hv) (hs hv'))
    change (g v:ℂ)=0
    rw [hz,Complex.ofReal_zero]
  have he := hzero W hW
  rw [cubicThetaStripHorizontalDensity_pairing] at he
  have hf : (∫ v in Ioi (2:ℝ), g v • cubicThetaStripHorizontalDensity F h v)=0 := by
    simpa only [W,CompactlySupportedContinuousMap.coe_mk,ContinuousMap.coe_mk,
      Complex.star_def,Complex.conj_ofReal,Complex.real_smul] using he
  rw [←setIntegral_eq_integral_of_forall_compl_eq_zero (s:=Ioi (2:ℝ))]
  · exact hf
  · intro v hv
    have hz : g v=0 := image_eq_zero_of_notMem_tsupport (fun hv' => hv (hs hv'))
    rw [hz,zero_smul]

end CubicFirstMoment

end

end OAI
