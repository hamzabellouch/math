import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPositiveStripRepresentative
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

namespace OAI

/-! Compact radial tests recover the horizontal Fourier coefficient
of an arbitrary cusp L2 vector at almost every height. -/
noncomputable section
open MeasureTheory Set
open scoped CompactlySupported ContDiff
namespace CubicFirstMoment
variable {ε : ℝ}

def cubicThetaPositiveStripHorizontalDensity (F : CubicThetaPositiveStripL2 ε) (h : Eisenstein) (v : ℝ) : ℂ :=
  ∫ z in cubicThetaHorizontalCell,
    star (Real.fourierChar (tracePair z (cubicThetaRowFrequency h)):ℂ)*
      cubicThetaPositiveStripRepresentative F (z,v)/(v:ℂ)^3

lemma cubicThetaPositiveStripHorizontalDensity_integrable (hε : 0<ε) (F : CubicThetaPositiveStripL2 ε) (h : Eisenstein) :
    IntegrableOn (cubicThetaPositiveStripHorizontalDensity F h) (Ioi ε) := by
  have hi := cubicThetaPositiveStripRepresentative_integrable hε F
  change Integrable (fun y : ℂ × ℝ => cubicThetaPositiveStripRepresentative F y/(y.2:ℂ)^3)
    (((volume : Measure ℂ).prod (volume : Measure ℝ)).restrict
      (cubicThetaHorizontalCell ×ˢ Ioi ε)) at hi
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
  unfold cubicThetaPositiveStripHorizontalDensity
  apply integral_congr_ae
  filter_upwards with z
  ring

lemma cubicThetaPositiveStripHorizontalDensity_pairing (hε : 0<ε) (F : CubicThetaPositiveStripL2 ε) (h : Eisenstein)
    (W : C_c(ℝ,ℂ)) :
    inner ℂ (cubicThetaPositiveStripFourierTest hε h W) F=
      ∫ v in Ioi ε,star (W v)*cubicThetaPositiveStripHorizontalDensity F h v := by
  rw [cubicThetaPositiveStripRepresentative_pairing hε]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro v _
  dsimp only
  unfold cubicThetaPositiveStripHorizontalDensity
  rw [integral_div]
  ring

theorem cubicThetaPositiveStripHorizontalDensity_zero (hε : 0<ε) (F : CubicThetaPositiveStripL2 ε) (h : Eisenstein)
    (hzero : ∀ W : C_c(ℝ,ℂ), (∀ v≤ε,W v=0) →
      ContDiff ℝ ∞ (W : ℝ → ℂ) →
      inner ℂ (cubicThetaPositiveStripFourierTest hε h W) F=0) :
    ∀ᵐ v ∂volume, v∈Ioi ε → cubicThetaPositiveStripHorizontalDensity F h v=0 := by
  apply isOpen_Ioi.ae_eq_zero_of_integral_contDiff_smul_eq_zero
    (cubicThetaPositiveStripHorizontalDensity_integrable hε F h).locallyIntegrableOn
  intro g hg hgs hs
  let W : C_c(ℝ,ℂ) :=
    ⟨⟨fun v => (g v:ℂ),Complex.continuous_ofReal.comp hg.continuous⟩,
      hgs.comp_left Complex.ofReal_zero⟩
  have hW (v : ℝ) (hv : v≤ε) : W v=0 := by
    have hz : g v=0 := image_eq_zero_of_notMem_tsupport
      (fun hv' => (not_lt_of_ge hv) (hs hv'))
    change (g v:ℂ)=0
    rw [hz,Complex.ofReal_zero]
  have hsm : ContDiff ℝ ∞ (W : ℝ → ℂ) := by
    change ContDiff ℝ ∞ (fun v => (g v:ℂ))
    exact Complex.ofRealCLM.contDiff.comp hg
  have he := hzero W hW hsm
  rw [cubicThetaPositiveStripHorizontalDensity_pairing hε] at he
  have hf : (∫ v in Ioi ε, g v • cubicThetaPositiveStripHorizontalDensity F h v)=0 := by
    simpa only [W,CompactlySupportedContinuousMap.coe_mk,ContinuousMap.coe_mk,
      Complex.star_def,Complex.conj_ofReal,Complex.real_smul] using he
  rw [←setIntegral_eq_integral_of_forall_compl_eq_zero (s:=Ioi ε)]
  · exact hf
  · intro v hv
    have hz : g v=0 := image_eq_zero_of_notMem_tsupport (fun hv' => hv (hs hv'))
    rw [hz,zero_smul]

end CubicFirstMoment

end

end OAI
