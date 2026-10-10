import Mathlib
import OAI.Analysis.CoulombIonization.ThomasFermi.PatchGap

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set
open scoped ENNReal

namespace CoulombAnalysis

local instance : Fact ((5/3:ℝ≥0∞) ≠ ⊤) := ⟨by finiteness⟩
local instance : Fact ((5/2:ℝ≥0∞) ≠ ⊤) := ⟨by finiteness⟩

local instance (R : ℝ) : MeasurableSpace (TFField R) := borel _
local instance (R : ℝ) : BorelSpace (TFField R) := ⟨rfl⟩
local instance (R : ℝ) : MeasurableSpace (TFLp (ballMeasure R)) := borel _
local instance (R : ℝ) : BorelSpace (TFLp (ballMeasure R)) := ⟨rfl⟩

lemma tfPowerDerivative_pair_measurable (R : ℝ) :
    Measurable (fun p : TFLp (ballMeasure R) × TFLp (ballMeasure R) =>
      ∫ z, tfPowerDerivative (p.1 z)*p.2 z ∂ballMeasure R) := by
  let f : (TFLp (ballMeasure R) × TFLp (ballMeasure R)) → ℝ → ℝ :=
    fun p t => ‖p.1+t • p.2‖^(5/3:ℝ)
  have hc : Continuous (Function.uncurry f) := by
    exact (continuous_fst.fst.add (continuous_snd.smul continuous_fst.snd)).norm.rpow_const
      (fun _ => Or.inr (by norm_num))
  have hm := (measurable_deriv_with_param hc).comp (measurable_id.prodMk (measurable_const (a := (0:ℝ))))
  convert hm using 1
  funext p
  exact (tfLp_kinetic_hasDerivAt p.1 p.2).deriv.symm

def tfPatchGap (R T : ℝ) (hT : 0 < T) (Φ : TFField R) (σ : TFLp (ballMeasure R)) : ℝ :=
  let ρ := tfPatchMinimizer R T hT Φ
  (1/2:ℝ)*tfCoulombL R (σ-ρ) (σ-ρ)+
    (∫ z, max (tfBallPotential R ρ z-Φ z) 0*σ z ∂ballMeasure R)

lemma tfPatchGap_eq_gradient (R T : ℝ) (hT : 0 < T) (Φ : TFField R)
    (σ : TFLp (ballMeasure R)) :
    tfPatchGap R T hT Φ σ =
      (1/2:ℝ)*tfCoulombL R (σ-tfPatchMinimizer R T hT Φ) (σ-tfPatchMinimizer R T hT Φ)+
      T*(∫ z, tfPowerDerivative (tfPatchMinimizer R T hT Φ z)*σ z ∂ballMeasure R)+
      tfPatchLinear R Φ σ+tfCoulombL R (tfPatchMinimizer R T hT Φ) σ := by
  have he := tfPatchGradient_eq_negative_field R Φ hT (tfPatchMinimizer_nonneg R T hT Φ)
    (fun u hu => tfPatchMinimizer_min R T hT Φ hu)
  have hi : (∫ z, max (tfBallPotential R (tfPatchMinimizer R T hT Φ) z-Φ z) 0*σ z ∂ballMeasure R) =
      ∫ z, tfPatchGradient R T Φ (tfPatchMinimizer R T hT Φ) z*σ z ∂ballMeasure R :=
    integral_congr_ae (he.mono (fun _ h => congrArg (fun a : ℝ => a*σ _) h.symm))
  rw [tfPatchGap,hi,tfPatchGradient_pair]
  ring

lemma tfPatchGap_measurable (R T : ℝ) (hT : 0 < T) :
    Measurable (fun p : TFField R × TFLp (ballMeasure R) => tfPatchGap R T hT p.1 p.2) := by
  have hr : Continuous (fun p : TFField R × TFLp (ballMeasure R) =>
      tfPatchMinimizer R T hT p.1) :=
    (tfPatchMinimizer_continuous R T hT).comp continuous_fst
  have hs := continuous_snd.sub hr
  have hq := ((tfCoulombL R).continuous.comp hs).clm_apply hs
  have hl := ((tfPatchLinear_continuous R).comp continuous_fst).clm_apply continuous_snd
  have hc := ((tfCoulombL R).continuous.comp hr).clm_apply continuous_snd
  have hd := (tfPowerDerivative_pair_measurable R).comp (hr.measurable.prodMk measurable_snd)
  simpa only [tfPatchGap_eq_gradient,Function.comp_apply,Pi.add_def,Pi.sub_def,Pi.add_apply,Pi.sub_apply] using
    (((hq.measurable.const_mul (1/2:ℝ)).add (hd.const_mul T)).add hl.measurable).add hc.measurable

lemma tfPatchGap_comp_aemeasurable {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (R T : ℝ) (hT : 0 < T) (Φ : α → TFField R) (σ : α → TFLp (ballMeasure R))
    (hΦ : AEMeasurable Φ μ) (hσ : AEMeasurable σ μ) :
    AEMeasurable (fun a => tfPatchGap R T hT (Φ a) (σ a)) μ := by
  have hm := (tfPatchGap_measurable R T hT).comp_aemeasurable (hΦ.prodMk hσ)
  simpa only [Function.comp_def] using hm

lemma tfPatchGap_nonneg (R T : ℝ) (hT : 0 < T) (Φ : TFField R)
    {σ : TFLp (ballMeasure R)} (hσ : NonnegDensity σ) : 0 ≤ tfPatchGap R T hT Φ σ := by
  unfold tfPatchGap
  exact add_nonneg (mul_nonneg (by norm_num) (tfCoulombL_nonneg R _))
    (integral_nonneg_of_ae (hσ.mono fun _ h => mul_nonneg (le_max_right _ _) h))

end CoulombAnalysis

end

end OAI
