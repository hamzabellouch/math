import Mathlib
import OAI.Analysis.Conductivity.Variational.CompactParametricIntegral
import OAI.Analysis.Conductivity.Variational.IntervalMeanPoincare

namespace OAI

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory

variable {E G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]

def unitAverage (f : ℝ → G) : G := ∫ t in Icc (0:ℝ) 1, f t

omit [CompleteSpace G] in
lemma unitAverage_eq_interval (f : ℝ → G) :
    unitAverage f = ∫ t in (0:ℝ)..1, f t := by
  rw [intervalIntegral.integral_of_le (by norm_num)]
  exact integral_Icc_eq_integral_Ioc

lemma unitAverage_const (c : G) : unitAverage (fun _ => c)=c := by
  rw [unitAverage_eq_interval,intervalIntegral.integral_const]
  simp

omit [CompleteSpace G] in
lemma unitAverage_add {f g : ℝ → G} (hf : Continuous f) (hg : Continuous g) :
    unitAverage (fun t => f t+g t)=unitAverage f+unitAverage g :=
  integral_add hf.integrableOn_Icc hg.integrableOn_Icc

omit [CompleteSpace G] in
lemma unitAverage_sub {f g : ℝ → G} (hf : Continuous f) (hg : Continuous g) :
    unitAverage (fun t => f t-g t)=unitAverage f-unitAverage g :=
  integral_sub hf.integrableOn_Icc hg.integrableOn_Icc

omit [CompleteSpace G] in
lemma unitAverage_smul (c : ℝ) (f : ℝ → G) :
    unitAverage (fun t => c • f t)=c • unitAverage f := integral_smul c f

lemma unitAverage_mul (c : ℝ) (f : ℝ → ℝ) :
    unitAverage (fun t => c*f t)=c*unitAverage f := integral_const_mul c f

lemma unitAverage_mono {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g)
    (h : ∀ t∈Icc (0:ℝ) 1, f t ≤ g t) : unitAverage f ≤ unitAverage g := by
  apply integral_mono_ae hf.integrableOn_Icc hg.integrableOn_Icc
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  exact h t ht

lemma unitAverage_nonneg {f : ℝ → ℝ} (hf : ∀ t∈Icc (0:ℝ) 1, 0 ≤ f t) :
    0 ≤ unitAverage f := by
  apply integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  exact hf t ht

lemma unitAverage_sq_le {f : ℝ → ℝ} (hf : Continuous f) :
    (unitAverage f)^2 ≤ unitAverage (fun t => (f t)^2) := by
  simpa only [unitAverage_eq_interval,sub_zero,one_mul] using
    interval_integral_sq_le (by norm_num : (0:ℝ) ≤ 1) hf

omit [NormedSpace ℝ E] [CompleteSpace G] in
lemma continuous_unitAverage {f : E×ℝ → G} (hf : Continuous f) :
    Continuous (fun x => unitAverage (fun t => f (x,t))) :=
  by
    exact continuous_parametric_integral_of_continuous (f := fun x t => f (x,t)) hf isCompact_Icc

lemma contDiff_unitAverage {f : E×ℝ → G} (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (fun x => unitAverage (fun t => f (x,t))) :=
  contDiff_compact_integral hf isCompact_Icc

omit [CompleteSpace G] in
lemma fderiv_unitAverage {f : E×ℝ → G} (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f)
    (x v : E) :
    fderiv ℝ (fun y => unitAverage (fun t => f (y,t))) x v =
      unitAverage (fun t => fderiv ℝ f (x,t) (v,0)) := by
  let D : E×ℝ → E →L[ℝ] G := fun z =>
    (fderiv ℝ f z).comp (ContinuousLinearMap.inl ℝ E ℝ)
  have hD : Continuous D := (hf.fderiv_right (m := 0) (by simp)).continuous.clm_comp continuous_const
  have hd (y : E) (t : ℝ) : HasFDerivAt (fun w => f (w,t)) (D (y,t)) y := by
    exact ((hf.differentiable (by simp) (y,t)).hasFDerivAt).comp y
      ((hasFDerivAt_id y).prodMk (hasFDerivAt_const t y))
  have hi := hasFDerivAt_compact_integral (μ := volume) hf.continuous hD hd
    (isCompact_Icc : IsCompact (Icc (0:ℝ) 1)) x
  change (fderiv ℝ (fun y => ∫ t in Icc (0:ℝ) 1, f (y,t)) x) v = _
  rw [hi.fderiv]
  exact ContinuousLinearMap.integral_apply (hD.comp (continuous_const.prodMk continuous_id) |>.integrableOn_Icc) v

lemma unitAverage_mean_poincare {f : ℝ → ℝ} (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) :
    unitAverage (fun t => (f t-unitAverage f)^2) ≤
      unitAverage (fun t => (deriv f t)^2) := by
  simpa only [unitAverage_eq_interval,sub_zero,one_pow,one_mul,div_one] using
    smooth_interval_mean_poincare hf (by norm_num : (0:ℝ)<1)

end ScalarConductivity

end

end OAI
