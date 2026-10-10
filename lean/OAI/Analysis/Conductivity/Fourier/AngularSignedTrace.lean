import Mathlib
import OAI.Analysis.Conductivity.Fourier.AngularIntegratedTrace

namespace OAI

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology UnitAddTorus

lemma sourceAngular_signed_deriv {f : (Fin 3 → ℝ) → ℝ}
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) (t a σ : ℝ) (x : UnitAddTorus (Fin 2)) :
    deriv (fun s => f (sourceAngularCollar (t+σ*s) x)) a=
      fderiv ℝ f (sourceAngularCollar (t+σ*a) x) (σ • sourceAngularVelocity x) := by
  have hd := (((hf.differentiable (by simp) (sourceAngularCollar t x+(σ*a) • sourceAngularVelocity x)).hasFDerivAt).comp_hasDerivAt a
    ((((hasDerivAt_id a).const_mul σ).smul_const (sourceAngularVelocity x)).const_add (sourceAngularCollar t x))).deriv
  change deriv (fun s : ℝ => f (sourceAngularCollar t x+(σ*s) • sourceAngularVelocity x)) a=_ at hd
  simpa only [sourceAngular_affine,mul_one] using hd

lemma continuous_sourceAngular_signed (t σ : ℝ) :
    Continuous (fun z : ℝ×UnitAddTorus (Fin 2) => sourceAngularCollar (t+σ*z.1) z.2) := by
  simp_rw [sourceAngular_affine]
  exact ((continuous_sourceAngularCollar t).comp continuous_snd).add
    ((continuous_const.mul continuous_fst).smul (continuous_sourceAngularVelocity.comp continuous_snd))

lemma sourceAngular_signed_pointwise {f : (Fin 3 → ℝ) → ℝ}
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) (t σ : ℝ) (hσ : |σ|≤1)
    {η : ℝ} (hη : 0<η) (x : UnitAddTorus (Fin 2)) :
    (f (sourceAngularCollar t x))^2≤(1+1/η)*(∫ a in (0:ℝ)..η,
      sourcePhysicalEnergy f (sourceAngularCollar (t+σ*a) x)) := by
  have hq : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun a : ℝ => f (sourceAngularCollar (t+σ*a) x)) := by
    simp_rw [sourceAngular_affine]
    exact hf.comp (contDiff_const.add ((contDiff_const.mul contDiff_id).smul contDiff_const))
  have hh := fourier_mode_trace_energy hq hη (m:=1) (by norm_num)
  simp only [mul_zero,add_zero,one_pow,one_mul] at hh
  apply hh.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply intervalIntegral.integral_mono_on hη.le
  · exact (((hq.continuous_deriv (by simp)).pow 2).add
      (continuous_const.mul (hq.continuous.pow 2))).intervalIntegrable _ _
  · have hc : Continuous (fun a : ℝ => sourceAngularCollar (t+σ*a) x) := by
      simp_rw [sourceAngular_affine]; fun_prop
    exact ((continuous_sourcePhysicalEnergy hf).comp hc).intervalIntegrable _ _
  · intro a _
    rw [sourceAngular_signed_deriv hf]
    have hv : ‖σ • sourceAngularVelocity x‖≤8 := by
      rw [norm_smul,Real.norm_eq_abs]
      exact (mul_le_mul hσ (sourceAngularVelocity_norm x) (norm_nonneg _) (by norm_num)).trans_eq (by ring)
    have hb := (fderiv ℝ f (sourceAngularCollar (t+σ*a) x)).le_opNorm (σ • sourceAngularVelocity x)
    have hb' := hb.trans (mul_le_mul_of_nonneg_left hv (norm_nonneg _))
    have hs := mul_self_le_mul_self (norm_nonneg _) hb'
    simp only [Real.norm_eq_abs,←pow_two,sq_abs] at hs
    unfold sourcePhysicalEnergy
    nlinarith

theorem sourceAngular_signed_trace {f : (Fin 3 → ℝ) → ℝ}
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) (t σ : ℝ) (hσ : |σ|≤1)
    {η : ℝ} (hη : 0<η) :
    (∫ x : UnitAddTorus (Fin 2),(f (sourceAngularCollar t x))^2)≤
      (1+1/η)*(∫ a in (0:ℝ)..η,∫ x : UnitAddTorus (Fin 2),
        sourcePhysicalEnergy f (sourceAngularCollar (t+σ*a) x)) := by
  apply integrate_torus_interval_bound (F:=fun x => (f (sourceAngularCollar t x))^2)
    (G:=fun a x => sourcePhysicalEnergy f (sourceAngularCollar (t+σ*a) x))
    ((hf.continuous.comp (continuous_sourceAngularCollar t)).pow 2)
    ((continuous_sourcePhysicalEnergy hf).comp (continuous_sourceAngular_signed t σ)) hη.le
  intro x
  exact sourceAngular_signed_pointwise hf t σ hσ hη x

end ScalarConductivity

end

end OAI
