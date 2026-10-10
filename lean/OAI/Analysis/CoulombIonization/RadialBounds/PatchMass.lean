import Mathlib
import OAI.Analysis.CoulombIonization.ThomasFermi.PatchTF

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped Topology ENNReal

namespace CoulombAnalysis

lemma ballMeasure_ae_ne (R : ℝ) :
    ∀ᵐ p ∂(ballMeasure R).prod (ballMeasure R), p.1 ≠ p.2 := by
  let : NullSingletonClass (ballMeasure R) := by
    dsimp [ballMeasure]
    infer_instance
  apply (Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun measurable_fst measurable_snd).compl).mpr
  apply Eventually.of_forall
  intro x
  have h := (ballMeasure R).ae_ne x
  exact h.mono fun y hy => Ne.symm hy

lemma tfCoulombL_mass_lower {R : ℝ} (_hR : 0 < R) {f : TFLp (ballMeasure R)}
    (hf : NonnegDensity f) :
    (∫ x, f x ∂ballMeasure R)^2 / (2*R) ≤ tfCoulombL R f f := by
  have hi := (Lp.memLp f).integrable (Fact.out : (1:ENNReal) ≤ 5/3)
  have hx : ∀ᵐ x ∂ballMeasure R, x ∈ ball (0 : TFSpace) R := ae_restrict_mem measurableSet_ball
  have hp : ∀ᵐ p ∂(ballMeasure R).prod (ballMeasure R),
      f p.1 * f p.2 / (2*R) ≤ f p.1 * f p.2 / ‖p.1-p.2‖ := by
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae hf, Measure.quasiMeasurePreserving_snd.ae hf,
      Measure.quasiMeasurePreserving_fst.ae hx, Measure.quasiMeasurePreserving_snd.ae hx,
      ballMeasure_ae_ne R] with p hf1 hf2 hx1 hx2 hne
    have hd : ‖p.1-p.2‖ ≤ 2*R := by
      have h1 := mem_ball_zero_iff.mp hx1
      have h2 := mem_ball_zero_iff.mp hx2
      exact (norm_sub_le p.1 p.2).trans (by linarith)
    have hd0 : 0 < ‖p.1-p.2‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
    exact div_le_div_of_nonneg_left (mul_nonneg hf1 hf2) hd0 hd
  have hh := integral_mono_ae ((hi.mul_prod hi).div_const (2*R)) (tfCoulomb_integrable R f f) hp
  rw [integral_div, integral_prod_mul, ← pow_two, ← tfCoulombL_apply] at hh
  exact hh

theorem tfPatchMinimizer_mass_le {R T F : ℝ} (hR : 0 < R) (hT : 0 < T)
    (hF : 0 ≤ F) (Φ : TFField R) (hΦ : ∀ᵐ x ∂ballMeasure R, Φ x ≤ F) :
    (∫ x, tfPatchMinimizer R T hT Φ x ∂ballMeasure R) ≤ 4*R*F := by
  let f := tfPatchMinimizer R T hT Φ
  have hf : NonnegDensity f := tfPatchMinimizer_nonneg R T hT Φ
  have hi := (Lp.memLp f).integrable (Fact.out : (1:ENNReal) ≤ 5/3)
  have he : (∫ x, Φ x * f x ∂ballMeasure R) ≤ F * (∫ x, f x ∂ballMeasure R) := by
    rw [← integral_const_mul]
    exact integral_mono_ae ((Lp.memLp Φ).integrable_mul (Lp.memLp f)) (hi.const_mul F)
      (by filter_upwards [hΦ, hf] with x hpx hfx; exact mul_le_mul_of_nonneg_right hpx hfx)
  have hmin := tfPatchMinimizer_min R T hT Φ (nonnegDensity_zero R)
  rw [tfPatchFunctional_zero] at hmin
  change tfPatchFunctional R T Φ f ≤ 0 at hmin
  rw [tfPatchFunctional, tfPatchLinear_apply] at hmin
  have hk : 0 ≤ T * ‖f‖ ^ (5/3:ℝ) := mul_nonneg hT.le (Real.rpow_nonneg (norm_nonneg _) _)
  have hm : 0 ≤ ∫ x, f x ∂ballMeasure R := integral_nonneg_of_ae hf
  have hc := (div_le_iff₀ (by positivity : (0:ℝ) < 2*R)).mp (tfCoulombL_mass_lower hR hf)
  by_cases hm0 : (∫ x, f x ∂ballMeasure R) = 0
  · change (∫ x, f x ∂ballMeasure R) ≤ _
    rw [hm0]
    positivity
  · have hmp : 0 < ∫ x, f x ∂ballMeasure R := lt_of_le_of_ne hm (Ne.symm hm0)
    change (∫ x, f x ∂ballMeasure R) ≤ _
    nlinarith

lemma tfPatchMinimizer_positive_energy_le {R T F : ℝ} (hR : 0 < R) (hT : 0 < T)
    (hF : 0 ≤ F) (Φ : TFField R) (hΦ : ∀ᵐ x ∂ballMeasure R, Φ x ≤ F) :
    T * ‖tfPatchMinimizer R T hT Φ‖^(5/3:ℝ) +
      (1/2:ℝ)*tfCoulombL R (tfPatchMinimizer R T hT Φ) (tfPatchMinimizer R T hT Φ)
        ≤ 4*R*F^2 := by
  let f := tfPatchMinimizer R T hT Φ
  have hf : NonnegDensity f := tfPatchMinimizer_nonneg R T hT Φ
  have hi := (Lp.memLp f).integrable (Fact.out : (1:ENNReal) ≤ 5/3)
  have he : (∫ x, Φ x * f x ∂ballMeasure R) ≤ F * (∫ x, f x ∂ballMeasure R) := by
    rw [← integral_const_mul]
    exact integral_mono_ae ((Lp.memLp Φ).integrable_mul (Lp.memLp f)) (hi.const_mul F)
      (by filter_upwards [hΦ, hf] with x hpx hfx; exact mul_le_mul_of_nonneg_right hpx hfx)
  have hmin := tfPatchMinimizer_min R T hT Φ (nonnegDensity_zero R)
  rw [tfPatchFunctional_zero] at hmin
  change tfPatchFunctional R T Φ f ≤ 0 at hmin
  rw [tfPatchFunctional, tfPatchLinear_apply] at hmin
  have hm := mul_le_mul_of_nonneg_left (tfPatchMinimizer_mass_le hR hT hF Φ hΦ) hF
  change T * ‖f‖^(5/3:ℝ) + (1/2:ℝ)*tfCoulombL R f f ≤ _
  nlinarith

lemma tfPatchMinimizer_mass_le_patch {R T F a : ℝ} (hR : 0 < R) (hRa : R ≤ 6*a)
    (hT : 0 < T) (hF : 0 ≤ F) (Φ : TFField R)
    (hΦ : ∀ᵐ x ∂ballMeasure R, Φ x ≤ F) :
    (∫ x, tfPatchMinimizer R T hT Φ x ∂ballMeasure R) ≤ 24*a*F := by
  apply (tfPatchMinimizer_mass_le hR hT hF Φ hΦ).trans
  nlinarith

end CoulombAnalysis

end

end OAI
