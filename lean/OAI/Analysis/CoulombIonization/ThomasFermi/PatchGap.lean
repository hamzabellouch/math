import Mathlib
import OAI.Analysis.CoulombIonization.ThomasFermi.PatchEuler

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped Topology ENNReal

namespace CoulombAnalysis

lemma tfPower_tangent {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    tfPowerDerivative a * (b-a) ≤ b^(5/3:ℝ)-a^(5/3:ℝ) := by
  rw [tfPowerDerivative_nonneg ha]
  have hc := (strictConvexOn_rpow (by norm_num : (1:ℝ) < 5/3)).convexOn
  have hd : HasDerivAt (fun x : ℝ => x^(5/3:ℝ)) ((5/3:ℝ)*a^(2/3:ℝ)) a := by
    convert Real.hasDerivAt_rpow_const (x := a) (p := 5/3) (Or.inr (by norm_num)) using 1; norm_num
  rcases lt_trichotomy a b with hab | rfl | hba
  · have hh := hc.le_slope_of_hasDerivAt ha hb hab hd
    rw [slope_def_field] at hh
    exact (le_div_iff₀ (sub_pos.mpr hab)).mp hh
  · simp
  · have hh := hc.slope_le_of_hasDerivAt hb ha hba hd
    rw [slope_def_field] at hh
    have hh' := (div_le_iff₀ (sub_pos.mpr hba)).mp hh
    nlinarith

lemma tfLp_kinetic_tangent {R : ℝ} {f g : TFLp (ballMeasure R)}
    (hf : NonnegDensity f) (hg : NonnegDensity g) :
    (∫ x, tfPowerDerivative (f x) * (g x-f x) ∂ballMeasure R) ≤
      ‖g‖^(5/3:ℝ)-‖f‖^(5/3:ℝ) := by
  have hd : Integrable (fun x => tfPowerDerivative (f x) * (g x-f x)) (ballMeasure R) := by
    apply (tfPowerDerivative_mul_integrable (Lp.memLp f) (Lp.memLp (g-f))).congr
    filter_upwards [Lp.coeFn_sub g f] with x hx
    rw [hx]
    rfl
  rw [tfLp_norm_rpow_nonneg hg, tfLp_norm_rpow_nonneg hf,
    ← integral_sub (tf_integrable (Lp.memLp g) hg) (tf_integrable (Lp.memLp f) hf)]
  apply integral_mono_ae hd ((tf_integrable (Lp.memLp g) hg).sub (tf_integrable (Lp.memLp f) hf))
  filter_upwards [hf, hg] with x hfx hgx
  exact tfPower_tangent hfx hgx

lemma tfCoulombL_sub_self (R : ℝ) (f g : TFLp (ballMeasure R)) :
    tfCoulombL R (g-f) (g-f) =
      tfCoulombL R g g - 2*tfCoulombL R f g + tfCoulombL R f f := by
  simp only [map_sub, sub_apply]
  rw [tfCoulombL_symmetric R g f]
  ring

lemma tfPatchFunctional_gap_gradient (R T : ℝ) (hT : 0 ≤ T) (Φ : TFField R)
    {f g : TFLp (ballMeasure R)} (hf : NonnegDensity f) (hg : NonnegDensity g)
    (hmin : ∀ u, NonnegDensity u → tfPatchFunctional R T Φ f ≤ tfPatchFunctional R T Φ u) :
    (1/2:ℝ)*tfCoulombL R (g-f) (g-f) +
      (∫ x, tfPatchGradient R T Φ f x * g x ∂ballMeasure R) ≤
      tfPatchFunctional R T Φ g - tfPatchFunctional R T Φ f := by
  have hp := mul_le_mul_of_nonneg_left (tfLp_kinetic_tangent hf hg) hT
  have hs := tfPatchFunctional_variation_self R T Φ hf hmin
  have hi1 := tfPowerDerivative_mul_integrable (Lp.memLp f) (Lp.memLp g)
  have hi2 := tfPowerDerivative_mul_integrable (Lp.memLp f) (Lp.memLp f)
  have he : (∫ x, tfPowerDerivative (f x) * (g x-f x) ∂ballMeasure R) =
      (∫ x, tfPowerDerivative (f x) * g x ∂ballMeasure R) -
        (∫ x, tfPowerDerivative (f x) * f x ∂ballMeasure R) := by
    simp_rw [mul_sub]
    exact integral_sub hi1 hi2
  rw [he] at hp
  rw [tfCoulombL_sub_self, tfPatchGradient_pair]
  unfold tfPatchFunctional
  linarith

lemma tfPatchGradient_eq_negative_field (R : ℝ) (Φ : TFField R) {T : ℝ} (hT : 0 < T)
    {f : TFLp (ballMeasure R)} (hf : NonnegDensity f)
    (hmin : ∀ u, NonnegDensity u → tfPatchFunctional R T Φ f ≤ tfPatchFunctional R T Φ u) :
    ∀ᵐ x ∂ballMeasure R,
      tfPatchGradient R T Φ f x = max (tfBallPotential R f x - Φ x) 0 := by
  filter_upwards [hf, tfPatchGradient_nonneg R T Φ hf hmin,
    tfPatchGradient_complementarity R T Φ hf hmin] with x hfx hgx hcx
  by_cases hz : f x = 0
  · simp only [tfPatchGradient, hz, tfPowerDerivative, abs_zero,
      mul_zero, zero_sub] at hgx ⊢
    rw [max_eq_left (by linarith)]
    ring
  · have hge := (mul_eq_zero.mp hcx).resolve_right hz
    rw [hge]
    symm
    apply max_eq_right
    have hk : 0 ≤ T * tfPowerDerivative (f x) := by
      rw [tfPowerDerivative_nonneg hfx]
      positivity
    dsimp [tfPatchGradient] at hge
    linarith

theorem tfPatchFunctional_clipping_gap (R : ℝ) (Φ : TFField R) {T : ℝ} (hT : 0 < T)
    {g : TFLp (ballMeasure R)} (hg : NonnegDensity g) :
    (1/2:ℝ)*tfCoulombL R (g-tfPatchMinimizer R T hT Φ) (g-tfPatchMinimizer R T hT Φ) +
      (∫ x, max (tfBallPotential R (tfPatchMinimizer R T hT Φ) x - Φ x) 0 * g x
        ∂ballMeasure R) ≤
      tfPatchFunctional R T Φ g - tfPatchFunctional R T Φ (tfPatchMinimizer R T hT Φ) := by
  have hf := tfPatchMinimizer_nonneg R T hT Φ
  have hm := fun u (hu : NonnegDensity u) => tfPatchMinimizer_min R T hT Φ hu
  have he := tfPatchGradient_eq_negative_field R Φ hT hf hm
  have hh := tfPatchFunctional_gap_gradient R T hT.le Φ hf hg hm
  convert hh using 1
  congr 1
  apply integral_congr_ae
  filter_upwards [he] with x hx
  rw [hx]

end CoulombAnalysis

end

end OAI
