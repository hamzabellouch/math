import Mathlib
import OAI.Analysis.CoulombIonization.ThomasFermi.TfPowerIntegralDeriv
import OAI.Analysis.CoulombIonization.ThomasFermi.PatchTF

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped Topology ENNReal

namespace CoulombAnalysis

lemma tfPatchFunctional_hasDerivAt (R T : ℝ) (Φ : TFField R) (f h : TFLp (ballMeasure R)) :
    HasDerivAt (fun t : ℝ => tfPatchFunctional R T Φ (f + t • h))
      (T * (∫ x, tfPowerDerivative (f x) * h x ∂ballMeasure R) +
        tfPatchLinear R Φ h + tfCoulombL R f h) 0 := by
  have he (t : ℝ) : tfPatchFunctional R T Φ (f + t • h) =
      T * ‖f + t • h‖ ^ (5 / 3 : ℝ) +
        (tfPatchLinear R Φ f + t * tfPatchLinear R Φ h) +
        (1 / 2 : ℝ) * (tfCoulombL R f f + 2 * t * tfCoulombL R f h +
          t * t * tfCoulombL R h h) := by
    simp only [tfPatchFunctional, map_add, map_smul, add_apply, smul_apply, smul_eq_mul]
    rw [tfCoulombL_symmetric R h f]
    ring
  simp_rw [he]
  have hk := (tfLp_kinetic_hasDerivAt f h).const_mul T
  have hl := (((hasDerivAt_id (0 : ℝ)).mul_const (tfPatchLinear R Φ h)).const_add (tfPatchLinear R Φ f))
  have hq := ((((hasDerivAt_id (0 : ℝ)).const_mul 2).mul_const (tfCoulombL R f h)).const_add
    (tfCoulombL R f f)).add (((hasDerivAt_id (0 : ℝ)).mul (hasDerivAt_id (0 : ℝ))).mul_const (tfCoulombL R h h))
  convert! (hk.add hl).add (hq.const_mul (1 / 2 : ℝ)) using 1
  simp only [id_eq]
  ring

lemma tfPatchFunctional_variation_nonneg (R T : ℝ) (Φ : TFField R) {f : TFLp (ballMeasure R)}
    (hf : NonnegDensity f)
    (hmin : ∀ g, NonnegDensity g → tfPatchFunctional R T Φ f ≤ tfPatchFunctional R T Φ g)
    {h : TFLp (ballMeasure R)} (hh : NonnegDensity h) :
    0 ≤ T * (∫ x, tfPowerDerivative (f x) * h x ∂ballMeasure R) +
      tfPatchLinear R Φ h + tfCoulombL R f h := by
  apply hasDerivAt_nonneg_of_right_min (tfPatchFunctional_hasDerivAt R T Φ f h)
  intro t ht
  simpa using hmin (f + t • h) (nonnegDensity_add hf (nonnegDensity_smul hh ht))

lemma tfPatchFunctional_variation_self (R T : ℝ) (Φ : TFField R) {f : TFLp (ballMeasure R)}
    (hf : NonnegDensity f)
    (hmin : ∀ g, NonnegDensity g → tfPatchFunctional R T Φ f ≤ tfPatchFunctional R T Φ g) :
    T * (∫ x, tfPowerDerivative (f x) * f x ∂ballMeasure R) +
      tfPatchLinear R Φ f + tfCoulombL R f f = 0 := by
  apply IsLocalMin.hasDerivAt_eq_zero (f := fun t : ℝ => tfPatchFunctional R T Φ (f + t • f))
    _ (tfPatchFunctional_hasDerivAt R T Φ f f)
  have hm : Ioi (-1 : ℝ) ∈ 𝓝 (0 : ℝ) := Ioi_mem_nhds (by norm_num)
  filter_upwards [hm] with t ht
  have hn : NonnegDensity (f + t • f) := by
    rw [show f + t • f = (1 + t) • f by rw [add_smul, one_smul]]
    exact nonnegDensity_smul hf (by change -1 < t at ht; linarith)
  simpa using hmin _ hn

def tfPatchGradient (R T : ℝ) (Φ : TFField R) (f : TFLp (ballMeasure R))
    (x : TFSpace) : ℝ :=
  T * tfPowerDerivative (f x) - Φ x + tfBallPotential R f x

lemma tfPatchGradient_integrable (R T : ℝ) (Φ : TFField R) (f : TFLp (ballMeasure R)) :
    Integrable (tfPatchGradient R T Φ f) (ballMeasure R) := by
  have hi : Integrable (fun x => tfPowerDerivative (f x)) (ballMeasure R) := by
    simpa only [mul_one] using tfPowerDerivative_mul_integrable (Lp.memLp f) (memLp_const (1 : ℝ))
  exact ((hi.const_mul T).sub ((Lp.memLp Φ).integrable
    (Fact.out : (1 : ENNReal) ≤ 5/2))).add (tfBallPotential_integrable R f)

lemma tfPatchGradient_mul_integrable (R T : ℝ) (Φ : TFField R) (f h : TFLp (ballMeasure R)) :
    Integrable (fun x => tfPatchGradient R T Φ f x * h x) (ballMeasure R) := by
  have hi := (tfPowerDerivative_mul_integrable (Lp.memLp f) (Lp.memLp h)).const_mul T
  have hn : Integrable (fun x => Φ x * h x) (ballMeasure R) :=
    (Lp.memLp Φ).integrable_mul (Lp.memLp h)
  apply ((hi.sub hn).add (tfBallPotential_mul_integrable R f h)).congr
  exact Eventually.of_forall fun x => by dsimp [tfPatchGradient]; ring

lemma tfPatchGradient_pair (R T : ℝ) (Φ : TFField R) (f h : TFLp (ballMeasure R)) :
    (∫ x, tfPatchGradient R T Φ f x * h x ∂ballMeasure R) =
      T * (∫ x, tfPowerDerivative (f x) * h x ∂ballMeasure R) +
        tfPatchLinear R Φ h + tfCoulombL R f h := by
  have hi := (tfPowerDerivative_mul_integrable (Lp.memLp f) (Lp.memLp h)).const_mul T
  have hn : Integrable (fun x => Φ x * h x) (ballMeasure R) :=
    (Lp.memLp Φ).integrable_mul (Lp.memLp h)
  have he : (fun x => tfPatchGradient R T Φ f x * h x) =
      (fun x => T * (tfPowerDerivative (f x) * h x) - Φ x * h x +
        tfBallPotential R f x * h x) := by
    ext x
    dsimp only [tfPatchGradient]
    ring
  rw [he, integral_add (hi.sub' hn) (tfBallPotential_mul_integrable R f h),
    integral_sub hi hn]
  simp only [integral_const_mul, tfPatchLinear_apply, tfCoulombL_potential]
  ring

lemma tfPatchGradient_nonneg (R T : ℝ) (Φ : TFField R) {f : TFLp (ballMeasure R)}
    (hf : NonnegDensity f)
    (hmin : ∀ g, NonnegDensity g → tfPatchFunctional R T Φ f ≤ tfPatchFunctional R T Φ g) :
    ∀ᵐ x ∂ballMeasure R, 0 ≤ tfPatchGradient R T Φ f x := by
  apply ae_nonneg_of_forall_setIntegral_nonneg (tfPatchGradient_integrable R T Φ f)
  intro s hs _
  let hm : MemLp (s.indicator (fun _ : TFSpace => (1 : ℝ))) (5 / 3) (ballMeasure R) :=
    (memLp_const 1).indicator hs
  let h := hm.toLp (s.indicator (fun _ : TFSpace => (1 : ℝ)))
  have hcoe : (fun x => h x) =ᵐ[ballMeasure R] s.indicator (fun _ => (1 : ℝ)) := hm.coeFn_toLp
  have hh : NonnegDensity h := by
    filter_upwards [hcoe] with x hx
    rw [hx]
    exact indicator_nonneg (fun _ _ => zero_le_one) x
  have hp := tfPatchFunctional_variation_nonneg R T Φ hf hmin hh
  rw [← tfPatchGradient_pair] at hp
  have he : (fun x => tfPatchGradient R T Φ f x * h x) =ᵐ[ballMeasure R]
      s.indicator (tfPatchGradient R T Φ f) := by
    filter_upwards [hcoe] with x hx
    rw [hx]
    by_cases hx' : x ∈ s <;> simp [hx']
  rwa [integral_congr_ae he, integral_indicator hs] at hp

lemma tfPatchGradient_complementarity (R T : ℝ) (Φ : TFField R) {f : TFLp (ballMeasure R)}
    (hf : NonnegDensity f)
    (hmin : ∀ g, NonnegDensity g → tfPatchFunctional R T Φ f ≤ tfPatchFunctional R T Φ g) :
    ∀ᵐ x ∂ballMeasure R, tfPatchGradient R T Φ f x * f x = 0 := by
  have hn : ∀ᵐ x ∂ballMeasure R, 0 ≤ tfPatchGradient R T Φ f x * f x := by
    filter_upwards [hf, tfPatchGradient_nonneg R T Φ hf hmin] with x hfx hgx
    exact mul_nonneg hgx hfx
  apply (integral_eq_zero_iff_of_nonneg_ae hn (tfPatchGradient_mul_integrable R T Φ f f)).mp
  rw [tfPatchGradient_pair]
  exact tfPatchFunctional_variation_self R T Φ hf hmin

theorem tfPatchFunctional_euler (R : ℝ) (Φ : TFField R) {T : ℝ} (hT : 0 < T)
    {f : TFLp (ballMeasure R)} (hf : NonnegDensity f)
    (hmin : ∀ g, NonnegDensity g → tfPatchFunctional R T Φ f ≤ tfPatchFunctional R T Φ g) :
    ∀ᵐ x ∂ballMeasure R, f x =
      (max (Φ x - tfBallPotential R f x) 0 / ((5 / 3 : ℝ) * T)) ^ (3 / 2 : ℝ) := by
  have hA : 0 < (5 / 3 : ℝ) * T := mul_pos (by norm_num) hT
  filter_upwards [hf, tfPatchGradient_nonneg R T Φ hf hmin,
    tfPatchGradient_complementarity R T Φ hf hmin] with x hfx hgx hcx
  have he : (5 / 3 : ℝ) * T * (f x) ^ (2 / 3 : ℝ) = max (Φ x - tfBallPotential R f x) 0 := by
    dsimp only [tfPatchGradient] at hgx hcx
    rw [tfPowerDerivative_nonneg hfx] at hgx hcx
    by_cases hf0 : f x = 0
    · simp only [hf0, Real.zero_rpow (by norm_num : (2 / 3 : ℝ) ≠ 0), mul_zero] at hgx ⊢
      rw [max_eq_right (by linarith)]
    · have hz := (mul_eq_zero.mp hcx).resolve_right hf0
      have hp := Real.rpow_nonneg hfx (2 / 3 : ℝ)
      have hxmax : 0 ≤ Φ x - tfBallPotential R f x := by nlinarith
      rw [max_eq_left hxmax]
      nlinarith
  have hdiv : (f x) ^ (2 / 3 : ℝ) = max (Φ x - tfBallPotential R f x) 0 / ((5 / 3 : ℝ) * T) :=
    (eq_div_iff hA.ne').mpr (by nlinarith [he])
  rw [← hdiv, ← Real.rpow_mul hfx]
  norm_num

end CoulombAnalysis

end

end OAI
