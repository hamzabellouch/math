import Mathlib
import OAI.Analysis.Conductivity.Model

namespace OAI

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory

lemma integral_sq_le_mass_mul {X : Type*} [MeasurableSpace X] {μ : Measure X}
    [IsFiniteMeasure μ] {f : X → ℝ} (hf : Integrable f μ)
    (hf2 : Integrable (fun x => f x^2) μ) :
    (∫ x, f x ∂μ)^2≤(μ univ).toReal*(∫ x, f x^2 ∂μ) := by
  by_cases h0 : μ univ=0
  · have : μ=0 := Measure.measure_univ_eq_zero.mp h0
    simp [this]
  have hm : 0<(μ univ).toReal := ENNReal.toReal_pos h0 (measure_ne_top _ _)
  let m := (∫ x, f x ∂μ)/(μ univ).toReal
  have hi : Integrable (fun x => f x^2-2*m*f x+m^2) μ :=
    (hf2.sub (hf.const_mul _)).add (integrable_const _)
  have hpos : 0≤∫ x, (f x^2-2*m*f x+m^2) ∂μ :=
    integral_nonneg (fun x => by change 0 ≤ f x^2-2*m*f x+m^2; nlinarith [sq_nonneg (f x-m)])
  rw [integral_add (f := fun x => f x^2-2*m*f x) (g := fun _ => m^2) (hf2.sub (hf.const_mul _)) (integrable_const _),
    integral_sub (f := fun x => f x^2) (g := fun x => 2*m*f x) hf2 (hf.const_mul _),integral_const_mul,integral_const,smul_eq_mul] at hpos
  have he : m*(μ univ).toReal=∫ x, f x ∂μ := by dsimp [m]; exact div_mul_cancel₀ _ hm.ne'
  dsimp [Measure.real] at hpos
  rw [←he] at hpos ⊢
  nlinarith [mul_nonneg hm.le hpos]

lemma interval_integral_sq_le {a b : ℝ} (hab : a≤b) {f : ℝ → ℝ} (hf : Continuous f) :
    (∫ t in a..b, f t)^2≤(b-a)*(∫ t in a..b, f t^2) := by
  have h := integral_sq_le_mass_mul
    (μ := volume.restrict (Ioc a b)) (hf.integrableOn_Icc.mono_set Ioc_subset_Icc_self)
    ((hf.pow 2).integrableOn_Icc.mono_set Ioc_subset_Icc_self)
  simpa only [intervalIntegral.integral_of_le hab,Measure.restrict_apply_univ,
    Real.volume_Ioc,ENNReal.toReal_ofReal (sub_nonneg.mpr hab)] using h

lemma smooth_interval_poincare_point {q : ℝ → ℝ}
    (hq : ContDiff ℝ (↑(⊤ : ℕ∞)) q) {a b : ℝ} (hab : a≤b) :
    (q b-q a)^2≤(b-a)*(∫ t in a..b, (deriv q t)^2) := by
  have hd : Continuous (deriv q) := hq.continuous_deriv (by simp)
  have hFTC := intervalIntegral.integral_deriv_eq_sub
    (fun x _ => hq.differentiable (by simp) x) (hd.intervalIntegrable a b)
  rw [←hFTC]
  exact interval_integral_sq_le hab hd

theorem fourier_mode_trace_energy {q : ℝ → ℝ}
    (hq : ContDiff ℝ (↑(⊤ : ℕ∞)) q) {η m : ℝ} (hη : 0<η) (_ : 0 ≤ m) :
    m*(q 0)^2≤(1+1/η)*(∫ t in (0:ℝ)..η,
      (deriv q t)^2+(1+m^2)*(q t)^2) := by
  let e := fun t => (deriv q t)^2+m^2*(q t)^2
  have hd : Continuous (deriv q) := hq.continuous_deriv (by simp)
  have he : Continuous e := (hd.pow 2).add (continuous_const.mul (hq.continuous.pow 2))
  have hpoint (t : ℝ) (ht : t∈Icc 0 η) :
      m*(q 0)^2≤ m*(q t)^2+∫ s in (0:ℝ)..η, e s := by
    have hder : ∀ s, HasDerivAt (fun x => m*(q x)^2) (2*m*q s*deriv q s) s := by
      intro s
      convert! ((hq.differentiable (by simp) s).hasDerivAt.pow 2).const_mul m using 1
      ring
    have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hder s)
      ((continuous_const.mul hq.continuous |>.mul hd).intervalIntegrable 0 t)
    have hi : ∫ s in (0:ℝ)..t, -(2*m*q s*deriv q s) ≤∫ s in (0:ℝ)..t, e s := by
      apply intervalIntegral.integral_mono_on ht.1
        ((continuous_const.mul hq.continuous |>.mul hd).neg.intervalIntegrable 0 t)
        (he.intervalIntegrable 0 t)
      intro s _
      dsimp [e]
      nlinarith [sq_nonneg (deriv q s+m*q s)]
    rw [intervalIntegral.integral_neg,hFTC] at hi
    have hi' : ∫ s in (0:ℝ)..t, e s ≤∫ s in (0:ℝ)..η, e s := by
      apply intervalIntegral.integral_mono_interval (le_refl 0) ht.1 ht.2
        _ (he.intervalIntegrable 0 η)
      exact Filter.Eventually.of_forall (fun s => by dsimp [e]; positivity)
    linarith
  have hav := intervalIntegral.integral_mono_on (μ := volume) (f := fun _ => m*(q 0)^2)
    (g := fun t => m*(q t)^2+∫ s in (0:ℝ)..η, e s) hη.le
    (continuous_const.intervalIntegrable 0 η)
    ((continuous_const.mul (hq.continuous.pow 2) |>.add continuous_const).intervalIntegrable 0 η)
    hpoint
  rw [intervalIntegral.integral_const,sub_zero,smul_eq_mul,
    intervalIntegral.integral_add (f := fun t => m*(q t)^2) (g := fun _ => ∫ s in (0:ℝ)..η, e s)
      ((continuous_const.mul (hq.continuous.pow 2)).intervalIntegrable 0 η)
      (continuous_const.intervalIntegrable 0 η),
    intervalIntegral.integral_const_mul,intervalIntegral.integral_const,sub_zero,smul_eq_mul] at hav
  have hI : 0≤∫ t in (0:ℝ)..η, (q t)^2 := intervalIntegral.integral_nonneg hη.le (fun _ _ => sq_nonneg _)
  have heI : 0≤∫ t in (0:ℝ)..η, e t := intervalIntegral.integral_nonneg hη.le (fun t _ => by dsimp [e]; positivity)
  have hE : (∫ t in (0:ℝ)..η, (deriv q t)^2+(1+m^2)*(q t)^2)=
      (∫ t in (0:ℝ)..η, e t)+(∫ t in (0:ℝ)..η, (q t)^2) := by
    rw [←intervalIntegral.integral_add (f := e) (g := fun t => (q t)^2) (he.intervalIntegrable 0 η) ((hq.continuous.pow 2).intervalIntegrable 0 η)]
    apply intervalIntegral.integral_congr
    intro t _
    dsimp [e]; ring
  rw [hE]
  have hmI : m*(∫ t in (0:ℝ)..η, (q t)^2)≤
      (∫ t in (0:ℝ)..η, e t)+(∫ t in (0:ℝ)..η, (q t)^2) := by
    rw [←intervalIntegral.integral_const_mul,←intervalIntegral.integral_add (f := e) (g := fun t => (q t)^2) (he.intervalIntegrable 0 η) ((hq.continuous.pow 2).intervalIntegrable 0 η)]
    apply intervalIntegral.integral_mono_on hη.le
      ((continuous_const.mul (hq.continuous.pow 2)).intervalIntegrable 0 η)
      ((he.add (hq.continuous.pow 2)).intervalIntegrable 0 η)
    intro t _
    dsimp [e]
    have hmm : m≤1+m^2 := by nlinarith [sq_nonneg (m-1/2)]
    nlinarith [mul_nonneg (sub_nonneg.mpr hmm) (sq_nonneg (q t)),sq_nonneg (deriv q t)]
  apply (mul_le_mul_iff_right₀ hη).mp
  have hfac : η*(1+1/η)=η+1 := by field_simp
  rw [←mul_assoc η (1+1/η),hfac]
  nlinarith [mul_nonneg hη.le hI]

end ScalarConductivity

end

end OAI
