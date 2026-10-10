import Mathlib

namespace OAI

section
section
noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
noncomputable section
open MeasureTheory Set Filter
open scoped Topology Interval
noncomputable section
open MeasureTheory Set
open scoped Interval
namespace SK.Analytic

theorem stein_brascampLieb_interval
    {a b : ℝ} (hab : a ≤ b) (f f₁ p V₁ V₂ g : ℝ → ℝ)
    (hf : ∀ x, HasDerivAt f (f₁ x) x)
    (hp : ∀ x, HasDerivAt p (-V₁ x * p x) x)
    (hV : ∀ x, HasDerivAt V₁ (V₂ x) x)
    (hg : ∀ x, HasDerivAt g (f x + V₁ x * g x) x)
    (hf₁c : Continuous f₁) (hV₂c : Continuous V₂)
    (hga : g a = 0) (hgb : g b = 0)
    (hp₀ : ∀ x, 0 ≤ p x) (hV₂ : ∀ x, 0 < V₂ x) :
    (∫ x in a..b, f x ^ 2 * p x) ≤
      ∫ x in a..b, f₁ x ^ 2 / V₂ x * p x := by
  have hfc : Continuous f := continuous_iff_continuousAt.mpr fun x => (hf x).continuousAt
  have hpc : Continuous p := continuous_iff_continuousAt.mpr fun x => (hp x).continuousAt
  have hVc : Continuous V₁ := continuous_iff_continuousAt.mpr fun x => (hV x).continuousAt
  have hgc : Continuous g := continuous_iff_continuousAt.mpr fun x => (hg x).continuousAt
  have hgpc : Continuous (fun x => g x * p x) := hgc.mul hpc
  have hgp : ∀ x, HasDerivAt (fun x => g x * p x) (f x * p x) x := by
    intro x
    convert! (hg x).fun_mul (hp x) using 1
    ring
  have hfirst : (∫ x in a..b, f x ^ 2 * p x) =
      -(∫ x in a..b, f₁ x * g x * p x) := by
    have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul
      (fun x _ => hf x) (fun x _ => hgp x)
      (hf₁c.intervalIntegrable a b) ((hfc.mul hpc).intervalIntegrable a b)
    simp only [hga, hgb, zero_mul, mul_zero, sub_self, zero_sub] at h
    simpa only [pow_two, mul_assoc] using h
  have hdg : ∀ x, HasDerivAt (fun x => g x ^ 2 * p x)
      ((2 * g x * (f x + V₁ x * g x) - V₁ x * g x ^ 2) * p x) x := by
    intro x
    convert! ((hg x).pow 2).fun_mul (hp x) using 1
    simp only [Pi.pow_apply]
    ring
  have hdc : Continuous (fun x =>
      (2 * g x * (f x + V₁ x * g x) - V₁ x * g x ^ 2) * p x) := by fun_prop
  have hboundary : (∫ x in a..b,
      V₂ x * (g x ^ 2 * p x) +
      V₁ x * ((2 * g x * (f x + V₁ x * g x) - V₁ x * g x ^ 2) * p x)) = 0 := by
    have h := intervalIntegral.integral_deriv_mul_eq_sub
      (fun x _ => hV x) (fun x _ => hdg x)
      (hV₂c.intervalIntegrable a b) (hdc.intervalIntegrable a b)
    simpa [hga, hgb] using h
  have hAc : Continuous (fun x => V₂ x * g x ^ 2 * p x) := by fun_prop
  have hBc : Continuous (fun x => (f x + V₁ x * g x) ^ 2 * p x) := by fun_prop
  have hIc : Continuous (fun x => f x ^ 2 * p x) := by fun_prop
  have hDc : Continuous (fun x => V₂ x * (g x ^ 2 * p x) +
      V₁ x * ((2 * g x * (f x + V₁ x * g x) - V₁ x * g x ^ 2) * p x)) := by fun_prop
  have henergy : (∫ x in a..b, V₂ x * g x ^ 2 * p x) +
      (∫ x in a..b, (f x + V₁ x * g x) ^ 2 * p x) =
      ∫ x in a..b, f x ^ 2 * p x := by
    calc
      _ = (∫ x in a..b, V₂ x * (g x ^ 2 * p x) +
          V₁ x * ((2 * g x * (f x + V₁ x * g x) - V₁ x * g x ^ 2) * p x)) +
          ∫ x in a..b, f x ^ 2 * p x := by
        rw [← intervalIntegral.integral_add (hAc.intervalIntegrable a b) (hBc.intervalIntegrable a b),
          ← intervalIntegral.integral_add (hDc.intervalIntegrable a b) (hIc.intervalIntegrable a b)]
        apply intervalIntegral.integral_congr
        intro x _
        ring
      _ = _ := by rw [hboundary, zero_add]
  have hB₀ : 0 ≤ ∫ x in a..b, (f x + V₁ x * g x) ^ 2 * p x :=
    intervalIntegral.integral_nonneg hab (fun x _ => mul_nonneg (sq_nonneg _) (hp₀ x))
  have hAle : (∫ x in a..b, V₂ x * g x ^ 2 * p x) ≤
      ∫ x in a..b, f x ^ 2 * p x := by linarith
  have hYc : Continuous (fun x => f₁ x ^ 2 / V₂ x * p x) := by
    exact ((hf₁c.pow 2).div hV₂c (fun x => ne_of_gt (hV₂ x))).mul hpc
  have hY : ∀ x, -2 * (f₁ x * g x * p x) ≤
      f₁ x ^ 2 / V₂ x * p x + V₂ x * g x ^ 2 * p x := by
    intro x
    have hsq : 0 ≤ (f₁ x + V₂ x * g x) ^ 2 / V₂ x :=
      div_nonneg (sq_nonneg _) (le_of_lt (hV₂ x))
    have heq : (f₁ x + V₂ x * g x) ^ 2 / V₂ x =
        f₁ x ^ 2 / V₂ x + 2 * f₁ x * g x + V₂ x * g x ^ 2 := by
      field_simp [ne_of_gt (hV₂ x)]
      ring
    rw [heq] at hsq
    have hprod := mul_nonneg hsq (hp₀ x)
    nlinarith
  have htwice : 2 * (∫ x in a..b, f x ^ 2 * p x) ≤
      (∫ x in a..b, f₁ x ^ 2 / V₂ x * p x) +
      ∫ x in a..b, V₂ x * g x ^ 2 * p x := by
    calc
      _ = ∫ x in a..b, -2 * (f₁ x * g x * p x) := by
        rw [intervalIntegral.integral_const_mul, hfirst]
        ring
      _ ≤ ∫ x in a..b, f₁ x ^ 2 / V₂ x * p x + V₂ x * g x ^ 2 * p x := by
        apply intervalIntegral.integral_mono_on hab
        · exact (((hf₁c.mul hgc).mul hpc).const_mul (-2)).intervalIntegrable a b
        · exact (hYc.add hAc).intervalIntegrable a b
        · intro x _
          exact hY x
      _ = _ := intervalIntegral.integral_add (hYc.intervalIntegrable a b) (hAc.intervalIntegrable a b)
  linarith

def intervalPartition (V : ℝ → ℝ) (a b : ℝ) : ℝ :=
  ∫ x in a..b, Real.exp (-V x)

def intervalMean (V f : ℝ → ℝ) (a b : ℝ) : ℝ :=
  (∫ x in a..b, f x * Real.exp (-V x)) / intervalPartition V a b

theorem intervalPartition_pos {V : ℝ → ℝ} (hV : Continuous V) {a b : ℝ} (hab : a < b) :
    0 < intervalPartition V a b := by
  apply intervalIntegral.integral_pos hab ((Real.continuous_exp.comp hV.neg).continuousOn)
  · intro x _
    exact le_of_lt (Real.exp_pos _)
  · exact ⟨a, ⟨le_rfl, hab.le⟩, Real.exp_pos _⟩

theorem brascampLieb_interval
    {a b : ℝ} (hab : a < b) (V V₁ V₂ f f₁ : ℝ → ℝ)
    (hV : ∀ x, HasDerivAt V (V₁ x) x)
    (hV₁ : ∀ x, HasDerivAt V₁ (V₂ x) x)
    (hf : ∀ x, HasDerivAt f (f₁ x) x)
    (hV₂c : Continuous V₂) (hf₁c : Continuous f₁)
    (hV₂ : ∀ x, 0 < V₂ x) :
    (∫ x in a..b, (f x - intervalMean V f a b) ^ 2 * Real.exp (-V x)) ≤
      ∫ x in a..b, f₁ x ^ 2 / V₂ x * Real.exp (-V x) := by
  let p : ℝ → ℝ := fun x => Real.exp (-V x)
  let m : ℝ := intervalMean V f a b
  let q : ℝ → ℝ := fun x => f x - m
  let U : ℝ → ℝ := fun x => ∫ y in a..x, q y * p y
  let g : ℝ → ℝ := fun x => U x / p x
  have hVc : Continuous V := continuous_iff_continuousAt.mpr fun x => (hV x).continuousAt
  have hfc : Continuous f := continuous_iff_continuousAt.mpr fun x => (hf x).continuousAt
  have hpc : Continuous p := Real.continuous_exp.comp hVc.neg
  have hqc : Continuous q := hfc.sub continuous_const
  have hp₀ : ∀ x, 0 < p x := fun x => Real.exp_pos _
  have hp' : ∀ x, HasDerivAt p (-V₁ x * p x) x := by
    intro x
    convert! (hV x).neg.exp using 1
    dsimp only [p, Pi.neg_apply]
    ring
  have hq : ∀ x, HasDerivAt q (f₁ x) x := fun x => (hf x).sub_const m
  have hU : ∀ x, HasDerivAt U (q x * p x) x := fun x =>
    ((hqc.mul hpc).integral_hasStrictDerivAt a x).hasDerivAt
  have hg : ∀ x, HasDerivAt g (q x + V₁ x * g x) x := by
    intro x
    convert! (hU x).fun_div (hp' x) (ne_of_gt (hp₀ x)) using 1
    dsimp only [g]
    field_simp [ne_of_gt (hp₀ x)]
    ring
  have hcentered : (∫ x in a..b, q x * p x) = 0 := by
    change (∫ x in a..b, (f x - m) * p x) = 0
    simp_rw [sub_mul]
    rw [intervalIntegral.integral_sub ((show Continuous (fun x => f x * p x) from hfc.mul hpc).intervalIntegrable a b)
      ((show Continuous (fun x => m * p x) from hpc.const_mul m).intervalIntegrable a b), intervalIntegral.integral_const_mul]
    have hZ : (∫ x in a..b, p x) ≠ 0 := ne_of_gt (intervalPartition_pos hVc hab)
    dsimp only [m, intervalMean, intervalPartition, p]
    rw [div_mul_cancel₀ _ hZ, sub_self]
  have hga : g a = 0 := by simp [g, U]
  have hgb : g b = 0 := by
    change (∫ x in a..b, q x * p x) / p b = 0
    rw [hcentered, zero_div]
  exact stein_brascampLieb_interval hab.le q f₁ p V₁ V₂ g hq hp' hV₁ hg
    hf₁c hV₂c hga hgb (fun x => (hp₀ x).le) hV₂

theorem interval_centered_square (V f : ℝ → ℝ) (hV : Continuous V)
    (hf : Continuous f) {a b : ℝ} (hab : a < b) :
    (∫ x in a..b, (f x - intervalMean V f a b) ^ 2 * Real.exp (-V x)) =
      (∫ x in a..b, f x ^ 2 * Real.exp (-V x)) -
      (∫ x in a..b, f x * Real.exp (-V x)) ^ 2 / intervalPartition V a b := by
  let m := intervalMean V f a b
  let p := fun x => Real.exp (-V x)
  have hp : Continuous p := Real.continuous_exp.comp hV.neg
  have hi₁ : IntervalIntegrable (fun x => f x ^ 2 * p x) volume a b :=
    ((hf.pow 2).mul hp).intervalIntegrable a b
  have hi₂ : IntervalIntegrable (fun x => 2 * m * (f x * p x)) volume a b :=
    ((hf.mul hp).const_mul (2*m)).intervalIntegrable a b
  have hi₃ : IntervalIntegrable (fun x => m ^ 2 * p x) volume a b :=
    (hp.const_mul (m^2)).intervalIntegrable a b
  change (∫ x in a..b, (f x - m)^2*p x) = _
  simp_rw [show ∀ x, (f x-m)^2*p x = f x^2*p x - 2*m*(f x*p x) + m^2*p x by intro x; ring]
  rw [intervalIntegral.integral_add (hi₁.sub hi₂) hi₃,
    intervalIntegral.integral_sub hi₁ hi₂, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul]
  have hZ := ne_of_gt (intervalPartition_pos hV hab)
  dsimp only [m, intervalMean, p]
  change _ = _ - _ / (∫ x in a..b, Real.exp (-V x))
  dsimp only [intervalPartition] at *
  field_simp
  ring

theorem brascampLieb_interval_variance
    {a b : ℝ} (hab : a < b) (V V₁ V₂ f f₁ : ℝ → ℝ)
    (hV : ∀ x, HasDerivAt V (V₁ x) x)
    (hV₁ : ∀ x, HasDerivAt V₁ (V₂ x) x)
    (hf : ∀ x, HasDerivAt f (f₁ x) x)
    (hV₂c : Continuous V₂) (hf₁c : Continuous f₁)
    (hV₂ : ∀ x, 0 < V₂ x) :
    intervalMean V (fun x => f x ^ 2) a b - (intervalMean V f a b) ^ 2 ≤
      intervalMean V (fun x => f₁ x ^ 2 / V₂ x) a b := by
  have hVc : Continuous V := continuous_iff_continuousAt.mpr fun x => (hV x).continuousAt
  have hfc : Continuous f := continuous_iff_continuousAt.mpr fun x => (hf x).continuousAt
  have hZ := intervalPartition_pos hVc hab
  have h := brascampLieb_interval hab V V₁ V₂ f f₁ hV hV₁ hf hV₂c hf₁c hV₂
  rw [interval_centered_square V f hVc hfc hab] at h
  have hdiv := div_le_div_of_nonneg_right h hZ.le
  convert! hdiv using 1
  dsimp only [intervalMean]
  field_simp

theorem brascampLieb_interval_schur
    {a b c : ℝ} (hab : a < b) (V V₁ V₂ f f₁ A : ℝ → ℝ)
    (hV : ∀ x, HasDerivAt V (V₁ x) x)
    (hV₁ : ∀ x, HasDerivAt V₁ (V₂ x) x)
    (hf : ∀ x, HasDerivAt f (f₁ x) x)
    (hV₂c : Continuous V₂) (hf₁c : Continuous f₁) (hAc : Continuous A)
    (hV₂ : ∀ x, 0 < V₂ x)
    (hschur : ∀ x, c ≤ A x - f₁ x ^ 2 / V₂ x) :
    c ≤ intervalMean V A a b -
      (intervalMean V (fun x => f x ^ 2) a b - (intervalMean V f a b) ^ 2) := by
  have hBL := brascampLieb_interval_variance hab V V₁ V₂ f f₁ hV hV₁ hf hV₂c hf₁c hV₂
  have hVc : Continuous V := continuous_iff_continuousAt.mpr fun x => (hV x).continuousAt
  have hp : Continuous (fun x => Real.exp (-V x)) := Real.continuous_exp.comp hVc.neg
  have hZ := intervalPartition_pos hVc hab
  have hFc : Continuous (fun x => f₁ x ^ 2 / V₂ x) :=
    (hf₁c.pow 2).div hV₂c (fun x => ne_of_gt (hV₂ x))
  have hmono : c * intervalPartition V a b ≤
      (∫ x in a..b, A x * Real.exp (-V x)) -
      (∫ x in a..b, (f₁ x ^ 2 / V₂ x) * Real.exp (-V x)) := by
    rw [intervalPartition, ← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_sub ((show Continuous (fun x => A x * Real.exp (-V x)) from hAc.mul hp).intervalIntegrable a b)
        ((show Continuous (fun x => (f₁ x^2/V₂ x) * Real.exp (-V x)) from hFc.mul hp).intervalIntegrable a b)]
    apply intervalIntegral.integral_mono_on hab.le
    · exact (hp.const_mul c).intervalIntegrable a b
    · exact ((hAc.mul hp).sub (hFc.mul hp)).intervalIntegrable a b
    · intro x _
      nlinarith [mul_le_mul_of_nonneg_right (hschur x) (Real.exp_pos (-V x)).le]
  have hS : c ≤ intervalMean V A a b - intervalMean V (fun x => f₁ x^2/V₂ x) a b := by
    dsimp only [intervalMean]
    rw [← sub_div, le_div_iff₀ hZ]
    exact hmono
  linarith

end SK.Analytic

end
end
end
end
end

end OAI
