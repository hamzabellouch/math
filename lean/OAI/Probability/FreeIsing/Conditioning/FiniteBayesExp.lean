import OAI.Probability.FreeIsing.Conditioning.FiniteBayes

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

namespace Problem367.FiniteBayes

theorem posterior_integral
    {A X : Type*} [MeasurableSpace A] [MeasurableSpace X]
    [Fintype A] [Nonempty A] [StandardBorelSpace A]
    [MeasurableSingletonClass A]
    (mu : Measure A) [IsProbabilityMeasure mu]
    (kappa : Kernel A X) [IsFiniteKernel kappa]
    (nu : Measure X) [SigmaFinite nu]
    (L : A → X → ℝ) (hL : ∀ a, Measurable (L a))
    (hLpos : ∀ a x, 0 < L a x)
    (hkappa : ∀ a, kappa a = nu.withDensity (fun x => ENNReal.ofReal (L a x)))
    (q : A → ℝ) :
    ∀ᵐ x ∂kappa ∘ₘ mu,
      (∫ a, q a ∂(kappa†mu) x) =
        (∑ a, mu.real {a} * L a x * q a) / (∑ a, mu.real {a} * L a x) := by
  have hpost := finite_posterior_singletons_of_positive mu nu kappa
    (fun a x => ENNReal.ofReal (L a x))
    (fun a => (hL a).ennreal_ofReal) hkappa
    (fun a x => ne_of_gt (ENNReal.ofReal_pos.mpr (hLpos a x)))
    (fun a x => ENNReal.ofReal_ne_top)
  filter_upwards [hpost] with x hx
  have hden : (∑ a, mu {a} * ENNReal.ofReal (L a x)).toReal =
      ∑ a, mu.real {a} * L a x := by
    rw [ENNReal.toReal_sum (fun a _ =>
      ENNReal.mul_ne_top (measure_ne_top mu {a}) ENNReal.ofReal_ne_top)]
    apply Finset.sum_congr rfl
    intro a _
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (hLpos a x).le]
    rfl
  rw [integral_fintype Integrable.of_finite, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro a _
  change ((kappa†mu) x {a}).toReal * q a = _
  rw [hx a, ENNReal.toReal_div, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (hLpos a x).le, hden]
  unfold Measure.real
  ring

theorem posterior_integral_exp
    {A X : Type*} [MeasurableSpace A] [MeasurableSpace X]
    [Fintype A] [Nonempty A] [StandardBorelSpace A]
    [MeasurableSingletonClass A]
    (mu : Measure A) [IsProbabilityMeasure mu]
    (kappa : Kernel A X) [IsFiniteKernel kappa]
    (nu : Measure X) [SigmaFinite nu]
    (E : A → X → ℝ) (hE : ∀ a, Measurable (E a))
    (c : X → ℝ) (hc : Measurable c) (hcpos : ∀ x, 0 < c x)
    (hkappa : ∀ a, kappa a =
      nu.withDensity (fun x => ENNReal.ofReal (c x * Real.exp (E a x))))
    (q : A → ℝ) :
    ∀ᵐ x ∂kappa ∘ₘ mu,
      (∫ a, q a ∂(kappa†mu) x) =
        (∑ a, mu.real {a} * Real.exp (E a x) * q a) /
          (∑ a, mu.real {a} * Real.exp (E a x)) := by
  have hpost := posterior_integral mu kappa nu
    (fun a x => c x * Real.exp (E a x))
    (fun a => hc.mul (hE a).exp)
    (fun a x => mul_pos (hcpos x) (Real.exp_pos _)) hkappa q
  filter_upwards [hpost] with x hx
  rw [hx]
  have hnum : (∑ a, mu.real {a} * (c x * Real.exp (E a x)) * q a) =
      c x * ∑ a, mu.real {a} * Real.exp (E a x) * q a := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    ring
  have hden : (∑ a, mu.real {a} * (c x * Real.exp (E a x))) =
      c x * ∑ a, mu.real {a} * Real.exp (E a x) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    ring
  rw [hnum, hden, mul_div_mul_left _ _ (ne_of_gt (hcpos x))]

end Problem367.FiniteBayes

end

end OAI
