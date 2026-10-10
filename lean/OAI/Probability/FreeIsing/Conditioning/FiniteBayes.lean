import Mathlib

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal ProbabilityTheory

namespace Problem367

theorem finite_observation_law_density
    {A X : Type*} [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
    [MeasurableSpace X] (π : Measure A) (ν : Measure X) (κ : Kernel A X)
    (L : A → X → ℝ≥0∞) (hL : ∀ a, Measurable (L a))
    (hκ : ∀ a, κ a = ν.withDensity (L a)) :
    κ ∘ₘ π = ν.withDensity (fun x => ∑ a, π {a} * L a x) := by
  ext s hs
  rw [Measure.bind_apply hs κ.aemeasurable, withDensity_apply _ hs,
    lintegral_fintype]
  simp_rw [hκ, withDensity_apply _ hs]
  rw [lintegral_finsetSum]
  · apply Finset.sum_congr rfl
    intro a ha
    rw [lintegral_const_mul _ (hL a), mul_comm]
  · intro a ha
    exact measurable_const.mul (hL a)

theorem finite_posterior_singletons
    {A X : Type*} [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
    [StandardBorelSpace A] [Nonempty A] [MeasurableSpace X]
    (π : Measure A) [IsFiniteMeasure π] (ν : Measure X) [SigmaFinite ν]
    (κ : Kernel A X) [IsFiniteKernel κ]
    (L : A → X → ℝ≥0∞) (hL : ∀ a, Measurable (L a))
    (hκ : ∀ a, κ a = ν.withDensity (L a))
    (hpos : ∀ᵐ x ∂ν, (∑ a, π {a} * L a x) ≠ 0)
    (hfinite : ∀ᵐ x ∂ν, (∑ a, π {a} * L a x) ≠ ∞) :
    ∀ᵐ x ∂κ ∘ₘ π, ∀ a,
      (posterior κ π) x {a} = π {a} * L a x / (∑ b, π {b} * L b x) := by
  let Z : X → ℝ≥0∞ := fun x => ∑ a, π {a} * L a x
  have hZ : Measurable Z := by
    exact Finset.measurable_sum _ (fun a _ => measurable_const.mul (hL a))
  have hdata : κ ∘ₘ π = ν.withDensity Z := finite_observation_law_density π ν κ L hL hκ
  have hRNν (a : A) :
      (κ a).rnDeriv (κ ∘ₘ π) =ᵐ[ν] fun x => L a x / Z x := by
    rw [hdata]
    have hright := Measure.rnDeriv_withDensity_right (κ a) ν hZ.aemeasurable hpos hfinite
    have hleft : (κ a).rnDeriv ν =ᵐ[ν] L a := by
      rw [hκ a]
      exact Measure.rnDeriv_withDensity ν (hL a)
    filter_upwards [hright, hleft] with x hr hl
    rw [hr, hl, div_eq_mul_inv, mul_comm]
  have hRN (a : A) :
      (κ a).rnDeriv (κ ∘ₘ π) =ᵐ[κ ∘ₘ π] fun x => L a x / Z x := by
    have hac : κ ∘ₘ π ≪ ν := by
      rw [hdata]
      exact withDensity_absolutelyContinuous ν Z
    exact hac.ae_eq (hRNν a)
  have hpost := posterior_eq_withDensity_of_countable κ π
  filter_upwards [hpost, ae_all_iff.mpr hRN] with x hx hRNx
  intro a
  rw [hx]
  simp only [withDensity_apply _ (measurableSet_singleton a), lintegral_singleton]
  rw [hRNx a]
  dsimp only [Z]
  simp only [div_eq_mul_inv]
  ac_rfl

theorem finite_posterior_singletons_of_positive
    {A X : Type*} [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
    [StandardBorelSpace A] [Nonempty A] [MeasurableSpace X]
    (π : Measure A) [IsProbabilityMeasure π] (ν : Measure X) [SigmaFinite ν]
    (κ : Kernel A X) [IsFiniteKernel κ]
    (L : A → X → ℝ≥0∞) (hL : ∀ a, Measurable (L a))
    (hκ : ∀ a, κ a = ν.withDensity (L a))
    (hpos : ∀ a x, L a x ≠ 0) (hfinite : ∀ a x, L a x ≠ ∞) :
    ∀ᵐ x ∂κ ∘ₘ π, ∀ a,
      (posterior κ π) x {a} = π {a} * L a x / (∑ b, π {b} * L b x) := by
  have hp : ∃ a, π {a} ≠ 0 := by
    by_contra! h
    have hs : (∑ a, π {a}) = 0 := Finset.sum_eq_zero (fun a _ => h a)
    simp at hs
  obtain ⟨a, ha⟩ := hp
  apply finite_posterior_singletons π ν κ L hL hκ
  · apply ae_of_all
    intro x
    apply ne_of_gt
    apply lt_of_lt_of_le (pos_iff_ne_zero.mpr (mul_ne_zero ha (hpos a x)))
    exact Finset.single_le_sum (f := fun b => π {b} * L b x)
      (fun b _ => zero_le) (Finset.mem_univ a)
  · apply ae_of_all
    intro x
    exact ENNReal.sum_ne_top.mpr (fun b _ => ENNReal.mul_ne_top (measure_ne_top π _) (hfinite b x))

theorem finite_posterior_mean
    {A X : Type*} [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
    [StandardBorelSpace A] [Nonempty A] [MeasurableSpace X]
    (π : Measure A) [IsProbabilityMeasure π] (ν : Measure X) [SigmaFinite ν]
    (κ : Kernel A X) [IsFiniteKernel κ]
    (L : A → X → ℝ≥0∞) (hL : ∀ a, Measurable (L a))
    (hκ : ∀ a, κ a = ν.withDensity (L a))
    (hpos : ∀ a x, L a x ≠ 0) (hfinite : ∀ a x, L a x ≠ ∞)
    (f : A → ℝ) :
    ∀ᵐ x ∂κ ∘ₘ π,
      (∫ a, f a ∂(posterior κ π) x) =
        ∑ a, f a * (π {a} * L a x / (∑ b, π {b} * L b x)).toReal := by
  filter_upwards [finite_posterior_singletons_of_positive π ν κ L hL hκ hpos hfinite]
    with x hx
  rw [integral_fintype Integrable.of_finite]
  apply Finset.sum_congr rfl
  intro a ha
  rw [measureReal_def, hx a, smul_eq_mul, mul_comm]

end Problem367

end

end OAI
