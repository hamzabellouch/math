import Mathlib

namespace OAI

universe u_A u_V

open MeasureTheory

namespace Problem310.ExposureMoments

/-- Joint masses of complete finite/countable patterns determine the law after
restriction to an exposure event. No division by the mass of the event is needed. -/
theorem map_restrict_eq_smul_of_fibers
    {A : Type u_A} {V : Type u_V} [MeasurableSpace A] [MeasurableSpace V]
    [Countable V] [MeasurableSingletonClass V]
    (μ : Measure A) (ν : Measure V) (E : Set A) (f : A → V)
    (hf : Measurable f)
    (hjoint : ∀ v, μ (E ∩ {a | f a = v}) = μ E * ν {v}) :
    Measure.map f (μ.restrict E) = μ E • ν := by
  apply Measure.ext_of_singleton
  intro v
  rw [Measure.map_apply hf (measurableSet_singleton v),
    Measure.restrict_apply (hf (measurableSet_singleton v)), Measure.smul_apply]
  change μ ({a | f a = v} ∩ E) = μ E * ν {v}
  rw [Set.inter_comm]
  exact hjoint v

/-- The exposure factorization extends from pattern events to every nonnegative
function of the fresh pattern, including the active-test generating function. -/
theorem lintegral_restrict_comp_of_fibers
    {A : Type u_A} {V : Type u_V} [MeasurableSpace A] [MeasurableSpace V]
    [Countable V] [MeasurableSingletonClass V]
    (μ : Measure A) (ν : Measure V) (E : Set A) (f : A → V)
    (hf : Measurable f)
    (hjoint : ∀ v, μ (E ∩ {a | f a = v}) = μ E * ν {v})
    (g : V → ENNReal) (hg : Measurable g) :
    (∫⁻ a in E, g (f a) ∂μ) = μ E * ∫⁻ v, g v ∂ν := by
  rw [← lintegral_map hg hf,
    map_restrict_eq_smul_of_fibers μ ν E f hf hjoint,
    lintegral_smul_measure]
  rfl

/-- A supplied fresh-pattern moment can be used unchanged after center exposure. -/
theorem lintegral_restrict_comp_eq_of_fibers
    {A : Type u_A} {V : Type u_V} [MeasurableSpace A] [MeasurableSpace V]
    [Countable V] [MeasurableSingletonClass V]
    (μ : Measure A) (ν : Measure V) (E : Set A) (f : A → V)
    (hf : Measurable f)
    (hjoint : ∀ v, μ (E ∩ {a | f a = v}) = μ E * ν {v})
    (g : V → ENNReal) (hg : Measurable g) (q : ENNReal)
    (hmoment : (∫⁻ v, g v ∂ν) = q) :
    (∫⁻ a in E, g (f a) ∂μ) = μ E * q := by
  rw [lintegral_restrict_comp_of_fibers μ ν E f hf hjoint g hg, hmoment]

end Problem310.ExposureMoments

end OAI
