import OAI.Probability.ClassicalON.PlanarAlgebra

namespace OAI

universe uE uX

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ClassicalON

theorem exp_gram_integral_nonneg {X : Type uX} {E : Type uE} [Fintype E]
    [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
    [SecondCountableTopology X] (μ : Measure X) [IsFiniteMeasure μ]
    {f : X → ℝ} {a : E → X → ℝ} (hf : Continuous f) (ha : ∀ e,Continuous (a e))
    (b : E → ℝ) (hb : ∀ e,0≤b e) :
    0≤∫ p : X×X,f p.1*f p.2*Real.exp (∑ e,b e*(a e p.1*a e p.2)) ∂μ.prod μ := by
  apply integral_mul_sum_exp_nonneg (μ.prod μ) (by fun_prop)
    (a := fun e p => a e p.1*a e p.2) (fun e => by fun_prop) b hb
  intro k p
  have he : (fun z : X×X => f z.1*f z.2*∏ i,a (p i) z.1*a (p i) z.2) =
      (fun z : X×X => (f z.1*∏ i,a (p i) z.1)*(f z.2*∏ i,a (p i) z.2)) := by
    funext z; rw [Finset.prod_mul_distrib]; ring
  rw [he,integral_prod_mul (fun x => f x*∏ i,a (p i) x) (fun x => f x*∏ i,a (p i) x)]
  exact mul_self_nonneg _

end ClassicalON

end

end OAI
