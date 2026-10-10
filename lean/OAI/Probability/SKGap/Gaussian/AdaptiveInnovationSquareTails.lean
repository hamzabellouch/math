import Mathlib
import OAI.Probability.SKGap.Gaussian.SquareTail2

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal ENNReal
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal ENNReal
open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix Matrix.Norms.Elementwise
open scoped BigOperators
open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix Matrix.Norms.Elementwise
open scoped BigOperators
open scoped BigOperators NNReal ENNReal
open MeasureTheory Metric Set
open scoped BigOperators NNReal ENNReal
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators NNReal ENNReal Matrix.Norms.L2Operator
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Matrix.Norms.L2Operator
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Set
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal ENNReal Matrix
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal ENNReal
open scoped BigOperators
open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix Matrix.Norms.Elementwise NNReal ENNReal
open scoped BigOperators
open Filter Topology
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal ENNReal Topology
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal ENNReal Topology
namespace SKGapCutoff.Regression

theorem adaptive_innovation_squareTails
    {H : ℕ → Type*} [∀ n, MeasurableSpace (H n)]
    (ρ : ∀ n, Measure (H n)) [∀ n, IsProbabilityMeasure (ρ n)] (r : ℕ)
    (U : ∀ n, H n → Fin n → Fin r → ℝ) (q : ∀ n, H n → Fin n → ℝ)
    (hUm : ∀ n, Measurable (U n)) (hqm : ∀ n, Measurable (q n))
    (hU : ∀ n h a, ∑ i, U n h i a^2 ≤ 1) (hq : ∀ n h, ∑ i, q n h i^2 ≤ 1) :
    ExponentialSquareTails (fun n => (ρ n).prod (standardArrayLaw (Fin n ⊕ Unit)))
      (fun n z i => Real.sqrt n *
        queryInnovation (residualProjection (U n z.1)) (q n z.1) z.2 i) := by
  have hs (n : ℕ) : HasLaw Prod.snd (standardArrayLaw (Fin n ⊕ Unit))
      ((ρ n).prod (standardArrayLaw (Fin n ⊕ Unit))) :=
    ⟨measurable_snd.aemeasurable, measurePreserving_snd.map_eq⟩
  have ht : ExponentialSquareTails (fun n => (ρ n).prod (standardArrayLaw (Fin n ⊕ Unit)))
      (fun _ z i => z.2 (Sum.inl i)) := by
    refine iid_exponential_squareTails
      (fun n => (ρ n).prod (standardArrayLaw (Fin n ⊕ Unit)))
      (fun _ z i => z.2 (Sum.inl i))
      (fun _ _ => (measurable_pi_apply _).comp measurable_snd) ?_ (gaussianReal 0 1) ?_ ?_
    · intro n
      apply iIndepFun_comp_hasLaw (hs n) (fun i g => g (Sum.inl i))
        (fun _ => (measurable_pi_apply _).aemeasurable)
      exact coordinates_independent.precomp Sum.inl_injective
    · intro n i
      exact (coordinate_hasLaw (Sum.inl i)).fun_comp (hs n)
    · exact gaussian_integrable_exp_quarter_sq
  exact ht.l2_stability (adaptive_innovation_error_exponential ρ r U q hUm hqm hU hq)

end SKGapCutoff.Regression

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal BigOperators Topology

end

end OAI
