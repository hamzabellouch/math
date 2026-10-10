import Mathlib
import OAI.Combinatorics.SharpRamsey.Entropy.LargeCard
import OAI.Combinatorics.RamseyFive.Probability.Aggregate

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.PoissonScore
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal Classical
variable {ι D H : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype D] [DecidableEq D] [Fintype H]

omit [DecidableEq ι] [Fintype D] [Fintype H] in
lemma typicalScore_aggregate (label : ι→D) {R : ℕ} (s : Finset H)
    (lines : H→Finset D) (b : ℝ) (own : H→Fin R→Bool) (ω : Fin R→ι→ℕ) :
    typicalScore s lines b own (fun r => aggregate label (ω r)) =
      typicalScore s (fun h => Finset.univ.filter fun i => label i∈lines h) b own ω := by
  unfold typicalScore
  simp_rw [scoreTerm_aggregate]

omit [Fintype H] in
lemma integral_original_score_pow (label : ι→D) (rate : ι→ℝ≥0)
    {R : ℕ} (s : Finset H) (lines : H→Finset D) (b : ℝ)
    (own : H→Fin R→Bool) (p : ℕ) :
    (∫ ω,(typicalScore s (fun h => Finset.univ.filter fun i => label i∈lines h) b own ω)^p
      ∂scheduleMeasure rate R) =
    ∫ ω,(typicalScore s lines b own ω)^p ∂scheduleMeasure (aggregateRate label rate) R := by
  simp_rw [←typicalScore_aggregate label s lines b own]
  exact (measurePreserving_schedule_aggregate label rate R).hasLaw.integral_comp
    (measurable_of_countable (fun ω : Fin R→D→ℕ => (typicalScore s lines b own ω)^p)).aestronglyMeasurable

end SharpRamseyFive.PoissonScore

end OAI
