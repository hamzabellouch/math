import Mathlib
import OAI.Combinatorics.SharpRamsey.Entropy.LargeCard
import OAI.Combinatorics.RamseyFive.Probability.TypicalScoreAggregate
import OAI.Combinatorics.RamseyFive.Probability.AbsScoreTerm

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.PoissonScore
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal Classical
variable {ι D H : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype D] [DecidableEq D] [Fintype H]

omit [DecidableEq ι] [DecidableEq D] [Fintype H] in
theorem original_uniform_weighted_score_moment (p : ι→Prop) [DecidablePred p]
    (e : {i // ¬p i}≃D) (rate : ℝ≥0) {R : ℕ}
    (F : Finset H) (lines : H→Finset D) {b : ℝ} (hb : b∈Set.Icc 0 1)
    (own : (Fin R→{i // p i}→ℕ)→H→Fin R→Bool)
    (g : (Fin R→D→ℕ)→ℝ) (hg : ∀v,|g v|≤1) (k : ℕ) (B : ℝ)
    (hB : ∀u,(∫ v,g v*(typicalScore F lines b (own u) v)^k
      ∂scheduleMeasure (fun _ : D => rate) R)≤B) :
    (∫ ω,g (fun r d => ω r (e.symm d).val)*
      (typicalScore F lines b (own (fun r i => ω r i))
        (fun r d => ω r (e.symm d).val))^k ∂scheduleMeasure (fun _ : ι => rate) R)≤B := by
  apply integral_split_schedule_le (fun _ : ι => rate) p
    (fun u v => g (fun r d => v r (e.symm d))*
      (typicalScore F lines b (own u) (fun r d => v r (e.symm d)))^k)
    ((F.card:ℝ)^k) B
  · intro u v
    rw [abs_mul,abs_pow]
    exact (mul_le_mul (hg _) (pow_le_pow_left₀ (abs_nonneg _)
      (abs_typicalScore_le_card F lines hb (own u) _) k) (pow_nonneg (abs_nonneg _) _)
      (by norm_num)).trans_eq (one_mul _)
  · intro u
    rw [integral_schedule_reindex e (fun _ : D => rate)
      (fun v => g v*(typicalScore F lines b (own u) v)^k)]
    exact hB u

omit [Fintype H] in
lemma integral_original_weighted_score_pow (label : ι→D) (rate : ι→ℝ≥0)
    {R : ℕ} (s : Finset H) (lines : H→Finset D) (b : ℝ)
    (own : H→Fin R→Bool) (p : ℕ) (g : (Fin R→D→ℕ)→ℝ) :
    (∫ ω,g (fun r => aggregate label (ω r))*
      (typicalScore s (fun h => Finset.univ.filter fun i => label i∈lines h) b own ω)^p
      ∂scheduleMeasure rate R) =
    ∫ ω,g ω*(typicalScore s lines b own ω)^p ∂scheduleMeasure (aggregateRate label rate) R := by
  simp_rw [←typicalScore_aggregate label s lines b own]
  exact (measurePreserving_schedule_aggregate label rate R).hasLaw.integral_comp
    (measurable_of_countable (fun ω : Fin R→D→ℕ =>
      g ω*(typicalScore s lines b own ω)^p)).aestronglyMeasurable

end SharpRamseyFive.PoissonScore

end OAI
