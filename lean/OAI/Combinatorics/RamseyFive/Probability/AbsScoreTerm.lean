import Mathlib
import OAI.Combinatorics.SharpRamsey.Entropy.LargeCard
import OAI.Combinatorics.RamseyFive.Probability.MeasurePreservingSplitSchedule

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.PoissonScore
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal Classical
variable {ι D H : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype D] [DecidableEq D] [Fintype H]

omit [Fintype ι] [DecidableEq ι] in
lemma abs_scoreTerm_le_one {R : ℕ} (s : Finset ι) {b : ℝ}
    (hb : b∈Set.Icc 0 1) (own : Fin R→Bool) (ω : Fin R→ι→ℕ) :
    |scoreTerm s b own ω|≤1 := by
  unfold scoreTerm
  rw [Finset.abs_prod]
  apply Finset.prod_le_one₀ (fun _ _ => abs_nonneg _)
  intro r _
  split_ifs
  · exact abs_centeredFactor_le_one s b hb _
  · simp

omit [Fintype ι] [DecidableEq ι] [Fintype H] in
lemma abs_typicalScore_le_card {R : ℕ} (F : Finset H) (lines : H→Finset ι)
    {b : ℝ} (hb : b∈Set.Icc 0 1) (own : H→Fin R→Bool) (ω : Fin R→ι→ℕ) :
    |typicalScore F lines b own ω|≤F.card := by
  apply (Finset.abs_sum_le_sum_abs ..).trans
  calc
    (∑ h∈F,|scoreTerm (lines h) b (own h) ω|)≤∑ _h∈F,(1:ℝ) :=
      Finset.sum_le_sum fun h _ => abs_scoreTerm_le_one (lines h) hb (own h) ω
    _ = _ := by simp

omit [DecidableEq ι] [DecidableEq D] in
lemma measurePreserving_schedule_reindex (e : ι≃D) (rate : D→ℝ≥0) (R : ℕ) :
    MeasurePreserving (fun ω : Fin R→ι→ℕ => fun r d => ω r (e.symm d))
      (scheduleMeasure (fun i => rate (e i)) R) (scheduleMeasure rate R) := by
  have h := measurePreserving_pi (fun _ : Fin R => batchMeasure (fun i => rate (e i)))
    (fun _ : Fin R => batchMeasure rate) (fun _ => measurePreserving_piCongrLeft
    (fun d => poissonMeasure (rate d)) e)
  convert h using 1 <;> try rfl
  funext ω r d
  simp [MeasurableEquiv.coe_piCongrLeft,Equiv.piCongrLeft_apply]

omit [DecidableEq ι] [DecidableEq D] in
lemma integral_schedule_reindex (e : ι≃D) (rate : D→ℝ≥0) {R : ℕ}
    (F : (Fin R→D→ℕ)→ℝ) :
    (∫ ω,F (fun r d => ω r (e.symm d)) ∂scheduleMeasure (fun i => rate (e i)) R) =
      ∫ ω,F ω ∂scheduleMeasure rate R :=
  (measurePreserving_schedule_reindex e rate R).hasLaw.integral_comp
    (measurable_of_countable F).aestronglyMeasurable

omit [DecidableEq ι] [DecidableEq D] [Fintype H] in
theorem original_uniform_score_moment (p : ι→Prop) [DecidablePred p]
    (e : {i // ¬p i}≃D) (rate : ℝ≥0) {R : ℕ}
    (F : Finset H) (lines : H→Finset D) {b : ℝ} (hb : b∈Set.Icc 0 1)
    (own : (Fin R→{i // p i}→ℕ)→H→Fin R→Bool) (k : ℕ) (B : ℝ)
    (hB : ∀ u,(∫ v,(typicalScore F lines b (own u) v)^k
      ∂scheduleMeasure (fun _ : D => rate) R)≤B) :
    (∫ ω,(typicalScore F lines b (own (fun r i => ω r i))
      (fun r d => ω r (e.symm d).val))^k ∂scheduleMeasure (fun _ : ι => rate) R)≤B := by
  apply integral_split_schedule_le (fun _ : ι => rate) p
    (fun u v => (typicalScore F lines b (own u) (fun r d => v r (e.symm d)))^k)
    ((F.card:ℝ)^k) B
  · intro u v
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (abs_typicalScore_le_card F lines hb (own u) _) k
  · intro u
    rw [integral_schedule_reindex e (fun _ : D => rate)
      (fun v => (typicalScore F lines b (own u) v)^k)]
    exact hB u

end SharpRamseyFive.PoissonScore

end OAI
