import Mathlib
import OAI.Combinatorics.SharpRamsey.Entropy.LargeCard

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.PoissonScore
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal Classical
variable {D : Type} [Fintype D] [DecidableEq D]

omit [DecidableEq D] in
lemma integral_forcedHits_le (rate : D→ℝ≥0) {R : ℕ} (d : D) (T : Finset (Fin R)) :
    (∫ ω,forcedHits d T ω ∂scheduleMeasure rate R) ≤ (rate d:ℝ)^T.card := by
  have he (ω : Fin R→D→ℕ) : forcedHits d T ω =
      ∏ r : Fin R,if r∈T then hitIndicator d (ω r) else 1 := by
    simp only [Finset.prod_ite_mem,Finset.univ_inter,forcedHits]
  simp_rw [he]
  unfold scheduleMeasure
  rw [integral_fintype_prod_eq_prod (f := fun r ω => if r∈T then hitIndicator d ω else 1)]
  have he' (r : Fin R) : (∫ ω : D→ℕ,(if r∈T then hitIndicator d ω else 1) ∂batchMeasure rate) =
      if r∈T then 1-Real.exp (-(rate d:ℝ)) else 1 := by
    split_ifs <;> simp [integral_hitIndicator]
  simp_rw [he']
  simp only [Finset.prod_ite_mem,Finset.univ_inter,Finset.prod_const]
  exact pow_le_pow_left₀ (by have := Real.exp_le_one_iff.mpr (neg_nonpos.mpr (rate d).coe_nonneg); linarith)
    (one_sub_exp_neg_le (rate d:ℝ)) _

omit [DecidableEq D] in
theorem overload_probability (rate : D→ℝ≥0) {R : ℕ} (s : Finset D) (J : ℕ) :
    (scheduleMeasure rate R).real (overloaded s J) ≤ ∑ d∈s,((R:ℝ)*(rate d:ℝ))^J := by
  have hint := integrable_schedule_of_abs_le (R := R) rate
    ((overloaded s J).indicator (fun _ => (1:ℝ))) 1 (by
      intro ω; by_cases he : ω∈overloaded s J <;> simp [he])
  have hf (d : D) (T : Finset (Fin R)) : Integrable (forcedHits d T) (scheduleMeasure rate R) :=
    integrable_schedule_of_abs_le rate _ 1 (fun ω => by
      rw [abs_of_nonneg (forcedHits_nonneg d T ω)]; exact forcedHits_le_one d T ω)
  have hset : MeasurableSet (overloaded s J : Set (Fin R→D→ℕ)) := Set.to_countable _ |>.measurableSet
  have heq := integral_indicator_const (μ := scheduleMeasure rate R) (1:ℝ) hset
  simp only [smul_eq_mul,mul_one] at heq
  rw [←heq]
  calc
    _ ≤ ∫ ω,∑ d∈s,∑ T∈(Finset.univ : Finset (Fin R)).powersetCard J,forcedHits d T ω
        ∂scheduleMeasure rate R := integral_mono hint
          (integrable_finsetSum _ (fun d _ => integrable_finsetSum _ (fun T _ => hf d T)))
          (overload_indicator_le_certificates s J)
    _ = ∑ d∈s,∑ T∈(Finset.univ : Finset (Fin R)).powersetCard J,
        ∫ ω,forcedHits d T ω ∂scheduleMeasure rate R := by
      rw [integral_finsetSum _ (fun d _ => integrable_finsetSum _ (fun T _ => hf d T))]
      apply Finset.sum_congr rfl
      intro d hd
      rw [integral_finsetSum _ (fun T _ => hf d T)]
    _ ≤ ∑ d∈s,((R:ℝ)*(rate d:ℝ))^J := by
      apply Finset.sum_le_sum
      intro d hd
      calc
        _ ≤ ∑ _T∈(Finset.univ : Finset (Fin R)).powersetCard J,(rate d:ℝ)^J :=
          Finset.sum_le_sum fun T hT => by
            simpa only [(Finset.mem_powersetCard.mp hT).2] using integral_forcedHits_le rate d T
        _ = (R.choose J:ℝ)*(rate d:ℝ)^J := by simp
        _ ≤ _ := by
          rw [mul_pow]
          apply mul_le_mul_of_nonneg_right _ (pow_nonneg (rate d).coe_nonneg _)
          exact_mod_cast Nat.choose_le_pow R J

end SharpRamseyFive.PoissonScore

namespace SharpRamseyFive.HighMoment
open MeasureTheory ProbabilityTheory PoissonScore TupleComponents
open scoped BigOperators NNReal Classical
variable {D : Type} [Fintype D] [DecidableEq D]

omit [DecidableEq D] in
lemma allTrunc_indicator (R J : ℕ) (ω : Fin R→D→ℕ) :
    1-allTrunc R J (Function.uncurry ω) =
      (overloaded Finset.univ J).indicator (fun _ => (1:ℝ)) ω := by
  by_cases he : ω∈(overloaded Finset.univ J : Set (Fin R→D→ℕ))
  · rw [Set.indicator_of_mem he]
    obtain ⟨d,_,hd⟩ := he
    have hz : allTrunc R J (Function.uncurry ω)=0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ d)
      exact ite_eq_right (by exact not_lt.mpr hd)
    rw [hz,sub_zero]
  · rw [Set.indicator_of_notMem he]
    have ho : allTrunc R J (Function.uncurry ω)=1 := by
      apply Finset.prod_eq_one
      intro d _
      apply ite_eq_left
      by_contra hn
      exact he ⟨d,Finset.mem_univ _,le_of_not_gt hn⟩
    rw [ho,sub_self]

omit [DecidableEq D] in
theorem allTrunc_failure (rate : D→ℝ≥0) (R J : ℕ) :
    (∫ ω,1-allTrunc R J ω ∂batchMeasure (fun p : Fin R×D => rate p.2)) ≤
      ∑ d : D,((R:ℝ)*(rate d:ℝ))^J := by
  rw [←(measurePreserving_uncurry_schedule rate R).integral_comp' (fun ω => 1-allTrunc R J ω)]
  change (∫ ω,1-allTrunc R J (Function.uncurry ω) ∂scheduleMeasure rate R) ≤ _
  simp_rw [allTrunc_indicator]
  have hset : MeasurableSet (overloaded Finset.univ J : Set (Fin R→D→ℕ)) := Set.to_countable _ |>.measurableSet
  rw [integral_indicator_const (1:ℝ) hset]
  simp only [smul_eq_mul,mul_one]
  exact overload_probability rate Finset.univ J

end SharpRamseyFive.HighMoment

end OAI
