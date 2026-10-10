import Mathlib
import OAI.Combinatorics.SharpRamsey.Entropy.LargeCard

namespace OAI

namespace SharpRamseyFive.PoissonScore
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal Classical
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
lemma batch_real_singleton (rate : ι→ℝ≥0) (ω : ι→ℕ) :
    (batchMeasure rate).real {ω}=
      Real.exp (-(∑i,(rate i:ℝ)))*(∏i,(rate i:ℝ)^(ω i))/(∏i,(ω i).factorial:ℝ) := by
  simp only [measureReal_def,batchMeasure,Measure.pi_singleton,ENNReal.toReal_prod]
  simp_rw [←measureReal_def,poissonMeasure_real_singleton]
  rw [Finset.prod_div_distrib,Finset.prod_mul_distrib,←Real.exp_sum,Finset.sum_neg_distrib]

omit [DecidableEq ι] in
lemma batch_singleton_likelihood (proposal trueRate : ι→ℝ≥0)
    (htotal : (∑i,(proposal i:ℝ))=∑i,(trueRate i:ℝ))
    {D : ℝ} (hD : ∀i,Real.exp (-D)*(trueRate i:ℝ)≤proposal i) (ω : ι→ℕ) :
    Real.exp (-D*(∑i,ω i))*(batchMeasure trueRate).real {ω}≤
      (batchMeasure proposal).real {ω} := by
  rw [batch_real_singleton,batch_real_singleton,htotal]
  have hp : Real.exp (-D*(∑i,ω i))*(∏i,(trueRate i:ℝ)^(ω i))≤
      ∏i,(proposal i:ℝ)^(ω i) := by
    calc
      _ = ∏i,(Real.exp (-D)*(trueRate i:ℝ))^(ω i) := by
        simp only [mul_pow,Finset.prod_mul_distrib,Finset.prod_pow_eq_pow_sum]
        rw [←Real.exp_nat_mul]
        congr 2
        push_cast
        ring
      _ ≤ _ := Finset.prod_le_prod₀ (fun _ _ => pow_nonneg (by positivity) _)
        (fun i _ => pow_le_pow_left₀ (by positivity) (hD i) _)
  have hn : (0:ℝ)<∏i,((ω i).factorial:ℝ) := Finset.prod_pos fun _ _ => Nat.cast_pos.mpr (Nat.factorial_pos _)
  calc
    _ = (Real.exp (-(∑i,(trueRate i:ℝ)))*
        (Real.exp (-D*(∑i,ω i))*(∏i,(trueRate i:ℝ)^(ω i))))/(∏i,(ω i).factorial:ℝ) := by ring
    _ ≤ _ := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hp (Real.exp_nonneg _)) hn.le

lemma real_event_domination {α : Type*} [MeasurableSpace α] [Countable α]
    [MeasurableSingletonClass α] (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (E : Set α) (hE : MeasurableSet E) {a : ℝ} (ha : 0≤a)
    (h : ∀x∈E,a*μ.real {x}≤ν.real {x}) : a*μ.real E≤ν.real E := by
  have hh (x : α) : ENNReal.ofReal a*E.indicator (fun y => μ {y}) x≤
      E.indicator (fun y => ν {y}) x := by
    by_cases hx : x∈E
    · simp only [Set.indicator_of_mem hx]
      have he := ENNReal.ofReal_le_ofReal (h x hx)
      simpa only [ENNReal.ofReal_mul ha,ofReal_measureReal (measure_ne_top μ {x}),ofReal_measureReal (measure_ne_top ν {x})] using he
    · simp [Set.indicator_of_notMem hx]
  have ht := ENNReal.tsum_le_tsum hh
  rw [ENNReal.tsum_mul_left,Measure.tsum_indicator_apply_singleton μ E hE,
    Measure.tsum_indicator_apply_singleton ν E hE] at ht
  have hr := ENNReal.toReal_mono (measure_ne_top ν E) ht
  simpa only [ENNReal.toReal_mul,ENNReal.toReal_ofReal ha,measureReal_def] using hr

omit [DecidableEq ι] in
theorem batch_event_likelihood (proposal trueRate : ι→ℝ≥0)
    (htotal : (∑i,(proposal i:ℝ))=∑i,(trueRate i:ℝ))
    {D K : ℝ} (hD : 0≤D) (hrate : ∀i,Real.exp (-D)*(trueRate i:ℝ)≤proposal i)
    (E : Set (ι→ℕ)) (hsize : ∀ω∈E,(∑i,ω i:ℕ)≤K) :
    Real.exp (-D*K)*(batchMeasure trueRate).real E≤(batchMeasure proposal).real E := by
  apply real_event_domination _ _ E (by exact Set.to_countable E |>.measurableSet) (Real.exp_nonneg _)
  intro ω hω
  apply le_trans _ (batch_singleton_likelihood proposal trueRate htotal hrate ω)
  apply mul_le_mul_of_nonneg_right _ measureReal_nonneg
  exact Real.exp_le_exp.mpr (by nlinarith only [hsize ω hω,hD])

end SharpRamseyFive.PoissonScore

end OAI
