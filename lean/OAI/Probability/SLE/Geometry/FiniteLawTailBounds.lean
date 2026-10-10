import OAI.Probability.SLE.Gauge.MomentBatches

namespace OAI

/-! The batch estimates need only upper moment bounds on finite laws.
Increasing finite-law tails can be passed to their supremum before summing. -/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace SLEExactGauge.MomentBatches

lemma upper_finite_batch_bound {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] (X : Ω → ℝ) (hX : Measurable X)
    (hX0 : ∀ ω, 0 ≤ X ω) {n : ℕ} (hn : 1 ≤ n)
    {m T : ℝ} (hm : 0 < m) (hi : Integrable (fun ω => X ω^n) P)
    (hMoment : (∫ ω, X ω^n ∂P) ≤ m) (S : Finset ℤ) :
    (∑ k ∈ S, (copies n m T k : ℝ)*P.real {ω | 16*dyadic k ≤ X ω}) ≤
      (4:ℝ)^n/16^n/(1-(1/2:ℝ)^n) := by
  let C := (4:ℝ)^n/(m*16^n*(1-(1/2:ℝ)^n))
  have hden : 0 < 1-(1/2:ℝ)^n := denominator_pos hn
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hset (k : ℤ) : MeasurableSet {ω | 16*dyadic k ≤ X ω} :=
    measurableSet_le measurable_const hX
  have hInt (k : ℤ) : Integrable
      (fun ω => if 16*dyadic k ≤ X ω then (copies n m T k : ℝ) else 0) P :=
    (integrable_const _).indicator (hset k)
  calc
    _ = ∫ ω, ∑ k ∈ S, if 16*dyadic k ≤ X ω then (copies n m T k : ℝ) else 0 ∂P :=
      (integral_hit_count P X hX n m T 16 S).symm
    _ ≤ ∫ ω, C*X ω^n ∂P := integral_mono
      (integrable_finsetSum S (fun k _ => hInt k)) (hi.const_mul C)
      (fun ω => hit_count_upper hn hm (hX0 ω) S)
    _ = C*(∫ ω, X ω^n ∂P) := integral_const_mul _ _
    _ ≤ C*m := mul_le_mul_of_nonneg_left hMoment hC
    _ = _ := by dsimp only [C]; field_simp

lemma cleanup_finite_tail_bound {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] (X : Ω → ℝ) (hX : Measurable X)
    (hX0 : ∀ ω, 0 ≤ X ω) (hi : Integrable X P) (S : Finset ℕ) :
    (∑ n ∈ S, P.real {ω | 16*((n:ℝ)+1) ≤ X ω}) ≤ (∫ ω, X ω ∂P)/16 := by
  classical
  have hset (n : ℕ) : MeasurableSet {ω | 16*((n:ℝ)+1) ≤ X ω} :=
    measurableSet_le measurable_const hX
  have hInt (n : ℕ) : Integrable
      (fun ω => if 16*((n:ℝ)+1) ≤ X ω then (1:ℝ) else 0) P :=
    (integrable_const _).indicator (hset n)
  calc
    _ = ∫ ω, ∑ n ∈ S, if 16*((n:ℝ)+1) ≤ X ω then (1:ℝ) else 0 ∂P := by
      rw [integral_finsetSum S (fun n _ => hInt n)]
      apply Finset.sum_congr rfl
      intro n _
      simpa only [Set.indicator,Set.mem_ofPred_eq,smul_eq_mul,mul_one] using
        (integral_indicator_const (μ := P) (1:ℝ) (hset n)).symm
    _ ≤ ∫ ω, X ω/16 ∂P := integral_mono
      (integrable_finsetSum S (fun n _ => hInt n)) (hi.div_const 16)
      (fun ω => cleanup_count_le (hX0 ω) S)
    _ = _ := integral_div _ _

lemma finite_monotone_tail_sum_bound {ι : Type*} (S : Finset ι)
    (c : ι → ℝ≥0∞) (p : ℕ → ι → ℝ≥0∞)
    (hp : ∀ i, Monotone (fun n => p n i)) (A : ℝ≥0∞)
    (hbound : ∀ n, (∑ i ∈ S, c i*p n i) ≤ A) :
    (∑ i ∈ S, c i*(⨆ n, p n i)) ≤ A := by
  simp_rw [ENNReal.mul_iSup]
  rw [ENNReal.finsetSum_iSup_of_monotone (s := S) (f := fun i n => c i*p n i)
    (fun i => fun n m hnm => mul_le_mul' le_rfl (hp i hnm))]
  exact iSup_le hbound

end SLEExactGauge.MomentBatches

end

end OAI
