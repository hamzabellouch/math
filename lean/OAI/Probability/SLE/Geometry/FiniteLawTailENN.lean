import OAI.Probability.SLE.Geometry.FiniteLawTailBounds

namespace OAI

/-! Summable dyadic and cleanup tails from increasing finite laws.
No limiting probability measure or future-dependent density is required. -/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace SLEExactGauge.MomentBatches

lemma finite_probability_sum_eq {Ω ι : Type*} [MeasurableSpace Ω]
    (Q : Measure Ω) [IsFiniteMeasure Q] (S : Finset ι)
    (c : ι → ℕ) (E : ι → Set Ω) :
    (∑ i ∈ S, (c i : ℝ≥0∞)*Q (E i)) =
      ENNReal.ofReal (∑ i ∈ S, (c i : ℝ)*Q.real (E i)) := by
  symm
  rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => mul_nonneg (Nat.cast_nonneg _) measureReal_nonneg)]
  apply Finset.sum_congr rfl
  intro i _
  rw [ENNReal.ofReal_mul (Nat.cast_nonneg _),ENNReal.ofReal_natCast,ofReal_measureReal]

lemma upper_finite_batch_bound_enn {Ω : Type*} [MeasurableSpace Ω]
    (Q : Measure Ω) [IsFiniteMeasure Q] (X : Ω → ℝ) (hX : Measurable X)
    (hX0 : ∀ ω, 0 ≤ X ω) {n : ℕ} (hn : 1 ≤ n)
    {m T : ℝ} (hm : 0 < m) (hi : Integrable (fun ω => X ω^n) Q)
    (hMoment : (∫ ω, X ω^n ∂Q) ≤ m) (S : Finset ℤ) :
    (∑ k ∈ S, (copies n m T k : ℝ≥0∞)*Q {ω | 16*dyadic k ≤ X ω}) ≤
      ENNReal.ofReal ((4:ℝ)^n/16^n/(1-(1/2:ℝ)^n)) := by
  rw [finite_probability_sum_eq]
  exact ENNReal.ofReal_le_ofReal (upper_finite_batch_bound Q X hX hX0 hn hm hi hMoment S)

lemma limiting_upper_batch_bound {Ω : Type*} [MeasurableSpace Ω]
    (Q : ℕ → Measure Ω) (hfin : ∀ j, IsFiniteMeasure (Q j))
    (X : ℕ → Ω → ℝ) (hX : ∀ j, Measurable (X j)) (hX0 : ∀ j ω, 0 ≤ X j ω)
    (hmono : ∀ b, Monotone (fun j => Q j {ω | b ≤ X j ω}))
    {n : ℕ} (hn : 1 ≤ n) {m T : ℝ} (hm : 0 < m)
    (hi : ∀ j, Integrable (fun ω => X j ω^n) (Q j))
    (hMoment : ∀ j, (∫ ω, X j ω^n ∂Q j) ≤ m) :
    (∑' k : ℤ, (copies n m T k : ℝ≥0∞)*
      (⨆ j, Q j {ω | 16*dyadic k ≤ X j ω})) ≤
        ENNReal.ofReal ((4:ℝ)^n/16^n/(1-(1/2:ℝ)^n)) := by
  rw [ENNReal.tsum_eq_iSup_sum]
  apply iSup_le
  intro S
  apply finite_monotone_tail_sum_bound S (fun k => (copies n m T k : ℝ≥0∞))
    (fun j k => Q j {ω | 16*dyadic k ≤ X j ω}) (fun k => hmono _) _
  intro j
  let := hfin j
  exact upper_finite_batch_bound_enn (Q j) (X j) (hX j) (hX0 j) hn hm (hi j) (hMoment j) S

lemma limiting_cleanup_tail_bound {Ω : Type*} [MeasurableSpace Ω]
    (Q : ℕ → Measure Ω) (hfin : ∀ j, IsFiniteMeasure (Q j))
    (X : ℕ → Ω → ℝ) (hX : ∀ j, Measurable (X j)) (hX0 : ∀ j ω, 0 ≤ X j ω)
    (hmono : ∀ b, Monotone (fun j => Q j {ω | b ≤ X j ω}))
    (hi : ∀ j, Integrable (X j) (Q j)) (m : ℝ)
    (hMoment : ∀ j, (∫ ω, X j ω ∂Q j) ≤ m) :
    (∑' n : ℕ, ⨆ j, Q j {ω | 16*((n:ℝ)+1) ≤ X j ω}) ≤ ENNReal.ofReal (m/16) := by
  rw [ENNReal.tsum_eq_iSup_sum]
  apply iSup_le
  intro S
  have hs := finite_monotone_tail_sum_bound S (fun _ => (1:ℝ≥0∞))
    (fun j n => Q j {ω | 16*((n:ℝ)+1) ≤ X j ω}) (fun n => hmono _) (ENNReal.ofReal (m/16))
  simp only [one_mul] at hs
  apply hs
  intro j
  let := hfin j
  have he := finite_probability_sum_eq (Q j) S (fun _ => 1)
    (fun n => {ω | 16*((n:ℝ)+1) ≤ X j ω})
  simp only [Nat.cast_one,one_mul] at he
  rw [he]
  apply ENNReal.ofReal_le_ofReal
  exact (cleanup_finite_tail_bound (Q j) (X j) (hX j) (hX0 j) (hi j) S).trans
    (div_le_div_of_nonneg_right (hMoment j) (by norm_num))

end SLEExactGauge.MomentBatches

end

end OAI
