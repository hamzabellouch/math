import OAI.Probability.InvariantIsing.Pressure.Concentration

namespace OAI

/-!
# Almost-sure concentration without independence across dimensions

A countable Borel–Cantelli argument upgrades Haar tails to almost-sure
concentration of the pressure about its medians.
-/

noncomputable section

open MeasureTheory Filter
open scoped Topology NNReal ENNReal

namespace InvariantIsing

/-- Summable exponential tails imply almost-sure convergence to zero. No
independence between the random variables is required. -/
lemma ae_tendsto_zero_of_exponential_tail {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f : ℕ → Ω → ℝ)
    (htail : ∀ ε : ℝ, 0 < ε → ∃ C a : ℝ, 0 ≤ C ∧ 0 < a ∧
      ∀ n, μ.real {ω | ε ≤ |f n ω|} ≤ C * Real.exp (-a * (n : ℝ))) :
    ∀ᵐ ω ∂μ, Tendsto (fun n => f n ω) atTop (𝓝 0) := by
  have hb (k : ℕ) : ∀ᵐ ω ∂μ, ∀ᶠ n in atTop,
      ¬ (1 / (k + 1 : ℝ) ≤ |f n ω|) := by
    have hk : 0 < 1 / (k + 1 : ℝ) := by positivity
    obtain ⟨C, a, hC, ha, ht⟩ := htail _ hk
    have hsum : Summable (fun n : ℕ => C * Real.exp (-a * (n : ℝ))) := by
      simp_rw [mul_comm (-a), Real.exp_nat_mul]
      exact (summable_geometric_of_lt_one (Real.exp_pos (-a)).le
        (Real.exp_lt_one_iff.mpr (neg_neg_of_pos ha))).mul_left C
    let q : ℕ → ℝ≥0 := fun n => NNReal.mk (C * Real.exp (-a * (n : ℝ)))
      (mul_nonneg hC (Real.exp_pos _).le)
    have hq : Summable q := (NNReal.summable_coe (f := q)).mp hsum
    have hfinite : (∑' n, (q n : ENNReal)) ≠ ∞ :=
      ENNReal.tsum_coe_ne_top_iff_summable.mpr hq
    have hbound (n : ℕ) : μ {ω | 1 / (k + 1 : ℝ) ≤ |f n ω|} ≤ (q n : ENNReal) := by
      rw [← ENNReal.ofReal_toReal (measure_ne_top μ {ω | 1 / (k + 1 : ℝ) ≤ |f n ω|})]
      change ENNReal.ofReal (μ.real {ω | 1 / (k + 1 : ℝ) ≤ |f n ω|}) ≤ _
      simpa only [q, ENNReal.ofReal_eq_coe_nnreal (mul_nonneg hC (Real.exp_pos _).le)] using
        ENNReal.ofReal_le_ofReal (ht n)
    exact ae_eventually_notMem (s := fun n => {ω | 1 / (k + 1 : ℝ) ≤ |f n ω|})
      (ne_top_of_le_ne_top hfinite (ENNReal.tsum_le_tsum hbound))
  filter_upwards [ae_all_iff.mpr hb] with ω hω
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt hε
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hω k)
  refine ⟨N, ?_⟩
  intro n hn
  simpa only [Real.dist_eq, sub_zero] using lt_trans (lt_of_not_ge (hN n hn)) hk

/-- For an arbitrary joint realization of the Haar matrices, pressure is almost
surely close to a deterministic sequence of medians. -/
theorem ae_pressure_sub_median_tendsto_zero (hpub : HaarConcentrationInput)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (U : (n : ℕ) → Ω → SpecialOrthogonal (n + 3))
    (hU : ∀ n, Measurable (U n))
    (hHaar : ∀ n, (P.map (U n)).IsMulLeftInvariant)
    (eig c : (n : ℕ) → Fin (n + 3) → ℝ)
    (K : ℝ) (hK : 0 < K) (heig : ∀ n i, |eig n i| ≤ K) :
    ∃ m : ℕ → ℝ, ∀ᵐ ω ∂P,
      Tendsto (fun n => rotatedPressure (eig n) (specialRotation (U n ω)) (c n) - m n)
        atTop (𝓝 0) := by
  obtain ⟨C, a, hC, ha, ht⟩ := haar_pressure_median_tail hpub
  have hm (n : ℕ) : ∃ m : ℝ,
      ∀ r : ℝ, 0 < r →
        (P.map (U n)).real {V | r ≤ |rotatedPressure (eig n) (specialRotation V) (c n) - m|} ≤
          C * Real.exp (-a * (n + 3 : ℝ) * r ^ 2 / K ^ 2) := by
    have hp : IsProbabilityMeasure (P.map (U n)) :=
      (Measure.isProbabilityMeasure_map_iff (hU n).aemeasurable).mpr inferInstance
    obtain ⟨m, _, _, hm⟩ := ht (n + 3) (by omega) (P.map (U n)) hp (hHaar n)
      (eig n) (c n) K hK (heig n)
    exact ⟨m, by simpa only [Nat.cast_add, Nat.cast_ofNat] using hm⟩
  choose m hm using hm
  refine ⟨m, ae_tendsto_zero_of_exponential_tail P _ ?_⟩
  intro ε hε
  refine ⟨C, a * ε ^ 2 / K ^ 2, hC.le, by positivity, ?_⟩
  intro n
  have hs : MeasurableSet {V : SpecialOrthogonal (n + 3) |
      ε ≤ |rotatedPressure (eig n) (specialRotation V) (c n) - m n|} :=
    measurableSet_le measurable_const ((measurable_rotatedPressure _ _).sub_const _).abs
  have hb := hm n ε hε
  rw [measureReal_def, Measure.map_apply (hU n) hs] at hb
  change P.real {ω | ε ≤ |rotatedPressure (eig n) (specialRotation (U n ω)) (c n) - m n|} ≤ _ at hb
  refine hb.trans ?_
  apply mul_le_mul_of_nonneg_left _ hC.le
  apply Real.exp_le_exp.mpr
  have hnonneg : 0 ≤ a * ε ^ 2 / K ^ 2 := by positivity
  calc
    -a * ((n : ℝ) + 3) * ε ^ 2 / K ^ 2 =
        -(a * ε ^ 2 / K ^ 2) * ((n : ℝ) + 3) := by ring
    _ ≤ -(a * ε ^ 2 / K ^ 2) * (n : ℝ) :=
      mul_le_mul_of_nonpos_left (by linarith) (neg_nonpos.mpr hnonneg)

end InvariantIsing

end

end OAI
