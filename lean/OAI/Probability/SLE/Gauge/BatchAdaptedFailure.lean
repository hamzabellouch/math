import OAI.Probability.SLE.Gauge.DenseCoverAdaptedTests

namespace OAI

/-! The prescribed batch uses unequal success probabilities. Their sum,
not independence, controls the probability that every adapted test fails. -/
noncomputable section
open Set Filter MeasureTheory
open scoped NNReal ENNReal

namespace SLEExactGauge

theorem adapted_failures_product_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    (F : Filtration ℕ mΩ) (failure : ℕ → Set Ω)
    (hmeas : ∀ n, MeasurableSet[F (n+1)] (failure n)) (q : ℕ → ℝ≥0∞)
    (hstep : ∀ n (A : Set Ω), MeasurableSet[F n] A → P (A ∩ failure n) ≤ q n*P A)
    (N : ℕ) :
    P (⋂ n ∈ Finset.range N, failure n) ≤ (∏ n∈Finset.range N, q n)*P univ := by
  induction N with
  | zero => simp
  | succ N ih =>
    let A : Set Ω := ⋂ n∈Finset.range N, failure n
    have hA : MeasurableSet[F N] A := by
      apply MeasurableSet.iInter
      intro n
      apply MeasurableSet.iInter
      intro hn
      exact (F.mono (Nat.succ_le_of_lt (Finset.mem_range.mp hn))) _ (hmeas n)
    have he : (⋂ n∈Finset.range (N+1), failure n)=A∩failure N := by
      ext ω
      simp only [mem_iInter,Finset.mem_range,mem_inter_iff,A]
      constructor
      · intro h
        exact ⟨fun n hn => h n (Nat.lt_succ_of_lt hn),h N (Nat.lt_succ_self N)⟩
      · rintro ⟨h,hN⟩ n hn
        rcases Nat.lt_succ_iff_lt_or_eq.mp hn with hn | rfl
        · exact h n hn
        · exact hN
    rw [he,Finset.prod_range_succ]
    exact (hstep N A hA).trans ((mul_le_mul' le_rfl ih).trans_eq (by ac_rfl))

lemma finite_failure_product_le_exp (p : ℕ → ℝ) (hp1 : ∀ n, p n ≤ 1) (N : ℕ) :
    (∏ n∈Finset.range N, ENNReal.ofReal (1-p n)) ≤
      ENNReal.ofReal (Real.exp (-(∑ n∈Finset.range N, p n))) := by
  rw [← ENNReal.ofReal_prod_of_nonneg (fun n _ => sub_nonneg.mpr (hp1 n))]
  apply ENNReal.ofReal_le_ofReal
  calc
    _ ≤ ∏ n∈Finset.range N, Real.exp (-p n) :=
      Finset.prod_le_prod₀ (fun n _ => sub_nonneg.mpr (hp1 n))
        (fun n _ => Real.one_sub_le_exp_neg (p n))
    _ = _ := by rw [← Real.exp_sum,Finset.sum_neg_distrib]

theorem adapted_successes_failure_exp_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (F : Filtration ℕ mΩ) (success : ℕ → Set Ω)
    (hmeas : ∀ n, MeasurableSet[F (n+1)] (success n))
    (p : ℕ → ℝ) (hp0 : ∀ n, 0 ≤ p n) (hp1 : ∀ n, p n ≤ 1)
    (hstep : ∀ n (A : Set Ω), MeasurableSet[F n] A →
      ENNReal.ofReal (p n)*P A ≤ P (A∩success n))
    (N : ℕ) :
    P (⋂ n∈Finset.range N, (success n)ᶜ) ≤
      ENNReal.ofReal (Real.exp (-(∑ n∈Finset.range N, p n))) := by
  have h := adapted_failures_product_bound P F (fun n => (success n)ᶜ)
    (fun n => (hmeas n).compl) (fun n => ENNReal.ofReal (1-p n))
    (fun n A hA => complement_inter_bound_of_success_lower P
      (F.le (n+1) _ (hmeas n)) (hp0 n) (hp1 n) (hstep n A hA)) N
  rw [measure_univ,mul_one] at h
  exact h.trans (finite_failure_product_le_exp p hp1 N)

end SLEExactGauge

end

end OAI
