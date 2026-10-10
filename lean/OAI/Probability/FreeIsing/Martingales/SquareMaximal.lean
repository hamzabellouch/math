import Mathlib

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped NNReal ENNReal

namespace Problem367.MartingaleSquareMaximal

variable {Ω ι : Type*} [mΩ : MeasurableSpace Ω] [Preorder ι]
  {μ : Measure Ω} {F : Filtration ι mΩ} {M : ι → Ω → ℝ}

theorem submartingale_sq (hM : Martingale M F μ)
    (h2 : ∀ t, MemLp (M t) 2 μ) :
    Submartingale (fun t ω => M t ω ^ 2) F μ := by
  refine ⟨fun t => (hM.stronglyMeasurable t).pow 2, ?_, fun t => (h2 t).integrable_sq⟩
  intro s t hst
  have hint : Integrable (fun ω => ‖M t ω‖ ^ (2 : ℝ)) μ := by
    simpa only [Real.rpow_two, Real.norm_eq_abs, sq_abs] using (h2 t).integrable_sq
  have hj := Integrable.norm_condExp_rpow_le (m := F s) (by norm_num : (1 : ℝ) ≤ 2) hint
  have hj' : (fun ω => μ[M t | F s] ω ^ 2) ≤ᵐ[μ]
      μ[(fun ω => M t ω ^ 2) | F s] := by
    simpa only [Real.rpow_two, Real.norm_eq_abs, sq_abs] using hj
  filter_upwards [hj', hM.condExp_ae_eq hst] with ω hω heq
  simpa only [heq] using hω

theorem finite_maximal_sq [IsFiniteMeasure μ]
    {F : Filtration ℕ mΩ} {M : ℕ → Ω → ℝ}
    (hM : Martingale M F μ) (h2 : ∀ t, MemLp (M t) 2 μ)
    (ε : ℝ≥0) (n : ℕ) :
    (ε : ℝ≥0∞) ^ 2 * μ {ω | ∃ k ≤ n, (ε : ℝ) ≤ |M k ω|} ≤
      ENNReal.ofReal (∫ ω, M n ω ^ 2 ∂μ) := by
  have hs := submartingale_sq hM h2
  have hmax := maximal_ineq hs (fun t ω => sq_nonneg (M t ω)) (ε := ε ^ 2) n
  have hevent : {ω | ((ε ^ 2 : ℝ≥0) : ℝ) ≤
      (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one (fun k => M k ω ^ 2)} =
      {ω | ∃ k ≤ n, (ε : ℝ) ≤ |M k ω|} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Finset.le_sup'_iff, Finset.mem_range, Nat.lt_succ_iff,
      NNReal.coe_pow]
    constructor
    · rintro ⟨k, hk, hval⟩
      refine ⟨k, hk, ?_⟩
      nlinarith [abs_nonneg (M k ω), sq_abs (M k ω), ε.coe_nonneg]
    · rintro ⟨k, hk, hval⟩
      refine ⟨k, hk, ?_⟩
      nlinarith [abs_nonneg (M k ω), sq_abs (M k ω), ε.coe_nonneg]
  rw [hevent] at hmax
  calc
    _ ≤ ENNReal.ofReal (∫ ω in {ω | ∃ k ≤ n, (ε : ℝ) ≤ |M k ω|}, M n ω ^ 2 ∂μ) := by
      simpa only [ENNReal.coe_pow] using hmax
    _ ≤ _ := ENNReal.ofReal_le_ofReal (setIntegral_le_integral (h2 n).integrable_sq
      (Filter.Eventually.of_forall (fun ω => sq_nonneg (M n ω))))

theorem integral_sq_le [IsFiniteMeasure μ]
    (hM : Martingale M F μ) (h2 : ∀ t, MemLp (M t) 2 μ)
    {s t : ι} (hst : s ≤ t) :
    (∫ ω, M s ω ^ 2 ∂μ) ≤ ∫ ω, M t ω ^ 2 ∂μ := by
  have hs := submartingale_sq hM h2
  calc
    _ ≤ ∫ ω, μ[(fun ω => M t ω ^ 2) | F s] ω ∂μ :=
      integral_mono_ae (h2 s).integrable_sq integrable_condExp (hs.2.1 s t hst)
    _ = _ := integral_condExp (F.le s)

theorem sampled_maximal_sq [IsFiniteMeasure μ]
    (hM : Martingale M F μ) (h2 : ∀ t, MemLp (M t) 2 μ)
    (q : ℕ → ι) (hq : Monotone q) (ε : ℝ≥0) (n : ℕ)
    {T : ι} (hT : q n ≤ T) :
    (ε : ℝ≥0∞) ^ 2 * μ {ω | ∃ k ≤ n, (ε : ℝ) ≤ |M (q k) ω|} ≤
      ENNReal.ofReal (∫ ω, M T ω ^ 2 ∂μ) := by
  let G : Filtration ℕ mΩ := ⟨fun k => F (q k),
    fun _ _ h => F.mono (hq h), fun k => F.le (q k)⟩
  have hMq : Martingale (fun k => M (q k)) G μ :=
    ⟨fun k => hM.stronglyMeasurable (q k), fun i j hij => hM.condExp_ae_eq (hq hij)⟩
  exact (finite_maximal_sq hMq (fun k => h2 (q k)) ε n).trans
    (ENNReal.ofReal_le_ofReal (integral_sq_le hM h2 hT))

end Problem367.MartingaleSquareMaximal

end

end OAI
