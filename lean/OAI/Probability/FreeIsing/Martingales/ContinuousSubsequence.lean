import OAI.Probability.FreeIsing.Martingales.ContinuousLimit

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace Problem367.MartingaleSquareMaximal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
  {F : Filtration ℝ≥0 mΩ} {M : ℕ → ℝ≥0 → Ω → ℝ}

theorem exists_continuous_subsequence_of_terminal_L2_cauchy
    (hM : ∀ n, Martingale (M n) F μ)
    (h2 : ∀ n t, MemLp (M n t) 2 μ)
    (hc : ∀ n, ∀ᵐ ω ∂μ, Continuous (fun t => M n t ω)) (T : ℝ≥0)
    (hC : CauchySeq (fun n => (h2 n T).toLp (M n T))) :
    ∃ v : ℕ → ℕ, StrictMono v ∧
      ∀ᵐ ω ∂μ, ∃ f : C(Set.Iic T, ℝ),
        ∀ t : Set.Iic T, Tendsto (fun n => M (v n) t ω) atTop (𝓝 (f t)) := by
  let u : ℕ → Lp ℝ 2 μ := fun n => (h2 n T).toLp (M n T)
  obtain ⟨v, hv, hb⟩ := Metric.exists_subseq_bounded_of_cauchySeq u hC
    (fun n => (1 / 4 : ℝ) ^ n) (fun n => by positivity)
  refine ⟨v, hv, ae_exists_continuous_limit_of_summable_energy
    (fun n => hM (v n)) (fun n => h2 (v n)) (fun n => hc (v n)) T ?_⟩
  have hfinite : (∑' n : ℕ, (1 / 4 : ℝ≥0∞) ^ n) ≠ ∞ :=
    (tsum_geometric_lt_top.mpr (by norm_num)).ne
  apply ne_top_of_le_ne_top hfinite
  apply ENNReal.tsum_le_tsum
  intro n
  have hnorm : ‖u (v (n + 1)) - u (v n)‖ < (1 / 4 : ℝ) ^ n := by
    simpa only [dist_eq_norm] using hb n (v (n + 1)) (hv.monotone (Nat.le_succ n))
  have heq : ‖u (v (n + 1)) - u (v n)‖ ^ 2 =
      ∫ ω, (M (v (n + 1)) T ω - M (v n) T ω) ^ 2 ∂μ := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    simp only [real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub (u (v (n + 1))) (u (v n)),
      (h2 (v (n + 1)) T).coeFn_toLp, (h2 (v n) T).coeFn_toLp] with ω hsub ha hb
    simp only [Pi.sub_apply] at hsub
    rw [hsub, ha, hb]
  have henergy : (∫ ω, (M (v (n + 1)) T ω - M (v n) T ω) ^ 2 ∂μ) ≤
      ((1 / 4 : ℝ) ^ n) ^ 2 := by
    rw [← heq]
    nlinarith [norm_nonneg (u (v (n + 1)) - u (v n))]
  have henergy' : ENNReal.ofReal
      (∫ ω, (M (v (n + 1)) T ω - M (v n) T ω) ^ 2 ∂μ) ≤
      ((1 / 4 : ℝ≥0∞) ^ n) ^ 2 := by
    have hh : ENNReal.ofReal (((1 / 4 : ℝ) ^ n) ^ 2) =
        ((1 / 4 : ℝ≥0∞) ^ n) ^ 2 := by
      rw [ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_pow (by norm_num)]
      congr 2
      rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 4)]
      norm_num
    exact (ENNReal.ofReal_le_ofReal henergy).trans_eq hh
  calc
    _ ≤ ((1 / 4 : ℝ≥0∞) ^ n) ^ 2 /
        ((((1 / 2 : ℝ≥0) ^ n : ℝ≥0) : ℝ≥0∞) ^ 2) :=
      ENNReal.div_le_div_right henergy' _
    _ = (1 / 4 : ℝ≥0∞) ^ n := by
      have hh : ((((1 / 2 : ℝ≥0) ^ n : ℝ≥0) : ℝ≥0∞) ^ 2) =
          ((1 / 2 : ℝ≥0∞) ^ n) ^ 2 := by
        norm_num [ENNReal.coe_pow, ENNReal.coe_div (by norm_num : (2 : ℝ≥0) ≠ 0)]
      rw [hh]
      simp only [div_eq_mul_inv, ENNReal.inv_pow, ← mul_pow, ← pow_mul]
      rw [Nat.mul_comm n 2, pow_mul]
      congr 1
      apply (ENNReal.toReal_eq_toReal_iff' (by simp [ENNReal.mul_ne_top]) (by simp)).mp
      norm_num

end Problem367.MartingaleSquareMaximal

end

end OAI
