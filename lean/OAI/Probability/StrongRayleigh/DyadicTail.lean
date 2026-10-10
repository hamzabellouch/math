import Mathlib

namespace OAI

universe u_1 u_2 u_3 u_4 u_5

noncomputable section

open MeasureTheory Filter
open scoped ENNReal Topology BigOperators

namespace Problem336AdditiveD139.DyadicTail

variable {Ω : Type u_1} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]

theorem measure_abs_gt_le_of_fourth_moment
    {f : Ω → ℝ} {a M : ℝ} (ha : 0 < a) (hM : 0 ≤ M)
    (hf : Integrable (fun ω => |f ω| ^ 4) μ)
    (hm : (∫ ω, |f ω| ^ 4 ∂μ) ≤ M) :
    μ {ω | a < |f ω|} ≤ ENNReal.ofReal (M / a ^ 4) := by
  apply (ENNReal.toReal_le_toReal (measure_ne_top _ _) ENNReal.ofReal_ne_top).mp
  rw [ENNReal.toReal_ofReal (div_nonneg hM (pow_nonneg ha.le _))]
  have hmark := mul_meas_ge_le_integral_of_nonneg
    (μ := μ) (f := fun ω => |f ω| ^ 4)
    (Filter.Eventually.of_forall fun ω => pow_nonneg (abs_nonneg _) _)
    hf (a ^ 4)
  calc
    (μ {ω | a < |f ω|}).toReal ≤ (μ {ω | a ^ 4 ≤ |f ω| ^ 4}).toReal := by
      apply ENNReal.toReal_mono (measure_ne_top _ _)
      apply measure_mono
      intro ω hω
      exact pow_le_pow_left₀ ha.le hω.le 4
    _ ≤ M / a ^ 4 := by
      apply (le_div_iff₀ (pow_pos ha 4)).2
      simpa [measureReal_def, mul_comm] using hmark.trans hm

theorem measure_exists_abs_gt_le_of_fourth_moment
    {κ : Type u_2} [Fintype κ] (f : κ → Ω → ℝ) {a M : ℝ}
    (ha : 0 < a) (hM : 0 ≤ M)
    (hf : ∀ k, Integrable (fun ω => |f k ω| ^ 4) μ)
    (hm : ∀ k, (∫ ω, |f k ω| ^ 4 ∂μ) ≤ M) :
    μ {ω | ∃ k, a < |f k ω|} ≤
      ENNReal.ofReal ((Fintype.card κ : ℝ) * M / a ^ 4) := by
  classical
  calc
    μ {ω | ∃ k, a < |f k ω|} = μ (⋃ k, {ω | a < |f k ω|}) := by
      congr 1
      ext ω
      simp
    _ ≤ ∑ k, μ {ω | a < |f k ω|} := measure_iUnion_fintype_le μ _
    _ ≤ ∑ _k : κ, ENNReal.ofReal (M / a ^ 4) := by
      exact Finset.sum_le_sum fun k _ =>
        measure_abs_gt_le_of_fourth_moment ha hM (hf k) (hm k)
    _ = ENNReal.ofReal ((Fintype.card κ : ℝ) * M / a ^ 4) := by
      rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => div_nonneg hM (pow_nonneg ha.le _))]
      congr 1
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      ring

theorem ae_eventually_forall_abs_le_of_summable_fourth_moments
    {κ : ℕ → Type u_4} [∀ n, Fintype (κ n)] (D : ∀ n, κ n → Ω → ℝ)
    {a M : ℕ → ℝ} (ha : ∀ n, 0 < a n) (hM : ∀ n, 0 ≤ M n)
    (hD : ∀ n k, Integrable (fun ω => |D n k ω| ^ 4) μ)
    (hm : ∀ n k, (∫ ω, |D n k ω| ^ 4 ∂μ) ≤ M n)
    (hs : Summable (fun n => (Fintype.card (κ n) : ℝ) * M n / (a n) ^ 4)) :
    ∀ᵐ ω ∂μ, ∀ᶠ n in atTop, ∀ k, |D n k ω| ≤ a n := by
  have hbound := fun n => measure_exists_abs_gt_le_of_fourth_moment
    (D n) (ha n) (hM n) (hD n) (hm n)
  have hsum : (∑' n, μ {ω | ∃ k, a n < |D n k ω|}) ≠ ∞ :=
    ne_top_of_le_ne_top hs.tsum_ofReal_ne_top (ENNReal.tsum_le_tsum hbound)
  filter_upwards [ae_eventually_notMem hsum] with ω hω
  filter_upwards [hω] with n hn
  simpa only [Set.mem_ofPred_eq, not_exists, not_lt] using hn

theorem dyadic_fourth_moment_cost (C : ℝ) (n : ℕ) :
    ((2 ^ n : ℕ) : ℝ) * (C * (1 / 4 : ℝ) ^ n) / ((9 / 10 : ℝ) ^ n) ^ 4 =
      C * (5000 / 6561 : ℝ) ^ n := by
  have hp : ((9 / 10 : ℝ) ^ n) ^ 4 = ((9 / 10 : ℝ) ^ 4) ^ n := by
    rw [← pow_mul, ← pow_mul, Nat.mul_comm n 4]
  rw [hp, Nat.cast_pow, Nat.cast_ofNat]
  calc
    (2 : ℝ) ^ n * (C * (1 / 4 : ℝ) ^ n) / ((9 / 10 : ℝ) ^ 4) ^ n =
        C * ((2 * (1 / 4 : ℝ)) / ((9 / 10 : ℝ) ^ 4)) ^ n := by
      simp only [div_pow, mul_pow]
      ring
    _ = C * (5000 / 6561 : ℝ) ^ n := by norm_num

theorem ae_eventually_dyadic_abs_le
    (D : ∀ n : ℕ, Fin (2 ^ n) → Ω → ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hD : ∀ n k, Integrable (fun ω => |D n k ω| ^ 4) μ)
    (hm : ∀ n k, (∫ ω, |D n k ω| ^ 4 ∂μ) ≤ C * (1 / 4 : ℝ) ^ n) :
    ∀ᵐ ω ∂μ, ∀ᶠ n in atTop, ∀ k, |D n k ω| ≤ (9 / 10 : ℝ) ^ n := by
  apply ae_eventually_forall_abs_le_of_summable_fourth_moments D
    (fun n => pow_pos (by norm_num) n)
    (fun n => mul_nonneg hC (pow_nonneg (by norm_num) n)) hD hm
  have hs : Summable (fun n : ℕ => C * (5000 / 6561 : ℝ) ^ n) :=
    (summable_geometric_of_norm_lt_one (by norm_num : ‖(5000 / 6561 : ℝ)‖ < 1)).mul_left C
  convert hs using 1
  funext n
  simp only [Fintype.card_fin]
  exact dyadic_fourth_moment_cost C n

theorem ae_all_eventually_dyadic_abs_le
    {J : Type u_3} [Countable J]
    (D : J → ∀ n : ℕ, Fin (2 ^ n) → Ω → ℝ) {C : J → ℝ} (hC : ∀ j, 0 ≤ C j)
    (hD : ∀ j n k, Integrable (fun ω => |D j n k ω| ^ 4) μ)
    (hm : ∀ j n k, (∫ ω, |D j n k ω| ^ 4 ∂μ) ≤ C j * (1 / 4 : ℝ) ^ n) :
    ∀ᵐ ω ∂μ, ∀ j, ∀ᶠ n in atTop, ∀ k, |D j n k ω| ≤ (9 / 10 : ℝ) ^ n := by
  rw [ae_all_iff]
  intro j
  exact ae_eventually_dyadic_abs_le (D j) (hC j) (hD j) (hm j)

theorem exists_geometric_bound_of_eventually
    {κ : ℕ → Type u_5} [∀ n, Fintype (κ n)] (D : ∀ n, κ n → ℝ)
    {q : ℝ} (hq : 0 < q)
    (h : ∀ᶠ n in atTop, ∀ k, |D n k| ≤ q ^ n) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ n k, |D n k| ≤ A * q ^ n := by
  classical
  obtain ⟨N, hN⟩ := eventually_atTop.1 h
  let s : ℕ → ℝ := fun n => ∑ k, |D n k| / q ^ n
  have hs (n : ℕ) : 0 ≤ s n := by
    exact Finset.sum_nonneg fun k _ => div_nonneg (abs_nonneg _) (pow_nonneg hq.le _)
  let A := 1 + ∑ n ∈ Finset.range N, s n
  have hA : 1 ≤ A := by
    dsimp [A]
    exact le_add_of_nonneg_right (Finset.sum_nonneg fun n _ => hs n)
  refine ⟨A, hA, ?_⟩
  intro n k
  by_cases hn : n < N
  · have hk : |D n k| / q ^ n ≤ s n := by
      exact Finset.single_le_sum
        (fun j _ => div_nonneg (abs_nonneg _) (pow_nonneg hq.le _)) (Finset.mem_univ k)
    have hn' : s n ≤ ∑ m ∈ Finset.range N, s m :=
      Finset.single_le_sum (fun m _ => hs m) (Finset.mem_range.mpr hn)
    apply (div_le_iff₀ (pow_pos hq n)).mp
    exact hk.trans (hn'.trans (by dsimp [A]; linarith))
  · exact (hN n (Nat.le_of_not_gt hn) k).trans
      (le_mul_of_one_le_left (pow_nonneg hq.le n) hA)

theorem ae_exists_dyadic_geometric_bound
    (D : ∀ n : ℕ, Fin (2 ^ n) → Ω → ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hD : ∀ n k, Integrable (fun ω => |D n k ω| ^ 4) μ)
    (hm : ∀ n k, (∫ ω, |D n k ω| ^ 4 ∂μ) ≤ C * (1 / 4 : ℝ) ^ n) :
    ∀ᵐ ω ∂μ, ∃ A : ℝ, 1 ≤ A ∧ ∀ n k, |D n k ω| ≤ A * (9 / 10 : ℝ) ^ n := by
  filter_upwards [ae_eventually_dyadic_abs_le D hC hD hm] with ω hω
  exact exists_geometric_bound_of_eventually (fun n k => D n k ω) (by norm_num) hω

end Problem336AdditiveD139.DyadicTail

end

end OAI
