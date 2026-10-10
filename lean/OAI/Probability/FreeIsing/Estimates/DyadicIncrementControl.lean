import Mathlib

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped BigOperators

namespace Problem367.DyadicIncrementControl

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]

theorem measureReal_abs_gt_le_fourth {X : Ω → ℝ} {a : ℝ} (ha : 0 < a)
    (hX : Integrable (fun ω => |X ω| ^ 4) μ) :
    μ.real {ω | a < |X ω|} ≤ (∫ ω, |X ω| ^ 4 ∂μ) / a ^ 4 := by
  have hm := mul_meas_ge_le_integral_of_nonneg
    (Filter.Eventually.of_forall (fun ω => pow_nonneg (abs_nonneg (X ω)) 4)) hX (a ^ 4)
  apply (le_div_iff₀ (pow_pos ha 4)).2
  calc
    μ.real {ω | a < |X ω|} * a ^ 4 ≤
        μ.real {ω | a ^ 4 ≤ |X ω| ^ 4} * a ^ 4 := by
      apply mul_le_mul_of_nonneg_right _ (pow_nonneg ha.le 4)
      exact measureReal_mono (fun ω hω => pow_le_pow_left₀ ha.le hω.le 4)
    _ ≤ ∫ ω, |X ω| ^ 4 ∂μ := by simpa only [mul_comm] using hm

theorem ae_eventually_of_measureReal_le {E : ℕ → Set Ω} {b : ℕ → ℝ}
    (hb : Summable b) (hE : ∀ n, μ.real (E n) ≤ b n) :
    ∀ᵐ ω ∂μ, ∀ᶠ n in atTop, ω ∉ E n := by
  apply ae_eventually_notMem
  apply ne_top_of_le_ne_top hb.tsum_ofReal_ne_top
  apply ENNReal.tsum_le_tsum
  intro n
  rw [← ENNReal.ofReal_toReal (measure_ne_top μ (E n))]
  exact ENNReal.ofReal_le_ofReal (hE n)

theorem ae_eventually_grid_bound {m : ℕ → ℕ}
    (X : ∀ n, Fin (m n) → Ω → ℝ) {C q b : ℝ}
    (hq : 0 ≤ q) (hb : 0 < b) (hqb : q < b ^ 4)
    (hInt : ∀ n i, Integrable (fun ω => |X n i ω| ^ 4) μ)
    (hMoment : ∀ n, (∑ i : Fin (m n), ∫ ω, |X n i ω| ^ 4 ∂μ) ≤ C * q ^ n) :
    ∀ᵐ ω ∂μ, ∀ᶠ n in atTop, ∀ i : Fin (m n), |X n i ω| ≤ b ^ n := by
  classical
  let E : ℕ → Set Ω := fun n => {ω | ∃ i : Fin (m n), b ^ n < |X n i ω|}
  have hratio0 : 0 ≤ q / b ^ 4 := div_nonneg hq (pow_nonneg hb.le _)
  have hratio1 : q / b ^ 4 < 1 := (div_lt_one (pow_pos hb 4)).2 hqb
  have hsum : Summable (fun n : ℕ => C * (q / b ^ 4) ^ n) :=
    (summable_geometric_of_lt_one hratio0 hratio1).mul_left C
  have hbound (n : ℕ) : μ.real (E n) ≤ C * (q / b ^ 4) ^ n := by
    calc
      μ.real (E n) = μ.real (⋃ i : Fin (m n), {ω | b ^ n < |X n i ω|}) := by
        congr 1
        ext ω
        simp [E]
      _ ≤ ∑ i : Fin (m n), μ.real {ω | b ^ n < |X n i ω|} :=
        measureReal_iUnion_fintype_le _
      _ ≤ ∑ i : Fin (m n), (∫ ω, |X n i ω| ^ 4 ∂μ) / (b ^ n) ^ 4 :=
        Finset.sum_le_sum (fun i _ => measureReal_abs_gt_le_fourth (pow_pos hb n) (hInt n i))
      _ = (∑ i : Fin (m n), ∫ ω, |X n i ω| ^ 4 ∂μ) / (b ^ n) ^ 4 := by
        rw [Finset.sum_div]
      _ ≤ (C * q ^ n) / (b ^ n) ^ 4 :=
        div_le_div_of_nonneg_right (hMoment n) (pow_nonneg (pow_nonneg hb.le n) 4)
      _ = C * (q / b ^ 4) ^ n := by
        rw [div_pow, ← pow_mul, ← pow_mul]
        rw [Nat.mul_comm n 4]
        ring
  filter_upwards [ae_eventually_of_measureReal_le hsum hbound] with ω hω
  filter_upwards [hω] with n hn i
  exact le_of_not_gt (fun hi => hn ⟨i, hi⟩)

theorem ae_eventually_dyadic_grid_bound (K : ℕ)
    (X : ∀ n, Fin (K * 2 ^ n) → Ω → ℝ) {C b : ℝ}
    (hb : 0 < b) (hdecay : (1 / 2 : ℝ) < b ^ 4)
    (hInt : ∀ n i, Integrable (fun ω => |X n i ω| ^ 4) μ)
    (hMoment : ∀ n i, (∫ ω, |X n i ω| ^ 4 ∂μ) ≤ C * (1 / 4 : ℝ) ^ n) :
    ∀ᵐ ω ∂μ, ∀ᶠ n in atTop, ∀ i : Fin (K * 2 ^ n), |X n i ω| ≤ b ^ n := by
  apply ae_eventually_grid_bound X (C := (K : ℝ) * C) (q := 1 / 2)
    (by norm_num) hb hdecay hInt
  intro n
  calc
    (∑ i : Fin (K * 2 ^ n), ∫ ω, |X n i ω| ^ 4 ∂μ) ≤
        ∑ _i : Fin (K * 2 ^ n), C * (1 / 4 : ℝ) ^ n :=
      Finset.sum_le_sum (fun i _ => hMoment n i)
    _ = ((K : ℝ) * C) * (1 / 2 : ℝ) ^ n := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
      calc
        ((K : ℝ) * 2 ^ n) * (C * (1 / 4 : ℝ) ^ n) =
            ((K : ℝ) * C) * ((2 : ℝ) ^ n * (1 / 4 : ℝ) ^ n) := by ring
        _ = ((K : ℝ) * C) * (1 / 2 : ℝ) ^ n := by
          rw [← mul_pow]
          norm_num

theorem ae_eventually_dyadic_grid_nine_tenths (K : ℕ)
    (X : ∀ n, Fin (K * 2 ^ n) → Ω → ℝ) {C : ℝ}
    (hInt : ∀ n i, Integrable (fun ω => |X n i ω| ^ 4) μ)
    (hMoment : ∀ n i, (∫ ω, |X n i ω| ^ 4 ∂μ) ≤ C * (1 / 4 : ℝ) ^ n) :
    ∀ᵐ ω ∂μ, ∀ᶠ n in atTop, ∀ i : Fin (K * 2 ^ n),
      |X n i ω| ≤ (9 / 10 : ℝ) ^ n :=
  ae_eventually_dyadic_grid_bound K X (by norm_num) (by norm_num) hInt hMoment

end Problem367.DyadicIncrementControl

end

end OAI
