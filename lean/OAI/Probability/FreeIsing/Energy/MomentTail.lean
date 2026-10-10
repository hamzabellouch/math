import Mathlib

namespace OAI

noncomputable section

open MeasureTheory

namespace Problem367

theorem exists_moment_order {K L : ℝ} (hK : 0 < K) (hL : 32 * K ≤ L) :
    ∃ p : ℕ, 1 ≤ p ∧
      K * (p : ℝ) ^ 2 - (p : ℝ) * L / 8 ≤ -(L ^ 2) / (512 * K) := by
  let p : ℕ := ⌊L / (16 * K)⌋₊
  have hL0 : 0 < L := lt_of_lt_of_le (by positivity) hL
  have hden : 0 < 16 * K := by positivity
  have hratio : 2 ≤ L / (16 * K) := by
    apply (le_div_iff₀ hden).mpr
    linarith
  have hp1 : 1 ≤ p := (Nat.one_le_floor_iff _).mpr (by linarith)
  have hpu : (p : ℝ) ≤ L / (16 * K) :=
    Nat.floor_le (by positivity)
  have hpl' : L / (16 * K) < (p : ℝ) + 1 := Nat.lt_floor_add_one _
  have hpl : L / (32 * K) ≤ (p : ℝ) := by
    have hratio' : L / (32 * K) = (L / (16 * K)) / 2 := by ring
    rw [hratio']
    linarith
  have hp0 : 0 ≤ (p : ℝ) := Nat.cast_nonneg p
  have hpu' : 16 * K * (p : ℝ) ≤ L := by
    nlinarith [(le_div_iff₀ hden).mp hpu]
  have hstep : K * (p : ℝ) ^ 2 - (p : ℝ) * L / 8 ≤ -(p : ℝ) * L / 16 := by
    nlinarith [mul_le_mul_of_nonneg_right hpu' hp0]
  have hpl'': L ≤ (p : ℝ) * (32 * K) :=
    (div_le_iff₀ (by positivity)).mp hpl
  refine ⟨p, hp1, hstep.trans ?_⟩
  apply (le_div_iff₀ (by positivity : 0 < 512 * K)).mpr
  nlinarith [mul_le_mul_of_nonneg_right hpl'' hL0.le]

theorem measureReal_abs_gt_le_moment {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {Y : Ω → ℝ} {a : ℝ} {p : ℕ}
    (ha : 0 < a) (hY : Integrable (fun ω => |Y ω| ^ p) μ) :
    μ.real {ω | a < |Y ω|} ≤ (∫ ω, |Y ω| ^ p ∂μ) / a ^ p := by
  have hsubset : {ω | a < |Y ω|} ⊆ {ω | a ^ p ≤ |Y ω| ^ p} := by
    intro ω hω
    exact pow_le_pow_left₀ ha.le hω.le p
  apply (le_div_iff₀ (pow_pos ha p)).mpr
  calc
    μ.real {ω | a < |Y ω|} * a ^ p ≤
        μ.real {ω | a ^ p ≤ |Y ω| ^ p} * a ^ p :=
      mul_le_mul_of_nonneg_right (measureReal_mono hsubset) (pow_nonneg ha.le p)
    _ ≤ ∫ ω, |Y ω| ^ p ∂μ := by
      simpa only [mul_comm] using
        mul_meas_ge_le_integral_of_nonneg
          (Filter.Eventually.of_forall (fun ω => pow_nonneg (abs_nonneg (Y ω)) p)) hY (a ^ p)

theorem measureReal_abs_gt_exp_le_of_moments {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {Y : Ω → ℝ} {K L : ℝ}
    (hK : 0 < K) (hL : 32 * K ≤ L)
    (hint : ∀ p : ℕ, 1 ≤ p → Integrable (fun ω => |Y ω| ^ p) μ)
    (hmom : ∀ p : ℕ, 1 ≤ p →
      (∫ ω, |Y ω| ^ p ∂μ) ≤ Real.exp (K * (p : ℝ) ^ 2 - (p : ℝ) * L / 4)) :
    μ.real {ω | Real.exp (-L / 8) < |Y ω|} ≤
      Real.exp (-(L ^ 2) / (512 * K)) := by
  obtain ⟨p, hp, hexponent⟩ := exists_moment_order hK hL
  calc
    μ.real {ω | Real.exp (-L / 8) < |Y ω|} ≤
        (∫ ω, |Y ω| ^ p ∂μ) / Real.exp (-L / 8) ^ p :=
      measureReal_abs_gt_le_moment (Real.exp_pos _) (hint p hp)
    _ ≤ Real.exp (K * (p : ℝ) ^ 2 - (p : ℝ) * L / 4) /
        Real.exp (-L / 8) ^ p :=
      div_le_div_of_nonneg_right (hmom p hp) (pow_nonneg (Real.exp_nonneg _) p)
    _ = Real.exp (K * (p : ℝ) ^ 2 - (p : ℝ) * L / 8) := by
      rw [← Real.exp_nat_mul, ← Real.exp_sub]
      congr 1
      ring
    _ ≤ Real.exp (-(L ^ 2) / (512 * K)) := Real.exp_le_exp.mpr hexponent

theorem measureReal_abs_gt_rpow_le_of_moments {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {Y : Ω → ℝ} {K t : ℝ}
    (hK : 0 < K) (ht : 0 < t) (hsmall : 32 * K ≤ Real.log (1 / t))
    (hint : ∀ p : ℕ, 1 ≤ p → Integrable (fun ω => |Y ω| ^ p) μ)
    (hmom : ∀ p : ℕ, 1 ≤ p →
      (∫ ω, |Y ω| ^ p ∂μ) ≤ Real.exp (K * (p : ℝ) ^ 2) * t ^ ((p : ℝ) / 4)) :
    μ.real {ω | t ^ (1 / 8 : ℝ) < |Y ω|} ≤
      Real.exp (-(Real.log (1 / t) ^ 2) / (512 * K)) := by
  have hthreshold : Real.exp (-Real.log (1 / t) / 8) = t ^ (1 / 8 : ℝ) := by
    rw [Real.rpow_def_of_pos ht, one_div, Real.log_inv]
    congr 1
    ring
  rw [← hthreshold]
  apply measureReal_abs_gt_exp_le_of_moments hK hsmall hint
  intro p hp
  convert hmom p hp using 1
  rw [Real.rpow_def_of_pos ht, ← Real.exp_add, one_div, Real.log_inv]
  congr 1
  ring

theorem measure_abs_gt_rpow_le_of_moments {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {Y : Ω → ℝ} {K t : ℝ}
    (hK : 0 < K) (ht : 0 < t) (hsmall : 32 * K ≤ Real.log (1 / t))
    (hint : ∀ p : ℕ, 1 ≤ p → Integrable (fun ω => |Y ω| ^ p) μ)
    (hmom : ∀ p : ℕ, 1 ≤ p →
      (∫ ω, |Y ω| ^ p ∂μ) ≤ Real.exp (K * (p : ℝ) ^ 2) * t ^ ((p : ℝ) / 4)) :
    μ {ω | t ^ (1 / 8 : ℝ) < |Y ω|} ≤
      ENNReal.ofReal (Real.exp (-(Real.log (1 / t) ^ 2) / (512 * K))) := by
  rw [← ofReal_measureReal]
  exact ENNReal.ofReal_le_ofReal
    (measureReal_abs_gt_rpow_le_of_moments hK ht hsmall hint hmom)

end Problem367

end

end OAI
