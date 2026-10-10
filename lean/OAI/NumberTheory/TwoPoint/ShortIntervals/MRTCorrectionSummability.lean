import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTCorrectionEuler

namespace OAI

/-! Absolute summability of the prime-power correction in MRT's reduction
from multiplicative to completely multiplicative functions. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical BigOperators

noncomputable def mrtCorrectionWeight (f : ℕ → ℂ) (n : ℕ) : ℝ :=
  ‖mrtArithmetic (mrtCorrection f) n‖ * (n : ℝ) ^ (-(3 / 4 : ℝ))

noncomputable def mrtCorrectionEulerConstant : ℝ :=
  2 / (1 - (2 : ℝ) ^ (-(3 / 4 : ℝ)))

noncomputable def mrtCorrectionBound : ℝ :=
  Real.exp (mrtCorrectionEulerConstant * ∑' n : ℕ, (n : ℝ) ^ (-(3 / 2 : ℝ)))

lemma mrtCorrectionWeight_nonneg (f : ℕ → ℂ) (n : ℕ) :
    0 ≤ mrtCorrectionWeight f n := by
  exact mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)

lemma mrtCorrectionWeight_zero (f : ℕ → ℂ) : mrtCorrectionWeight f 0 = 0 := by
  simp [mrtCorrectionWeight]

lemma mrtCorrectionWeight_one (f : ℕ → ℂ) : mrtCorrectionWeight f 1 = 1 := by
  simp [mrtCorrectionWeight, mrtCorrection, mrtArithmetic]

lemma mrtCorrectionWeight_mul (f : ℕ → ℂ) {m n : ℕ} (hcop : m.Coprime n) :
    mrtCorrectionWeight f (m * n) = mrtCorrectionWeight f m * mrtCorrectionWeight f n := by
  have hmult : (mrtArithmetic (mrtCorrection f)).IsMultiplicative :=
    mrtArithmetic_isMultiplicative _ (fromPrimePowers_multiplicative _) (fromPrimePowers_one _)
  unfold mrtCorrectionWeight
  rw [hmult.map_mul_of_coprime hcop, norm_mul, Nat.cast_mul,
    Real.mul_rpow (Nat.cast_nonneg m) (Nat.cast_nonneg n)]
  ring

lemma mrtCorrectionWeight_prime_pow (f : ℕ → ℂ) {p : ℕ} (hp : p.Prime) (k : ℕ) :
    mrtCorrectionWeight f (p ^ k) =
      ‖mrtCorrectionLocal f p k‖ * ((p : ℝ) ^ (-(3 / 4 : ℝ))) ^ k := by
  unfold mrtCorrectionWeight
  rw [mrtArithmetic_apply_pos _ (pow_pos hp.pos k), mrtCorrection_prime_pow f hp,
    Nat.cast_pow, Real.rpow_pow_comm (Nat.cast_nonneg p)]

lemma mrtCorrectionEulerConstant_nonneg : 0 ≤ mrtCorrectionEulerConstant := by
  have hlt : (2 : ℝ) ^ (-(3 / 4 : ℝ)) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
  exact div_nonneg (by norm_num) (sub_nonneg.mpr hlt.le)

lemma mrt_correction_local_summable (f : ℕ → ℂ) (hf : OneBounded f)
    {p : ℕ} (hp : p.Prime) : Summable (fun k : ℕ => mrtCorrectionWeight f (p ^ k)) := by
  let r : ℝ := (p : ℝ) ^ (-(3 / 4 : ℝ))
  have hr0 : 0 ≤ r := Real.rpow_nonneg (Nat.cast_nonneg p) _
  have hr1 : r < 1 := Real.rpow_lt_one_of_one_lt_of_neg
    (by exact_mod_cast hp.one_lt) (by norm_num)
  apply Summable.of_nonneg_of_le (fun k => mrtCorrectionWeight_nonneg f (p ^ k))
    (f := fun k => 2 * r ^ k)
  · intro k
    rw [mrtCorrectionWeight_prime_pow f hp]
    apply mul_le_mul_of_nonneg_right _ (pow_nonneg hr0 k)
    rcases k with _ | k
    · simp
    · exact mrtCorrectionLocal_norm_le f hf hp (Nat.succ_pos k)
  · exact (summable_geometric_of_lt_one hr0 hr1).mul_left 2

lemma mrt_correction_local_sum_bound (f : ℕ → ℂ) (hf : OneBounded f) (h1 : f 1 = 1)
    {p : ℕ} (hp : p.Prime) :
    (∑' k : ℕ, mrtCorrectionWeight f (p ^ k)) ≤
      Real.exp (mrtCorrectionEulerConstant * (p : ℝ) ^ (-(3 / 2 : ℝ))) := by
  let r : ℝ := (p : ℝ) ^ (-(3 / 4 : ℝ))
  let rho : ℝ := (2 : ℝ) ^ (-(3 / 4 : ℝ))
  have hr0 : 0 ≤ r := Real.rpow_nonneg (Nat.cast_nonneg p) _
  have hrho : rho < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
  have hrle : r ≤ rho := Real.rpow_le_rpow_of_nonpos (by norm_num)
    (by exact_mod_cast hp.two_le) (by norm_num)
  have hr1 : r < 1 := hrle.trans_lt hrho
  have hsum := mrt_correction_local_summable f hf hp
  have htail := (summable_geometric_of_lt_one hr0 hr1).mul_left (2 * r ^ 2)
  have ht : (∑' k : ℕ, mrtCorrectionWeight f (p ^ (k + 2))) ≤
      (2 * r ^ 2) * (1 - r)⁻¹ := by
    rw [← tsum_geometric_of_lt_one hr0 hr1, ← tsum_mul_left]
    apply (hsum.comp_injective (fun _ _ h => Nat.add_right_cancel h)).tsum_le_tsum
      (fun k => ?_) htail
    change mrtCorrectionWeight f (p ^ (k + 2)) ≤ _
    rw [mrtCorrectionWeight_prime_pow f hp, pow_add]
    have hb := mrtCorrectionLocal_norm_le f hf hp (by omega : 0 < k + 2)
    calc
      _ ≤ 2 * (r ^ k * r ^ 2) := mul_le_mul_of_nonneg_right hb (by positivity)
      _ = _ := by ring
  have hs : (∑' k : ℕ, mrtCorrectionWeight f (p ^ k)) ≤
      1 + (2 * r ^ 2) * (1 - r)⁻¹ := by
    calc
      _ = 1 + ∑' k : ℕ, mrtCorrectionWeight f (p ^ (k + 2)) := by
        simpa [sum_range_succ, mrtCorrectionWeight_prime_pow f hp,
          mrtCorrectionLocal_one f h1] using (hsum.sum_add_tsum_nat_add 2).symm
      _ ≤ _ := add_le_add le_rfl ht
  have hinv : (1 - r)⁻¹ ≤ (1 - rho)⁻¹ :=
    inv_anti₀ (sub_pos.mpr hrho) (sub_le_sub_left hrle 1)
  have hsq : r ^ 2 = (p : ℝ) ^ (-(3 / 2 : ℝ)) := by
    dsimp [r]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg p)]
    congr 1
    norm_num
  calc
    _ ≤ 1 + (2 * r ^ 2) * (1 - r)⁻¹ := hs
    _ ≤ 1 + (2 * r ^ 2) * (1 - rho)⁻¹ := by
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hinv
        (show 0 ≤ 2 * r ^ 2 by positivity))
    _ = 1 + mrtCorrectionEulerConstant * (p : ℝ) ^ (-(3 / 2 : ℝ)) := by
      rw [hsq]
      unfold mrtCorrectionEulerConstant
      dsimp [rho]
      ring
    _ ≤ _ := by
      simpa only [add_comm] using (Real.add_one_le_exp
        (mrtCorrectionEulerConstant * (p : ℝ) ^ (-(3 / 2 : ℝ))))

/-- Uniform absolute convergence at exponent `3/4`, exactly as required by
the general-multiplicative reduction in corrected MRT. -/
theorem mrt_correction_summable (f : ℕ → ℂ) (hf : OneBounded f) (h1 : f 1 = 1) :
    Summable (mrtCorrectionWeight f) ∧
      (∑' n : ℕ, mrtCorrectionWeight f n) ≤ mrtCorrectionBound := by
  exact mrt_summable_of_local_euler_bound _ (mrtCorrectionWeight_zero f)
    (mrtCorrectionWeight_one f) (mrtCorrectionWeight_nonneg f)
    (mrtCorrectionWeight_mul f) (fun _ hp => mrt_correction_local_summable f hf hp)
    _ mrtCorrectionEulerConstant_nonneg
    (fun _ hp => mrt_correction_local_sum_bound f hf h1 hp)

/-- The large-divisor correction costs `O(W^(-1/4))`, with an absolute
constant independent of the multiplicative function and of the finite sum. -/
theorem mrt_correction_tail_bound (f : ℕ → ℂ) (hf : OneBounded f) (h1 : f 1 = 1)
    {W : ℕ} (hW : 0 < W) (S : Finset ℕ) (hS : ∀ n ∈ S, W ≤ n) :
    (∑ n ∈ S, ‖mrtCorrection f n‖ / (n : ℝ)) ≤
      mrtCorrectionBound * (W : ℝ) ^ (-(1 / 4 : ℝ)) := by
  have hsum := mrt_correction_summable f hf h1
  have hWr : (0 : ℝ) < W := by exact_mod_cast hW
  calc
    _ ≤ ∑ n ∈ S, mrtCorrectionWeight f n * (W : ℝ) ^ (-(1 / 4 : ℝ)) := by
      apply sum_le_sum
      intro n hn
      have hn0 : 0 < n := hW.trans_le (hS n hn)
      have hnr : (0 : ℝ) < n := by exact_mod_cast hn0
      have hid : ‖mrtCorrection f n‖ / (n : ℝ) =
          mrtCorrectionWeight f n * (n : ℝ) ^ (-(1 / 4 : ℝ)) := by
        unfold mrtCorrectionWeight
        rw [mrtArithmetic_apply_pos _ hn0, mul_assoc, ← Real.rpow_add hnr]
        norm_num
        rw [Real.rpow_neg_one, div_eq_mul_inv]
      rw [hid]
      apply mul_le_mul_of_nonneg_left _ (mrtCorrectionWeight_nonneg f n)
      exact Real.rpow_le_rpow_of_nonpos hWr (by exact_mod_cast hS n hn) (by norm_num)
    _ = (∑ n ∈ S, mrtCorrectionWeight f n) * (W : ℝ) ^ (-(1 / 4 : ℝ)) :=
      (sum_mul _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_right
      ((hsum.1.sum_le_tsum S (fun n _ => mrtCorrectionWeight_nonneg f n)).trans hsum.2)
      (Real.rpow_nonneg hWr.le _)

end TwoPointCorrelations

end OAI
