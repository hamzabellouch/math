import OAI.NumberTheory.JointDickman.Arithmetic.RoughMeanBounds
import OAI.NumberTheory.JointDickman.Counting.CoefficientWeights

namespace OAI

/-! # First and second moments of the actual coefficient A₀

These are the estimates in equation (5) of the manuscript.  The two
specializations of the published Selberg–Delange input suffice here.
-/

namespace JointDickman

open Filter Finset
open scoped Topology

theorem roughSquarefreeWeight_sq (E : Finset ℕ) (z : ℝ) (n : ℕ) :
    roughSquarefreeWeight E z n ^ 2 = roughSquarefreeWeight E (z ^ 2) n := by
  simp only [roughSquarefreeWeight, squarefreeWeight, ArithmeticFunction.coe_mk]
  split_ifs <;> simp [← pow_mul, Nat.mul_comm]

theorem coefficientScale_eq_roughMeanNormalization (B : ℕ) :
    coefficientScale B = roughMeanNormalization B (1 / 2) := by
  norm_num [coefficientScale, roughMeanNormalization]

theorem coefficientScale_sq (B : ℕ) (hB : 1 < B) :
    coefficientScale B ^ 2 =
      (Real.log (auxiliaryCutoff B) * auxiliaryRatio B ^ (1 / 4 : ℝ)) *
        roughMeanNormalization B (1 / 4) := by
  have hR := auxiliaryRatio_pos hB
  have hhalf : (auxiliaryRatio B ^ (1 / 2 : ℝ)) ^ 2 = auxiliaryRatio B := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hR.le]
    norm_num
  have hquarter : auxiliaryRatio B ^ (1 / 4 : ℝ) *
      auxiliaryRatio B ^ (1 - 1 / 4 : ℝ) = auxiliaryRatio B := by
    rw [← Real.rpow_add hR]
    norm_num
  simp only [coefficientScale, roughMeanNormalization, mul_pow, hhalf]
  rw [mul_mul_mul_comm, hquarter]
  ring

theorem coefficient_second_moment_factor {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ B : ℕ in atTop,
      Real.log (auxiliaryCutoff B) * auxiliaryRatio B ^ (1 / 4 : ℝ) ≤
        (B : ℝ) ^ (1 / 4 + ε) := by
  have hsmall : ∀ᶠ B : ℕ in atTop,
      (1000 : ℝ) ^ (3 / 4 : ℝ) * (Real.log B) ^ (3 / 4 : ℝ) /
        (B : ℝ) ^ ε ≤ 1 := by
    have h := ((log_power_div_power_tendsto_zero (3 / 4) hε).const_mul
      ((1000 : ℝ) ^ (3 / 4 : ℝ))).comp tendsto_natCast_atTop_atTop
    simp only [mul_zero] at h
    filter_upwards [h.eventually (eventually_le_nhds (by norm_num : (0 : ℝ) < 1))] with B hB
    simpa [mul_div_assoc] using hB
  filter_upwards [hsmall, eventually_gt_atTop 1] with B hsmallB hB
  have hB0 : (0 : ℝ) < B := by exact_mod_cast (lt_trans Nat.zero_lt_one hB)
  have hl : 0 < Real.log (auxiliaryCutoff B) := by
    simpa [auxiliaryCutoff, Nat.cast_pow, Real.log_pow] using
      mul_pos (by norm_num : (0 : ℝ) < 1000)
        (Real.log_pos (show (1 : ℝ) < B by exact_mod_cast hB))
  have hr : auxiliaryRatio B = (B : ℝ) / Real.log (auxiliaryCutoff B) := by
    simp [auxiliaryRatio, auxiliaryCutoff, Nat.cast_pow, Real.log_pow]
  have hpow : Real.log (auxiliaryCutoff B) ^ (3 / 4 : ℝ) ≤ (B : ℝ) ^ ε := by
    simp only [auxiliaryCutoff, Nat.cast_pow, Real.log_pow, Nat.cast_ofNat]
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 1000) (Real.log_natCast_nonneg B)]
    exact (div_le_one (Real.rpow_pos_of_pos hB0 ε)).mp hsmallB
  calc
    _ = (B : ℝ) ^ (1 / 4 : ℝ) * Real.log (auxiliaryCutoff B) ^ (3 / 4 : ℝ) := by
      rw [hr, Real.div_rpow hB0.le hl.le]
      have he : Real.log (auxiliaryCutoff B) /
          Real.log (auxiliaryCutoff B) ^ (1 / 4 : ℝ) =
          Real.log (auxiliaryCutoff B) ^ (3 / 4 : ℝ) := by
        calc
          _ = Real.log (auxiliaryCutoff B) ^ (1 : ℝ) /
              Real.log (auxiliaryCutoff B) ^ (1 / 4 : ℝ) := by rw [Real.rpow_one]
          _ = _ := by rw [← Real.rpow_sub hl]; norm_num
      calc
        _ = (B : ℝ) ^ (1 / 4 : ℝ) *
            (Real.log (auxiliaryCutoff B) / Real.log (auxiliaryCutoff B) ^ (1 / 4 : ℝ)) := by ring
        _ = _ := by rw [he]
    _ ≤ (B : ℝ) ^ (1 / 4 : ℝ) * (B : ℝ) ^ ε :=
      mul_le_mul_of_nonneg_left hpow (by positivity)
    _ = _ := (Real.rpow_add hB0 _ _).symm

theorem coefficient_first_moment
    (hSD : PublishedInputs.SquarefreeSelbergDelangeInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    (hMP : PublishedInputs.PrimeProductMertensInput) {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ B : ℕ in atTop, ∀ Y : ℝ,
      9 ≤ Y → δ * B ≤ Real.log Y →
      ∑ n ∈ Ioc 0 ⌊Y⌋₊, coefficientWeight B n ≤ C * Y := by
  obtain ⟨C, hC, hbound⟩ := rough_normalized_mean_bound hSD hM hMP (Or.inr rfl) hδ
  refine ⟨C, hC, ?_⟩
  filter_upwards [hbound] with B hboundB
  intro Y hY hlog
  simpa only [coefficientWeight, ← mul_sum, coefficientScale_eq_roughMeanNormalization,
    roughSquarefreeSummatory] using hboundB Y hY hlog

theorem coefficient_second_moment
    (hSD : PublishedInputs.SquarefreeSelbergDelangeInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    (hMP : PublishedInputs.PrimeProductMertensInput) {δ ε : ℝ}
    (hδ : 0 < δ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ B : ℕ in atTop, ∀ Y : ℝ,
      9 ≤ Y → δ * B ≤ Real.log Y →
      ∑ n ∈ Ioc 0 ⌊Y⌋₊, coefficientWeight B n ^ 2 ≤
        C * Y * (B : ℝ) ^ (1 / 4 + ε) := by
  obtain ⟨C, hC, hbound⟩ := rough_normalized_mean_bound hSD hM hMP (Or.inl rfl) hδ
  refine ⟨C, hC, ?_⟩
  filter_upwards [hbound, coefficient_second_moment_factor hε, eventually_gt_atTop 1]
    with B hboundB hfactor hB
  intro Y hY hlog
  have hY0 : 0 ≤ Y := by linarith
  calc
    _ = coefficientScale B ^ 2 *
        roughSquarefreeSummatory (Nat.primesLE (auxiliaryCutoff B)) (1 / 4) Y := by
      simp only [coefficientWeight, mul_pow, roughSquarefreeWeight_sq]
      norm_num [roughSquarefreeSummatory, mul_sum]
    _ = (Real.log (auxiliaryCutoff B) * auxiliaryRatio B ^ (1 / 4 : ℝ)) *
        (roughMeanNormalization B (1 / 4) *
          roughSquarefreeSummatory (Nat.primesLE (auxiliaryCutoff B)) (1 / 4) Y) := by
      rw [coefficientScale_sq B hB, mul_assoc]
    _ ≤ (Real.log (auxiliaryCutoff B) * auxiliaryRatio B ^ (1 / 4 : ℝ)) * (C * Y) :=
      mul_le_mul_of_nonneg_left (hboundB Y hY hlog)
        (mul_nonneg (Real.log_natCast_nonneg _) (Real.rpow_nonneg
          (auxiliaryRatio_pos hB).le _))
    _ ≤ (B : ℝ) ^ (1 / 4 + ε) * (C * Y) :=
      mul_le_mul_of_nonneg_right hfactor (mul_nonneg hC hY0)
    _ = _ := by ring

end JointDickman

end OAI
