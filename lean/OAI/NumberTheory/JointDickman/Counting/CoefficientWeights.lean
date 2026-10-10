import OAI.NumberTheory.JointDickman.Probability.ResidueSummatory
import OAI.NumberTheory.JointDickman.Arithmetic.RoughDensityDerivative

namespace OAI

/-! # The actual arithmetic coefficient weight A₀ -/

namespace JointDickman

open Filter Finset
open scoped Topology

noncomputable def coefficientScale (B : ℕ) : ℝ :=
  Real.log (auxiliaryCutoff B) * auxiliaryRatio B ^ (1 / 2 : ℝ)

noncomputable def coefficientWeight (B n : ℕ) : ℝ :=
  coefficientScale B * roughSquarefreeWeight (Nat.primesLE (auxiliaryCutoff B)) (1 / 2) n

noncomputable def coefficientModel (c : ℕ → ℝ) (H B : ℕ) (Y : ℝ) : ℝ :=
  coefficientScale B * (Y * ∑ j ∈ range (H + 1),
    roughCoefficient c (Nat.primesLE (auxiliaryCutoff B)) (1 / 2) j *
      (Real.log Y) ^ ((1 / 2 : ℝ) - 1 - j))

noncomputable def coefficientDensity (c : ℕ → ℝ) (H B : ℕ) (s : ℝ) : ℝ :=
  coefficientScale B * roughDensityPolynomial c (Nat.primesLE (auxiliaryCutoff B)) (1 / 2) H (B * s)

theorem coefficientScale_nonneg (B : ℕ) : 0 ≤ coefficientScale B := by
  unfold coefficientScale
  exact mul_nonneg (Real.log_natCast_nonneg _) (Real.rpow_nonneg
    (div_nonneg (Nat.cast_nonneg B) (mul_nonneg (by norm_num) (Real.log_natCast_nonneg B))) _)

theorem coefficientWeight_nonneg (B n : ℕ) : 0 ≤ coefficientWeight B n := by
  have hs := coefficientScale_nonneg B
  unfold coefficientWeight roughSquarefreeWeight squarefreeWeight
  simp only [ArithmeticFunction.coe_mk]
  split_ifs <;> positivity

theorem coefficientScale_eventually_le : ∀ᶠ B : ℕ in atTop, coefficientScale B ≤ B := by
  filter_upwards [auxiliaryRatio_tendsto.eventually_ge_atTop 1, eventually_gt_atTop 1] with B hR hB
  have hp : auxiliaryRatio B ^ (1 / 2 : ℝ) ≤ auxiliaryRatio B := by
    simpa only [Real.rpow_one] using
      (Real.rpow_le_rpow_of_exponent_le hR (by norm_num : (1 / 2 : ℝ) ≤ 1))
  calc
    coefficientScale B ≤ Real.log (auxiliaryCutoff B) * auxiliaryRatio B :=
      mul_le_mul_of_nonneg_left hp (Real.log_natCast_nonneg _)
    _ = B := by rw [mul_comm, auxiliaryRatio_mul_log hB]

open Classical in
theorem coefficientProgression_eq {q : ℕ} (r : ZMod q) (B : ℕ) (Y : ℝ) :
    progressionSum (Ioc 0 ⌊Y⌋₊) (coefficientWeight B) r =
      coefficientScale B * roughResidueSummatory r (Nat.primesLE (auxiliaryCutoff B)) (1 / 2) Y := by
  unfold roughResidueSummatory progressionSum coefficientWeight
  rw [mul_sum]
  apply sum_congr rfl
  intro n _
  split_ifs <;> ring

theorem hasDerivAt_coefficientModel (c : ℕ → ℝ) (H B : ℕ) {Y : ℝ}
    (hB : 0 < B) (hY : 1 < Y) :
    HasDerivAt (coefficientModel c H B) (coefficientDensity c H B (Real.log Y / B)) Y := by
  have h := (hasDerivAt_logarithmic_model c (Nat.primesLE (auxiliaryCutoff B)) (1 / 2) H hY).const_mul
    (coefficientScale B)
  have hB0 : (B : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hB)
  change HasDerivAt (fun y => coefficientScale B * (y * ∑ j ∈ range (H + 1),
    roughCoefficient c (Nat.primesLE (auxiliaryCutoff B)) (1 / 2) j *
      (Real.log y) ^ ((1 / 2 : ℝ) - 1 - j))) _ Y
  simpa only [coefficientDensity, mul_div_cancel₀ _ hB0] using h

open Classical in
/-- The progression expansion for the actual A₀ weight, retaining an
arbitrary prescribed polynomial saving after normalization. -/
theorem coefficientProgression_expansion
    (hSD : PublishedInputs.SquarefreeSelbergDelangeInput)
    (hSW : PublishedInputs.SquarefreeCharacterEstimateInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    {D : ℝ} (hD : 0 ≤ D) :
    ∃ c : ℕ → ℝ, c 0 = squarefreeLeadingConstant (1 / 2) ∧ 0 < c 0 ∧
      ∃ H : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ B : ℕ in atTop, ∀ Y : ℝ,
        (B : ℝ) ^ (89 / 100 : ℝ) ≤ Real.log Y → 9 ≤ Y →
        ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ (B : ℝ) ^ (100 : ℝ) → ∀ r : (ZMod q)ˣ,
        |progressionSum (Ioc 0 ⌊Y⌋₊) (coefficientWeight B) (r : ZMod q) -
          coefficientModel c H B Y / q.totient| ≤ K * Y * (B : ℝ) ^ (-D) := by
  obtain ⟨c, hc, hcpos, H, K, hK, hbound⟩ := roughResidueSummatory_expansion hSD hSW hM
    (Or.inr rfl : (1 / 2 : ℝ) = 1 / 4 ∨ (1 / 2 : ℝ) = 1 / 2) (by linarith : 0 ≤ D + 1)
  refine ⟨c, hc, hcpos, H, K, hK, ?_⟩
  filter_upwards [hbound, coefficientScale_eventually_le, eventually_gt_atTop 0] with B hboundB hscale hB
  intro Y hY hY9 q _ hq r
  have hB0 : (0 : ℝ) < B := by exact_mod_cast hB
  have hh := hboundB Y hY hY9 q hq r
  rw [coefficientProgression_eq]
  change |coefficientScale B * _ - coefficientScale B * _ / _| ≤ _
  rw [mul_div_assoc, ← mul_sub, abs_mul, abs_of_nonneg (coefficientScale_nonneg B)]
  calc
    _ ≤ coefficientScale B * (K * Y * (B : ℝ) ^ (-(D + 1))) :=
      mul_le_mul_of_nonneg_left hh (coefficientScale_nonneg B)
    _ ≤ (B : ℝ) * (K * Y * (B : ℝ) ^ (-(D + 1))) :=
      mul_le_mul_of_nonneg_right hscale (by positivity)
    _ = _ := by
      have he : (B : ℝ) * (B : ℝ) ^ (-(D + 1)) = (B : ℝ) ^ (-D) := by
        calc
          _ = (B : ℝ) ^ (1 + -(D + 1)) := by rw [Real.rpow_add hB0, Real.rpow_one]
          _ = _ := by congr 1; ring
      calc
        _ = K * Y * ((B : ℝ) * (B : ℝ) ^ (-(D + 1))) := by ring
        _ = _ := by rw [he]

end JointDickman

end OAI
