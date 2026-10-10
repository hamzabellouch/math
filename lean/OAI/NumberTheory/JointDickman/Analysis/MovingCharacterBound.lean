import OAI.NumberTheory.JointDickman.Analysis.CharacterTruncation
import OAI.NumberTheory.JointDickman.Arithmetic.RoughAuxiliaryExpansion

namespace OAI

/-! # The nonprincipal character estimate after removing the small primes -/

namespace JointDickman

open Finset Filter
open scoped Topology

theorem roughTruncation_rankin_full {Y : ℝ} {P : ℕ}
    (hY : 0 < Y) (hL : 16 ≤ Real.log Y) (hP : 0 < Real.log P) :
    1 / (roughTruncation Y : ℝ) ^ (1 / Real.log P) ≤
      Real.exp (-(Real.log Y / (8 * Real.log P))) := by
  obtain ⟨hV, _, hlogV⟩ := roughTruncation_bounds hY hL
  have hV0 : (0 : ℝ) < roughTruncation Y := by exact_mod_cast hV
  rw [Real.rpow_def_of_pos hV0, one_div, ← Real.exp_neg]
  apply Real.exp_le_exp.mpr
  have h := mul_le_mul_of_nonneg_right hlogV
    (show 0 ≤ 1 / Real.log P by positivity)
  have hpos : 0 ≤ Real.log Y / (8 * Real.log P) := by positivity
  have heq : (Real.log Y / 4) * (1 / Real.log P) =
      2 * (Real.log Y / (8 * Real.log P)) := by ring
  rw [heq] at h
  linarith

/-- Every fixed logarithmic saving survives the convolution, at the
cost of a fixed power of the cutoff logarithm and an explicit Rankin error. -/
theorem roughCharacterSum_exponential
    (hSW : PublishedInputs.SquarefreeCharacterEstimateInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) {z : ℝ}
    (hz : z = 1 / 4 ∨ z = 1 / 2) {D : ℝ} (hD : 0 ≤ D) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (P : ℕ) (Y : ℝ),
      2 ≤ P → 1 ≤ Real.log P → 9 ≤ Y → 16 ≤ Real.log Y →
      ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ (Real.log Y / 2) ^ (200 : ℝ) →
      ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
      ‖roughCharacterSum χ (Nat.primesLE P) z Y‖ ≤
        Y * K * ((Real.log Y) ^ (-D) * (Real.log P) ^ (Real.exp 1 + 1) +
          (Real.log P) ^ (Real.exp 1) * Real.exp (-(Real.log Y / (8 * Real.log P)))) := by
  obtain ⟨C, hC, hbound⟩ := roughCharacterSum_truncated hSW hz (by norm_num : (0 : ℝ) < 200) hD
  obtain ⟨A, hA, hmom⟩ := smoothCorrection_log_moments_bound hM
  obtain ⟨A', hA', hshift⟩ := smoothCorrection_shifted_bound hM
  let K := C * A * (2 : ℝ) ^ D + A'
  have hz0 : 0 ≤ z := by rcases hz with rfl | rfl <;> norm_num
  have hzh : z ≤ 1 / 2 := by rcases hz with rfl | rfl <;> norm_num
  have hK : 0 ≤ K := by dsimp [K]; positivity
  refine ⟨K, hK, fun P Y hP hlogP hY hL q _ hq χ hχ => ?_⟩
  have hY0 : 0 < Y := by linarith
  have hLP : 0 < Real.log P := by linarith
  have hLY : 0 < Real.log Y := by linarith
  obtain ⟨hV, hV2, _⟩ := roughTruncation_bounds hY0 hL
  have hmain := hbound (Nat.primesLE P) Y (roughTruncation Y) hY hV2 q hq χ hχ
  have habs : (∑ v ∈ Ioc 0 (roughTruncation Y),
      |smoothCorrection (Nat.primesLE P) z v| / (v : ℝ)) ≤ A * (Real.log P) ^ (Real.exp 1) := by
    simpa using hmom P (Ioc 0 (roughTruncation Y)) z 0 hP hlogP hz0 hzh
  have htail : ‖characterConvolutionTail χ (Nat.primesLE P) z ⌊Y⌋₊ (roughTruncation Y)‖ ≤
      Y * A' * (Real.log P) ^ (Real.exp 1) * Real.exp (-(Real.log Y / (8 * Real.log P))) := by
    have ht := characterConvolutionTail_rankin χ (Nat.primesLE P) hz0 (by linarith)
      (by positivity : 0 ≤ 1 / Real.log P) ⌊Y⌋₊ (roughTruncation Y) hV
    calc
      _ ≤ ((⌊Y⌋₊ : ℝ) / (roughTruncation Y : ℝ) ^ (1 / Real.log P)) *
          (A' * (Real.log P) ^ (Real.exp 1)) :=
        ht.trans (mul_le_mul_of_nonneg_left
          (hshift P (Ioc (roughTruncation Y) ⌊Y⌋₊) z hP hlogP hz0 hzh) (by positivity))
      _ ≤ (Y / (roughTruncation Y : ℝ) ^ (1 / Real.log P)) *
          (A' * (Real.log P) ^ (Real.exp 1)) := by
        gcongr
        exact Nat.floor_le hY0.le
      _ = Y * (A' * (Real.log P) ^ (Real.exp 1)) *
          (1 / (roughTruncation Y : ℝ) ^ (1 / Real.log P)) := by ring
      _ ≤ Y * (A' * (Real.log P) ^ (Real.exp 1)) *
          Real.exp (-(Real.log Y / (8 * Real.log P))) :=
        mul_le_mul_of_nonneg_left (roughTruncation_rankin_full hY0 hL hLP) (by positivity)
      _ = _ := by ring
  have hfactor : (Real.log Y / 2) ^ (-D) = (2 : ℝ) ^ D * (Real.log Y) ^ (-D) := by
    rw [Real.div_rpow hLY.le (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), div_inv_eq_mul]
    ring
  have hlogpow : (Real.log P) ^ (Real.exp 1) ≤ (Real.log P) ^ (Real.exp 1 + 1) :=
    Real.rpow_le_rpow_of_exponent_le hlogP (by linarith)
  have hK1 : C * A * (2 : ℝ) ^ D ≤ K := by dsimp [K]; linarith
  have hK2 : A' ≤ K := by
    dsimp [K]
    have hpos : 0 ≤ C * A * (2 : ℝ) ^ D := by positivity
    linarith
  calc
    _ ≤ C * Y * (Real.log Y / 2) ^ (-D) * (A * (Real.log P) ^ (Real.exp 1)) +
        Y * A' * (Real.log P) ^ (Real.exp 1) * Real.exp (-(Real.log Y / (8 * Real.log P))) :=
      hmain.trans (add_le_add (mul_le_mul_of_nonneg_left habs (by positivity)) htail)
    _ = Y * (C * A * (2 : ℝ) ^ D) * (Real.log Y) ^ (-D) * (Real.log P) ^ (Real.exp 1) +
        Y * A' * (Real.log P) ^ (Real.exp 1) * Real.exp (-(Real.log Y / (8 * Real.log P))) := by
      rw [hfactor]
      ring
    _ ≤ Y * K * (Real.log Y) ^ (-D) * (Real.log P) ^ (Real.exp 1 + 1) +
        Y * K * (Real.log P) ^ (Real.exp 1) * Real.exp (-(Real.log Y / (8 * Real.log P))) := by
      apply add_le_add
      · exact mul_le_mul (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hK1 hY0.le) (by positivity)) hlogpow (by positivity) (by positivity)
      · gcongr
    _ = _ := by ring

end JointDickman

end OAI
