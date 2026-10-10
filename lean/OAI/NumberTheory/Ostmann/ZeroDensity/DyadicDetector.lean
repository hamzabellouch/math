import Mathlib.Algebra.Order.BigOperators.Group.LocallyFinite
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Log.Base
import OAI.NumberTheory.Ostmann.ZeroDensity.FiniteDetector

namespace OAI

noncomputable section
open scoped BigOperators

namespace Ostmann.ZeroDensity

theorem sum_dyadic_intervals {E : Type*} [AddCommMonoid E] (f : ℕ → E) (X J : ℕ) :
    (∑ j ∈ Finset.range J, ∑ n ∈ Finset.Ioc (2 ^ j * X) (2 ^ (j + 1) * X), f n) =
      ∑ n ∈ Finset.Ioc X (2 ^ J * X), f n := by
  induction J with
  | zero => simp
  | succ J ih =>
      rw [Finset.sum_range_succ, ih]
      apply Finset.sum_Ioc_consecutive f
      · have hpow : 1 ≤ 2 ^ J := by
          have : 0 < (2 : ℕ) ^ J := by positivity
          omega
        simpa using Nat.mul_le_mul_right X hpow
      · exact Nat.mul_le_mul_right X (Nat.pow_le_pow_right (by decide) (by omega))

def detectorBlock {q : ℕ} (χ : DirichletCharacter ℂ q) (X N j : ℕ) (s : ℂ) : ℂ :=
  ∑ n ∈ Finset.Ioc (2 ^ j * X) (2 ^ (j + 1) * X),
    mollifierCoefficient X N n * χ n * (n : ℂ) ^ (-s)

theorem detector_eq_sum_blocks {q : ℕ} (χ : DirichletCharacter ℂ q)
    (X N J : ℕ) (hN : N ≤ 2 ^ J) (s : ℂ) :
    detectorPolynomial χ X N s = ∑ j ∈ Finset.range J, detectorBlock χ X N j s := by
  unfold detectorPolynomial detectorBlock
  rw [sum_dyadic_intervals]
  apply Finset.sum_subset
  · intro n hn
    apply Finset.mem_Ioc.mpr
    refine ⟨(Finset.mem_Ioc.mp hn).1, (Finset.mem_Ioc.mp hn).2.trans ?_⟩
    simpa [mul_comm] using Nat.mul_le_mul_left X hN
  · intro n hn hnot
    have hnX : X < n := (Finset.mem_Ioc.mp hn).1
    have hsupport : X * N < n := by
      simp only [Finset.mem_Ioc] at hnot
      omega
    simp [mollifierCoefficient_support hsupport]

theorem norm_sum_sq_le_card_mul {ι : Type*} (s : Finset ι) (f : ι → ℂ) :
    ‖∑ i ∈ s, f i‖ ^ 2 ≤ (s.card : ℝ) * ∑ i ∈ s, ‖f i‖ ^ 2 := by
  calc
    ‖∑ i ∈ s, f i‖ ^ 2 ≤ (∑ i ∈ s, ‖f i‖) ^ 2 := by
      have h := norm_sum_le s f
      have hnonneg : 0 ≤ ∑ i ∈ s, ‖f i‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
      nlinarith [norm_nonneg (∑ i ∈ s, f i)]
    _ ≤ _ := sq_sum_le_card_mul_sum_sq

theorem detector_norm_sq_le_blocks {q : ℕ} (χ : DirichletCharacter ℂ q)
    (X N J : ℕ) (hN : N ≤ 2 ^ J) (s : ℂ) :
    ‖detectorPolynomial χ X N s‖ ^ 2 ≤
      (J : ℝ) * ∑ j ∈ Finset.range J, ‖detectorBlock χ X N j s‖ ^ 2 := by
  rw [detector_eq_sum_blocks χ X N J hN s]
  simpa using norm_sum_sq_le_card_mul (Finset.range J) (fun j => detectorBlock χ X N j s)

theorem detected_family_card_le {ι : Type*} (samples : Finset ι) (J : ℕ)
    (block : ι → ℕ → ℂ)
    (hdetector : ∀ i ∈ samples, 1 / 2 ≤ ‖∑ j ∈ Finset.range J, block i j‖) :
    (samples.card : ℝ) ≤
      4 * J * ∑ j ∈ Finset.range J, ∑ i ∈ samples, ‖block i j‖ ^ 2 := by
  have hpoint : ∀ i ∈ samples,
      (1 : ℝ) ≤ 4 * J * ∑ j ∈ Finset.range J, ‖block i j‖ ^ 2 := by
    intro i hi
    have hlo := hdetector i hi
    have hhi := norm_sum_sq_le_card_mul (Finset.range J) (block i)
    simp only [Finset.card_range] at hhi
    nlinarith [norm_nonneg (∑ j ∈ Finset.range J, block i j)]
  calc
    (samples.card : ℝ) = ∑ _i ∈ samples, (1 : ℝ) := by simp
    _ ≤ ∑ i ∈ samples, 4 * J * ∑ j ∈ Finset.range J, ‖block i j‖ ^ 2 :=
      Finset.sum_le_sum hpoint
    _ = 4 * J * ∑ j ∈ Finset.range J, ∑ i ∈ samples, ‖block i j‖ ^ 2 := by
      rw [← Finset.mul_sum, Finset.sum_comm]

def detectorBlockCount (N : ℕ) : ℕ := Nat.log 2 N + 1

theorem detectorBlockCount_covers (N : ℕ) : N ≤ 2 ^ detectorBlockCount N :=
  (Nat.lt_pow_succ_log_self (by decide : 1 < 2) N).le

theorem detectorBlockCount_le_log (N : ℕ) :
    (detectorBlockCount N : ℝ) ≤ Real.log N / Real.log 2 + 1 := by
  simpa [detectorBlockCount, Real.logb] using add_le_add_right (Real.natLog_le_logb N 2) 1

theorem detectorBlockCount_pow_le {N : ℕ} (hN : 1 ≤ N) :
    2 ^ detectorBlockCount N ≤ 2 * N := by
  unfold detectorBlockCount
  rw [pow_succ]
  have h := Nat.mul_le_mul_right 2 (Nat.pow_log_le_self 2 (by omega : N ≠ 0))
  simpa [mul_comm] using h

end Ostmann.ZeroDensity

end

end OAI
