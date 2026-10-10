import OAI.NumberTheory.Ostmann.Arithmetic.BulkKernelPairComparison
import OAI.NumberTheory.Ostmann.Arithmetic.MovingFourierBudget
import OAI.NumberTheory.Ostmann.Construction.SpectatorBulkScale

namespace OAI

/-! # Fixed-depth cost of the actual sharp pattern kernel -/

namespace Ostmann
open scoped SchwartzMap

theorem movingFourierVariationBudget_nonneg (ψ : 𝓢(ℝ, ℂ))
    (V lo hi : ℝ) (n : ℕ) (hV : 0 ≤ V) (hhi : lo ≤ hi) :
    0 ≤ movingFourierVariationBudget ψ V lo hi n := by
  have hB := (norm_nonneg (ψ 0)).trans (ψ.norm_le_seminorm ℝ 0)
  have hD := schwartz_profile_lip_nonneg ψ
  have hW := sub_nonneg.mpr hhi
  unfold movingFourierVariationBudget
  positivity

/-- Both the polynomial root count and the smooth variation use the bounds
of the constructed pattern tree. The constant is independent of bulk size. -/
theorem movingPatternKernelBudget_exp (ψ : 𝓢(ℝ, ℂ)) (n r₀ : ℕ)
    (A lo hi B D : ℝ) (hA : 0 ≤ A) (hhi : lo ≤ hi) :
    ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ,
      bulkKernelPairComparisonBudget ψ (Real.exp (A * m)) lo hi n
        (2 ^ n * (r₀ + m + 4 * n + 4)) (2 ^ n * (r₀ + m + 4 * n)) 0 B D ≤
      Real.exp (C * ((m : ℝ) + 1)) := by
  obtain ⟨C, hC, hV⟩ := movingFourierVariationBudget_exp ψ n A lo hi hA hhi
  let c := (2 ^ n + (2 ^ n - 1)) + (3 * (2 ^ n - 1) + 2 * 2 ^ n)
  let a := 2 * c * (2 * n + 1) * 2 ^ n
  let b := 2 * c * (2 * n * (2 ^ n * (r₀ + 4 * n + 4)) +
    2 ^ n * (r₀ + 4 * n)) + 1
  let K : ℝ := a + b
  let H : ℝ := ((2 * B + D * (Real.exp 2 - 1)) ^ (2 ^ n - 1)) ^ 2
  have hK : 0 < K := by dsimp only [K, b]; positivity
  have hH : 0 ≤ H := sq_nonneg _
  refine ⟨K + 2 * C + H, by positivity, ?_⟩
  intro m
  have hm : 0 ≤ (m : ℝ) := Nat.cast_nonneg _
  have hcount :
      2 * (((2 ^ n + (2 ^ n - 1)) * (2 * (n * (2 ^ n * (r₀ + m + 4 * n + 4)) + 0) +
        2 ^ n * (r₀ + m + 4 * n))) +
        ((3 * (2 ^ n - 1) + 2 * 2 ^ n) * (2 * (n * (2 ^ n * (r₀ + m + 4 * n + 4)) + 0) +
        2 ^ n * (r₀ + m + 4 * n)))) + 1 = a * m + b := by
    dsimp only [a, b, c]
    ring
  have hroot : ((a * m + b : ℕ) : ℝ) ≤ Real.exp (K * ((m : ℝ) + 1)) := by
    have hab : ((a * m + b : ℕ) : ℝ) ≤ K * ((m : ℝ) + 1) := by
      push_cast
      dsimp only [K]
      nlinarith [mul_nonneg (Nat.cast_nonneg b : (0 : ℝ) ≤ b) hm]
    exact hab.trans (by linarith [Real.add_one_le_exp (K * ((m : ℝ) + 1))])
  have hv0 := movingFourierVariationBudget_nonneg ψ (Real.exp (A * m)) lo hi n
    (Real.exp_nonneg _) hhi
  have hv2 := pow_le_pow_left₀ hv0 (hV m hm) 2
  have hh : H ≤ Real.exp (H * ((m : ℝ) + 1)) := by
    have : H ≤ H * ((m : ℝ) + 1) := by nlinarith [mul_nonneg hH hm]
    exact this.trans (by linarith [Real.add_one_le_exp (H * ((m : ℝ) + 1))])
  unfold bulkKernelPairComparisonBudget
  rw [hcount, mul_pow]
  change ((a * m + b : ℕ) : ℝ) *
    (movingFourierVariationBudget ψ (Real.exp (A * m)) lo hi n ^ 2 * H) ≤ _
  calc
    _ ≤ Real.exp (K * ((m : ℝ) + 1)) *
        ((Real.exp (C * ((m : ℝ) + 1))) ^ 2 * Real.exp (H * ((m : ℝ) + 1))) := by
      gcongr
    _ = Real.exp ((K + 2 * C + H) * ((m : ℝ) + 1)) := by
      rw [← Real.exp_nat_mul]
      simp only [← Real.exp_add]
      congr 1
      ring

/-- The manuscript chooses a bulk length linear in `L` at fixed depth.
Consequently the complete sharp comparison budget fits the quadratic cost
used by the weighted prime-error estimate. -/
theorem movingPatternKernelBudget_spectatorScale (ψ : 𝓢(ℝ, ℂ)) (n r₀ k : ℕ)
    (A lo hi B D : ℝ) (hA : 0 ≤ A) (hhi : lo ≤ hi) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ L : ℝ, 1 ≤ L →
      let m := spectatorBulkCount k L
      bulkKernelPairComparisonBudget ψ (Real.exp (A * m)) lo hi n
        (2 ^ n * (r₀ + m + 4 * n + 4)) (2 ^ n * (r₀ + m + 4 * n)) 0 B D ≤
      Real.exp (C * L ^ 2) := by
  obtain ⟨C, hC, hb⟩ := movingPatternKernelBudget_exp ψ n r₀ A lo hi B D hA hhi
  refine ⟨C * ((k : ℝ) ^ 4 + 1) + 1, ?_, ?_⟩
  · have : 0 ≤ C * ((k : ℝ) ^ 4 + 1) := by positivity
    linarith
  intro L hL
  dsimp only
  apply (hb _).trans
  apply Real.exp_le_exp.mpr
  have hL0 : 0 ≤ L := by linarith
  have hm := spectatorBulkCount_upper k L hL0
  have hLsq : L ≤ L ^ 2 := by nlinarith
  have hscale : (spectatorBulkCount k L : ℝ) + 1 ≤ ((k : ℝ) ^ 4 + 1) * L ^ 2 := by
    have := mul_le_mul_of_nonneg_left hLsq (pow_nonneg (Nat.cast_nonneg k : (0 : ℝ) ≤ k) 4)
    nlinarith
  have := mul_le_mul_of_nonneg_left hscale hC.le
  nlinarith [sq_nonneg L]

theorem movingPatternKernelBudget_exp_window (ψ : 𝓢(ℝ, ℂ)) (n r₀ : ℕ)
    (A H B D : ℝ) (hA : 0 ≤ A) (hH : 0 ≤ H) :
    ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, ∀ lo hi : ℝ, lo ≤ hi →
      hi - lo ≤ Real.exp (H * m) →
      bulkKernelPairComparisonBudget ψ (Real.exp (A * m)) lo hi n
        (2 ^ n * (r₀ + m + 4 * n + 4)) (2 ^ n * (r₀ + m + 4 * n)) 0 B D ≤
      Real.exp (C * ((m : ℝ) + 1)) := by
  obtain ⟨C, hC, hV⟩ := movingFourierVariationBudget_exp_window ψ n A H hA hH
  let c := (2 ^ n + (2 ^ n - 1)) + (3 * (2 ^ n - 1) + 2 * 2 ^ n)
  let a := 2 * c * (2 * n + 1) * 2 ^ n
  let b := 2 * c * (2 * n * (2 ^ n * (r₀ + 4 * n + 4)) +
    2 ^ n * (r₀ + 4 * n)) + 1
  let K : ℝ := a + b
  let H : ℝ := ((2 * B + D * (Real.exp 2 - 1)) ^ (2 ^ n - 1)) ^ 2
  have hK : 0 < K := by dsimp only [K, b]; positivity
  have hH : 0 ≤ H := sq_nonneg _
  refine ⟨K + 2 * C + H, by positivity, ?_⟩
  intro m lo hi hhi hwidth
  have hm : 0 ≤ (m : ℝ) := Nat.cast_nonneg _
  have hcount :
      2 * (((2 ^ n + (2 ^ n - 1)) * (2 * (n * (2 ^ n * (r₀ + m + 4 * n + 4)) + 0) +
        2 ^ n * (r₀ + m + 4 * n))) +
        ((3 * (2 ^ n - 1) + 2 * 2 ^ n) * (2 * (n * (2 ^ n * (r₀ + m + 4 * n + 4)) + 0) +
        2 ^ n * (r₀ + m + 4 * n)))) + 1 = a * m + b := by
    dsimp only [a, b, c]
    ring
  have hroot : ((a * m + b : ℕ) : ℝ) ≤ Real.exp (K * ((m : ℝ) + 1)) := by
    have hab : ((a * m + b : ℕ) : ℝ) ≤ K * ((m : ℝ) + 1) := by
      push_cast
      dsimp only [K]
      nlinarith [mul_nonneg (Nat.cast_nonneg b : (0 : ℝ) ≤ b) hm]
    exact hab.trans (by linarith [Real.add_one_le_exp (K * ((m : ℝ) + 1))])
  have hv0 := movingFourierVariationBudget_nonneg ψ (Real.exp (A * m)) lo hi n
    (Real.exp_nonneg _) hhi
  have hv2 := pow_le_pow_left₀ hv0 (hV m hm lo hi hhi hwidth) 2
  have hh : H ≤ Real.exp (H * ((m : ℝ) + 1)) := by
    have : H ≤ H * ((m : ℝ) + 1) := by nlinarith [mul_nonneg hH hm]
    exact this.trans (by linarith [Real.add_one_le_exp (H * ((m : ℝ) + 1))])
  unfold bulkKernelPairComparisonBudget
  rw [hcount, mul_pow]
  change ((a * m + b : ℕ) : ℝ) *
    (movingFourierVariationBudget ψ (Real.exp (A * m)) lo hi n ^ 2 * H) ≤ _
  calc
    _ ≤ Real.exp (K * ((m : ℝ) + 1)) *
        ((Real.exp (C * ((m : ℝ) + 1))) ^ 2 * Real.exp (H * ((m : ℝ) + 1))) := by
      gcongr
    _ = Real.exp ((K + 2 * C + H) * ((m : ℝ) + 1)) := by
      rw [← Real.exp_nat_mul]
      simp only [← Real.exp_add]
      congr 1
      ring

theorem movingPatternKernelBudget_spectatorScale_window (ψ : 𝓢(ℝ, ℂ)) (n r₀ k : ℕ)
    (A H B D : ℝ) (hA : 0 ≤ A) (hH : 0 ≤ H) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ L : ℝ, 1 ≤ L →
      let m := spectatorBulkCount k L
      ∀ lo hi : ℝ, lo ≤ hi → hi - lo ≤ Real.exp (H * m) →
      bulkKernelPairComparisonBudget ψ (Real.exp (A * m)) lo hi n
        (2 ^ n * (r₀ + m + 4 * n + 4)) (2 ^ n * (r₀ + m + 4 * n)) 0 B D ≤
      Real.exp (C * L ^ 2) := by
  obtain ⟨C, hC, hb⟩ := movingPatternKernelBudget_exp_window ψ n r₀ A H B D hA hH
  refine ⟨C * ((k : ℝ) ^ 4 + 1) + 1, ?_, ?_⟩
  · have : 0 ≤ C * ((k : ℝ) ^ 4 + 1) := by positivity
    linarith
  intro L hL
  dsimp only
  intro lo hi hhi hwidth
  apply (hb _ lo hi hhi hwidth).trans
  apply Real.exp_le_exp.mpr
  have hL0 : 0 ≤ L := by linarith
  have hm := spectatorBulkCount_upper k L hL0
  have hLsq : L ≤ L ^ 2 := by nlinarith
  have hscale : (spectatorBulkCount k L : ℝ) + 1 ≤ ((k : ℝ) ^ 4 + 1) * L ^ 2 := by
    have := mul_le_mul_of_nonneg_left hLsq (pow_nonneg (Nat.cast_nonneg k : (0 : ℝ) ≤ k) 4)
    nlinarith
  have := mul_le_mul_of_nonneg_left hscale hC.le
  nlinarith [sq_nonneg L]

end Ostmann

end OAI
