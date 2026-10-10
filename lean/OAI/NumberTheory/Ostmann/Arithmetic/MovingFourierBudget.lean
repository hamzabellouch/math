import OAI.NumberTheory.Ostmann.Arithmetic.MovingFourierVariation
import OAI.NumberTheory.Ostmann.Arithmetic.ArithmeticErrorRates

namespace OAI

/-! # Fixed-depth cost of the constructed Fourier variation bound -/

namespace Ostmann
open scoped SchwartzMap

/-- Frequencies of size exp(O(m)) give a variation cost exp(O(m)). The
constant is chosen before the bulk size and both top giant coordinates. -/
theorem movingFourierVariationBudget_exp (ψ : 𝓢(ℝ, ℂ)) (n : ℕ)
    (A lo hi : ℝ) (hA : 0 ≤ A) (hhi : lo ≤ hi) :
    ∃ C : ℝ, 0 < C ∧ ∀ m : ℝ, 0 ≤ m →
      movingFourierVariationBudget ψ (Real.exp (A * m)) lo hi n ≤ Real.exp (C * (m + 1)) := by
  let B := SchwartzMap.seminorm ℝ 0 0 ψ
  let D := SchwartzMap.seminorm ℝ 0 1 ψ
  let W := hi - lo
  let K := 2 * B + B * W + D * W
  let r : ℝ := (2 ^ n : ℕ)
  have hB : 0 ≤ B := (norm_nonneg (ψ 0)).trans (ψ.norm_le_seminorm ℝ 0)
  have hD : 0 ≤ D := schwartz_profile_lip_nonneg ψ
  have hW : 0 ≤ W := sub_nonneg.mpr hhi
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have hr : 0 < r := by dsimp only [r]; positivity
  refine ⟨r * (K + A + 1), by positivity, ?_⟩
  intro m hm
  have hE : 1 ≤ Real.exp (A * m) := Real.one_le_exp_iff.mpr (mul_nonneg hA hm)
  have hpoly : 2 * B + (B + D * Real.exp (A * m)) * W ≤ K * Real.exp (A * m) := by
    have := mul_nonneg (show 0 ≤ 2 * B + B * W by positivity) (sub_nonneg.mpr hE)
    dsimp only [K]
    nlinarith
  have hKe : K ≤ Real.exp K := by linarith [Real.add_one_le_exp K]
  have hbase : 2 * B + (B + D * Real.exp (A * m)) * W ≤ Real.exp (K + A * m) := by
    rw [Real.exp_add]
    exact hpoly.trans (mul_le_mul_of_nonneg_right hKe (Real.exp_pos _).le)
  unfold movingFourierVariationBudget
  change (2 * B + (B + D * Real.exp (A * m)) * W) ^ (2 ^ n) ≤ _
  apply (pow_le_pow_left₀ (by positivity) hbase (2 ^ n)).trans
  rw [← Real.exp_nat_mul]
  apply Real.exp_le_exp.mpr
  change r * (K + A * m) ≤ r * (K + A + 1) * (m + 1)
  have hKm := mul_nonneg hK hm
  nlinarith

/-- Uniform in moving endpoints whose width has the actual exponential scale. -/
theorem movingFourierVariationBudget_exp_window (ψ : 𝓢(ℝ, ℂ)) (n : ℕ)
    (A H : ℝ) (hA : 0 ≤ A) (hH : 0 ≤ H) :
    ∃ C : ℝ, 0 < C ∧ ∀ m : ℝ, 0 ≤ m → ∀ lo hi : ℝ, lo ≤ hi →
      hi - lo ≤ Real.exp (H * m) →
      movingFourierVariationBudget ψ (Real.exp (A * m)) lo hi n ≤
        Real.exp (C * (m + 1)) := by
  let B := SchwartzMap.seminorm ℝ 0 0 ψ
  let D := SchwartzMap.seminorm ℝ 0 1 ψ
  let K := 3 * B + D
  let r : ℝ := (2 ^ n : ℕ)
  have hB : 0 ≤ B := (norm_nonneg (ψ 0)).trans (ψ.norm_le_seminorm ℝ 0)
  have hD : 0 ≤ D := schwartz_profile_lip_nonneg ψ
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have hr : 0 < r := by dsimp only [r]; positivity
  refine ⟨r * (K + A + H + 1), by positivity, ?_⟩
  intro m hm lo hi hhi hwidth
  have heA : 1 ≤ Real.exp (A * m) := Real.one_le_exp_iff.mpr (mul_nonneg hA hm)
  have heH : 1 ≤ Real.exp (H * m) := Real.one_le_exp_iff.mpr (mul_nonneg hH hm)
  have heAll : Real.exp (A * m) * Real.exp (H * m) = Real.exp ((A + H) * m) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hproduct : 1 ≤ Real.exp (A * m) * Real.exp (H * m) :=
    heH.trans (le_mul_of_one_le_left (Real.exp_nonneg _) heA)
  have hHproduct : Real.exp (H * m) ≤ Real.exp (A * m) * Real.exp (H * m) :=
    le_mul_of_one_le_left (Real.exp_nonneg _) heA
  have hpoly : 2 * B + (B + D * Real.exp (A * m)) * (hi - lo) ≤
      K * Real.exp ((A + H) * m) := by
    calc
      _ ≤ 2 * B + (B + D * Real.exp (A * m)) * Real.exp (H * m) := by gcongr
      _ ≤ K * (Real.exp (A * m) * Real.exp (H * m)) := by
        dsimp only [K]
        nlinarith [mul_le_mul_of_nonneg_left hproduct hB,
          mul_le_mul_of_nonneg_left hHproduct hB]
      _ = _ := by rw [heAll]
  have hKe : K ≤ Real.exp K := by linarith [Real.add_one_le_exp K]
  have hbase : 2 * B + (B + D * Real.exp (A * m)) * (hi - lo) ≤
      Real.exp (K + (A + H) * m) := by
    rw [Real.exp_add]
    exact hpoly.trans (mul_le_mul_of_nonneg_right hKe (Real.exp_nonneg _))
  unfold movingFourierVariationBudget
  change (2 * B + (B + D * Real.exp (A * m)) * (hi - lo)) ^ (2 ^ n) ≤ _
  apply (pow_le_pow_left₀ (by positivity) hbase (2 ^ n)).trans
  rw [← Real.exp_nat_mul]
  apply Real.exp_le_exp.mpr
  change r * (K + (A + H) * m) ≤ r * (K + A + H + 1) * (m + 1)
  nlinarith [mul_nonneg hK hm]

end Ostmann

end OAI
