import Mathlib
import OAI.Analysis.RieszRectifiability.Projections.FiniteProjectionAveraging

namespace OAI

namespace RieszRectifiability

noncomputable section

open scoped BigOperators

variable {ι : Type*} {d : ℕ}

theorem finiteProjectionAverage_increment_identity (F : Finset ι)
    (θ : ι → Ambient d → ℝ) (π : ι → Ambient d → Ambient d)
    (p : Ambient d → Ambient d) (x y : Ambient d)
    (hx : (∑ i ∈ F, θ i x) = 1) (hy : (∑ i ∈ F, θ i y) = 1) :
    (finiteProjectionAverage F θ π x - finiteProjectionAverage F θ π y) - (p x - p y) =
      (∑ i ∈ F, θ i x • ((π i x - π i y) - (p x - p y))) +
      ∑ i ∈ F, (θ i x - θ i y) • (π i y - p y) := by
  rw [finiteProjectionAverage_eq_weighted_sum F θ π x hx,
    finiteProjectionAverage_eq_weighted_sum F θ π y hy]
  simp only [smul_sub, sub_smul, Finset.sum_sub_distrib,
    ← Finset.sum_smul, hx, hy, one_smul]
  abel

theorem finiteProjectionAverage_increment_estimate (F : Finset ι)
    (θ : ι → Ambient d → ℝ) (π : ι → Ambient d → Ambient d)
    (p : Ambient d → Ambient d) (x y : Ambient d) (α B : ℝ)
    (hθ : ∀ i ∈ F, 0 ≤ θ i x)
    (hx : (∑ i ∈ F, θ i x) = 1) (hy : (∑ i ∈ F, θ i y) = 1)
    (hlinear : ∀ i ∈ F, θ i x ≠ 0 →
      ‖(π i x - π i y) - (p x - p y)‖ ≤ α * dist x y)
    (hoffset : ∀ i ∈ F, θ i x ≠ θ i y → dist (π i y) (p y) ≤ B) :
    ‖(finiteProjectionAverage F θ π x - finiteProjectionAverage F θ π y) - (p x - p y)‖ ≤
      α * dist x y + B * (∑ i ∈ F, |θ i x - θ i y|) := by
  have hfirst : ‖∑ i ∈ F, θ i x • ((π i x - π i y) - (p x - p y))‖ ≤
      α * dist x y := by
    calc
      _ ≤ ∑ i ∈ F, ‖θ i x • ((π i x - π i y) - (p x - p y))‖ := norm_sum_le _ _
      _ ≤ ∑ i ∈ F, θ i x * (α * dist x y) := by
        apply Finset.sum_le_sum
        intro i hi
        by_cases hz : θ i x = 0
        · simp only [hz, zero_smul, norm_zero, zero_mul, le_refl]
        · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hθ i hi)]
          exact mul_le_mul_of_nonneg_left (hlinear i hi hz) (hθ i hi)
      _ = _ := by rw [← Finset.sum_mul, hx, one_mul]
  have hsecond : ‖∑ i ∈ F, (θ i x - θ i y) • (π i y - p y)‖ ≤
      B * (∑ i ∈ F, |θ i x - θ i y|) := by
    calc
      _ ≤ ∑ i ∈ F, ‖(θ i x - θ i y) • (π i y - p y)‖ := norm_sum_le _ _
      _ ≤ ∑ i ∈ F, |θ i x - θ i y| * B := by
        apply Finset.sum_le_sum
        intro i hi
        by_cases hz : θ i x = θ i y
        · simp only [hz, sub_self, zero_smul, norm_zero, abs_zero, zero_mul, le_refl]
        · rw [norm_smul, Real.norm_eq_abs]
          exact mul_le_mul_of_nonneg_left (hoffset i hi hz) (abs_nonneg _)
      _ = _ := by rw [← Finset.sum_mul, mul_comm]
  rw [finiteProjectionAverage_increment_identity F θ π p x y hx hy]
  exact (norm_add_le _ _).trans (add_le_add hfirst hsecond)

theorem finiteProjectionAverage_increment_bound (F : Finset ι)
    (θ : ι → Ambient d → ℝ) (π : ι → Ambient d → Ambient d)
    (p : Ambient d → Ambient d) (x y : Ambient d) (α B L : ℝ)
    (hB : 0 ≤ B) (hθ : ∀ i ∈ F, 0 ≤ θ i x)
    (hx : (∑ i ∈ F, θ i x) = 1) (hy : (∑ i ∈ F, θ i y) = 1)
    (hlinear : ∀ i ∈ F, θ i x ≠ 0 →
      ‖(π i x - π i y) - (p x - p y)‖ ≤ α * dist x y)
    (hoffset : ∀ i ∈ F, θ i x ≠ θ i y → dist (π i y) (p y) ≤ B)
    (hvariation : (∑ i ∈ F, |θ i x - θ i y|) ≤ L * dist x y) :
    ‖(finiteProjectionAverage F θ π x - finiteProjectionAverage F θ π y) - (p x - p y)‖ ≤
      (α + B * L) * dist x y := by
  have h := finiteProjectionAverage_increment_estimate F θ π p x y α B
    hθ hx hy hlinear hoffset
  calc
    _ ≤ α * dist x y + B * (∑ i ∈ F, |θ i x - θ i y|) := h
    _ ≤ α * dist x y + B * (L * dist x y) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hvariation hB)
    _ = _ := by ring

end

end RieszRectifiability

end OAI
