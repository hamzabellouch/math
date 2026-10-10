import OAI.NumberTheory.TwoPoint.Fourier.MinorArcOriginSum

namespace OAI

/-! The discrete weighted-window fourth moment in MRT's minor-arc argument. -/

namespace TwoPointCorrelations

open Finset

/-- A prime block contributes only `X (3H+1)^3` possible origin quadruples.
The remaining cancellation is exactly the four-prime geometric kernel. -/
theorem minor_arc_window_fourth (P : Finset ℕ) (X M H d : ℕ) (hd : 0 < d)
    (hP : ∀ p ∈ P, 0 < p ∧ ∀ q ∈ P, q ≤ 2 * p)
    (c θ : ℕ → ℂ) (hc : ∀ p ∈ P, ‖c p‖ ≤ 1) (hθ : ∀ k, ‖θ k‖ ≤ 1)
    (α V : ℝ) (hV : ∀ p ∈ P, (H : ℝ) / (d * p : ℕ) + 1 ≤ V) :
    (∑ m ∈ range M, ‖∑ p ∈ P, ∑ k ∈ range X,
      minorArcWindowTerm M (d * p) k H (c p * θ k) (α * p) m‖ ^ 4) ≤
      (X * (3 * H + 1) ^ 3 : ℕ) *
        ∑ p₁ ∈ P, ∑ p₂ ∈ P, ∑ p₃ ∈ P, ∑ p₄ ∈ P,
          minorArcGeometricBound V (α * ((p₁ : ℝ) + p₂ - p₃ - p₄)) := by
  classical
  let f := fun v : ℕ × ℕ =>
    minorArcWindowTerm M (d * v.1) v.2 H (c v.1 * θ v.2) (α * v.1)
  have he := minor_arc_fourth_moment_bound (P ×ˢ range X) (range M) f
  dsimp [f] at he
  simp only [sum_product] at he
  simp_rw [sum_comm (s := range X) (t := P)] at he
  apply he.trans
  simp only [mul_sum]
  apply sum_le_sum
  intro p₁ hp₁
  apply sum_le_sum
  intro p₂ hp₂
  apply sum_le_sum
  intro p₃ hp₃
  apply sum_le_sum
  intro p₄ hp₄
  have hcoef (p : ℕ) (hp : p ∈ P) (k : ℕ) : ‖c p * θ k‖ ≤ 1 := by
    rw [norm_mul]
    calc
      _ ≤ 1 * 1 := mul_le_mul (hc p hp) (hθ k) (norm_nonneg _) (by norm_num)
      _ = 1 := by norm_num
  have h := minor_arc_origin_kernel_sum X M (d * p₁) (d * p₂) (d * p₃) (d * p₄) H
    (Nat.mul_pos hd (hP p₁ hp₁).1)
    (Nat.mul_pos hd (hP p₂ hp₂).1)
    (Nat.mul_pos hd (hP p₃ hp₃).1)
    (Nat.mul_pos hd (hP p₄ hp₄).1)
    (by nlinarith [(hP p₁ hp₁).2 p₂ hp₂])
    (by nlinarith [(hP p₁ hp₁).2 p₃ hp₃])
    (by nlinarith [(hP p₁ hp₁).2 p₄ hp₄])
    (fun k => c p₁ * θ k) (fun k => c p₂ * θ k)
    (fun k => c p₃ * θ k) (fun k => c p₄ * θ k)
    (hcoef p₁ hp₁) (hcoef p₂ hp₂) (hcoef p₃ hp₃) (hcoef p₄ hp₄)
    (α * p₁) (α * p₂) (α * p₃) (α * p₄) V (hV p₁ hp₁)
  have hphase : α * (p₁ : ℝ) + α * p₂ - α * p₃ - α * p₄ =
      α * ((p₁ : ℝ) + p₂ - p₃ - p₄) := by ring
  rw [hphase] at h
  exact h

end TwoPointCorrelations

end OAI
