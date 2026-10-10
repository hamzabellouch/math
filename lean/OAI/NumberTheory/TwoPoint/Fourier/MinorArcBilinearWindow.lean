import OAI.NumberTheory.TwoPoint.Fourier.MinorArcHolder

namespace OAI

/-! A literal finite bilinear short-window bound, before substituting the
Ramaré cofactor coefficient or the sieve kernel estimate. -/

namespace TwoPointCorrelations

open Finset

noncomputable def minorArcBilinearWindow (P : Finset ℕ) (M H d : ℕ)
    (a c : ℕ → ℂ) (α : ℝ) (k : ℕ) : ℂ :=
  ∑ m ∈ range M, a m * ∑ p ∈ P,
    minorArcWindowTerm M (d * p) k H (c p) (α * p) m

lemma minor_arc_window_scalar (M A k H : ℕ) (z w : ℂ) (β : ℝ) (m : ℕ) :
    w * minorArcWindowTerm M A k H z β m =
      minorArcWindowTerm M A k H (z * w) β m := by
  unfold minorArcWindowTerm
  split_ifs <;> ring

lemma minor_arc_bilinear_dual (P : Finset ℕ) (X M H d : ℕ)
    (a c θ : ℕ → ℂ) (α : ℝ) :
    (∑ k ∈ range X, θ k * minorArcBilinearWindow P M H d a c α k) =
      ∑ m ∈ range M, a m * ∑ p ∈ P, ∑ k ∈ range X,
        minorArcWindowTerm M (d * p) k H (c p * θ k) (α * p) m := by
  unfold minorArcBilinearWindow
  simp only [mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro m _
  rw [sum_comm]
  apply sum_congr rfl
  intro p _
  apply sum_congr rfl
  intro k _
  rw [← minor_arc_window_scalar]
  ring

/-- The full finite minor-arc inequality obtained by polarization,
Hölder, geometric summation and the four-origin support estimate. -/
theorem minor_arc_bilinear_fourth (P : Finset ℕ) (X M H d : ℕ) (hd : 0 < d)
    (hP : ∀ p ∈ P, 0 < p ∧ ∀ q ∈ P, q ≤ 2 * p)
    (a c : ℕ → ℂ) (ha : ∀ m ∈ range M, ‖a m‖ ≤ 1) (hc : ∀ p ∈ P, ‖c p‖ ≤ 1)
    (α V : ℝ) (hV : ∀ p ∈ P, (H : ℝ) / (d * p : ℕ) + 1 ≤ V) :
    (∑ k ∈ range X, ‖minorArcBilinearWindow P M H d a c α k‖) ^ 4 ≤
      (M : ℝ) ^ 3 * (X * (3 * H + 1) ^ 3 : ℕ) *
        ∑ p₁ ∈ P, ∑ p₂ ∈ P, ∑ p₃ ∈ P, ∑ p₄ ∈ P,
          minorArcGeometricBound V (α * ((p₁ : ℝ) + p₂ - p₃ - p₄)) := by
  obtain ⟨θ, hθ, hdual⟩ := minor_arc_norm_sum_duality (range X)
    (minorArcBilinearWindow P M H d a c α)
  rw [hdual, minor_arc_bilinear_dual]
  have hholder := minor_arc_weighted_fourth (range M) a
    (fun m => ∑ p ∈ P, ∑ k ∈ range X,
      minorArcWindowTerm M (d * p) k H (c p * θ k) (α * p) m) ha
  simp only [card_range] at hholder
  apply hholder.trans
  have hfour := minor_arc_window_fourth P X M H d hd hP c θ hc
    (fun k => (hθ k).le) α V hV
  have hh := mul_le_mul_of_nonneg_left hfour (by positivity : 0 ≤ (M : ℝ) ^ 3)
  simpa only [mul_assoc] using hh

end TwoPointCorrelations

end OAI
