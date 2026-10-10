import OAI.NumberTheory.TwoPoint.Fourier.MinorArcGeometric

namespace OAI

/-! Exact finite fourth-moment expansion, before any sieve or rational
approximation is used. -/

namespace TwoPointCorrelations

open Finset Complex
open scoped ComplexConjugate

lemma minor_arc_fourth_power (z : ℂ) :
    ‖z‖ ^ 4 = (z * z * conj z * conj z).re := by
  rw [show ‖z‖ ^ 4 = (‖z‖ ^ 2) ^ 2 by ring, Complex.sq_norm]
  simp only [Complex.normSq_apply, Complex.mul_re, Complex.mul_im,
    Complex.conj_re, Complex.conj_im]
  ring

lemma minor_arc_fourth_sum {ι : Type*} (P : Finset ι) (f : ι → ℂ) :
    ‖∑ p ∈ P, f p‖ ^ 4 =
      ∑ p₁ ∈ P, ∑ p₂ ∈ P, ∑ p₃ ∈ P, ∑ p₄ ∈ P,
        (f p₁ * f p₂ * conj (f p₃) * conj (f p₄)).re := by
  have h₂ : (∑ p ∈ P, f p) * (∑ p ∈ P, f p) =
      ∑ p₁ ∈ P, ∑ p₂ ∈ P, f p₁ * f p₂ := sum_mul_sum _ _ _ _
  have h₃ : (∑ p ∈ P, f p) * (∑ p ∈ P, f p) * conj (∑ p ∈ P, f p) =
      ∑ p₁ ∈ P, ∑ p₂ ∈ P, ∑ p₃ ∈ P, f p₁ * f p₂ * conj (f p₃) := by
    rw [h₂, map_sum]
    simp only [sum_mul]
    simp only [mul_sum]
  rw [minor_arc_fourth_power, h₃, map_sum]
  simp only [sum_mul]
  simp only [mul_sum, Complex.re_sum]

lemma minor_arc_fourth_moment_expansion {ι : Type*} (P : Finset ι)
    (S : Finset ℕ) (f : ι → ℕ → ℂ) :
    (∑ m ∈ S, ‖∑ p ∈ P, f p m‖ ^ 4) =
      ∑ p₁ ∈ P, ∑ p₂ ∈ P, ∑ p₃ ∈ P, ∑ p₄ ∈ P,
        (∑ m ∈ S, f p₁ m * f p₂ m * conj (f p₃ m) * conj (f p₄ m)).re := by
  simp_rw [minor_arc_fourth_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro p₁ _
  rw [sum_comm]
  apply sum_congr rfl
  intro p₂ _
  rw [sum_comm]
  apply sum_congr rfl
  intro p₃ _
  rw [sum_comm]
  apply sum_congr rfl
  intro p₄ _
  rw [Complex.re_sum]

lemma minor_arc_fourth_moment_bound {ι : Type*} (P : Finset ι)
    (S : Finset ℕ) (f : ι → ℕ → ℂ) :
    (∑ m ∈ S, ‖∑ p ∈ P, f p m‖ ^ 4) ≤
      ∑ p₁ ∈ P, ∑ p₂ ∈ P, ∑ p₃ ∈ P, ∑ p₄ ∈ P,
        ‖∑ m ∈ S, f p₁ m * f p₂ m * conj (f p₃ m) * conj (f p₄ m)‖ := by
  rw [minor_arc_fourth_moment_expansion]
  repeat' apply sum_le_sum fun _ _ => ?_
  exact Complex.re_le_norm _

end TwoPointCorrelations

end OAI
