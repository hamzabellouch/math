import OAI.NumberTheory.TwoPoint.Bounds.RoughFourier
import OAI.NumberTheory.TwoPoint.Bounds.ShortSumSampling

namespace OAI

/-! Exact Fourier convolution for the translated rough-shift average. -/

namespace TwoPointCorrelations

open Finset MeasureTheory
open scoped Classical

noncomputable def forwardWindowPolynomial (f : ℕ → ℂ) (D v : ℕ) :
    AddCircle (1 : ℝ) → ℂ :=
  fourierPolynomial (Icc 1 D) (fun m => (m : ℤ)) (fun m => f (v + m))

noncomputable def backwardWindowPolynomial (g : ℕ → ℂ) (Q v : ℕ) :
    AddCircle (1 : ℝ) → ℂ :=
  fourierPolynomial (Icc 1 Q) (fun a => -(a : ℤ)) (fun a => g (v + a))

/-- Orthogonality imposes precisely `a=m+hz`; the long window contains
every selected frequency, so there is no further truncation error. -/
theorem rough_shift_convolution (f g : ℕ → ℂ) (Z : Finset ℕ) (D h v : ℕ)
    (hZ : ∀ z ∈ Z, z ≤ 2 * D) :
    (∫ θ, roughFourierPolynomial Z h θ * forwardWindowPolynomial f D v θ *
      backwardWindowPolynomial g ((2 * h + 1) * D) v θ ∂AddCircle.haarAddCircle) =
      ∑ z ∈ Z, (z : ℂ)⁻¹ * ∑ m ∈ Icc 1 D, f (v + m) * g (v + m + h * z) := by
  unfold roughFourierPolynomial forwardWindowPolynomial backwardWindowPolynomial
  simp_rw [fourierPolynomial_mul]
  rw [integral_fourierPolynomial]
  simp only [sum_product]
  apply sum_congr rfl
  intro z hz
  rw [mul_sum]
  apply sum_congr rfl
  intro m hm
  have hm1 : 1 ≤ m := (mem_Icc.mp hm).1
  have hmD : m ≤ D := (mem_Icc.mp hm).2
  have ha : m + h * z ∈ Icc 1 ((2 * h + 1) * D) := by
    simp only [mem_Icc]
    constructor
    · omega
    · nlinarith [Nat.mul_le_mul_left h (hZ z hz)]
  rw [sum_eq_single (m + h * z)]
  · have he : (h : ℤ) * z + m + -(↑(m + h * z) : ℤ) = 0 := by
      push_cast
      ring
    rw [ite_eq_left he]
    rw [show v + (m + h * z) = v + m + h * z by omega]
    ring
  · intro a _ hne
    have he : ¬((h : ℤ) * z + m + -(a : ℤ) = 0) := by
      intro hh
      apply hne
      exact_mod_cast (show (a : ℤ) = m + h * z by linarith)
    exact ite_eq_right he
  · exact fun hnot => False.elim (hnot ha)

/-- Summing the convolution identity gives the exact translated average
used before the endpoint comparison. -/
theorem summed_rough_shift_convolution (f g : ℕ → ℂ) (Z : Finset ℕ)
    (D h Y : ℕ) (hZ : ∀ z ∈ Z, z ≤ 2 * D) :
    (∑ v ∈ range Y, ∫ θ,
      roughFourierPolynomial Z h θ * forwardWindowPolynomial f D (v + 1) θ *
      backwardWindowPolynomial g ((2 * h + 1) * D) (v + 1) θ
        ∂AddCircle.haarAddCircle) =
      ∑ m ∈ Icc 1 D, ∑ v ∈ range Y, ∑ z ∈ Z,
        (z : ℂ)⁻¹ * (f (v + 1 + m) * g (v + 1 + m + h * z)) := by
  simp_rw [rough_shift_convolution f g Z D h _ hZ, mul_sum]
  calc
    _ = ∑ v ∈ range Y, ∑ m ∈ Icc 1 D, ∑ z ∈ Z,
        (z : ℂ)⁻¹ * (f (v + 1 + m) * g (v + 1 + m + h * z)) := by
      apply sum_congr rfl
      intro v _
      rw [sum_comm]
    _ = _ := sum_comm

end TwoPointCorrelations

end OAI
