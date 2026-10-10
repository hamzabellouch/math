import Mathlib

namespace OAI

noncomputable section
namespace Ostmann.QuadraticCenter
open scoped BigOperators ComplexConjugate

theorem weighted_complex_energy_expansion {ι : Type*} (D : Finset ι) (T : Finset ℕ)
    (a : ι → ℂ) (G : ι → ℕ → ℂ) :
    ((∑ s ∈ T, (s : ℝ)⁻¹ * ‖∑ d ∈ D, a d * G d s‖ ^ 2 : ℝ) : ℂ) =
      ∑ d ∈ D, ∑ e ∈ D, a d * conj (a e) *
        (∑ s ∈ T, G d s * conj (G e s) / (s : ℂ)) := by
  conv_rhs => rw [Finset.sum_comm]
  simp only [Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_inv,
    Complex.ofReal_natCast, Complex.ofReal_pow, ← Complex.mul_conj', map_sum, map_mul,
    Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d hd
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e he
  apply Finset.sum_congr rfl
  intro s hs
  ring

theorem weighted_complex_energy_le_correlations {ι : Type*} (D : Finset ι) (T : Finset ℕ)
    (a : ι → ℂ) (G : ι → ℕ → ℂ) :
    (∑ s ∈ T, (s : ℝ)⁻¹ * ‖∑ d ∈ D, a d * G d s‖ ^ 2) ≤
      ∑ d ∈ D, ∑ e ∈ D, ‖a d‖ * ‖a e‖ *
        ‖∑ s ∈ T, G d s * conj (G e s) / (s : ℂ)‖ := by
  have hn : 0 ≤ ∑ s ∈ T, (s : ℝ)⁻¹ * ‖∑ d ∈ D, a d * G d s‖ ^ 2 := by
    apply Finset.sum_nonneg
    intro s hs
    positivity
  calc
    _ = ‖((∑ s ∈ T, (s : ℝ)⁻¹ * ‖∑ d ∈ D, a d * G d s‖ ^ 2 : ℝ) : ℂ)‖ := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hn]
    _ = _ := congrArg norm (weighted_complex_energy_expansion D T a G)
    _ ≤ ∑ d ∈ D, ∑ e ∈ D,
        ‖a d * conj (a e) * (∑ s ∈ T, G d s * conj (G e s) / (s : ℂ))‖ :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum (fun d hd => norm_sum_le _ _))
    _ = _ := by simp only [norm_mul, Complex.norm_conj]

end Ostmann.QuadraticCenter

end

end OAI
