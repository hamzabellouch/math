import OAI.NumberTheory.Ostmann.QuadraticCenter.QuadraticEnergyExpansion

namespace OAI

noncomputable section
namespace Ostmann.QuadraticCenter
open scoped BigOperators ComplexConjugate

theorem weighted_complex_energy_expansion_general {ι : Type*}
    (D : Finset ι) (T : Finset ℕ) (weight : ℕ → ℝ) (a : ι → ℂ) (G : ι → ℕ → ℂ) :
    ((∑ s ∈ T, (weight s / s) * ‖∑ d ∈ D, a d * G d s‖ ^ 2 : ℝ) : ℂ) =
      ∑ d ∈ D, ∑ e ∈ D, a d * conj (a e) *
        (∑ s ∈ T, (weight s : ℂ) * (G d s * conj (G e s) / (s : ℂ))) := by
  conv_rhs => rw [Finset.sum_comm]
  simp only [Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_div,
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

theorem weighted_complex_energy_le_correlations_general {ι : Type*}
    (D : Finset ι) (T : Finset ℕ) (weight : ℕ → ℝ) (hw : ∀ s ∈ T, 0 ≤ weight s)
    (a : ι → ℂ) (G : ι → ℕ → ℂ) :
    (∑ s ∈ T, (weight s / s) * ‖∑ d ∈ D, a d * G d s‖ ^ 2) ≤
      ∑ d ∈ D, ∑ e ∈ D, ‖a d‖ * ‖a e‖ *
        ‖∑ s ∈ T, (weight s : ℂ) * (G d s * conj (G e s) / (s : ℂ))‖ := by
  have hn : 0 ≤ ∑ s ∈ T, (weight s / s) * ‖∑ d ∈ D, a d * G d s‖ ^ 2 := by
    exact Finset.sum_nonneg (fun s hs => mul_nonneg (div_nonneg (hw s hs) (Nat.cast_nonneg _))
      (sq_nonneg _))
  calc
    _ = ‖((∑ s ∈ T, (weight s / s) * ‖∑ d ∈ D, a d * G d s‖ ^ 2 : ℝ) : ℂ)‖ := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hn]
    _ = _ := congrArg norm (weighted_complex_energy_expansion_general D T weight a G)
    _ ≤ ∑ d ∈ D, ∑ e ∈ D,
        ‖a d * conj (a e) *
          (∑ s ∈ T, (weight s : ℂ) * (G d s * conj (G e s) / (s : ℂ)))‖ :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum (fun d hd => norm_sum_le _ _))
    _ = _ := by simp only [norm_mul, Complex.norm_conj]

end Ostmann.QuadraticCenter

end

end OAI
