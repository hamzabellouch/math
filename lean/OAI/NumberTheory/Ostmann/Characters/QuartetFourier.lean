import OAI.NumberTheory.Ostmann.Characters.TwistCauchy
import OAI.NumberTheory.Ostmann.Characters.CharacterEnergy
import OAI.NumberTheory.Ostmann.Preliminaries.OrientedAutocorrelation

namespace OAI

/-!
# Fourier estimates for quartet terms

The friendly term follows from the uniform Mellin estimate and Parseval
energy. A nonprincipal Gauss transform also has the uniform maximum used
when exactly one of the two quartet twists is principal.
-/

namespace Ostmann

open scoped BigOperators

noncomputable local instance quartetFourierFintype {p : ℕ} [Fact p.Prime] :
    Fintype (MulChar (ZMod p) ℂ) := Fintype.ofFinite _

theorem weightedCharacterSum_norm_le {p : ℕ} [Fact p.Prime]
    (w : ZMod p → ℝ) (hw : ∀ b, 0 ≤ w b)
    (χ : MulChar (ZMod p) ℂ) (a : ZMod p) :
    ‖weightedCharacterSum w χ a‖ ≤ ∑ b : ZMod p, w b := by
  unfold weightedCharacterSum
  calc
    _ ≤ ∑ b : ZMod p, ‖(w b : ℂ) * χ (a - b)‖ := norm_sum_le _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro b _
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hw b)]
      exact mul_le_of_le_one_right (hw b) (norm_mulChar_le_one χ (a - b))

theorem nonprincipal_fourier_norm_sq_le {p : ℕ} [Fact p.Prime]
    (f : ZMod p → ℂ) (w : ZMod p → ℝ)
    (hf : ∀ b, additiveFourier f b = (w b : ℂ)) (hw : ∀ b, 0 ≤ w b)
    (J : ℝ) (hJ : (∑ b : ZMod p, w b) ≤ J)
    (χ : MulChar (ZMod p) ℂ) (hχ : χ ≠ 1) (a : ZMod p) :
    ‖additiveFourier (fun x => f x * χ x) a‖ ^ 2 ≤ (p : ℝ)⁻¹ * J ^ 2 := by
  have hm := (weightedCharacterSum_norm_le w hw χ⁻¹ a).trans hJ
  have hfour : ‖additiveFourier (fun x => f x * χ x) a‖ ^ 4 ≤
      ((p : ℝ)⁻¹) ^ 2 * J ^ 4 := by
    rw [additiveFourier_character_norm_four f w hf χ hχ a]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hm 4) (sq_nonneg _)
  have hp : 0 ≤ (p : ℝ)⁻¹ * J ^ 2 := mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg p)) (sq_nonneg J)
  apply (sq_le_sq₀ (sq_nonneg _) hp).mp
  convert hfour using 1 <;> ring

/-- The friendly convolution sum uses one uniform Mellin bound and one total energy. -/
theorem friendly_fourier_sum_le {p : ℕ} [Fact p.Prime]
    (P Q : MulChar (ZMod p) ℂ → ZMod p → ℂ)
    (δ C : ℝ) (hδ : 0 ≤ δ)
    (hP : ∀ (η : MulChar (ZMod p) ℂ) (a : ZMod p),
      (∑ χ : MulChar (ZMod p) ℂ,
        ‖additiveFourier (fun x => P χ x * χ x * η x) a‖ ^ 2) ≤ δ)
    (hQ : (∑ ψ : MulChar (ZMod p) ℂ, ∑ a : ZMod p, ‖additiveFourier (Q ψ) a‖ ^ 2) ≤ C)
    (η : MulChar (ZMod p) ℂ → MulChar (ZMod p) ℂ) :
    (∑ a : ZMod p, ∑ ψ : MulChar (ZMod p) ℂ, ∑ χ : MulChar (ZMod p) ℂ,
      ‖additiveFourier (fun x => P χ x * χ x * η ψ x) a‖ ^ 2 *
        ‖additiveFourier (Q ψ) (-a)‖ ^ 2) ≤ δ * C := by
  have hneg (ψ : MulChar (ZMod p) ℂ) :
      (∑ a : ZMod p, ‖additiveFourier (Q ψ) (-a)‖ ^ 2) =
        ∑ a : ZMod p, ‖additiveFourier (Q ψ) a‖ ^ 2 :=
    (Equiv.neg (ZMod p)).bijective.sum_comp (fun a => ‖additiveFourier (Q ψ) a‖ ^ 2)
  calc
    _ ≤ ∑ a : ZMod p, ∑ ψ : MulChar (ZMod p) ℂ,
        δ * ‖additiveFourier (Q ψ) (-a)‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro a _
      apply Finset.sum_le_sum
      intro ψ _
      rw [← Finset.sum_mul]
      exact mul_le_mul_of_nonneg_right (hP (η ψ) a) (sq_nonneg _)
    _ = δ * (∑ ψ : MulChar (ZMod p) ℂ, ∑ a : ZMod p,
        ‖additiveFourier (Q ψ) a‖ ^ 2) := by
      simp_rw [← Finset.mul_sum]
      rw [Finset.sum_comm]
      simp only [hneg]
    _ ≤ δ * C := mul_le_mul_of_nonneg_left hQ hδ

end Ostmann

end OAI
