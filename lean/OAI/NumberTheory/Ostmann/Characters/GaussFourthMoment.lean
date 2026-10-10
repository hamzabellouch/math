import OAI.NumberTheory.Ostmann.ZeroDensity.PrincipalFourthMoment
import OAI.NumberTheory.Ostmann.Characters.GaussFourier

namespace OAI

/-!
# Fourth moments after a nonprincipal multiplicative twist

Gauss convolution transfers the weighted character fourth moment to
Fourier coefficients. The character inversion merely permutes the
nonprincipal characters.
-/

namespace Ostmann

open scoped BigOperators

noncomputable local instance gaussFourthFintype {p : ℕ} [Fact p.Prime] :
    Fintype (MulChar (ZMod p) ℂ) := Fintype.ofFinite _

noncomputable local instance gaussFourthDecidableEq {p : ℕ} : DecidableEq (MulChar (ZMod p) ℂ) := Classical.decEq _

theorem normalizedGauss_norm_sq {p : ℕ} [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (hχ : χ ≠ 1) :
    ‖(p : ℂ)⁻¹ * gaussSum χ (ZMod.stdAddChar (N := p))‖ ^ 2 = (p : ℝ)⁻¹ := by
  have hp : (p : ℝ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  rw [norm_mul, mul_pow, norm_inv, Complex.norm_natCast, gaussSum_norm_sq χ hχ]
  field_simp

theorem additiveFourier_character_norm_four {p : ℕ} [Fact p.Prime]
    (f : ZMod p → ℂ) (w : ZMod p → ℝ)
    (hf : ∀ b, additiveFourier f b = (w b : ℂ))
    (χ : MulChar (ZMod p) ℂ) (hχ : χ ≠ 1) (a : ZMod p) :
    ‖additiveFourier (fun x => f x * χ x) a‖ ^ 4 =
      ((p : ℝ)⁻¹) ^ 2 * ‖weightedCharacterSum w χ⁻¹ a‖ ^ 4 := by
  have hphase (b : ZMod p) : χ⁻¹ (-(a - b)) = χ⁻¹ (-1) * χ⁻¹ (a - b) := by
    rw [← map_mul]
    congr 1
    ring
  have hsum : (∑ b : ZMod p, additiveFourier f b * χ⁻¹ (-(a - b))) =
      χ⁻¹ (-1) * weightedCharacterSum w χ⁻¹ a := by
    simp only [hf, weightedCharacterSum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b _
    rw [hphase]
    ring
  rw [additiveFourier_mul_character f χ hχ, hsum, norm_mul,
    norm_mul (χ⁻¹ (-1)) (weightedCharacterSum w χ⁻¹ a),
    show ‖χ⁻¹ (-1)‖ = 1 from norm_mulChar_unit χ⁻¹ (-1), one_mul, mul_pow]
  have hfour : ‖(p : ℂ)⁻¹ * gaussSum χ (ZMod.stdAddChar (N := p))‖ ^ 4 =
      ((p : ℝ)⁻¹) ^ 2 := by
    calc
      _ = (‖(p : ℂ)⁻¹ * gaussSum χ (ZMod.stdAddChar (N := p))‖ ^ 2) ^ 2 := by ring
      _ = _ := by rw [normalizedGauss_norm_sq χ hχ]
  rw [hfour]

theorem nonprincipal_fourier_fourth_bound {p : ℕ} [Fact p.Prime]
    (f : ZMod p → ℂ) (w : ZMod p → ℝ)
    (hf : ∀ b, additiveFourier f b = (w b : ℂ)) (hw : ∀ b, 0 ≤ w b) :
    (∑ χ ∈ (Finset.univ : Finset (MulChar (ZMod p) ℂ)).erase 1,
      ∑ a : ZMod p, ‖additiveFourier (fun x => f x * χ x) a‖ ^ 4) ≤
      ((p : ℝ)⁻¹) ^ 2 *
        (2 * (p : ℝ) * (Fintype.card (ZMod p)ˣ : ℝ) *
          (∑ b : ZMod p, w b ^ 2) ^ 2 + 3 * (∑ b : ZMod p, w b) ^ 4) := by
  classical
  let S : Finset (MulChar (ZMod p) ℂ) := Finset.univ.erase 1
  have hinv : (∑ χ ∈ S, ∑ a : ZMod p, ‖weightedCharacterSum w χ⁻¹ a‖ ^ 4) =
      ∑ χ ∈ S, ∑ a : ZMod p, ‖weightedCharacterSum w χ a‖ ^ 4 := by
    apply Finset.sum_bij (fun χ _ => χ⁻¹)
    · intro χ hχ
      refine Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩
      intro h
      exact (Finset.mem_erase.mp hχ).1 (inv_injective (by simpa only [inv_one] using h))
    · intro χ _ ψ _ h
      exact inv_injective h
    · intro χ hχ
      refine ⟨χ⁻¹, ?_, inv_inv χ⟩
      refine Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩
      intro h
      exact (Finset.mem_erase.mp hχ).1 (inv_injective (by simpa only [inv_one] using h))
    · intro χ _
      rfl
  calc
    _ = ((p : ℝ)⁻¹) ^ 2 *
        (∑ χ ∈ S, ∑ a : ZMod p, ‖weightedCharacterSum w χ⁻¹ a‖ ^ 4) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro χ hχ
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      exact additiveFourier_character_norm_four f w hf χ (Finset.mem_erase.mp hχ).1 a
    _ = ((p : ℝ)⁻¹) ^ 2 *
        (∑ χ ∈ S, ∑ a : ZMod p, ‖weightedCharacterSum w χ a‖ ^ 4) := by rw [hinv]
    _ ≤ _ := mul_le_mul_of_nonneg_left (nonprincipal_fourth_moment_bound w hw) (sq_nonneg _)

end Ostmann

end OAI
