import OAI.NumberTheory.Ostmann.Characters.UniformMellin

namespace OAI

/-!
# Symmetries of the mixed Fourier bound

Conjugation and multiplication of the field argument by a unit preserve
both the energy hypothesis and the mixed character/Fourier bound. These
are the orientation changes used by the bottom pairs.
-/

namespace Ostmann

open scoped BigOperators ComplexConjugate

def MixedFourierBound {p : ℕ} [Fact p.Prime] (g : ZMod p → ℂ) (ε : ℝ) : Prop :=
  ∀ (χ : MulChar (ZMod p) ℂ) (a : ZMod p),
    ‖additiveFourier (fun x => g x * χ x) a‖ ≤ ε

theorem additiveFourier_conj {p : ℕ} [NeZero p]
    (f : ZMod p → ℂ) (a : ZMod p) :
    additiveFourier (fun x => conj (f x)) a = conj (additiveFourier f (-a)) := by
  simp only [additiveFourier_apply, map_mul, map_inv₀, map_natCast, map_sum,
    stdAddChar_conj, mul_neg, neg_neg]

theorem MixedFourierBound.conj {p : ℕ} [Fact p.Prime]
    {g : ZMod p → ℂ} {ε : ℝ} (h : MixedFourierBound g ε) :
    MixedFourierBound (fun x => conj (g x)) ε := by
  intro χ a
  have hfun : (fun x => conj (g x) * χ x) =
      (fun x => conj (g x * χ⁻¹ x)) := by
    funext x
    have hc := MulChar.star_apply' χ⁻¹ x
    change conj (χ⁻¹ x) = _ at hc
    simp only [inv_inv] at hc
    rw [map_mul, hc]
  rw [hfun, additiveFourier_conj, Complex.norm_conj]
  exact h χ⁻¹ (-a)

theorem MixedFourierBound.unit_mul {p : ℕ} [Fact p.Prime]
    {g : ZMod p → ℂ} {ε : ℝ} (h : MixedFourierBound g ε) (u : (ZMod p)ˣ) :
    MixedFourierBound (fun x => g ((u : ZMod p) * x)) ε := by
  intro χ a
  have hunit : χ ((u⁻¹ : (ZMod p)ˣ) : ZMod p) * χ (u : ZMod p) = 1 := by
    rw [← map_mul, ← Units.val_mul]
    simp only [inv_mul_cancel, Units.val_one, map_one]
  have hfun : (fun x => g ((u : ZMod p) * x) * χ x) =
      (fun x => χ ((u⁻¹ : (ZMod p)ˣ) : ZMod p) *
        ((g ((u : ZMod p) * x)) * χ ((u : ZMod p) * x))) := by
    funext x
    rw [map_mul]
    calc
      _ = (χ ((u⁻¹ : (ZMod p)ˣ) : ZMod p) * χ (u : ZMod p)) *
          (g ((u : ZMod p) * x) * χ x) := by rw [hunit, one_mul]
      _ = _ := by ring
  rw [hfun, additiveFourier_const_mul,
    additiveFourier_unit_mul (fun x => g x * χ x), norm_mul,
    norm_mulChar_unit χ u⁻¹, one_mul]
  exact h χ _

theorem unit_mul_energy {p : ℕ} [Fact p.Prime]
    (g : ZMod p → ℂ) (u : (ZMod p)ˣ) :
    (∑ x : ZMod p, ‖g ((u : ZMod p) * x)‖ ^ 2) = ∑ x : ZMod p, ‖g x‖ ^ 2 :=
  (Equiv.mulLeft₀ (u : ZMod p) (Units.ne_zero u)).bijective.sum_comp (fun x => ‖g x‖ ^ 2)

end Ostmann

end OAI
