import OAI.NumberTheory.Ostmann.Tree.Fourier

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate
namespace Ostmann.Characters
variable {p : ℕ} [NeZero p]

def translatedMean (S : Finset (ZMod p)) (χ : MulChar (ZMod p) ℂ)
    (t : ZMod p) : ℂ := (S.card : ℂ)⁻¹ * ∑ x ∈ S, χ (x-t)

def translatedBias (S : Finset (ZMod p)) (χ : MulChar (ZMod p) ℂ)
    (t : ZMod p) : ℝ := ‖translatedMean S χ t‖

def maxTranslatedBias (S : Finset (ZMod p)) (χ : MulChar (ZMod p) ℂ) : NNReal :=
  Finset.univ.sup (fun t => ‖translatedMean S χ t‖₊)

theorem translatedBias_le_max (S : Finset (ZMod p))
    (χ : MulChar (ZMod p) ℂ) (t : ZMod p) :
    translatedBias S χ t ≤ (maxTranslatedBias S χ : ℝ) := by
  exact_mod_cast Finset.le_sup (f := fun t => ‖translatedMean S χ t‖₊)
    (Finset.mem_univ t)

omit [NeZero p] in
theorem square_ne_one (χ : MulChar (ZMod p) ℂ) (hχ : 2 < orderOf χ) : χ^2 ≠ 1 := by
  intro h
  exact (not_le_of_gt hχ) (orderOf_le_of_pow_eq_one (by decide) h)

theorem square_sum_zero (χ : MulChar (ZMod p) ℂ) (hχ : 2 < orderOf χ) :
    ∑ x : ZMod p, (χ^2) x = 0 :=
  MulChar.sum_eq_zero_of_ne_one (square_ne_one χ hχ)

theorem sum_affine_eq_zero (χ : MulChar (ZMod p) ℂ) (hχ : χ ≠ 1)
    (u : (ZMod p)ˣ) (a : ZMod p) : ∑ x : ZMod p, χ (↑u*x+a) = 0 := by
  calc
    _ = ∑ x : ZMod p, χ x :=
      Fintype.sum_bijective _ ((Equiv.addRight a).bijective.comp u.mulLeft_bijective) _ _ (fun _ => rfl)
    _ = 0 := MulChar.sum_eq_zero_of_ne_one hχ
end Ostmann.Characters

end

end OAI
