import OAI.NumberTheory.Ostmann.Tree.ReciprocalPair
import OAI.NumberTheory.Ostmann.Characters.MellinDiagonal
import OAI.NumberTheory.Ostmann.Characters.BottomPairMellin

namespace OAI

/-!
# The diagonal average is an affine correlation

The substitution `r = lam - 1/d` turns the weighted bottom-pair diagonal
into the affine averaging operator applied to the reciprocal twist.
-/

namespace Ostmann

open scoped BigOperators ComplexConjugate

theorem fieldBottomPair_eq_bottomPairValue {p : ℕ} [Fact p.Prime]
    (g : ZMod p → ℂ) (hg : g 0 = 0) (d t : (ZMod p)ˣ) :
    fieldBottomPair g d t = bottomPairValue g d t := by
  classical
  by_cases ht : t = 1
  · subst t
    simp [fieldBottomPair, bottomPairValue, hg]
  · simp only [bottomPairValue, ht, ite_false, fieldBottomPair]

theorem mellinDiagonal_reciprocal {p : ℕ} [Fact p.Prime]
    (g : ZMod p → ℂ) (hg : g 0 = 0) (η : MulChar (ZMod p) ℂ)
    (a : ZMod p) (lam : (ZMod p)ˣ) :
    mellinDiagonal (bottomPairValue g)
      (fun d : (ZMod p)ˣ => η d * ZMod.stdAddChar (-(a * (d : ZMod p)))) lam =
        conj (η lam) *
          affineAverage (fun r : (ZMod p)ˣ => conj (reciprocalTwist g η a r))
            (reciprocalTwist g η a) ((lam : ZMod p)⁻¹) := by
  classical
  let G := reciprocalTwist g η a
  let H : ZMod p → ℂ := fun d =>
    fieldBottomPair g d ((lam : ZMod p) * d) * η d * ZMod.stdAddChar (-(a * d))
  let F : ZMod p → ℂ := fun r => conj (G r) * G (r - r ^ 2 / (lam : ZMod p))
  have hH0 : H 0 = 0 := by simp [H, fieldBottomPair, hg]
  have hF0 : F 0 = 0 := by simp [F, G, reciprocalTwist_zero g hg]
  have hpoint (d : ZMod p) : H d = conj (η lam) * F ((lam : ZMod p) - d⁻¹) :=
    reciprocal_diagonal_pair g hg η a lam d
  have hreindex : (∑ d : ZMod p, F ((lam : ZMod p) - d⁻¹)) = ∑ r : ZMod p, F r :=
    (reciprocalCoordinates (lam : ZMod p)).bijective.sum_comp F
  calc
    _ = (p : ℂ)⁻¹ * ∑ d : (ZMod p)ˣ, H d := by
      unfold mellinDiagonal
      congr 1
      apply Finset.sum_congr rfl
      intro d _
      dsimp only [H]
      rw [← Units.val_mul, fieldBottomPair_eq_bottomPairValue g hg]
      ring
    _ = (p : ℂ)⁻¹ * ∑ d : ZMod p, H d := by
      rw [sum_units_eq_sum_of_zero H hH0]
    _ = conj (η lam) * ((p : ℂ)⁻¹ * ∑ r : ZMod p, F r) := by
      simp_rw [hpoint]
      rw [← Finset.mul_sum, hreindex]
      ring
    _ = _ := by
      rw [← sum_units_eq_sum_of_zero F hF0]
      simp only [F, G, affineAverage, affineGenerator, div_eq_mul_inv]

end Ostmann

end OAI
