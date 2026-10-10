import OAI.NumberTheory.Ostmann.Tree.ReciprocalCoordinates
import OAI.NumberTheory.Ostmann.Characters.ReciprocalTwist
import OAI.NumberTheory.Ostmann.Tree.BottomPairCoordinates

namespace OAI

/-!
# The reciprocal pair identity

The character and additive phases in the reciprocal twist combine into
the diagonal bottom-pair weight. This is the pointwise calculation behind
the affine-operator parametrization of the uniform Mellin estimate.
-/

namespace Ostmann

open scoped BigOperators ComplexConjugate

noncomputable def fieldBottomPair {p : ℕ} [Fact p.Prime]
    (g : ZMod p → ℂ) (d t : ZMod p) : ℂ :=
  g (d * t / (t - 1)) * conj (g (d / (t - 1)))

theorem reciprocalTwist_pair_identity {p : ℕ} [Fact p.Prime]
    (g : ZMod p → ℂ) (η : MulChar (ZMod p) ℂ) (a : ZMod p)
    (lam : (ZMod p)ˣ) (d x z : ZMod p) (hz : z ≠ 0)
    (hx : x = (lam : ZMod p) * d * z) (hdiff : x - z = d) :
    conj (η lam) * (conj (reciprocalTwist g η a z⁻¹) * reciprocalTwist g η a x⁻¹) =
      g x * conj (g z) * η d * ZMod.stdAddChar (-(a * d)) := by
  have hchar : η x = η lam * η d * η z := by rw [hx, map_mul, map_mul]
  have hphase : ZMod.stdAddChar (-(a * x)) =
      ZMod.stdAddChar (-(a * d)) * ZMod.stdAddChar (-(a * z)) := by
    rw [show -(a * x) = -(a * d) + -(a * z) by rw [← hdiff]; ring,
      AddChar.map_add_eq_mul]
  have hnlam : ‖η lam‖ = 1 := norm_mulChar_unit η lam
  have hnz : ‖η z‖ = 1 := norm_mulChar_unit η (Units.mk0 z hz)
  have hne : ‖ZMod.stdAddChar (-(a * z))‖ = 1 := by simp [ZMod.stdAddChar_apply]
  calc
    _ = (g x * conj (g z) * η d * ZMod.stdAddChar (-(a * d))) *
        (conj (η lam) * η lam) * (conj (η z) * η z) *
        (conj (ZMod.stdAddChar (-(a * z))) * ZMod.stdAddChar (-(a * z))) := by
      simp only [reciprocalTwist, inv_inv, hchar, hphase, map_mul]
      ring
    _ = _ := by rw [Complex.conj_mul', Complex.conj_mul', Complex.conj_mul', hnlam, hnz, hne]; norm_num

theorem reciprocal_diagonal_pair {p : ℕ} [Fact p.Prime]
    (g : ZMod p → ℂ) (hg : g 0 = 0) (η : MulChar (ZMod p) ℂ)
    (a : ZMod p) (lam : (ZMod p)ˣ) (d : ZMod p) :
    fieldBottomPair g d ((lam : ZMod p) * d) * η d * ZMod.stdAddChar (-(a * d)) =
      conj (η lam) *
        (conj (reciprocalTwist g η a ((lam : ZMod p) - d⁻¹)) *
          reciprocalTwist g η a
            (((lam : ZMod p) - d⁻¹) - ((lam : ZMod p) - d⁻¹) ^ 2 / (lam : ZMod p))) := by
  by_cases hd : d = 0
  · subst d
    have hgen : (lam : ZMod p) - (lam : ZMod p) ^ 2 / (lam : ZMod p) = 0 := by
      field_simp
      ring
    simp only [fieldBottomPair, mul_zero, zero_sub, zero_div, hg, zero_mul, inv_zero,
      sub_zero, hgen, reciprocalTwist_zero g hg, mul_zero]
  · by_cases hsing : (lam : ZMod p) * d = 1
    · have hr : (lam : ZMod p) - d⁻¹ = 0 := (reciprocal_coordinate_eq_zero _ _ hd).mpr hsing
      simp only [fieldBottomPair, hsing, sub_self, div_zero, hg, zero_mul, hr,
        reciprocalTwist_zero g hg, map_zero, mul_zero]
    · let x := d * ((lam : ZMod p) * d) / ((lam : ZMod p) * d - 1)
      let z := d / ((lam : ZMod p) * d - 1)
      have hz : z ≠ 0 := div_ne_zero hd (sub_ne_zero.mpr hsing)
      have hx : x = (lam : ZMod p) * d * z := by dsimp [x, z]; ring
      have hdiff : x - z = d := pair_coordinate_difference d ((lam : ZMod p) * d) hsing
      have hr : z⁻¹ = (lam : ZMod p) - d⁻¹ := reciprocal_right_argument _ _ hd
      have hq : x⁻¹ = ((lam : ZMod p) - d⁻¹) -
          ((lam : ZMod p) - d⁻¹) ^ 2 / (lam : ZMod p) :=
        reciprocal_left_argument _ _ (Units.ne_zero lam) hd
      simpa only [fieldBottomPair, x, z, hr, hq] using
        (reciprocalTwist_pair_identity g η a lam d x z hz hx hdiff).symm

end Ostmann

end OAI
