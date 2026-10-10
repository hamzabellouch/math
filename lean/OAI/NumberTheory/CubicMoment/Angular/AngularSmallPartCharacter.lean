import OAI.NumberTheory.CubicMoment.Estimates.SmallPartCharacter
import OAI.NumberTheory.CubicMoment.Angular.AngularLogSmallTwist

namespace OAI

/-! The finite small-part twist preserves its fixed infinity type. -/
noncomputable section
namespace CubicFirstMoment

lemma productResidueChar_angular_units {q r : Eisenstein}
    (χ : MulChar (Residues q) ℂ) (η : MulChar (Residues r) ℂ)
    (hχ : ∀ u : Eisensteinˣ, χ (Ideal.Quotient.mk (modulus q) u) = 1)
    {ℓ : ℤ} (hη : AngularUnitCompatible r η ℓ) :
    AngularUnitCompatible (q*r) (productResidueChar χ η) ℓ := by
  intro u
  rw [productResidueChar_mk,hχ u,one_mul]
  exact hη u

lemma smallPartResidueTwist_angular_units (v : Eisenstein) {a b q : Eisenstein}
    (ha : primary a) (hb : primary b) (η : MulChar (Residues q) ℂ)
    {ℓ : ℤ} (hη : AngularUnitCompatible q η ℓ) :
    AngularUnitCompatible ((3*(primarySmallPart v a*primarySmallPart v b))*q)
      (smallPartResidueTwist v a b q ha hb η) ℓ :=
  productResidueChar_angular_units _ _
    (primaryMixedResidueChar_trivialInfinity (primarySmallPart_primary v ha)
      (primarySmallPart_primary v hb)) hη

lemma primaryAngularSmallTwistSmoothSum_small_parts (ℓ : ℤ) (v : Eisenstein)
    {a b q : Eisenstein} (ha : primary a) (hb : primary b)
    (η : MulChar (Residues q) ℂ) (W : ℝ → ℂ) (Z t : ℝ) :
    primaryAngularSmallTwistSmoothSum ℓ a b q η W Z t =
      primaryAngularSmallTwistSmoothSum ℓ (primaryOutsidePart v a) (primaryOutsidePart v b)
        ((3*(primarySmallPart v a*primarySmallPart v b))*q)
        (smallPartResidueTwist v a b q ha hb η) W Z t := by
  unfold primaryAngularSmallTwistSmoothSum
  apply tsum_congr
  intro x
  by_cases hx : primary x
  · simp only [ite_eq_left hx,smallPartResidueTwist_primary v ha hb hx η]
  · simp only [ite_eq_right hx]

end CubicFirstMoment

end

end OAI
