import OAI.Analysis.KadisonKastler.PublishedSimpleDerivation
import OAI.Analysis.Pureness.Completion.ClosedStarIdealQuotientCStar
import OAI.Analysis.TracialSplitting.FullProjections

namespace OAI

/-! # Separating a simple unital algebra from ideals in an extension

These are the norm-separation steps used in the maximal-ideal construction
in Sakai, *Derivations of simple C*-algebras II*, p.260. A proper closed
star ideal in a unital extension has an isometric quotient map on the
simple unital subalgebra. In particular it cannot approach a nonzero
element of that subalgebra more closely than its norm.
-/

namespace KadisonKastler

noncomputable section

open CuntzPureness

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]

theorem closedStarIdeal_quotient_nontrivial (J : ClosedStarIdeal B)
    (hJ : J.ideal ≠ ⊤) : Nontrivial J.Quotient := by
  apply (RingCon.nontrivial_quotient (c := J.ideal.ringCon)).mpr
  intro h
  apply hJ
  apply TwoSidedIdeal.ringCon_injective
  simpa only [TwoSidedIdeal.top_ringCon] using h

theorem simple_quotient_composition_injective (hA : CStarSimple A)
    (φ : A →⋆ₐ[ℂ] B) (J : ClosedStarIdeal B) (hJ : J.ideal ≠ ⊤) :
    Function.Injective (J.quotientStarHom.comp φ) := by
  let : PartialOrder B := CStarAlgebra.spectralOrder B
  let : StarOrderedRing B := CStarAlgebra.spectralOrderedRing B
  let : Nontrivial J.Quotient := closedStarIdeal_quotient_nontrivial J hJ
  exact CurrentMain.simple_starAlgHom_injective hA (J.quotientStarHom.comp φ)

theorem simple_quotient_composition_norm (hA : CStarSimple A)
    (φ : A →⋆ₐ[ℂ] B) (J : ClosedStarIdeal B) (hJ : J.ideal ≠ ⊤) (a : A) :
    ‖J.quotientStarHom (φ a)‖ = ‖a‖ := by
  let : PartialOrder B := CStarAlgebra.spectralOrder B
  let : StarOrderedRing B := CStarAlgebra.spectralOrderedRing B
  exact NonUnitalStarAlgHom.norm_map (J.quotientStarHom.comp φ)
    (simple_quotient_composition_injective hA φ J hJ) a

theorem simple_norm_le_sub_ideal (hA : CStarSimple A)
    (φ : A →⋆ₐ[ℂ] B) (J : ClosedStarIdeal B) (hJ : J.ideal ≠ ⊤)
    (a : A) {b : B} (hb : b ∈ J.ideal) : ‖a‖ ≤ ‖φ a - b‖ := by
  have hb0 : J.quotientStarHom b = 0 := Quotient.sound hb
  calc
    ‖a‖ = ‖J.quotientStarHom (φ a)‖ :=
      (simple_quotient_composition_norm hA φ J hJ a).symm
    _ = ‖J.quotientStarHom (φ a - b)‖ := by rw [map_sub, hb0, sub_zero]
    _ ≤ ‖φ a - b‖ := J.quotientMap_norm_le _

end

end KadisonKastler

end OAI
