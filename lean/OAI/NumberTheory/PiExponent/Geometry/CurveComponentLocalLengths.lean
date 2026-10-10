import OAI.NumberTheory.PiExponent.Geometry.CurveLocalAssociativity
import OAI.NumberTheory.PiExponent.Geometry.CurveLocalMultiplicity

namespace OAI

namespace PiExponent.CurveCycle
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentJets.W28.LocalIntersection
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames

instance finite_componentsThrough {X : Scheme.{0}} [IsLocallyNoetherian X] (x : X) :
    Finite {C : irreducibleComponents X // x ∈ C.val} := by
  let : Finite (minimalPrimes (X.presheaf.stalk x)) :=
    ((⊥ : Ideal (X.presheaf.stalk x)).finite_minimalPrimes_of_isNoetherianRing _).to_subtype
  exact Finite.of_equiv _ (stalkMinimalPrimesEquivComponentsThrough X x)

def componentLocalPrime (X : Scheme.{0}) (x : X)
    (C : {C : irreducibleComponents X // x ∈ C.val}) :
    Ideal (X.presheaf.stalk x) :=
  ((stalkMinimalPrimesEquivComponentsThrough X x).symm C).val

def componentLocalCutLength (X : Scheme.{0}) (x : X)
    (C : {C : irreducibleComponents X // x ∈ C.val})
    (c : X.presheaf.stalk x) : ℕ∞ :=
  Module.length (X.presheaf.stalk x)
    ((X.presheaf.stalk x) ⧸ (componentLocalPrime X x C ⊔ Ideal.span {c}))

theorem minimalPrimeCutSum_eq_component_sum {X : Scheme.{0}} [IsLocallyNoetherian X]
    (x : X) (c : X.presheaf.stalk x) :
    letI : Fintype {C : irreducibleComponents X // x ∈ C.val} := Fintype.ofFinite _
    minimalPrimeCutSum (⊥ : Ideal (X.presheaf.stalk x)) c =
      ∑ C : {C : irreducibleComponents X // x ∈ C.val},
        (componentMultiplicity X C.val : ℕ∞) * componentLocalCutLength X x C c := by
  classical
  let : Fintype {C : irreducibleComponents X // x ∈ C.val} := Fintype.ofFinite _
  let : Fintype (minimalPrimes (X.presheaf.stalk x)) :=
    ((⊥ : Ideal (X.presheaf.stalk x)).finite_minimalPrimes_of_isNoetherianRing _).fintype
  unfold minimalPrimeCutSum
  apply Fintype.sum_equiv (stalkMinimalPrimesEquivComponentsThrough X x)
  intro P
  let : P.val.IsPrime := P.property.1.1
  rw [Ideal.map_bot]
  have hlength := SectionZeroStalk.intrinsic_length_eq_of_ringEquiv
    (RingEquiv.quotientBot (Localization.AtPrime P.val))
  have hsc : Module.length (Localization.AtPrime P.val)
      (Localization.AtPrime P.val ⧸ (⊥ : Ideal (Localization.AtPrime P.val))) =
      Module.length (Localization.AtPrime P.val ⧸ (⊥ : Ideal (Localization.AtPrime P.val)))
        (Localization.AtPrime P.val ⧸ (⊥ : Ideal (Localization.AtPrime P.val))) :=
    Module.length_eq_of_surjective (M := Localization.AtPrime P.val ⧸
      (⊥ : Ideal (Localization.AtPrime P.val))) Ideal.Quotient.mk_surjective
  rw [hsc,hlength,localMinimalPrime_length_eq_componentMultiplicity x P]
  congr 1
  exact (congrArg (fun Q : minimalPrimes (X.presheaf.stalk x) =>
    Module.length (X.presheaf.stalk x)
      ((X.presheaf.stalk x) ⧸ (Q.val ⊔ Ideal.span {c})))
    ((stalkMinimalPrimesEquivComponentsThrough X x).symm_apply_apply P)).symm

theorem zero_stalk_length_eq_component_sum {X : Scheme.{0}} [IsLocallyNoetherian X]
    (hd : topologicalKrullDim X ≤ 1)
    (L : LineBundle X) (s : GlobalSections X L.sheaf) [Mono s]
    (U : X.affineOpens) (e : L.sheaf.restrict U.1.ι ≅ O U.1.toScheme)
    (y : (SectionZeroIdeal.zeroIdeal L s).subscheme)
    (hy : (SectionZeroIdeal.zeroIdeal L s).subschemeι y ∈ U.1) :
    let x := (SectionZeroIdeal.zeroIdeal L s).subschemeι y
    letI : Fintype {C : irreducibleComponents X // x ∈ C.val} := Fintype.ofFinite _
    Module.length ((SectionZeroIdeal.zeroIdeal L s).subscheme.presheaf.stalk y)
      ((SectionZeroIdeal.zeroIdeal L s).subscheme.presheaf.stalk y) =
      ∑ C : {C : irreducibleComponents X // x ∈ C.val},
        (componentMultiplicity X C.val : ℕ∞) * componentLocalCutLength X x C
          (SectionZeroStalk.sectionGerm L s U e x hy) := by
  exact (zero_stalk_length_eq_minimalPrimeCutSum hd L s U e y hy).trans
    (minimalPrimeCutSum_eq_component_sum _ _)

end
end PiExponent.CurveCycle

end OAI
