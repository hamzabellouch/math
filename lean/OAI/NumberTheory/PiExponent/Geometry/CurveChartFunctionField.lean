import OAI.NumberTheory.PiExponent.Ampleness.AffineFunctionFieldCompatibility

namespace OAI

noncomputable section
namespace PiExponent.CurveNormalizationModel
open CategoryTheory AlgebraicGeometry
universe u
variable (A E : Type u) [CommRing A] [IsDomain A] [Field E]
  [Algebra A E] [IsFractionRing A E]

def affineChartFunctionFieldMap {X : Scheme.{u}} [IsIntegral X]
    (i : Spec (.of A) ⟶ X) [IsOpenImmersion i] : X.functionField →+* E :=
  (affineFunctionFieldEquiv A E).toRingHom.comp (functionFieldRestriction i).hom

theorem affineChartFunctionFieldMap_stalk {X : Scheme.{u}} [IsIntegral X]
    (i : Spec (.of A) ⟶ X) [IsOpenImmersion i] (q : PrimeSpectrum A)
    [Algebra (Localization.AtPrime q.asIdeal) E]
    [IsScalarTower A (Localization.AtPrime q.asIdeal) E]
    (a : X.presheaf.stalk (i q)) :
    affineChartFunctionFieldMap A E i
      (X.presheaf.stalkSpecializes (genericPoint_specializes (i q)) a) =
      algebraMap (Localization.AtPrime q.asIdeal) E
        ((Spec.stalkIso (.of A) q).hom (i.stalkMap q a)) := by
  have h := congrArg (fun h => h a) (functionFieldRestriction_stalk i q)
  change functionFieldRestriction i
    (X.presheaf.stalkSpecializes (genericPoint_specializes (i q)) a) =
    (Spec (.of A)).presheaf.stalkSpecializes (genericPoint_specializes q)
      (i.stalkMap q a) at h
  change affineFunctionFieldEquiv A E (_) = _
  rw [h]
  exact affineFunctionFieldEquiv_stalk A E q _

private theorem restriction_congr {U X : Scheme.{u}} [IsIntegral U] [IsIntegral X]
    {i j : U ⟶ X} [IsOpenImmersion i] [IsOpenImmersion j] (h : i = j) :
    functionFieldRestriction i = functionFieldRestriction j := by
  subst j
  rfl

theorem affineChartFunctionFieldMap_eq_of_overlap
    (B G : Type u) [CommRing B] [IsDomain B] [CommRing G] [IsDomain G]
    [Algebra B E] [IsFractionRing B E] [Algebra G E] [IsFractionRing G E]
    [Algebra A G] [Algebra B G] [IsScalarTower A G E] [IsScalarTower B G E]
    {X : Scheme.{u}} [IsIntegral X]
    (iA : Spec (.of A) ⟶ X) (iB : Spec (.of B) ⟶ X)
    [IsOpenImmersion iA] [IsOpenImmersion iB]
    [IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap A G)))]
    [IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap B G)))]
    (h : Spec.map (CommRingCat.ofHom (algebraMap A G)) ≫ iA =
      Spec.map (CommRingCat.ofHom (algebraMap B G)) ≫ iB) :
    affineChartFunctionFieldMap A E iA = affineChartFunctionFieldMap B E iB := by
  have hr : functionFieldRestriction iA ≫
      functionFieldRestriction (Spec.map (CommRingCat.ofHom (algebraMap A G))) =
      functionFieldRestriction iB ≫
      functionFieldRestriction (Spec.map (CommRingCat.ofHom (algebraMap B G))) := by
    rw [← functionFieldRestriction_comp, ← functionFieldRestriction_comp]
    exact restriction_congr h
  apply RingHom.ext
  intro z
  have hz := congrArg (fun g => affineFunctionFieldEquiv G E (g z)) hr
  change affineFunctionFieldEquiv G E
    (functionFieldRestriction (Spec.map (CommRingCat.ofHom (algebraMap A G)))
      (functionFieldRestriction iA z)) =
    affineFunctionFieldEquiv G E
    (functionFieldRestriction (Spec.map (CommRingCat.ofHom (algebraMap B G)))
      (functionFieldRestriction iB z)) at hz
  have hA := RingHom.congr_fun (affineFunctionFieldEquiv_naturality A E G)
    (functionFieldRestriction iA z)
  have hB := RingHom.congr_fun (affineFunctionFieldEquiv_naturality B E G)
    (functionFieldRestriction iB z)
  exact hA.symm.trans (hz.trans hB)

end PiExponent.CurveNormalizationModel

end

end OAI
