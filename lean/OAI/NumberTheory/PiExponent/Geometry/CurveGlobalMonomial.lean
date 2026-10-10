import OAI.NumberTheory.PiExponent.Geometry.CurveModelGenericPoint
import OAI.NumberTheory.PiExponent.Geometry.CurveMonomialMap
import OAI.NumberTheory.PiExponent.Geometry.CurveStalkGluing

namespace OAI

noncomputable section
universe u
namespace PiExponent.CurveGlobalMonomial
open AlgebraicGeometry CategoryTheory
open CurveNormalizationModel CurveProperExtension CurveMonomialMap WeightedCompactification

theorem exists_extension
    {X Y S : Scheme.{u}} [IsIntegral X]
    (sX : X ⟶ S) (sY : Y ⟶ S) [IsProper sY]
    (hDVR : ∀ x : X, x ≠ genericPoint X → IsDiscreteValuationRing (X.presheaf.stalk x))
    (η : Spec X.functionField ⟶ Y)
    (hη : η ≫ sY = X.fromSpecStalk (genericPoint X) ≫ sX) :
    ∃ g : X ⟶ Y, g ≫ sY = sX ∧ X.fromSpecStalk (genericPoint X) ≫ g = η :=
  CurveStalkGluing.exists_morphism_of_stalk_maps sX sY η
    (exists_stalk_map sX sY hDVR η hη)

theorem exists_parameterCurve_extension
    {F E : Type u} [Field F] [CharZero F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f)
    [FiniteDimensional (IntermediateField.adjoin F {f}) E]
    {Y : Scheme.{u}} (sY : Y ⟶ Spec (CommRingCat.of F)) [IsProper sY]
    (ηE : Spec (CommRingCat.of E) ⟶ Y)
    (hηE : ηE ≫ sY = Spec.map (CommRingCat.ofHom (algebraMap F E))) :
    ∃ g : parameterCurve f hf ⟶ Y,
      g ≫ sY = parameterCurveStructureMap f hf ∧ parameterCurveGenericPoint f hf ≫ g = ηE := by
  let e := parameterCurveFunctionFieldEquiv f hf
  let eSpec : Spec (CommRingCat.of E) ≅ Spec (parameterCurve f hf).functionField :=
    Scheme.Spec.mapIso e.toCommRingCatIso.op
  let η := eSpec.inv ≫ ηE
  have hη : η ≫ sY = (parameterCurve f hf).fromSpecStalk
      (genericPoint (parameterCurve f hf)) ≫ parameterCurveStructureMap f hf := by
    apply (cancel_epi eSpec.hom).mp
    change eSpec.hom ≫ (eSpec.inv ≫ ηE) ≫ sY = _
    rw [← Category.assoc, eSpec.hom_inv_id_assoc, hηE]
    exact (parameterCurveGenericPoint_over_base f hf).symm
  obtain ⟨g, hbase, hgeneric⟩ := exists_extension (parameterCurveStructureMap f hf) sY
    (parameterCurve_stalkDVR f hf) η hη
  refine ⟨g, hbase, ?_⟩
  change (eSpec.hom ≫ (parameterCurve f hf).fromSpecStalk
    (genericPoint (parameterCurve f hf))) ≫ g = ηE
  rw [Category.assoc, hgeneric]
  exact eSpec.hom_inv_id_assoc ηE

theorem exists_globalMonomialMap
    {F E ι σ : Type u} [Field F] [CharZero F] [Field E] [Algebra F E] [Finite σ]
    (f : E) (hf : Transcendental F f)
    [FiniteDimensional (IntermediateField.adjoin F {f}) E]
    (a : σ → ι →₀ ℕ) (z : σ) (hz : a z = 0)
    (coordinate : ι → σ) (hcoordinate : ∀ i, a (coordinate i) = Finsupp.single i 1)
    (x : ι → E) :
    ∃ g : parameterCurve f hf ⟶ Proj (imageGrade (R := F) a),
      g ≫ projection a = parameterCurveStructureMap f hf ∧
      parameterCurveGenericPoint f hf ≫ g = genericMonomialMap a z hz coordinate hcoordinate x :=
  exists_parameterCurve_extension f hf (projection a)
    (genericMonomialMap a z hz coordinate hcoordinate x)
    (genericMonomialMap_over_base a z hz coordinate hcoordinate x)

end PiExponent.CurveGlobalMonomial

end

end OAI
