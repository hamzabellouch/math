import Mathlib.RingTheory.Localization.LocalizationLocalization
import OAI.NumberTheory.PiExponent.Geometry.CurveFunctionFieldCompatibility

namespace OAI

noncomputable section
namespace PiExponent.CurveNormalizationModel
open CategoryTheory AlgebraicGeometry
universe u
variable (A E : Type u) [CommRing A] [IsDomain A] [Field E]
  [Algebra A E] [IsFractionRing A E]

theorem isFractionRing_of_intermediate_domain
    (B : Type u) [CommRing B] [IsDomain B] [Algebra A B]
    [Algebra B E] [IsScalarTower A B E]
    (hB : Function.Injective (algebraMap B E)) : IsFractionRing B E where
  map_units b := isUnit_iff_ne_zero.mpr (by
    intro h
    exact (mem_nonZeroDivisors_iff_ne_zero.mp b.2) (hB (by simpa using h)))
  surj z := by
    obtain ⟨⟨a, s⟩, hs⟩ := IsLocalization.surj (nonZeroDivisors A) z
    have hn : algebraMap A B s ≠ 0 := by
      intro he
      have he' : algebraMap A E s = 0 := by
        rw [IsScalarTower.algebraMap_apply A B E, he, map_zero]
      exact (mem_nonZeroDivisors_iff_ne_zero.mp s.2)
        ((IsFractionRing.injective A E) (by simp at he'))
    refine ⟨⟨algebraMap A B a, ⟨algebraMap A B s, mem_nonZeroDivisors_iff_ne_zero.mpr hn⟩⟩, ?_⟩
    simpa only [← IsScalarTower.algebraMap_apply A B E] using hs
  exists_of_eq {a b} h := ⟨1, by simpa using hB h⟩

def affineFunctionFieldEquiv : (Spec (.of A)).functionField ≃+* E := by
  letI : Algebra A (Spec (.of A)).functionField :=
    AlgebraicGeometry.instAlgebraCarrierFunctionFieldSpec (.of A)
  letI : IsFractionRing A (Spec (.of A)).functionField :=
    functionField_isFractionRing_of_affine (.of A)
  exact (IsLocalization.algEquiv (nonZeroDivisors A) (Spec (.of A)).functionField E).toRingEquiv

@[simp] theorem affineFunctionFieldEquiv_toStalk (a : A) :
    affineFunctionFieldEquiv A E (StructureSheaf.toStalk A
      (genericPoint (Spec (.of A))) a) = algebraMap A E a := by
  let : Algebra A (Spec (.of A)).functionField :=
    AlgebraicGeometry.instAlgebraCarrierFunctionFieldSpec (.of A)
  let : IsFractionRing A (Spec (.of A)).functionField :=
    functionField_isFractionRing_of_affine (.of A)
  exact (IsLocalization.algEquiv (nonZeroDivisors A)
    (Spec (.of A)).functionField E).commutes a

theorem affineFunctionFieldEquiv_stalk (q : PrimeSpectrum A)
    [Algebra (Localization.AtPrime q.asIdeal) E]
    [IsScalarTower A (Localization.AtPrime q.asIdeal) E]
    (a : (Spec (.of A)).presheaf.stalk q) :
    affineFunctionFieldEquiv A E
      ((Spec (.of A)).presheaf.stalkSpecializes (genericPoint_specializes q) a) =
      algebraMap (Localization.AtPrime q.asIdeal) E ((Spec.stalkIso (.of A) q).hom a) := by
  let : Algebra A ((Spec (.of A)).presheaf.stalk q) := StructureSheaf.stalkAlgebra A q
  let : IsLocalization.AtPrime ((Spec (.of A)).presheaf.stalk q) q.asIdeal :=
    StructureSheaf.IsLocalization.to_stalk A q
  have heq : (affineFunctionFieldEquiv A E).toRingHom.comp
      ((Spec (.of A)).presheaf.stalkSpecializes (genericPoint_specializes q)).hom =
      (algebraMap (Localization.AtPrime q.asIdeal) E).comp
        (Spec.stalkIso (.of A) q).hom.hom := by
    apply IsLocalization.ringHom_ext q.asIdeal.primeCompl
    apply RingHom.ext
    intro b
    change affineFunctionFieldEquiv A E
      ((Spec (.of A)).presheaf.stalkSpecializes (genericPoint_specializes q)
        (StructureSheaf.toStalk A q b)) =
      algebraMap (Localization.AtPrime q.asIdeal) E
        ((Spec.stalkIso (.of A) q).hom (StructureSheaf.toStalk A q b))
    have hs : (Spec (.of A)).presheaf.stalkSpecializes (genericPoint_specializes q)
        (StructureSheaf.toStalk A q b) =
        StructureSheaf.toStalk A (genericPoint (Spec (.of A))) b := by
      exact congrArg (fun h => h b)
        (StructureSheaf.toStalk_stalkSpecializes (R := A) (genericPoint_specializes q))
    have ht : (Spec.stalkIso (.of A) q).hom (StructureSheaf.toStalk A q b) =
        algebraMap A (Localization.AtPrime q.asIdeal) b :=
      (StructureSheaf.stalkIso A q).symm.commutes b
    rw [hs, ht, affineFunctionFieldEquiv_toStalk]
    exact IsScalarTower.algebraMap_apply A (Localization.AtPrime q.asIdeal) E b
  exact RingHom.congr_fun heq a

theorem affineFunctionFieldEquiv_naturality
    (B : Type u) [CommRing B] [IsDomain B] [Algebra A B]
    [Algebra B E] [IsFractionRing B E] [IsScalarTower A B E]
    [IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap A B)))] :
    (affineFunctionFieldEquiv B E).toRingHom.comp
      (functionFieldRestriction (Spec.map (CommRingCat.ofHom (algebraMap A B)))).hom =
      (affineFunctionFieldEquiv A E).toRingHom := by
  let : Algebra A (Spec (.of A)).functionField :=
    AlgebraicGeometry.instAlgebraCarrierFunctionFieldSpec (.of A)
  let : IsFractionRing A (Spec (.of A)).functionField :=
    functionField_isFractionRing_of_affine (.of A)
  apply IsLocalization.ringHom_ext (nonZeroDivisors A)
  apply RingHom.ext
  intro a
  change affineFunctionFieldEquiv B E
    (functionFieldRestriction (Spec.map (CommRingCat.ofHom (algebraMap A B)))
      (StructureSheaf.toStalk A (genericPoint (Spec (.of A))) a)) =
    affineFunctionFieldEquiv A E
      (StructureSheaf.toStalk A (genericPoint (Spec (.of A))) a)
  have h := congrArg (fun h => h a)
    (functionFieldRestriction_toStalk (CommRingCat.ofHom (algebraMap A B)))
  change functionFieldRestriction (Spec.map (CommRingCat.ofHom (algebraMap A B)))
    (StructureSheaf.toStalk A (genericPoint (Spec (.of A))) a) =
    StructureSheaf.toStalk B (genericPoint (Spec (.of B))) (algebraMap A B a) at h
  rw [h, affineFunctionFieldEquiv_toStalk, affineFunctionFieldEquiv_toStalk]
  exact (IsScalarTower.algebraMap_apply A B E a).symm

end PiExponent.CurveNormalizationModel

end

end OAI
