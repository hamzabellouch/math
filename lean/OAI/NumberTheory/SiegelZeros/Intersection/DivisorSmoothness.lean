import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import OAI.NumberTheory.SiegelZeros.Determinants.GenericNormalizationFinite
import OAI.NumberTheory.SiegelZeros.Structure.CodimensionOne

namespace OAI

namespace SiegelZeros

namespace SiegelZerosAwei.Workers.W15

open CategoryTheory AlgebraicGeometry

variable (p : Ideal (SiegelZeros.W58.TorusRing ℂ)) [p.IsPrime]

noncomputable abbrev NormalizedProjectiveTorus : Scheme :=
  GenericNormalization (TorusProjectiveClosure p)

instance normalizedProjectiveTorus_integral : IsIntegral (NormalizedProjectiveTorus p) :=
  inferInstance

noncomputable def normalizedProjectiveTorusToBase :
    NormalizedProjectiveTorus p ⟶ Spec (CommRingCat.of ℂ) :=
  genericNormalizationMap (TorusProjectiveClosure p) ≫ torusProjectiveClosureToBase p

instance normalizedProjectiveTorus_proper : IsProper (normalizedProjectiveTorusToBase p) :=
  genericNormalization_proper (TorusProjectiveClosure p) ℂ (torusProjectiveClosureToBase p)

instance normalizedProjectiveTorus_locallyNoetherian :
    IsLocallyNoetherian (NormalizedProjectiveTorus p) :=
  LocallyOfFiniteType.isLocallyNoetherian (normalizedProjectiveTorusToBase p)

theorem normalizedProjectiveTorus_stalk_integrallyClosed (x : NormalizedProjectiveTorus p) :
    IsIntegrallyClosed ((NormalizedProjectiveTorus p).presheaf.stalk x) :=
  genericNormalization_stalk_integrallyClosed (TorusProjectiveClosure p) x

noncomputable def normalizedProjectiveTorusFunctionFieldEquiv :
    (NormalizedProjectiveTorus p).functionField ≃+* (TorusSubvariety ℂ p).functionField :=
  (genericNormalizationFunctionFieldEquiv (TorusProjectiveClosure p)).trans
    (torusProjectiveClosureFunctionFieldEquiv p)

noncomputable def compactifiedTorusCoordinate (i : Fin 4) :
    (NormalizedProjectiveTorus p).functionField :=
  (normalizedProjectiveTorusFunctionFieldEquiv p).symm (torusCoordinateFunction ℂ p i)

theorem compactifiedTorusCoordinate_identification (i : Fin 4) :
    normalizedProjectiveTorusFunctionFieldEquiv p (compactifiedTorusCoordinate p i) =
      torusCoordinateFunction ℂ p i :=
  (normalizedProjectiveTorusFunctionFieldEquiv p).apply_symm_apply _

theorem compactifiedTorusCoordinate_ne_zero (i : Fin 4) :
    compactifiedTorusCoordinate p i ≠ 0 := by
  intro h
  apply torusCoordinateFunction_ne_zero ℂ p i
  rw [← compactifiedTorusCoordinate_identification p i, h, map_zero]

end SiegelZerosAwei.Workers.W15

noncomputable section
open CategoryTheory AlgebraicGeometry
namespace W58

open SiegelZerosAwei.Workers.W15

variable (p : Ideal (TorusRing ℂ)) [p.IsPrime]

abbrev ProjectiveDivisorStalk (x : NormalizedProjectiveTorus p) :=
  (NormalizedProjectiveTorus p).presheaf.stalk x

theorem projective_divisor_stalk_dvr (x : NormalizedProjectiveTorus p)
    (hx : ringKrullDim (ProjectiveDivisorStalk p x) = 1) :
    IsDiscreteValuationRing (ProjectiveDivisorStalk p x) := by
  let := normalizedProjectiveTorus_stalk_integrallyClosed p x
  exact dvr_of_local_normal_dimension_one (ProjectiveDivisorStalk p x) hx

theorem projective_divisor_stalkMap_essFiniteType (x : NormalizedProjectiveTorus p) :
    ((normalizedProjectiveTorusToBase p).stalkMap x).hom.EssFiniteType :=
  LocallyOfFiniteType.stalkMap (normalizedProjectiveTorusToBase p) x

theorem projective_divisor_residueMap_essFiniteType (x : NormalizedProjectiveTorus p) :
    ((IsLocalRing.residue (ProjectiveDivisorStalk p x)).comp
      ((normalizedProjectiveTorusToBase p).stalkMap x).hom).EssFiniteType :=
  (projective_divisor_stalkMap_essFiniteType p x).comp
    (RingHom.FiniteType.of_surjective _ IsLocalRing.residue_surjective).essFiniteType

theorem projective_divisor_residueMap_formallySmooth (x : NormalizedProjectiveTorus p) :
    ((IsLocalRing.residue (ProjectiveDivisorStalk p x)).comp
      ((normalizedProjectiveTorusToBase p).stalkMap x).hom).FormallySmooth := by
  let f := normalizedProjectiveTorusToBase p
  let y : PrimeSpectrum ℂ := f x
  let k' := (Spec.structureSheaf ℂ).presheaf.stalk y
  let residueMap : k' →+* IsLocalRing.ResidueField (ProjectiveDivisorStalk p x) :=
    (IsLocalRing.residue (ProjectiveDivisorStalk p x)).comp (f.stalkMap x).hom
  change residueMap.FormallySmooth
  have hfinite : residueMap.EssFiniteType := projective_divisor_residueMap_essFiniteType p x
  algebraize [residueMap]
  let e : ℂ ≃ₐ[ℂ] k' := IsLocalization.atUnits _ y.asIdeal.primeCompl
    (fun z hz => by aesop (add simp IsUnit.mem_submonoid_iff))
  have : Algebra.IsAlgebraic ℂ k' :=
    .of_injective e.symm.toAlgHom e.symm.injective
  let : Field k' := (e.toRingEquiv.symm.isField (Field.toIsField ℂ)).toField
  have : PerfectField k' := Algebra.IsAlgebraic.perfectField (K := ℂ) (L := k')
  exact Algebra.FormallySmooth.of_perfectField

end W58

end

end SiegelZeros

end OAI
