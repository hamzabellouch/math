import Mathlib.Algebra.Field.Equiv
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Normalization
import Mathlib.FieldTheory.Perfect
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.NoetherNormalization
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import OAI.NumberTheory.SiegelZeros.Intersection.TorusProjectiveClosure

namespace OAI

namespace SiegelZeros

namespace SiegelZerosAwei.Workers.W15

section

open Module
attribute [local instance] FractionRing.liftAlgebra

theorem finite_normalization_of_finite_normal_base
    (A R : Type*) [CommRing A] [IsDomain A] [CharZero A]
    [IsIntegrallyClosed A] [IsNoetherianRing A]
    [CommRing R] [IsDomain R] [Algebra A R] [Module.IsTorsionFree A R]
    [Module.Finite A R] : Module.Finite R (NormalizationRing R) := by
  let integralClosureInstance : IsIntegralClosure (NormalizationRing R) A (FractionRing R) :=
    { algebraMap_injective :=
        IsIntegralClosure.algebraMap_injective (NormalizationRing R) R (FractionRing R)
      isIntegral_iff := by
        intro x
        constructor
        · intro hx
          exact (IsIntegralClosure.isIntegral_iff (R := R)).mp hx.tower_top
        · intro hx
          exact isIntegral_trans (R := A) x
            ((IsIntegralClosure.isIntegral_iff (R := R)).mpr hx) }
  let finiteDimensionalInstance : FiniteDimensional (FractionRing A) (FractionRing R) := inferInstance
  let separableInstance : Algebra.IsSeparable (FractionRing A) (FractionRing R) := inferInstance
  let finiteNormalization : Module.Finite A (NormalizationRing R) :=
    IsIntegralClosure.finite A (FractionRing A) (FractionRing R) (NormalizationRing R)
  exact Module.Finite.of_restrictScalars_finite A R (NormalizationRing R)

theorem finite_normalization_of_finiteType
    (k R : Type*) [Field k] [CharZero k] [CommRing R] [IsDomain R]
    [Algebra k R] [Algebra.FiniteType k R] :
    Module.Finite R (NormalizationRing R) := by
  obtain ⟨n, g, hg, hfinite⟩ := exists_finite_inj_algHom_of_fg k R
  let polynomialAlgebra : Algebra (MvPolynomial (Fin n) k) R := g.toRingHom.toAlgebra
  let finitePolynomialModule : Module.Finite (MvPolynomial (Fin n) k) R := hfinite
  let torsionFreeInstance : Module.IsTorsionFree (MvPolynomial (Fin n) k) R :=
    (Module.isTorsionFree_iff_algebraMap_injective).2 hg
  exact finite_normalization_of_finite_normal_base (MvPolynomial (Fin n) k) R

theorem finite_integralClosure_of_finiteType
    (k R K : Type*) [Field k] [CharZero k] [CommRing R] [IsDomain R]
    [Algebra k R] [Algebra.FiniteType k R] [Field K] [Algebra R K]
    [IsFractionRing R K] : Module.Finite R (integralClosure R K) := by
  let finiteNormalization := finite_normalization_of_finiteType k R
  exact Module.Finite.equiv
    (IsLocalization.algEquiv (nonZeroDivisors R) (FractionRing R) K).mapIntegralClosure.toLinearEquiv

theorem affineNormalizationMap_finite_of_finiteType
    (k R : Type*) [Field k] [CharZero k] [CommRing R] [IsDomain R]
    [Algebra k R] [Algebra.FiniteType k R] :
    AlgebraicGeometry.IsFinite (affineNormalizationMap R) := by
  apply (AlgebraicGeometry.IsFinite.SpecMap_iff _).mpr
  exact RingHom.finite_algebraMap.mpr (finite_normalization_of_finiteType k R)

theorem affineNormalizationMap_proper_of_finiteType
    (k R : Type*) [Field k] [CharZero k] [CommRing R] [IsDomain R]
    [Algebra k R] [Algebra.FiniteType k R] :
    AlgebraicGeometry.IsProper (affineNormalizationMap R) := by
  let finiteMap := affineNormalizationMap_finite_of_finiteType k R
  infer_instance

end

open CategoryTheory AlgebraicGeometry TopologicalSpace

section

universe u
variable (X : Scheme.{u}) [IsIntegral X] [QuasiSeparatedSpace X]

noncomputable abbrev genericPointMorphism :
    Spec (CommRingCat.of X.functionField) ⟶ X :=
  X.fromSpecStalk (genericPoint X)

noncomputable abbrev GenericNormalization : Scheme :=
  (genericPointMorphism X).normalization

noncomputable abbrev genericNormalizationMap : GenericNormalization X ⟶ X :=
  (genericPointMorphism X).fromNormalization

instance genericNormalization_integral : IsIntegral (GenericNormalization X) := inferInstance

instance genericNormalizationMap_integral : IsIntegralHom (genericNormalizationMap X) :=
  inferInstance

omit [QuasiSeparatedSpace X] in
theorem genericPointMorphism_preimage (U : X.Opens) [Nonempty U] :
    genericPointMorphism X ⁻¹ᵁ U = ⊤ := by
  have hη : genericPoint X ∈ U :=
    ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr (by simpa using ‹Nonempty U›)
  ext z
  constructor
  · intro _
    trivial
  intro _
  have hz : z = IsLocalRing.closedPoint (X.presheaf.stalk (genericPoint X)) :=
    Subsingleton.elim _ _
  change X.fromSpecStalk (genericPoint X) z ∈ U
  rw [hz, Scheme.fromSpecStalk_closedPoint]
  exact hη

noncomputable def genericSourceSectionsIso (U : X.Opens) [Nonempty U] :
    Γ(Spec (CommRingCat.of X.functionField), genericPointMorphism X ⁻¹ᵁ U) ≅
      CommRingCat.of X.functionField :=
  (Spec (CommRingCat.of X.functionField)).presheaf.mapIso
    (eqToIso (genericPointMorphism_preimage X U).symm).op ≪≫
      Scheme.ΓSpecIso (CommRingCat.of X.functionField)

omit [QuasiSeparatedSpace X] in
theorem genericNormalization_chart_integrallyClosed (U : X.Opens)
    (hU : IsAffineOpen U) [Nonempty U] :
    IsIntegrallyClosed Γ(GenericNormalization X, genericNormalizationMap X ⁻¹ᵁ U) := by
  let f := genericPointMorphism X
  let sectionAlgebra : Algebra Γ(X, U) Γ(Spec (CommRingCat.of X.functionField), f ⁻¹ᵁ U) :=
    (f.app U).hom.toAlgebra
  let e := (genericSourceSectionsIso X U).commRingCatIsoToRingEquiv
  let sectionField : Field Γ(Spec (CommRingCat.of X.functionField), f ⁻¹ᵁ U) :=
    (e.toMulEquiv.isField (Field.toIsField X.functionField)).toField
  let integrallyClosedInstance : IsIntegrallyClosed
      (integralClosure Γ(X, U) Γ(Spec (CommRingCat.of X.functionField), f ⁻¹ᵁ U)) :=
    IsIntegrallyClosed.of_isIntegrallyClosedIn
      (integralClosure Γ(X, U) Γ(Spec (CommRingCat.of X.functionField), f ⁻¹ᵁ U))
      Γ(Spec (CommRingCat.of X.functionField), f ⁻¹ᵁ U)
  exact IsIntegrallyClosed.of_equiv
    (f.normalizationObjIso hU).commRingCatIsoToRingEquiv.symm

omit [QuasiSeparatedSpace X] in
theorem genericNormalization_stalk_integrallyClosed (x : GenericNormalization X) :
    IsIntegrallyClosed ((GenericNormalization X).presheaf.stalk x) := by
  let ν := genericNormalizationMap X
  let U : X.Opens := (X.affineCover.f (X.affineCover.idx (ν x))).opensRange
  have hU : IsAffineOpen U := isAffineOpen_opensRange _
  have hx : ν x ∈ U := X.affineCover.covers (ν x)
  let nonemptyChart : Nonempty U := ⟨⟨ν x, hx⟩⟩
  let V : (GenericNormalization X).Opens := ν ⁻¹ᵁ U
  have hV : IsAffineOpen V := hU.preimage ν
  let nonemptyPreimage : Nonempty V := ⟨⟨x, hx⟩⟩
  let integrallyClosedInstance : IsIntegrallyClosed Γ(GenericNormalization X, V) :=
    genericNormalization_chart_integrallyClosed X U hU
  let stalkAlgebra : Algebra Γ(GenericNormalization X, V)
      ((GenericNormalization X).presheaf.stalk x) :=
    ((GenericNormalization X).presheaf.germ V x hx).hom.toAlgebra
  let stalkLocalization : IsLocalization (hV.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl
      ((GenericNormalization X).presheaf.stalk x) :=
    hV.isLocalization_stalk ⟨x, hx⟩
  exact isIntegrallyClosed_of_isLocalization ((GenericNormalization X).presheaf.stalk x)
    (hV.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl
    (hV.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl_le_nonZeroDivisors

end

universe u
variable (X : Scheme.{u}) [IsIntegral X] [QuasiSeparatedSpace X]

omit [QuasiSeparatedSpace X] in
theorem toGenericNormalization_closedPoint :
    (genericPointMorphism X).toNormalization
        (IsLocalRing.closedPoint (CommRingCat.of X.functionField)) =
      genericPoint (GenericNormalization X) := by
  let a := (genericPointMorphism X).toNormalization
  have hr : Set.range a = {a (IsLocalRing.closedPoint (CommRingCat.of X.functionField))} := by
    ext z
    constructor
    · rintro ⟨y, rfl⟩
      exact congrArg a (Subsingleton.elim _ _)
    · intro hz
      exact ⟨_, hz.symm⟩
  apply ((genericPoint_spec (GenericNormalization X)).eq _).symm
  rw [isGenericPoint_def, ← hr]
  exact a.denseRange.closure_range

omit [QuasiSeparatedSpace X] in
theorem toGenericNormalization_stalk_surjective :
    Function.Surjective
      (Scheme.stalkClosedPointTo (genericPointMorphism X).toNormalization).hom := by
  let a := (genericPointMorphism X).toNormalization
  let ν := genericNormalizationMap X
  have hi : IsIso (Scheme.stalkClosedPointTo (a ≫ ν)) := by
    dsimp only [a, ν, genericNormalizationMap]
    rw [Scheme.Hom.toNormalization_fromNormalization]
    change IsIso (Scheme.stalkClosedPointTo (X.fromSpecStalk (genericPoint X)))
    rw [Scheme.stalkClosedPointTo_fromSpecStalk]
    infer_instance
  have hs := (ConcreteCategory.bijective_of_isIso
    (Scheme.stalkClosedPointTo (a ≫ ν))).2
  rw [Scheme.stalkClosedPointTo_comp] at hs
  exact Function.Surjective.of_comp hs

noncomputable def genericNormalizationFunctionFieldEquiv :
    (GenericNormalization X).functionField ≃+* X.functionField := by
  let a := (genericPointMorphism X).toNormalization
  let e := (GenericNormalization X).presheaf.stalkCongr
    (.of_eq (toGenericNormalization_closedPoint X).symm)
  let φ := Scheme.stalkClosedPointTo a
  let ψ := e.hom ≫ φ
  exact RingEquiv.ofBijective ψ.hom
    ⟨ψ.hom.injective,
      (toGenericNormalization_stalk_surjective X).comp
        (ConcreteCategory.bijective_of_isIso e.hom).2⟩


open CategoryTheory AlgebraicGeometry TopologicalSpace

variable (X : Scheme.{u}) [IsIntegral X] [QuasiSeparatedSpace X]

omit [QuasiSeparatedSpace X] in
theorem genericSourceSectionsIso_app (U : X.Opens) [Nonempty U] :
    (genericPointMorphism X).app U ≫ (genericSourceSectionsIso X U).hom =
      X.germToFunctionField U := by
  have hmem : genericPointMorphism X
      (IsLocalRing.closedPoint (CommRingCat.of X.functionField)) ∈ U := by
    change IsLocalRing.closedPoint (CommRingCat.of X.functionField) ∈
      genericPointMorphism X ⁻¹ᵁ U
    rw [genericPointMorphism_preimage X U]
    trivial
  have hg := Scheme.germ_stalkClosedPointTo (genericPointMorphism X) U hmem
  rw [Scheme.stalkClosedPointTo_fromSpecStalk] at hg
  simp only [TopCat.Presheaf.stalkCongr_hom] at hg
  erw [TopCat.Presheaf.germ_stalkSpecializes] at hg
  simpa only [genericSourceSectionsIso] using hg.symm

omit [QuasiSeparatedSpace X] in
theorem genericSourceSections_isFractionRing (U : X.Opens) (hU : IsAffineOpen U)
    [Nonempty U] :
    letI := ((genericPointMorphism X).app U).hom.toAlgebra
    IsFractionRing Γ(X, U)
      Γ(Spec (CommRingCat.of X.functionField), genericPointMorphism X ⁻¹ᵁ U) := by
  let sectionAlgebra := ((genericPointMorphism X).app U).hom.toAlgebra
  let functionFieldFractionRing := functionField_isFractionRing_of_isAffineOpen X U hU
  let e : Γ(Spec (CommRingCat.of X.functionField), genericPointMorphism X ⁻¹ᵁ U)
      ≃ₐ[Γ(X, U)] X.functionField :=
    { (genericSourceSectionsIso X U).commRingCatIsoToRingEquiv with
      commutes' := fun r => congrArg (fun φ : Γ(X, U) ⟶ X.functionField => φ.hom r)
        (genericSourceSectionsIso_app X U) }
  exact IsLocalization.isLocalization_of_algEquiv (nonZeroDivisors Γ(X, U)) e.symm

variable (k : Type u) [Field k] [CharZero k]
variable (s : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType s]

include k s

omit [QuasiSeparatedSpace X] in
theorem genericNormalizationMap_finite :
    AlgebraicGeometry.IsFinite (genericNormalizationMap X) := by
  constructor
  intro U hU
  by_cases hne : Nonempty U
  · let nonemptyChart := hne
    let R := Γ(X, U)
    let f := genericPointMorphism X
    let K := Γ(Spec (CommRingCat.of X.functionField), f ⁻¹ᵁ U)
    let φ : CommRingCat.of k ⟶ R :=
      (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ s.appLE ⊤ U (by simp)
    let baseAlgebra : Algebra k R := φ.hom.toAlgebra
    have hφ : φ.hom.FiniteType :=
      (s.finiteType_appLE (isAffineOpen_top _) hU (by simp)).comp
        (RingHom.FiniteType.of_surjective _
          (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of k)).inv).2)
    let finiteTypeInstance : Algebra.FiniteType k R := hφ
    let sectionAlgebra : Algebra R K := (f.app U).hom.toAlgebra
    let e := (genericSourceSectionsIso X U).commRingCatIsoToRingEquiv
    let sectionField : Field K := (e.toMulEquiv.isField (Field.toIsField X.functionField)).toField
    let fractionRingInstance : IsFractionRing R K := genericSourceSections_isFractionRing X U hU
    have hfin : (algebraMap R (integralClosure R K)).Finite :=
      RingHom.finite_algebraMap.mpr (finite_integralClosure_of_finiteType k R K)
    change (f.fromNormalization.app U).hom.Finite
    rw [Scheme.Hom.fromNormalization_app f hU, CommRingCat.hom_comp]
    exact (RingHom.Finite.of_surjective _
      (ConcreteCategory.bijective_of_isIso (f.normalizationObjIso hU).inv).2).comp hfin
  · have hUbot : U = ⊥ := by
      ext x
      exact ⟨fun hx => False.elim (hne ⟨⟨x, hx⟩⟩), fun hx => False.elim hx⟩
    subst U
    let subsingletonSections :
        Subsingleton Γ(GenericNormalization X, genericNormalizationMap X ⁻¹ᵁ ⊥) := by
      simpa only [Scheme.Hom.preimage_bot] using
        (inferInstance : Subsingleton Γ(GenericNormalization X, ⊥))
    apply RingHom.Finite.of_surjective
    intro y
    exact ⟨0, Subsingleton.elim _ _⟩

omit [LocallyOfFiniteType s] [QuasiSeparatedSpace X] in
theorem genericNormalization_proper [IsProper s] :
    IsProper (genericNormalizationMap X ≫ s) := by
  let finiteMap := genericNormalizationMap_finite X k s
  infer_instance

end SiegelZerosAwei.Workers.W15

end SiegelZeros

end OAI
