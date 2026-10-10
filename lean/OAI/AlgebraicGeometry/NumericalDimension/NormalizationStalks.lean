import Mathlib
import OAI.AlgebraicGeometry.NumericalDimension.NormalizationRings

namespace OAI

/-! Normalization Stalks. -/

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne
section LocalizedBranches
variable (A B R C : Type*) [CommRing A] [CommRing B] [CommRing R] [CommRing C]
  [Algebra A B] [Algebra A R] [Algebra A C] [Algebra B C] [Algebra R C]
  [IsScalarTower A B C] [IsScalarTower A R C]
  (p : Ideal A) [p.IsPrime] [IsLocalization.AtPrime R p] [IsLocalRing R]
  [IsLocalization (Algebra.algebraMapSubmonoid B p.primeCompl) C]

noncomputable def localizedPrimesOverEquiv :
    (IsLocalRing.maximalIdeal R).primesOver C ≃ p.primesOver B := by
  let M := Algebra.algebraMapSubmonoid B p.primeCompl
  have hdis (q : p.primesOver B) : Disjoint (M : Set B) q.1 := by
    rw [Set.disjoint_left]
    rintro b ⟨a,ha,rfl⟩ hb
    exact ha ((q.1.mem_of_liesOver p a).mpr hb)
  let forward : (IsLocalRing.maximalIdeal R).primesOver C → p.primesOver B := fun q =>
    ⟨q.1.under B, inferInstance, ⟨by
      rw [Ideal.under_under, ← Ideal.under_under (A := A) (B := R)]
      rw [← q.1.over_def (IsLocalRing.maximalIdeal R),
        IsLocalization.AtPrime.under_maximalIdeal R p]⟩⟩
  let backward : p.primesOver B → (IsLocalRing.maximalIdeal R).primesOver C := fun q =>
    ⟨q.1.map (algebraMap B C),
      IsLocalization.isPrime_of_isPrime_disjoint M C q.1 inferInstance (hdis q), ⟨by
      apply (IsLocalization.orderEmbedding p.primeCompl R).injective
      change (IsLocalRing.maximalIdeal R).under A =
        ((q.1.map (algebraMap B C)).under R).under A
      rw [IsLocalization.AtPrime.under_maximalIdeal R p, Ideal.under_under,
        ← Ideal.under_under (A := A) (B := B),
        IsLocalization.under_map_of_isPrime_disjoint M C (q.2.1) (hdis q)]
      exact q.1.over_def p⟩⟩
  refine { toFun := forward, invFun := backward, left_inv := ?_, right_inv := ?_ }
  · intro q
    apply Subtype.ext
    exact IsLocalization.map_under M C q.1
  · intro q
    apply Subtype.ext
    exact IsLocalization.under_map_of_isPrime_disjoint M C q.2.1 (hdis q)

end LocalizedBranches
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne
open AlgebraicGeometry CategoryTheory
open scoped nonZeroDivisors
variable {X : Scheme} [IsIntegral X]
attribute [local instance] genericPointMap_quasiCompact

noncomputable def genericNormalizationFiberEquiv (U : X.Opens)
    (hU : IsAffineOpen U) (x : U) :
    (IsLocalRing.maximalIdeal (X.presheaf.stalk x.1)).primesOver
      (integralClosure (X.presheaf.stalk x.1) X.functionField) ≃
    {y : (X.fromSpecStalk (genericPoint X)).normalization //
      (X.fromSpecStalk (genericPoint X)).fromNormalization y = x.1} := by
  let : Nonempty U := ⟨x⟩
  let f := (X.fromSpecStalk (genericPoint X)).fromNormalization
  let N := (X.fromSpecStalk (genericPoint X)).normalization
  let V := f ⁻¹ᵁ U
  have hV : IsAffineOpen V := hU.preimage f
  let A := Γ(X,U)
  let B := Γ(N,V)
  let R := X.presheaf.stalk x.1
  let K := X.functionField
  let C := integralClosure A K
  let D := integralClosure R K
  let : Algebra A R := X.presheaf.algebra_section_stalk x
  have : IsScalarTower A R K := functionField_isScalarTower X U x
  let : Algebra A B := (f.app U).hom.toAlgebra
  let : Algebra C D := (integralClosureBaseMap A R K).toAlgebra
  have : IsScalarTower A C D := integralClosureBaseMap_tower A R K
  have : IsLocalization.AtPrime R (hU.primeIdealOf x).asIdeal :=
    hU.isLocalization_stalk x
  have := functionField_isFractionRing_of_isAffineOpen X U hU
  have hM : (hU.primeIdealOf x).asIdeal.primeCompl ≤ A⁰ := by
    intro a ha
    exact mem_nonZeroDivisors_iff_ne_zero.mpr (fun h => ha (h ▸ Ideal.zero_mem _))
  have : IsLocalization (Algebra.algebraMapSubmonoid C
      (hU.primeIdealOf x).asIdeal.primeCompl) D :=
    integralClosureBaseMap_isLocalization A R K _ hM
  exact (localizedPrimesOverEquiv A C R D (hU.primeIdealOf x).asIdeal).trans
    ((primesOverAlgEquiv (hU.primeIdealOf x).asIdeal
      (genericNormalizationSectionsEquiv U hU)).trans
      (affineFiberEquiv f U hU hV x).symm)
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne
open AlgebraicGeometry CategoryTheory
variable {X : Scheme} [IsIntegral X]
attribute [local instance] genericPointMap_quasiCompact

lemma genericNormalizationFiberEquiv_symm_asIdeal (U : X.Opens)
    (hU : IsAffineOpen U) (x : U)
    (y : {y : (X.fromSpecStalk (genericPoint X)).normalization //
      (X.fromSpecStalk (genericPoint X)).fromNormalization y = x.1}) :
    letI : Nonempty U := ⟨x⟩
    letI := X.presheaf.algebra_section_stalk x
    letI := functionField_isScalarTower X U x
    let f := (X.fromSpecStalk (genericPoint X)).fromNormalization
    letI := (f.app U).hom.toAlgebra
    let hV : IsAffineOpen (f ⁻¹ᵁ U) := hU.preimage f
    ((genericNormalizationFiberEquiv U hU x).symm y).1 =
      ((hV.primeIdealOf ⟨y.1, by
        change f y.1 ∈ U
        rw [y.2]
        exact x.2⟩).asIdeal.comap
          (genericNormalizationSectionsEquiv U hU).symm.toRingHom).map
            (integralClosureBaseMap Γ(X,U) (X.presheaf.stalk x.1) X.functionField) := by
  rfl
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne
open scoped nonZeroDivisors
section IntermediateNormal
variable (R S K : Type*) [CommRing R] [CommRing S] [Field K]
  [Algebra R S] [Algebra R K] [Algebra S K] [IsScalarTower R S K]
  [IsFractionRing S K] [IsIntegrallyClosed S]

noncomputable def integralClosureToNormal : integralClosure R K →ₐ[R] S where
  toFun x := IsIntegralClosure.mk' S x.1 (x.2.tower_top (A := S))
  map_zero' := by apply IsFractionRing.injective S K; simp
  map_one' := by apply IsFractionRing.injective S K; simp
  map_add' x y := by apply IsFractionRing.injective S K; simp
  map_mul' x y := by apply IsFractionRing.injective S K; simp
  commutes' x := by
    apply IsFractionRing.injective S K
    simp only [IsIntegralClosure.algebraMap_mk', Subalgebra.coe_algebraMap,
      ← IsScalarTower.algebraMap_apply R S K]

@[simp] lemma integralClosureToNormal_map (x : integralClosure R K) :
    algebraMap S K (integralClosureToNormal R S K x) = x.1 :=
  IsIntegralClosure.algebraMap_mk' S x.1 (x.2.tower_top (A := S))

lemma integralClosureToNormal_injective :
    Function.Injective (integralClosureToNormal R S K) := by
  intro x y h
  apply Subtype.ext
  simpa only [integralClosureToNormal_map] using congrArg (algebraMap S K) h
end IntermediateNormal
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne
namespace LocalizationTower
variable {A B S : Type*} [CommRing A] [CommRing B] [CommRing S]
  [Algebra A B] [Algebra A S] [Algebra B S] [IsScalarTower A B S]
  [IsLocalRing S]

theorem atPrime_of_localized_base (M : Submonoid A) [IsLocalization M S]
    (hi : Function.Injective (algebraMap B S)) :
    IsLocalization.AtPrime S ((IsLocalRing.maximalIdeal S).comap (algebraMap B S)) := by
  let p := (IsLocalRing.maximalIdeal S).comap (algebraMap B S)
  change IsLocalization p.primeCompl S
  refine ⟨⟨?_, ?_, ?_⟩⟩
  · intro a
    exact IsLocalRing.notMem_maximalIdeal.mp a.2
  · intro s
    obtain ⟨⟨a, b⟩, he⟩ := IsLocalization.surj M s
    refine ⟨⟨algebraMap A B a, ⟨algebraMap A B b, ?_⟩⟩, ?_⟩
    · change algebraMap B S (algebraMap A B b) ∉ IsLocalRing.maximalIdeal S
      rw [← IsScalarTower.algebraMap_apply A B S]
      exact by
        simpa only [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not] using
          (IsLocalization.map_units S b)
    · simpa only [← IsScalarTower.algebraMap_apply A B S] using he
  · intro a b he
    exact ⟨1, by simpa only [OneMemClass.coe_one, one_mul] using hi he⟩
end LocalizationTower
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne
open scoped nonZeroDivisors

theorem normal_overring_isLocalization_integralClosure
    (A B R S K : Type*) [CommRing A] [CommRing B] [CommRing R] [CommRing S] [Field K]
    [Algebra A B] [Module.Finite A B] [Algebra A R]
    [Algebra A K] [Algebra R K] [IsScalarTower A R K]
    [Algebra B K] [IsScalarTower A B K]
    [Algebra R S] [Algebra S K] [IsScalarTower R S K]
    [Algebra B S] [IsScalarTower B S K]
    [IsFractionRing S K] [IsIntegrallyClosed S] [IsLocalRing S]
    (M : Submonoid B) [IsLocalization M S] :
    letI := (integralClosureToNormal R S K).toRingHom.toAlgebra
    IsLocalization.AtPrime S ((IsLocalRing.maximalIdeal S).comap
      (integralClosureToNormal R S K).toRingHom) := by
  let C := integralClosure R K
  let φ := integralClosureToNormal R S K
  let : Algebra C S := φ.toRingHom.toAlgebra
  let β : B →+* C :=
    { toFun := fun b => ⟨algebraMap B K b,
        ((Algebra.IsIntegral.isIntegral (R := A) b).map
          (IsScalarTower.toAlgHom A B K)).tower_top⟩
      map_zero' := Subtype.ext (map_zero _)
      map_one' := Subtype.ext (map_one _)
      map_add' := fun b c => Subtype.ext (map_add _ b c)
      map_mul' := fun b c => Subtype.ext (map_mul _ b c) }
  let : Algebra B C := β.toAlgebra
  have : IsScalarTower B C S := IsScalarTower.of_algebraMap_eq fun b => by
    apply IsFractionRing.injective S K
    change algebraMap S K (algebraMap B S b) = algebraMap S K (φ (β b))
    rw [← IsScalarTower.algebraMap_apply B S K, integralClosureToNormal_map]
    rfl
  exact LocalizationTower.atPrime_of_localized_base M
    (integralClosureToNormal_injective R S K)
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne
open AlgebraicGeometry CategoryTheory
variable {C X : Scheme} [IsIntegral C] [IsIntegral X]
  (f : C ⟶ X) [IsDominant f]
  (hf : Function.Bijective (dominantFunctionFieldMap f))

noncomputable def birationalStalkToField (x : C) :
    C.presheaf.stalk x →+* X.functionField :=
  (RingEquiv.ofBijective (dominantFunctionFieldMap f) hf).symm.toRingHom.comp
    (algebraMap (C.presheaf.stalk x) C.functionField)

theorem birationalStalk_isFractionRing (x : C) :
    letI := (birationalStalkToField f hf x).toAlgebra
    IsFractionRing (C.presheaf.stalk x) X.functionField := by
  let e := RingEquiv.ofBijective (dominantFunctionFieldMap f) hf
  let : Algebra (C.presheaf.stalk x) X.functionField :=
    (birationalStalkToField f hf x).toAlgebra
  let e' : C.functionField ≃ₐ[C.presheaf.stalk x] X.functionField :=
    { e.symm with commutes' := fun _ => rfl }
  exact IsLocalization.isLocalization_of_algEquiv _ e'

theorem birationalStalk_tower (x : C) :
    letI := (f.stalkMap x).hom.toAlgebra
    letI := (birationalStalkToField f hf x).toAlgebra
    IsScalarTower (X.presheaf.stalk (f x)) (C.presheaf.stalk x) X.functionField := by
  let : Algebra (X.presheaf.stalk (f x)) (C.presheaf.stalk x) :=
    (f.stalkMap x).hom.toAlgebra
  let : Algebra (C.presheaf.stalk x) X.functionField :=
    (birationalStalkToField f hf x).toAlgebra
  apply IsScalarTower.of_algebraMap_eq
  intro a
  apply (RingEquiv.ofBijective (dominantFunctionFieldMap f) hf).injective
  change dominantFunctionFieldMap f (algebraMap _ X.functionField a) =
    (RingEquiv.ofBijective (dominantFunctionFieldMap f) hf)
      ((RingEquiv.ofBijective (dominantFunctionFieldMap f) hf).symm
        (algebraMap _ C.functionField (f.stalkMap x a)))
  rw [RingEquiv.apply_symm_apply]
  exact dominantFunctionFieldMap_algebraMap f x a

theorem finite_birational_stalk_normalization [IsFinite f] (x : C)
    [IsIntegrallyClosed (C.presheaf.stalk x)] :
    letI := (f.stalkMap x).hom.toAlgebra
    letI := (birationalStalkToField f hf x).toAlgebra
    letI := birationalStalk_isFractionRing f hf x
    letI := birationalStalk_tower f hf x
    letI := (integralClosureToNormal (X.presheaf.stalk (f x))
      (C.presheaf.stalk x) X.functionField).toRingHom.toAlgebra
    IsLocalization.AtPrime (C.presheaf.stalk x)
      ((IsLocalRing.maximalIdeal (C.presheaf.stalk x)).comap
        (integralClosureToNormal (X.presheaf.stalk (f x))
          (C.presheaf.stalk x) X.functionField).toRingHom) := by
  let R := X.presheaf.stalk (f x)
  let S := C.presheaf.stalk x
  let K := X.functionField
  let : Algebra R S := (f.stalkMap x).hom.toAlgebra
  let : Algebra S K := (birationalStalkToField f hf x).toAlgebra
  have : IsFractionRing S K := birationalStalk_isFractionRing f hf x
  have : IsScalarTower R S K := birationalStalk_tower f hf x
  obtain ⟨U,hU,hxU,_⟩ := exists_isAffineOpen_mem_and_subset
    (show f x ∈ (⊤ : X.Opens) from trivial)
  let : Nonempty U := ⟨⟨f x,hxU⟩⟩
  let V := f ⁻¹ᵁ U
  have hV : IsAffineOpen V := hU.preimage f
  let A := Γ(X,U)
  let B := Γ(C,V)
  let : Algebra A R := X.presheaf.algebra_section_stalk ⟨f x,hxU⟩
  let : Algebra A B := (f.app U).hom.toAlgebra
  let : Algebra B S := C.presheaf.algebra_section_stalk ⟨x,hxU⟩
  have : Module.Finite A B := (f.finite_app U hU)
  have : IsScalarTower A R K := functionField_isScalarTower X U ⟨f x,hxU⟩
  let : Algebra B K := ((algebraMap S K).comp (algebraMap B S)).toAlgebra
  have : IsScalarTower B S K := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower A B K := IsScalarTower.of_algebraMap_eq fun a => by
    change algebraMap A K a = algebraMap S K (algebraMap B S (algebraMap A B a))
    rw [IsScalarTower.algebraMap_apply A R K, IsScalarTower.algebraMap_apply R S K]
    exact congrArg (algebraMap S K) (f.germ_stalkMap_apply U x hxU a)
  have := hV.isLocalization_stalk ⟨x,hxU⟩
  exact normal_overring_isLocalization_integralClosure A B R S K
    (hV.primeIdealOf ⟨x,hxU⟩).asIdeal.primeCompl
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne
open AlgebraicGeometry CategoryTheory
variable {C X : Scheme}

noncomputable def fiberStalkMap (f : C ⟶ X) (x : X) (y : {y : C // f y = x}) :
    X.presheaf.stalk x →+* C.presheaf.stalk y.1 :=
  ((eqToHom (congrArg X.presheaf.stalk y.2.symm)) ≫ f.stalkMap y.1).hom

@[simp] lemma fiberStalkMap_self (f : C ⟶ X) (y : C) :
    fiberStalkMap f (f y) ⟨y,rfl⟩ = (f.stalkMap y).hom := by
  simp [fiberStalkMap]

lemma fiberStalkMap_germ (f : C ⟶ X) (U : X.Opens) (x : U)
    (y : {y : C // f y = x.1}) (hy : y.1 ∈ f ⁻¹ᵁ U) (a : Γ(X,U)) :
    fiberStalkMap f x.1 y (X.presheaf.germ U x.1 x.2 a) =
      C.presheaf.germ (f ⁻¹ᵁ U) y.1 hy (f.app U a) := by
  rcases x with ⟨x,hx⟩
  rcases y with ⟨y,hyx⟩
  change f y = x at hyx
  subst x
  simpa only [fiberStalkMap_self] using
    (f.germ_stalkMap_apply U y hy a)

lemma fiberStalkMap_isLocalHom (f : C ⟶ X) (x : X) (y : {y : C // f y = x}) :
    IsLocalHom (fiberStalkMap f x y) := by
  rcases y with ⟨y,hy⟩
  subst x
  simpa only [fiberStalkMap_self] using
    (inferInstance : IsLocalHom (f.stalkMap y).hom)

variable [IsIntegral C] [IsIntegral X] (f : C ⟶ X) [IsDominant f]
  (hf : Function.Bijective (dominantFunctionFieldMap f))

lemma birationalFiberStalk_tower (x : X) (y : {y : C // f y = x}) :
    letI := (fiberStalkMap f x y).toAlgebra
    letI := (birationalStalkToField f hf y.1).toAlgebra
    IsScalarTower (X.presheaf.stalk x) (C.presheaf.stalk y.1) X.functionField := by
  dsimp only
  rcases y with ⟨y,hy⟩
  subst x
  exact
    birationalStalk_tower f hf y

lemma finite_birational_fiberStalk_normalization [IsFinite f]
    (x : X) (y : {y : C // f y = x})
    [IsIntegrallyClosed (C.presheaf.stalk y.1)] :
    letI := (fiberStalkMap f x y).toAlgebra
    letI := (birationalStalkToField f hf y.1).toAlgebra
    letI := birationalStalk_isFractionRing f hf y.1
    letI := birationalFiberStalk_tower f hf x y
    letI := (integralClosureToNormal (X.presheaf.stalk x)
      (C.presheaf.stalk y.1) X.functionField).toRingHom.toAlgebra
    IsLocalization.AtPrime (C.presheaf.stalk y.1)
      ((IsLocalRing.maximalIdeal (C.presheaf.stalk y.1)).comap
        (integralClosureToNormal (X.presheaf.stalk x)
          (C.presheaf.stalk y.1) X.functionField).toRingHom) := by
  dsimp only
  rcases y with ⟨y,hy⟩
  subst x
  exact
    finite_birational_stalk_normalization f hf y
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne
open scoped nonZeroDivisors

lemma subalgebraFractionMap_eq {R K : Type*} [CommRing R] [Field K]
    [Algebra R K] [IsFractionRing R K] (B : Subalgebra R K) (φ : B →ₐ[R] K)
    (b : B) : φ b = b.1 := by
  have := (algebraMap R K).domain_nontrivial
  obtain ⟨⟨a,s⟩,he⟩ := IsLocalization.surj R⁰ b.1
  have hs : algebraMap R K s ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors s.2
  apply mul_right_cancel₀ hs
  have he' : b * algebraMap R B s = algebraMap R B a := Subtype.ext he
  have hφ := congrArg φ he'
  simp only [map_mul, AlgHom.commutes] at hφ
  exact hφ.trans he.symm
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne
variable (A B R S K : Type*) [CommRing A] [CommRing B] [CommRing R]
  [CommRing S] [Field K] [Algebra A B] [Algebra A R] [Algebra A S] [Algebra A K]
  [Algebra B S] [Algebra R S] [Algebra R K] [Algebra S K]
  [IsScalarTower A R K] [IsScalarTower R S K] [IsScalarTower A B S]
  [IsScalarTower A S K] [IsFractionRing A K] [IsFractionRing S K]
  [IsIntegrallyClosed S]

lemma integralClosureToNormal_comp_base
    (e : B ≃ₐ[A] integralClosure A K) (a : integralClosure A K) :
    integralClosureToNormal R S K (integralClosureBaseMap A R K a) =
      algebraMap B S (e.symm a) := by
  apply IsFractionRing.injective S K
  rw [integralClosureToNormal_map]
  let φ : integralClosure A K →ₐ[A] K :=
    { toRingHom := (algebraMap S K).comp ((algebraMap B S).comp e.symm.toRingHom)
      commutes' := fun a => by
        change algebraMap S K (algebraMap B S (e.symm (algebraMap A _ a))) = _
        rw [e.symm.commutes, ← IsScalarTower.algebraMap_apply A B S,
          ← IsScalarTower.algebraMap_apply A S K] }
  exact (subalgebraFractionMap_eq (integralClosure A K) φ a).symm

end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne
open AlgebraicGeometry CategoryTheory
open scoped nonZeroDivisors
variable {X : Scheme} [IsIntegral X] [QuasiSeparatedSpace X]
attribute [local instance] genericPointMap_quasiCompact

theorem genericNormalization_stalk_atPrime (sX : X ⟶ Spec (.of ℂ))
    [LocallyOfFiniteType sX] (U : X.Opens) (hU : IsAffineOpen U) (x : U)
    (y : {y : (X.fromSpecStalk (genericPoint X)).normalization //
      (X.fromSpecStalk (genericPoint X)).fromNormalization y = x.1}) :
    let N := (X.fromSpecStalk (genericPoint X)).normalization
    let f := (X.fromSpecStalk (genericPoint X)).fromNormalization
    let hf := genericNormalization_bijective_functionField (X := X)
    letI := (fiberStalkMap f x.1 y).toAlgebra
    letI := (birationalStalkToField f hf y.1).toAlgebra
    letI := birationalStalk_isFractionRing f hf y.1
    letI := birationalFiberStalk_tower f hf x.1 y
    letI := (genericNormalization_stalk y.1).2
    letI := (integralClosureToNormal (X.presheaf.stalk x.1)
      (N.presheaf.stalk y.1) X.functionField).toRingHom.toAlgebra
    IsLocalization.AtPrime (N.presheaf.stalk y.1)
      (((genericNormalizationFiberEquiv U hU x).symm y).1) := by
  let N := (X.fromSpecStalk (genericPoint X)).normalization
  let f := (X.fromSpecStalk (genericPoint X)).fromNormalization
  let hf := genericNormalization_bijective_functionField (X := X)
  let R := X.presheaf.stalk x.1
  let S := N.presheaf.stalk y.1
  let K := X.functionField
  let : Algebra R S := (fiberStalkMap f x.1 y).toAlgebra
  let : Algebra S K := (birationalStalkToField f hf y.1).toAlgebra
  have : IsFractionRing S K := birationalStalk_isFractionRing f hf y.1
  have : IsScalarTower R S K := birationalFiberStalk_tower f hf x.1 y
  have : IsIntegrallyClosed S := (genericNormalization_stalk y.1).2
  let D := integralClosure R K
  let : Algebra D S := (integralClosureToNormal R S K).toRingHom.toAlgebra
  have : IsFinite f := finite_genericNormalization sX
  have hs := finite_birational_fiberStalk_normalization f hf x.1 y
  let q := (IsLocalRing.maximalIdeal S).comap (integralClosureToNormal R S K).toRingHom
  change IsLocalization.AtPrime S q at hs
  have hq : q = ((genericNormalizationFiberEquiv U hU x).symm y).1 := by
    let : Nonempty U := ⟨x⟩
    let A := Γ(X,U)
    let V := f ⁻¹ᵁ U
    have hV : IsAffineOpen V := hU.preimage f
    have hy : y.1 ∈ V := by
      change f y.1 ∈ U
      rw [y.2]
      exact x.2
    let B := Γ(N,V)
    let C := integralClosure A K
    let : Algebra A R := X.presheaf.algebra_section_stalk x
    let : Algebra A B := (f.app U).hom.toAlgebra
    let : Algebra B S := N.presheaf.algebra_section_stalk ⟨y.1,hy⟩
    let : Algebra A S := ((algebraMap R S).comp (algebraMap A R)).toAlgebra
    have : IsScalarTower A R S := IsScalarTower.of_algebraMap_eq' rfl
    have : IsScalarTower A R K := functionField_isScalarTower X U x
    have : IsScalarTower A S K := IsScalarTower.to₁₃₄ A R S K
    have : IsScalarTower A B S := IsScalarTower.of_algebraMap_eq fun a =>
      fiberStalkMap_germ f U x y hy a
    let e : B ≃ₐ[A] C := genericNormalizationSectionsEquiv U hU
    let : Algebra C D := (integralClosureBaseMap A R K).toAlgebra
    have : IsScalarTower A C D := integralClosureBaseMap_tower A R K
    have : IsFractionRing A K := functionField_isFractionRing_of_isAffineOpen X U hU
    have : IsLocalization.AtPrime R (hU.primeIdealOf x).asIdeal := hU.isLocalization_stalk x
    let M := Algebra.algebraMapSubmonoid C (hU.primeIdealOf x).asIdeal.primeCompl
    have : IsLocalization M D := integralClosureBaseMap_isLocalization A R K _
      (hU.primeIdealOf x).asIdeal.primeCompl_le_nonZeroDivisors
    have : IsLocalization.AtPrime S (hV.primeIdealOf ⟨y.1,hy⟩).asIdeal :=
      hV.isLocalization_stalk ⟨y.1,hy⟩
    have hcomp : (integralClosureToNormal R S K).toRingHom.comp
        (integralClosureBaseMap A R K) = (algebraMap B S).comp e.symm.toRingHom := by
      ext a
      exact integralClosureToNormal_comp_base A B R S K e a
    have hqc : q.under C =
        (hV.primeIdealOf ⟨y.1,hy⟩).asIdeal.comap e.symm.toRingHom := by
      change ((IsLocalRing.maximalIdeal S).comap
        (integralClosureToNormal R S K).toRingHom).comap
        (integralClosureBaseMap A R K) = _
      rw [Ideal.comap_comap, hcomp, ← Ideal.comap_comap]
      exact congrArg (Ideal.comap e.symm.toRingHom)
        (IsLocalization.AtPrime.under_maximalIdeal S (hV.primeIdealOf ⟨y.1,hy⟩).asIdeal)
    calc
      q = (q.under C).map (algebraMap C D) := (IsLocalization.map_under M D q).symm
      _ = ((hV.primeIdealOf ⟨y.1,hy⟩).asIdeal.comap e.symm.toRingHom).map
          (integralClosureBaseMap A R K) := congrArg (Ideal.map (algebraMap C D)) hqc
      _ = ((genericNormalizationFiberEquiv U hU x).symm y).1 :=
        (genericNormalizationFiberEquiv_symm_asIdeal U hU x y).symm
  simpa only [hq] using hs

end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne
open scoped nonZeroDivisors

theorem finite_integralClosure_localization
    {A R K : Type*} [CommRing A] [IsDomain A] [CommRing R] [Field K]
    [Algebra A R] [Algebra A K] [Algebra R K] [IsScalarTower A R K]
    [IsFractionRing A K] (M : Submonoid A) (hM : M ≤ A⁰) [IsLocalization M R]
    [Module.Finite A (integralClosure A K)] :
    Module.Finite R (integralClosure R K) := by
  let C := integralClosure A K
  let D := integralClosure R K
  let φ : C →+* D :=
    { toFun := fun x => ⟨x.1,x.2.tower_top⟩
      map_one' := rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl
      map_mul' := fun _ _ => rfl }
  let : Algebra C D := φ.toAlgebra
  have : IsScalarTower C D K := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have : IsScalarTower A C D := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hunit : Algebra.algebraMapSubmonoid K M ≤ IsUnit.submonoid K := by
    rintro _ ⟨x,hx,rfl⟩
    exact isUnit_iff_ne_zero.mpr ((map_ne_zero_iff _ (IsFractionRing.injective A K)).mpr
      (mem_nonZeroDivisors_iff_ne_zero.mp (hM hx)))
  let : IsLocalization (Algebra.algebraMapSubmonoid K M) K := IsLocalization.self hunit
  let : IsLocalization (Algebra.algebraMapSubmonoid C M) D :=
    IsLocalization.integralClosure M
  exact Module.Finite.of_isLocalization A C M
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne
open AlgebraicGeometry CategoryTheory
variable {k : Type*} [Field k] [CharZero k]
  {X : Scheme} [IsIntegral X]

theorem finite_integralClosure_stalk (sX : X ⟶ Spec (.of k))
    [LocallyOfFiniteType sX] (x : X) :
    Module.Finite (X.presheaf.stalk x)
      (integralClosure (X.presheaf.stalk x) X.functionField) := by
  obtain ⟨U,hU,hx,_hUtop⟩ := exists_isAffineOpen_mem_and_subset (show x ∈ (⊤ : X.Opens) from trivial)
  let : Nonempty U := ⟨⟨x,hx⟩⟩
  let A := Γ(X,U)
  let : Algebra k A :=
    ((sX.appLE ⊤ U (by simp)).hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom).toAlgebra
  have : Algebra.FiniteType k A :=
    (sX.finiteType_appLE (isAffineOpen_top _) hU (by simp)).comp
      (RingHom.FiniteType.of_surjective _ (ConcreteCategory.bijective_of_isIso
        (Scheme.ΓSpecIso (.of k)).inv).2)
  let := TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨x,hx⟩
  have := hU.isLocalization_stalk ⟨x,hx⟩
  have := functionField_isFractionRing_of_isAffineOpen X U hU
  have := functionField_isScalarTower X U ⟨x,hx⟩
  have : Module.Finite A (integralClosure A X.functionField) :=
    finite_integralClosure_of_finiteType k A X.functionField
  exact finite_integralClosure_localization
    (hU.primeIdealOf ⟨x,hx⟩).asIdeal.primeCompl
    (hU.primeIdealOf ⟨x,hx⟩).asIdeal.primeCompl_le_nonZeroDivisors
end NumericalDimensionOne

end OAI
