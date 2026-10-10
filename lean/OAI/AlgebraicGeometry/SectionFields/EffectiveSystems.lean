import Mathlib
import OAI.AlgebraicGeometry.SectionFields.Recovery

namespace OAI

/-! Complete linear systems, rational maps and geometric effective-base definitions. -/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Order Polynomial
open scoped TensorProduct WithZero
universe u

namespace RelativeDenominators.EffectiveBase

 

structure ComplexVariety where
  scheme : Scheme
  structural : scheme ⟶ Spec (CommRingCat.of ℂ)
  integral : IsIntegral scheme
  finiteType : LocallyOfFiniteType structural
  quasiCompact : QuasiCompact structural

attribute [instance] ComplexVariety.integral ComplexVariety.finiteType
  ComplexVariety.quasiCompact

namespace ComplexVariety

instance (X : ComplexVariety) : IsNoetherian X.scheme where
  toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian X.structural
  toCompactSpace := QuasiCompact.compactSpace_of_compactSpace X.structural

 
def IsNormal (X : ComplexVariety) : Prop :=
  ∀ x : X.scheme, IsIntegrallyClosed (X.scheme.presheaf.stalk x)

 
def scalarMap (X : ComplexVariety) (x : X.scheme) :
    ℂ →+* X.scheme.presheaf.stalk x :=
  ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv ≫ X.structural.appTop ≫
    X.scheme.presheaf.germ ⊤ x (by trivial)).hom

instance stalkComplexAlgebra (X : ComplexVariety) (x : X.scheme) :
    Algebra ℂ (X.scheme.presheaf.stalk x) := (X.scalarMap x).toAlgebra

instance functionFieldComplexAlgebra (X : ComplexVariety) :
    Algebra ℂ X.scheme.functionField :=
  stalkComplexAlgebra X (genericPoint X.scheme)

instance stalkFunctionFieldTower (X : ComplexVariety) (x : X.scheme) :
    IsScalarTower ℂ (X.scheme.presheaf.stalk x) X.scheme.functionField := by
  apply IsScalarTower.of_algebraMap_eq'
  change (X.scalarMap (genericPoint X.scheme)) =
    (algebraMap (X.scheme.presheaf.stalk x) X.scheme.functionField).comp (X.scalarMap x)
  change ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv ≫ X.structural.appTop ≫
    X.scheme.presheaf.germ ⊤ (genericPoint X.scheme) (by trivial)).hom =
    ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv ≫ X.structural.appTop ≫
      X.scheme.presheaf.germ ⊤ x (by trivial) ≫
      X.scheme.presheaf.stalkSpecializes
        ((genericPoint_spec X.scheme).specializes (Set.mem_univ x))).hom
  congr 1
  erw [TopCat.Presheaf.germ_stalkSpecializes]

end ComplexVariety

attribute [local instance] MvPolynomial.gradedAlgebra

 
def projectiveSpace (n : ℕ) : Scheme :=
  Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) ℂ)

 
def constantToDegreeZero (n : ℕ) :
    ℂ →+* MvPolynomial.homogeneousSubmodule (Fin (n + 1)) ℂ 0 where
  toFun z := ⟨MvPolynomial.C z, MvPolynomial.isHomogeneous_C _ z⟩
  map_one' := Subtype.ext (map_one MvPolynomial.C)
  map_zero' := Subtype.ext (map_zero MvPolynomial.C)
  map_mul' x y := Subtype.ext (map_mul MvPolynomial.C x y)
  map_add' x y := Subtype.ext (map_add MvPolynomial.C x y)

def projectiveSpaceStructural (n : ℕ) :
    projectiveSpace n ⟶ Spec (CommRingCat.of ℂ) :=
  Proj.toSpecZero (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) ℂ) ≫
    Spec.map (CommRingCat.ofHom (constantToDegreeZero n))

 
def ComplexVariety.IsProjective (X : ComplexVariety) : Prop :=
  ∃ n : ℕ, ∃ e : X.scheme ⟶ projectiveSpace n,
    IsClosedImmersion e ∧ e ≫ projectiveSpaceStructural n = X.structural

 
def IsProjectiveMorphism (X Z : ComplexVariety) (f : X.scheme ⟶ Z.scheme) : Prop :=
  ∃ n : ℕ, ∃ e : X.scheme ⟶ pullback Z.structural (projectiveSpaceStructural n),
    IsClosedImmersion e ∧ e ≫ pullback.fst _ _ = f

 

structure Contraction (X Z : ComplexVariety) where
  morphism : X.scheme ⟶ Z.scheme
  over_base : morphism ≫ Z.structural = X.structural
  projective : IsProjectiveMorphism X Z morphism
  surjective : Surjective morphism
  sheaf_iso : IsIso morphism.c

attribute [instance] Contraction.surjective Contraction.sheaf_iso

 
def rationalize (X : Scheme) (K : WeilDivisor X) : RationalWeilDivisor X :=
  K.mapRange (Int.castRingHom ℚ) (by simp)

 
def exteriorPullback {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    {V W : Type*} [AddCommGroup V] [AddCommGroup W] [Module R V] [Module S W]
    [Module R W] [IsScalarTower R S W] (d : ℕ) (f : V →ₗ[R] W) :
    (⋀[R]^d V) →ₗ[R] (⋀[S]^d W) := by
  let a : W [⋀^Fin d]→ₗ[R] (⋀[S]^d W) :=
    { toMultilinearMap := (exteriorPower.ιMulti S d).toMultilinearMap.restrictScalars R
      map_eq_zero_of_eq' := fun v i j hv hij =>
        (exteriorPower.ιMulti S d).map_eq_zero_of_eq v hv hij }
  exact exteriorPower.alternatingMapLinearEquiv (a.compLinearMap f)

abbrev RationalTopForms (X : ComplexVariety) (d : ℕ) :=
  ⋀[X.scheme.functionField]^d Ω[X.scheme.functionField⁄ℂ]

 

def RegularAt (X : ComplexVariety) (d : ℕ) (x : X.scheme)
    (ω : RationalTopForms X d) : Prop :=
  ∃ α : ⋀[X.scheme.presheaf.stalk x]^d Ω[X.scheme.presheaf.stalk x⁄ℂ],
    exteriorPullback (S := X.scheme.functionField) d
      (KaehlerDifferential.map ℂ ℂ (X.scheme.presheaf.stalk x) X.scheme.functionField) α = ω

 

def IsDivisorOfForm (X : ComplexVariety) (d : ℕ) (ω : RationalTopForms X d)
    (K : WeilDivisor X.scheme) : Prop :=
  ω ≠ 0 ∧ ∀ x : PrimeDivisor X.scheme, ∀ v : X.scheme.functionFieldˣ,
    RegularAt X d x.1 ((v : X.scheme.functionField) • ω) ↔
      0 ≤ X.scheme.ord (v : X.scheme.functionField) x.1 + K x

 

structure BirationalModel (X : ComplexVariety) where
  variety : ComplexVariety
  normal : variety.IsNormal
  morphism : variety.scheme ⟶ X.scheme
  proper : IsProper morphism
  over_base : morphism ≫ X.structural = variety.structural
  dominant : IsDominant morphism
  fieldEquiv : X.scheme.functionField ≃ₐ[ℂ] variety.scheme.functionField
  induced : fieldEquiv.toRingEquiv.toRingHom =
    @functionFieldPullback _ _ variety.integral X.integral morphism dominant

attribute [instance] BirationalModel.dominant

 
def fieldPullback {K L : Type*} [Field K] [Field L] [Algebra ℂ K] [Algebra ℂ L]
    (e : K ≃ₐ[ℂ] L) (d : ℕ) : (⋀[K]^d Ω[K⁄ℂ]) → (⋀[L]^d Ω[L⁄ℂ]) := by
  letI : Algebra K L := e.toRingEquiv.toRingHom.toAlgebra
  letI : IsScalarTower ℂ K L := IsScalarTower.of_algebraMap_eq' (by
    ext z
    exact (e.commutes z).symm)
  exact fun ω => exteriorPullback (S := L) d (KaehlerDifferential.map ℂ ℂ K L) ω

 

def IsLogCanonical (X : ComplexVariety) (hNX : X.IsNormal) (d : ℕ)
    (ω : RationalTopForms X d) (K : WeilDivisor X.scheme)
    (B : RationalWeilDivisor X.scheme)
    (hAdj : IsQCartier X.scheme (rationalize X.scheme K + B)) : Prop :=
  IsDivisorOfForm X d ω K ∧ (∀ E, 0 ≤ B E) ∧
  ∀ Y : BirationalModel X, ∃ KY : WeilDivisor Y.variety.scheme,
    IsDivisorOfForm Y.variety d (fieldPullback Y.fieldEquiv d ω) KY ∧
    ∀ E : PrimeDivisor Y.variety.scheme,
      (-1 : ℚ) ≤ (KY E : ℚ) -
        pullbackQCartier hNX Y.morphism (rationalize X.scheme K + B) hAdj E

 
def CoefficientsIn {X : Scheme} (B : RationalWeilDivisor X) (Φ : Finset ℚ) : Prop :=
  ∀ E : PrimeDivisor X, B E ≠ 0 → B E ∈ Φ

 

def sectionSpace (X : ComplexVariety) (A : RationalWeilDivisor X.scheme) :
    Submodule ℂ X.scheme.functionField :=
  Submodule.span ℂ ((fun u : X.scheme.functionFieldˣ => (u : X.scheme.functionField)) ''
    divisorialSections X.scheme A)

 

def IsBig (X : ComplexVariety) (A : RationalWeilDivisor X.scheme) : Prop :=
  ∃ e : ℕ, topologicalKrullDim X.scheme = e ∧
    ∃ c : ℝ, 0 < c ∧ ∀ N : ℕ, ∃ n : ℕ, N < n ∧
      c * (n : ℝ) ^ e ≤ (Module.finrank ℂ (sectionSpace X ((n : ℚ) • A)) : ℝ)

 
def IsSectionBasis (X : ComplexVariety) (A : RationalWeilDivisor X.scheme)
    (n : ℕ) (b : Fin (n + 1) → X.scheme.functionFieldˣ) : Prop :=
  (∀ i, b i ∈ divisorialSections X.scheme A) ∧
  LinearIndependent ℂ (fun i => (b i : X.scheme.functionField)) ∧
  Submodule.span ℂ (Set.range (fun i => (b i : X.scheme.functionField))) = sectionSpace X A

 

def coordinatesEvaluation (X : ComplexVariety) (n : ℕ)
    (b : Fin (n + 1) → X.scheme.functionFieldˣ) :
    MvPolynomial (Fin (n + 1)) ℂ →+* Γ(Spec X.scheme.functionField, ⊤) :=
  (Scheme.ΓSpecIso X.scheme.functionField).inv.hom.comp
    (MvPolynomial.eval₂Hom (algebraMap ℂ X.scheme.functionField)
      (fun i => (b i : X.scheme.functionField)))

 
theorem coordinates_irrelevant_eq_top (X : ComplexVariety) (n : ℕ)
    (b : Fin (n + 1) → X.scheme.functionFieldˣ) :
    (HomogeneousIdeal.irrelevant (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) ℂ)).toIdeal.map
      (coordinatesEvaluation X n b) = ⊤ := by
  let i : Fin (n + 1) := ⟨0, Nat.succ_pos n⟩
  apply Ideal.eq_top_of_isUnit_mem (x := coordinatesEvaluation X n b (MvPolynomial.X i))
  · apply Ideal.mem_map_of_mem
    exact HomogeneousIdeal.mem_irrelevant_of_mem _ (by decide : 0 < (1 : ℕ))
      (MvPolynomial.isHomogeneous_X ℂ i)
  · change IsUnit ((Scheme.ΓSpecIso X.scheme.functionField).inv.hom
      ((MvPolynomial.eval₂Hom (algebraMap ℂ X.scheme.functionField)
        (fun j => (b j : X.scheme.functionField))) (MvPolynomial.X i)))
    simp only [MvPolynomial.eval₂Hom_X']
    exact (b i).isUnit.map _

 
def projectiveGenericPoint (X : ComplexVariety) (n : ℕ)
    (b : Fin (n + 1) → X.scheme.functionFieldˣ) :
    Spec X.scheme.functionField ⟶ projectiveSpace n :=
  Proj.fromOfGlobalSections (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) ℂ)
    (coordinatesEvaluation X n b) (coordinates_irrelevant_eq_top X n b)

 

def IsCompleteSystemMap (X : ComplexVariety) (A : RationalWeilDivisor X.scheme)
    (Y : ComplexVariety) (φ : X.scheme ⤏ Y.scheme) : Prop :=
  φ.compHom Y.structural = X.structural.toRationalMap ∧
  IsDominant φ.fromFunctionField ∧
  ∃ n : ℕ, ∃ b : Fin (n + 1) → X.scheme.functionFieldˣ,
    IsSectionBasis X A n b ∧
    ∃ e : Y.scheme ⟶ projectiveSpace n,
      IsClosedImmersion e ∧ e ≫ projectiveSpaceStructural n = Y.structural ∧
      φ.fromFunctionField ≫ e = projectiveGenericPoint X n b

 

def BirationallyEquivalentMaps (X Y Z : ComplexVariety)
    (φ : X.scheme ⤏ Y.scheme) (ψ : X.scheme ⤏ Z.scheme) : Prop :=
  ∃ U : Y.scheme.Opens, ∃ V : Z.scheme.Opens,
    Dense (U : Set Y.scheme) ∧ Dense (V : Set Z.scheme) ∧
    ∃ e : U.toScheme ≅ V.toScheme,
      e.hom ≫ V.ι ≫ Z.structural = U.ι ≫ Y.structural ∧
      ∃ t : Spec X.scheme.functionField ⟶ U.toScheme,
        t ≫ U.ι = φ.fromFunctionField ∧
        t ≫ e.hom ≫ V.ι = ψ.fromFunctionField

 

def IsIitakaFibration (X : ComplexVariety) (A : RationalWeilDivisor X.scheme)
    (I : ComplexVariety) (ι : X.scheme ⤏ I.scheme) : Prop :=
  I.IsNormal ∧ I.IsProjective ∧
  ι.compHom I.structural = X.structural.toRationalMap ∧
  IsDominant ι.fromFunctionField ∧
  ∃ r : ℕ, 0 < r ∧ ∀ k : ℕ, 0 < k →
    ∃ Y : ComplexVariety, ∃ φ : X.scheme ⤏ Y.scheme,
      IsCompleteSystemMap X (((r * k : ℕ) : ℚ) • A) Y φ ∧
      BirationallyEquivalentMaps X Y I φ ι

 

def RecoversBaseAndIitaka (X Z : ComplexVariety) (f : Contraction X Z)
    (A : RationalWeilDivisor X.scheme) (l : ℕ) : Prop :=
  (divisorialSections X.scheme ((l : ℚ) • A)).Nonempty ∧
  sectionField X.scheme ((l : ℚ) • A) = (functionFieldPullback f.morphism).fieldRange ∧
  ∃ Y : ComplexVariety, ∃ φ : X.scheme ⤏ Y.scheme,
    IsCompleteSystemMap X ((l : ℚ) • A) Y φ ∧
    BirationallyEquivalentMaps X Y Z φ f.morphism.toRationalMap ∧
    ∃ I : ComplexVariety, ∃ ι : X.scheme ⤏ I.scheme,
      IsIitakaFibration X A I ι ∧ BirationallyEquivalentMaps X Y I φ ι

end RelativeDenominators.EffectiveBase
end

end OAI
