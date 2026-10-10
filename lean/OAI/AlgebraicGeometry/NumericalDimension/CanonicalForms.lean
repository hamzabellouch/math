import Mathlib
import OAI.AlgebraicGeometry.NumericalDimension.RationalPullbacks

namespace OAI

/-! Canonical Forms. -/

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct

namespace NumericalDimensionOne
section CanonicalDivisors
universe u
variable (k : CommRingCat.{u}) {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]

noncomputable abbrev rationalTopForms (sX : X ⟶ Spec k) (n : ℕ) :=
  letI := schemeFieldAlgebra k sX
  ⋀[X.functionField]^n Ω[X.functionField⁄k]

def IsCanonicalDivisorOf (sX : X ⟶ Spec k) (n : ℕ)
    (ω : rationalTopForms k sX n) (D : WeilDivisor X) : Prop :=
  ω ≠ 0 ∧ ∀ p : PrimeDivisor X,
    letI := schemeStalkAlgebra k sX p.1
    letI := schemeFieldAlgebra k sX
    letI := stalk_field_scalar_tower k sX p.1
    ∃ b : Module.Basis (Fin 1) (X.presheaf.stalk p.1)
        (⋀[X.presheaf.stalk p.1]^n Ω[X.presheaf.stalk p.1⁄k]),
    ∃ a : X.functionField, a ≠ 0 ∧
      ω = a • topDifferentialMap k (X.presheaf.stalk p.1) X.functionField n (b 0) ∧
      D p = X.ord a p.1

def IsCanonicalDivisor (sX : X ⟶ Spec k) (n : ℕ) (D : WeilDivisor X) : Prop :=
  ∃ ω : rationalTopForms k sX n, IsCanonicalDivisorOf k sX n ω D

end CanonicalDivisors
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct

namespace NumericalDimensionOne
section AmpleForMain
variable {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X] [CompactSpace X]

def divisorSupport (D : WeilDivisor X) : Set X :=
  ⋃ p ∈ D.support, closure ({p.1} : Set X)

omit [IsIntegral X] [IsLocallyNoetherian X] [CompactSpace X] in
lemma isClosed_divisorSupport (D : WeilDivisor X) : IsClosed (divisorSupport D) := by
  exact D.support.finite_toSet.isClosed_biUnion (fun p _ => isClosed_closure)

def divisorComplement (D : WeilDivisor X) : X.Opens :=
  ⟨(divisorSupport D)ᶜ, (isClosed_divisorSupport D).isOpen_compl⟩

noncomputable def sectionNonvanishing (D : WeilDivisor X) (f : X.functionField) : X.Opens :=
  divisorComplement (principalWeilDivisor f + D)

def IsAmpleDivisor (D : WeilDivisor X) : Prop :=
  IsCartierDivisor D ∧ ∀ (x : X) (U : X.Opens), x ∈ U →
    ∃ m : ℕ, 0 < m ∧ ∃ f : X.functionField, f ≠ 0 ∧
      IsDivisorSection (m • D) f ∧ IsAffineOpen (sectionNonvanishing (m • D) f) ∧
      x ∈ sectionNonvanishing (m • D) f ∧ sectionNonvanishing (m • D) f ≤ U

end AmpleForMain
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct

namespace NumericalDimensionOne
section SectionModules
variable {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X] [StalkwiseNormal X]
variable (R : CommRingCat)

noncomputable def divisorSectionsOver (sX : X ⟶ Spec R) (D : WeilDivisor X) :
    letI := schemeFieldAlgebra R sX
    Submodule R X.functionField := by
  letI := schemeFieldAlgebra R sX
  exact
    { carrier := {r | IsDivisorSection D r}
      zero_mem' := Or.inl rfl
      add_mem' := divisorSection_add
      smul_mem' := fun a r hr =>
        divisorSection_smul (sX.appTop ((Scheme.ΓSpecIso R).inv a)) hr }

end SectionModules
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct

namespace NumericalDimensionOne

instance projectiveVariety_proper (X : ComplexProjectiveVariety) :
    IsProper X.structureMap := isProper_of_isComplexProjective X.structureMap X.projective

instance projectiveVariety_locallyNoetherian (X : ComplexProjectiveVariety) :
    IsLocallyNoetherian X.scheme := LocallyOfFiniteType.isLocallyNoetherian X.structureMap

instance projectiveVariety_compact (X : ComplexProjectiveVariety) :
    CompactSpace X.scheme := QuasiCompact.compactSpace_of_compactSpace X.structureMap

lemma smoothNormal (X : ComplexProjectiveVariety) {n : ℕ} (hn : IsSmoothNfold X n) :
    StalkwiseNormal X.scheme := by
  let : SmoothOfRelativeDimension n X.structureMap := hn
  let : Smooth X.structureMap := SmoothOfRelativeDimension.smooth n X.structureMap
  exact ⟨integrallyClosed_stalk_of_smooth_field X.structureMap⟩

structure CurveOn (X : ComplexProjectiveVariety) where
  curve : ComplexProjectiveVariety
  smooth : IsSmoothNfold curve 1
  morphism : curve.scheme ⟶ X.scheme
  overComplex : morphism ≫ X.structureMap = curve.structureMap

instance curveOn_normal {X : ComplexProjectiveVariety} (C : CurveOn X) :
    StalkwiseNormal C.curve.scheme := smoothNormal C.curve C.smooth

def complexWeilDegree {X : Scheme} (D : WeilDivisor X) : ℤ := D.sum fun _ a => a

noncomputable def pulledCartierRepresentative {X : ComplexProjectiveVariety}
    [StalkwiseNormal X.scheme] (C : CurveOn X) (D : WeilDivisor X.scheme)
    (hD : IsCartierDivisor D) : WeilDivisor C.curve.scheme :=
  Classical.choose (exists_pulledCartierRepresentative C.morphism D hD)

lemma pulledCartierRepresentative_spec {X : ComplexProjectiveVariety}
    [StalkwiseNormal X.scheme] (C : CurveOn X) (D : WeilDivisor X.scheme)
    (hD : IsCartierDivisor D) :
    IsPulledCartierRepresentative C.morphism D (pulledCartierRepresentative C D hD) :=
  Classical.choose_spec (exists_pulledCartierRepresentative C.morphism D hD)

noncomputable def cartierCurveDegree {X : ComplexProjectiveVariety}
    [StalkwiseNormal X.scheme] (D : cartierDivisors (X := X.scheme)) (C : CurveOn X) : ℤ :=
  complexWeilDegree (pulledCartierRepresentative C D.1 D.2)

end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct

namespace NumericalDimensionOne
section MainNumericalDefinitions
open Filter
open scoped ENNReal

variable (X : ComplexProjectiveVariety) [StalkwiseNormal X.scheme]

noncomputable def sectionDimension (D : WeilDivisor X.scheme) : ℝ≥0∞ := by
  letI := schemeFieldAlgebra (.of ℂ) X.structureMap
  exact (Cardinal.toENat (Module.rank ℂ (divisorSectionsOver (.of ℂ) X.structureMap D))).toENNReal

noncomputable def divisorSectionLimsup (D A : WeilDivisor X.scheme) (k : ℕ) : ℝ≥0∞ :=
  Filter.limsup (fun m : ℕ => sectionDimension X (m • D + A) / (m : ℝ≥0∞) ^ k) atTop

noncomputable def kappaSigma (n : ℕ) (D : WeilDivisor X.scheme) : WithBot ℕ := by
  classical
  exact ((Finset.range (n + 1)).filter (fun k =>
    ∃ A : WeilDivisor X.scheme, IsAmpleDivisor A ∧ 0 < divisorSectionLimsup X D A k)).sup
      (fun k : ℕ => (k : WithBot ℕ))

noncomputable def cartierNumericalVector (D : cartierDivisors (X := X.scheme)) :
    CurveOn X → ℝ := fun C => cartierCurveDegree D C

def effectiveNumericalCone : Set (CurveOn X → ℝ) :=
  {v | ∃ r : ℕ, ∃ D : Fin r → cartierDivisors (X := X.scheme), ∃ a : Fin r → ℝ,
    (∀ i, 0 ≤ a i) ∧ (∀ i, 0 ≤ (D i).1) ∧
    v = fun C => ∑ i, a i * cartierNumericalVector X (D i) C}

def IsPseudoEffective (D : cartierDivisors (X := X.scheme)) : Prop :=
  cartierNumericalVector X D ∈ closure (effectiveNumericalCone X)

def IsNefCartier (D : cartierDivisors (X := X.scheme)) : Prop :=
  ∀ C : CurveOn X, 0 ≤ cartierCurveDegree D C

end MainNumericalDefinitions

abbrev QWeilDivisor (X : Scheme) := PrimeDivisor X →₀ ℚ

noncomputable def rationalWeilDivisor {X : Scheme} (D : WeilDivisor X) : QWeilDivisor X :=
  D.mapRange (Int.castAddHom ℚ) (map_zero _)

section RationalCartier
variable {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X]

def IsQCartierDivisor (D : QWeilDivisor X) : Prop :=
  ∃ m : ℕ, 0 < m ∧ ∃ A : WeilDivisor X,
    IsCartierDivisor A ∧ (m : ℚ) • D = rationalWeilDivisor A

def IsQFactorial : Prop :=
  ∀ D : WeilDivisor X, IsQCartierDivisor (rationalWeilDivisor D)

variable [CompactSpace X]

def IsAmpleQDivisor (D : QWeilDivisor X) : Prop :=
  ∃ m : ℕ, 0 < m ∧ ∃ A : WeilDivisor X,
    IsAmpleDivisor A ∧ (m : ℚ) • D = rationalWeilDivisor A

end RationalCartier

def IsNefQDivisor (X : ComplexProjectiveVariety) [StalkwiseNormal X.scheme]
    (D : QWeilDivisor X.scheme) : Prop :=
  IsQCartierDivisor D ∧ ∀ (m : ℕ) (_hm : 0 < m) (A : WeilDivisor X.scheme)
    (hA : IsCartierDivisor A), (m : ℚ) • D = rationalWeilDivisor A →
      IsNefCartier X ⟨A, hA⟩

def IsQCartierPullback {X Y : Scheme} [IsIntegral X] [IsIntegral Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (f : X ⟶ Y) [IsDominant f] (D : QWeilDivisor Y) (E : QWeilDivisor X) : Prop :=
  ∃ m : ℕ, 0 < m ∧ ∃ A : WeilDivisor Y, ∃ B : WeilDivisor X,
    IsCartierDivisor A ∧ (m : ℚ) • D = rationalWeilDivisor A ∧
    (m : ℚ) • E = rationalWeilDivisor B ∧ IsCartierPullback f A B

end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct

namespace NumericalDimensionOne
section DominantCanonicalScalars
variable {X Y : Scheme} [IsIntegral X] [IsIntegral Y]

lemma dominantFunctionFieldMap_section (f : X ⟶ Y) [IsDominant f]
    (a : Γ(Y, ⊤)) :
    dominantFunctionFieldMap f (Y.germToFunctionField ⊤ a) =
      X.germToFunctionField ⊤ (f.appTop a) := by
  let x : X := Classical.arbitrary X
  rw [← Y.algebraMap_germ_eq_germToFunctionField (x := f x) (by trivial),
    dominantFunctionFieldMap_algebraMap]
  exact (congrArg (algebraMap (X.presheaf.stalk x) X.functionField)
    (f.germ_stalkMap_apply ⊤ x (by trivial) a)).trans
      (X.algebraMap_germ_eq_germToFunctionField (U := ⊤) (x := x) (by trivial) _)

lemma dominantFunctionFieldMap_scalar (k : CommRingCat)
    (sX : X ⟶ Spec k) (sY : Y ⟶ Spec k) (f : X ⟶ Y) [IsDominant f]
    (hf : f ≫ sY = sX) (a : k) :
    dominantFunctionFieldMap f (schemeFieldScalar k sY a) =
      schemeFieldScalar k sX a := by
  change dominantFunctionFieldMap f
    (Y.germToFunctionField ⊤ (sY.appTop ((Scheme.ΓSpecIso k).inv a))) = _
  rw [dominantFunctionFieldMap_section]
  have h := congrArg (fun t : X ⟶ Spec k =>
    t.appTop ((Scheme.ΓSpecIso k).inv a)) hf
  exact congrArg (X.germToFunctionField ⊤) h

noncomputable def rationalTopFormPullback (k : CommRingCat)
    (sX : X ⟶ Spec k) (sY : Y ⟶ Spec k) (f : X ⟶ Y) [IsDominant f]
    (hf : f ≫ sY = sX) (n : ℕ) :
    rationalTopForms k sY n → rationalTopForms k sX n := by
  letI := schemeFieldAlgebra k sX
  letI := schemeFieldAlgebra k sY
  letI : Algebra Y.functionField X.functionField := (dominantFunctionFieldMap f).toAlgebra
  letI : IsScalarTower k Y.functionField X.functionField :=
    IsScalarTower.of_algebraMap_eq (fun a => (dominantFunctionFieldMap_scalar k sX sY f hf a).symm)
  exact fun ω => topDifferentialMap k Y.functionField X.functionField n ω

end DominantCanonicalScalars
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct

namespace NumericalDimensionOne

structure NormalProjectiveVariety extends ComplexProjectiveVariety where
  normal : StalkwiseNormal scheme

attribute [instance] NormalProjectiveVariety.normal

def IsBirationalMorphism {X Y : Scheme} (f : X ⟶ Y) : Prop :=
  ∃ φ : X.PartialIso Y, φ.IsOver f (𝟙 Y)

structure CanonicalModel (n : ℕ) extends NormalProjectiveVariety where
  form : rationalTopForms (.of ℂ) structureMap n
  canonical : WeilDivisor scheme
  canonical_of_form :
    letI : IsLocallyNoetherian scheme :=
      projectiveVariety_locallyNoetherian toComplexProjectiveVariety
    IsCanonicalDivisorOf (.of ℂ) structureMap n form canonical
  qCartier :
    letI : IsLocallyNoetherian scheme :=
      projectiveVariety_locallyNoetherian toComplexProjectiveVariety
    IsQCartierDivisor (rationalWeilDivisor canonical)

def IsTerminalModel {n : ℕ} (Y : CanonicalModel n) : Prop :=
  ∀ W : ComplexProjectiveVariety, IsSmoothNfold W n →
    ∀ f : W.scheme ⟶ Y.scheme, ∀ (_ : IsDominant f),
      IsProper f → IsBirationalMorphism f →
      ∀ hf : f ≫ Y.structureMap = W.structureMap,
        ∀ KW : WeilDivisor W.scheme,
          IsCanonicalDivisorOf (.of ℂ) W.structureMap n
            (rationalTopFormPullback (.of ℂ) W.structureMap Y.structureMap f hf n Y.form) KW →
          ∀ P : QWeilDivisor W.scheme,
            IsQCartierPullback f (rationalWeilDivisor Y.canonical) P →
            ∀ p : PrimeDivisor W.scheme, 1 < Order.coheight (f p.1) →
              0 < (rationalWeilDivisor KW - P) p

def IsCurveContracted {X R : ComplexProjectiveVariety}
    (f : X.scheme ⟶ R.scheme) (C : CurveOn X) : Prop :=
  ∃ r : R.scheme, ∀ x : C.curve.scheme, f (C.morphism x) = r

noncomputable def relativeNumericalSpace {X R : ComplexProjectiveVariety}
    [StalkwiseNormal X.scheme] (f : X.scheme ⟶ R.scheme) :
    Submodule ℝ ({C : CurveOn X // IsCurveContracted f C} → ℝ) :=
  Submodule.span ℝ (Set.range (fun D : cartierDivisors (X := X.scheme) =>
    fun C : {C : CurveOn X // IsCurveContracted f C} => cartierNumericalVector X D C.1))

def IsElementary {X R : ComplexProjectiveVariety}
    [StalkwiseNormal X.scheme] (f : X.scheme ⟶ R.scheme) : Prop :=
  Module.rank ℝ (relativeNumericalSpace f) = 1

def IsRelativelyAmpleQ {X R : ComplexProjectiveVariety}
    (f : X.scheme ⟶ R.scheme) [IsDominant f] (D : QWeilDivisor X.scheme) : Prop :=
  ∃ A : WeilDivisor R.scheme, IsAmpleDivisor A ∧
    ∃ E : WeilDivisor X.scheme, IsCartierPullback f A E ∧
      IsAmpleQDivisor (D + rationalWeilDivisor E)

def IsSmallMorphism {X Y : Scheme} (f : X ⟶ Y) : Prop :=
  ∀ p : PrimeDivisor X, Order.coheight (f p.1) = 1

end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct

namespace NumericalDimensionOne
section ExteriorBaseChange
open scoped TensorProduct
variable {R S M N : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
    [Module S N] [IsScalarTower R S N]

theorem isBaseChange_of_basis {I : Type*} (b : Module.Basis I R M)
    (c : Module.Basis I S N) (f : M →ₗ[R] N)
    (hf : ∀ i, f (b i) = c i) : IsBaseChange S f := by
  let bt := (TensorProduct.isBaseChange R M S).basis b
  let e := bt.equiv c (Equiv.refl I)
  apply IsBaseChange.of_equiv e
  have he : (e.toLinearMap.restrictScalars R).comp (TensorProduct.mk R S M 1) = f := by
    apply b.ext
    intro i
    change e (1 ⊗ₜ[R] b i) = f (b i)
    have ht : bt i = 1 ⊗ₜ[R] b i := (TensorProduct.isBaseChange R M S).basis_apply b i
    rw [← ht]
    exact (bt.equiv_apply i c (Equiv.refl I)).trans (hf i).symm
  exact LinearMap.congr_fun he

end ExteriorBaseChange

section TopBaseChange
variable (k A B : Type*) [CommRing k] [CommRing A] [CommRing B]
    [Algebra k A] [Algebra k B] [Algebra A B] [IsScalarTower k A B]

theorem topDifferential_isBaseChange [Module.Free A Ω[A⁄k]]
    [Algebra.FormallyEtale A B] (n : ℕ) :
    IsBaseChange B (topDifferentialMap k A B n) := by
  classical
  let I := Module.Free.ChooseBasisIndex A Ω[A⁄k]
  let : LinearOrder I := linearOrderOfSTO WellOrderingRel
  let b := Module.Free.chooseBasis A Ω[A⁄k]
  let h := KaehlerDifferential.isBaseChange_of_formallyEtale k A B
  apply isBaseChange_of_basis (b.exteriorPower n) ((h.basis b).exteriorPower n)
  intro i
  simp only [exteriorPower.basis_apply, exteriorPower.ιMulti_family,
    topDifferentialMap_ιMulti]
  congr 1
  funext j
  exact (h.basis_apply b _).symm

end TopBaseChange
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct

namespace NumericalDimensionOne

theorem nonempty_topDifferential_basis (k A : Type*) [CommRing k] [CommRing A]
    [Algebra k A] [Nontrivial A] (n : ℕ)
    [Algebra.IsStandardSmoothOfRelativeDimension n k A] :
    Nonempty (Module.Basis (Fin 1) A (⋀[A]^n Ω[A⁄k])) := by
  let : Algebra.IsStandardSmooth k A :=
    Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth n
  have h : Module.finrank A (⋀[A]^n Ω[A⁄k]) = 1 := by
    rw [exteriorPower.finrank_eq,
      Module.finrank_eq_of_rank_eq
        (Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential n),
      Nat.choose_self]
  exact ⟨(Module.finBasis A (⋀[A]^n Ω[A⁄k])).reindex (finCongr h)⟩

theorem nonempty_localized_topDifferential_basis (k A B : Type*)
    [CommRing k] [CommRing A] [CommRing B] [Algebra k A] [Algebra k B]
    [Algebra A B] [IsScalarTower k A B] [Nontrivial A] (n : ℕ)
    [Algebra.IsStandardSmoothOfRelativeDimension n k A]
    (S : Submonoid A) [IsLocalization S B] :
    Nonempty (Module.Basis (Fin 1) B (⋀[B]^n Ω[B⁄k])) := by
  let : Algebra.IsStandardSmooth k A :=
    Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth n
  let : Algebra.FormallyEtale A B := Algebra.FormallyEtale.of_isLocalization S
  obtain ⟨b⟩ := nonempty_topDifferential_basis k A n
  exact ⟨(topDifferential_isBaseChange k A B n).basis b⟩

end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct

namespace NumericalDimensionOne
section SmoothCharts
universe u
variable {k : Type u} [Field k] {X : Scheme.{u}}

noncomputable def schemeOpenScalar (sX : X ⟶ Spec (.of k)) (U : X.Opens) :
    k →+* Γ(X, U) :=
  (sX.appLE ⊤ U (by simp)).hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom

@[instance_reducible]
noncomputable def schemeOpenAlgebra (sX : X ⟶ Spec (.of k)) (U : X.Opens) :
    Algebra k Γ(X, U) := (schemeOpenScalar sX U).toAlgebra

theorem exists_standard_smooth_chart (sX : X ⟶ Spec (.of k)) (n : ℕ)
    [SmoothOfRelativeDimension n sX] (x : X) :
    ∃ (U : X.Opens), IsAffineOpen U ∧ x ∈ U ∧
      RingHom.IsStandardSmoothOfRelativeDimension n (schemeOpenScalar sX U) := by
  obtain ⟨U, _, V, hV, hxV, e, hf⟩ :=
    SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension
      (f := sX) (n := n) x
  have hU : U = ⊤ := by
    ext y
    have hmem : sX.base x ∈ U := e hxV
    rw [show sX.base x = y from Subsingleton.elim _ _] at hmem
    exact ⟨fun _ => trivial, fun _ => hmem⟩
  subst U
  refine ⟨V, hV, hxV, ?_⟩
  exact RingHom.isStandardSmoothOfRelativeDimension_respectsIso.right
    (sX.appLE ⊤ V e).hom
    (Scheme.ΓSpecIso (.of k)).symm.commRingCatIsoToRingEquiv hf

end SmoothCharts
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct

namespace NumericalDimensionOne
section OpenStalkScalars
universe u
variable {k : Type u} [Field k] {X : Scheme.{u}}

theorem open_stalk_scalar_tower (sX : X ⟶ Spec (.of k)) (U : X.Opens) (x : U) :
    letI := schemeOpenAlgebra sX U
    letI := schemeStalkAlgebra (.of k) sX x.1
    letI := TopCat.Presheaf.algebra_section_stalk X.presheaf x
    IsScalarTower k Γ(X, U) (X.presheaf.stalk x.1) := by
  let := schemeOpenAlgebra sX U
  let := schemeStalkAlgebra (.of k) sX x.1
  let := TopCat.Presheaf.algebra_section_stalk X.presheaf x
  apply IsScalarTower.of_algebraMap_eq
  intro a
  simp only [schemeStalkScalar, schemeOpenScalar, RingHom.algebraMap_toAlgebra, RingHom.coe_comp,
    Function.comp_apply,
    Scheme.Hom.appTop, Scheme.Hom.appLE, CommRingCat.hom_comp,
    TopCat.Presheaf.germ_res_apply]
  rfl

end OpenStalkScalars
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct

namespace NumericalDimensionOne
section SmoothCanonicalStalks
universe u
variable {k : Type u} [Field k] {X : Scheme.{u}}

theorem smooth_stalk_differentials_free (sX : X ⟶ Spec (.of k)) (n : ℕ)
    [SmoothOfRelativeDimension n sX] (x : X) :
    letI := schemeStalkAlgebra (.of k) sX x
    Module.Free (X.presheaf.stalk x) Ω[X.presheaf.stalk x⁄k] := by
  let := schemeStalkAlgebra (.of k) sX x
  obtain ⟨U, hU, hxU, hs⟩ := exists_standard_smooth_chart sX n x
  let y : U := ⟨x, hxU⟩
  let : Nonempty U := ⟨y⟩
  let := schemeOpenAlgebra sX U
  let : Algebra.IsStandardSmoothOfRelativeDimension n k Γ(X, U) := hs
  let : Algebra.IsStandardSmooth k Γ(X, U) :=
    Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth n
  let := TopCat.Presheaf.algebra_section_stalk X.presheaf y
  let := open_stalk_scalar_tower sX U y
  let := hU.isLocalization_stalk y
  let : Algebra.FormallyEtale Γ(X, U) (X.presheaf.stalk x) :=
    Algebra.FormallyEtale.of_isLocalization (hU.primeIdealOf y).asIdeal.primeCompl
  exact (KaehlerDifferential.isBaseChange_of_formallyEtale k Γ(X, U)
    (X.presheaf.stalk x)).free

theorem nonempty_smooth_canonical_stalk_basis (sX : X ⟶ Spec (.of k)) (n : ℕ)
    [SmoothOfRelativeDimension n sX] (x : X) :
    letI := schemeStalkAlgebra (.of k) sX x
    Nonempty (Module.Basis (Fin 1) (X.presheaf.stalk x)
      (⋀[X.presheaf.stalk x]^n Ω[X.presheaf.stalk x⁄k])) := by
  let := schemeStalkAlgebra (.of k) sX x
  obtain ⟨U, hU, hxU, hs⟩ := exists_standard_smooth_chart sX n x
  let y : U := ⟨x, hxU⟩
  let : Nonempty U := ⟨y⟩
  let := schemeOpenAlgebra sX U
  let : Algebra.IsStandardSmoothOfRelativeDimension n k Γ(X, U) := hs
  let : Algebra.IsStandardSmooth k Γ(X, U) :=
    Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth n
  let := TopCat.Presheaf.algebra_section_stalk X.presheaf y
  let := open_stalk_scalar_tower sX U y
  let := hU.isLocalization_stalk y
  exact nonempty_localized_topDifferential_basis k Γ(X, U) (X.presheaf.stalk x)
    n (hU.primeIdealOf y).asIdeal.primeCompl

end SmoothCanonicalStalks
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct

namespace NumericalDimensionOne
section CanonicalGeneric
universe u
variable {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X]

theorem nonempty_smooth_canonical_field_basis (sX : X ⟶ Spec (.of k)) (n : ℕ)
    [SmoothOfRelativeDimension n sX] :
    letI := schemeFieldAlgebra (.of k) sX
    Nonempty (Module.Basis (Fin 1) X.functionField
      (⋀[X.functionField]^n Ω[X.functionField⁄k])) := by
  exact nonempty_smooth_canonical_stalk_basis sX n (genericPoint X)

theorem canonical_stalk_field_isBaseChange (sX : X ⟶ Spec (.of k)) (n : ℕ)
    [SmoothOfRelativeDimension n sX] (x : X) :
    letI := schemeStalkAlgebra (.of k) sX x
    letI := schemeFieldAlgebra (.of k) sX
    letI := stalk_field_scalar_tower (.of k) sX x
    IsBaseChange X.functionField
      (topDifferentialMap k (X.presheaf.stalk x) X.functionField n) := by
  let := schemeStalkAlgebra (.of k) sX x
  let := schemeFieldAlgebra (.of k) sX
  let := stalk_field_scalar_tower (.of k) sX x
  let := smooth_stalk_differentials_free sX n x
  let : Algebra.FormallyEtale (X.presheaf.stalk x) X.functionField :=
    Algebra.FormallyEtale.of_isLocalization (nonZeroDivisors (X.presheaf.stalk x))
  exact topDifferential_isBaseChange k (X.presheaf.stalk x) X.functionField n

end CanonicalGeneric
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct

namespace NumericalDimensionOne
section TopDifferentialComposition
variable (k A B C : Type*) [CommRing k] [CommRing A] [CommRing B] [CommRing C]
    [Algebra k A] [Algebra k B] [Algebra k C] [Algebra A B] [Algebra A C]
    [Algebra B C] [IsScalarTower k A B] [IsScalarTower k A C]
    [IsScalarTower k B C] [IsScalarTower A B C]

theorem differentialMap_comp :
    ((KaehlerDifferential.map k k B C).restrictScalars A).comp
      (KaehlerDifferential.map k k A B) = KaehlerDifferential.map k k A C := by
  apply Derivation.liftKaehlerDifferential_unique
  ext a
  change KaehlerDifferential.map k k B C
    (KaehlerDifferential.map k k A B (KaehlerDifferential.D k A a)) =
      KaehlerDifferential.map k k A C (KaehlerDifferential.D k A a)
  simp only [KaehlerDifferential.map_D, ← IsScalarTower.algebraMap_apply]

theorem topDifferentialMap_comp (n : ℕ) :
    ((topDifferentialMap k B C n).restrictScalars A).comp
      (topDifferentialMap k A B n) = topDifferentialMap k A C n := by
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro v
  simp only [LinearMap.compAlternatingMap_apply, LinearMap.comp_apply,
    LinearMap.restrictScalars_apply, topDifferentialMap_ιMulti]
  apply congrArg (exteriorPower.ιMulti C n)
  funext i
  exact LinearMap.congr_fun (differentialMap_comp k A B C) (v i)

end TopDifferentialComposition
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct

namespace NumericalDimensionOne
section CanonicalChange
universe u
variable {k : CommRingCat.{u}} {X : Scheme.{u}} [IsIntegral X]
  [IsLocallyNoetherian X] [CompactSpace X]

theorem canonicalDivisorOf_smul (sX : X ⟶ Spec k) (n : ℕ)
    {ω : rationalTopForms k sX n} {D : WeilDivisor X}
    (hD : IsCanonicalDivisorOf k sX n ω D)
    {f : X.functionField} (hf : f ≠ 0) :
    IsCanonicalDivisorOf k sX n (f • ω) (D + principalWeilDivisor f) := by
  refine ⟨smul_ne_zero hf hD.1, ?_⟩
  intro p
  let := schemeStalkAlgebra k sX p.1
  let := schemeFieldAlgebra k sX
  let := stalk_field_scalar_tower k sX p.1
  obtain ⟨b, a, ha, hω, hDa⟩ := hD.2 p
  refine ⟨b, f * a, mul_ne_zero hf ha, ?_, ?_⟩
  · rw [hω, mul_smul]
  · simp only [Finsupp.add_apply, principalWeilDivisor_apply, hDa, X.ord_mul hf ha]
    omega

end CanonicalChange
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct

namespace NumericalDimensionOne
section CanonicalExistenceHelpers
universe u

lemma basis_singleton_repr {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (b : Module.Basis (Fin 1) R M) (v : M) : v = b.repr v 0 • b 0 := by
  simpa using (b.sum_repr v).symm

variable {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X]

theorem open_field_scalar_tower (sX : X ⟶ Spec (.of k)) (U : X.Opens) [Nonempty U] :
    letI := schemeOpenAlgebra sX U
    letI := schemeFieldAlgebra (.of k) sX
    IsScalarTower k Γ(X, U) X.functionField := by
  exact open_stalk_scalar_tower sX U
    ⟨genericPoint X, ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr
      (by simpa using (show Nonempty U from inferInstance))⟩

end CanonicalExistenceHelpers
end NumericalDimensionOne

end OAI
