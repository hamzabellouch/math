import Mathlib

namespace OAI

noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

namespace ReverseLogKodaira

attribute [local instance] MvPolynomial.gradedAlgebra

abbrev complexBase : Scheme := Spec (CommRingCat.of ℂ)

abbrev projectiveGrading (N : ℕ) := MvPolynomial.homogeneousSubmodule (Fin (N + 1)) ℂ

abbrev complexProjectiveSpace (N : ℕ) : Scheme := Proj (projectiveGrading N)

def projectiveConstants (N : ℕ) : ℂ →+* projectiveGrading N 0 where
  toFun r := ⟨MvPolynomial.C r, MvPolynomial.isHomogeneous_C (Fin (N + 1)) r⟩
  map_zero' := Subtype.ext (map_zero MvPolynomial.C)
  map_one' := Subtype.ext (map_one MvPolynomial.C)
  map_add' x y := Subtype.ext (map_add MvPolynomial.C x y)
  map_mul' x y := Subtype.ext (map_mul MvPolynomial.C x y)

def complexProjectiveStructure (N : ℕ) : complexProjectiveSpace N ⟶ complexBase :=
  Proj.toSpecZero (projectiveGrading N) ≫ Spec.map (CommRingCat.ofHom (projectiveConstants N))

 
structure SmoothProjectiveVariety where
  scheme : Scheme
  structural : scheme ⟶ complexBase
  dimension : ℕ
  integral : IsIntegral scheme
  smooth : SmoothOfRelativeDimension dimension structural
  projective : ∃ (N : ℕ) (i : scheme ⟶ complexProjectiveSpace N),
    IsClosedImmersion i ∧ i ≫ complexProjectiveStructure N = structural

attribute [instance] SmoothProjectiveVariety.integral SmoothProjectiveVariety.smooth

namespace SmoothProjectiveVariety

instance (X : SmoothProjectiveVariety) : Smooth X.structural :=
  SmoothOfRelativeDimension.smooth X.dimension X.structural

 
def globalConstants (X : SmoothProjectiveVariety) : ℂ →+* Γ(X.scheme, ⊤) :=
  X.structural.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom

 
def constants (X : SmoothProjectiveVariety) (U : X.scheme.Opens) : ℂ →+* Γ(X.scheme, U) :=
  (X.scheme.presheaf.map (homOfLE (le_top (a := U))).op).hom.comp X.globalConstants

instance (X : SmoothProjectiveVariety) (U : X.scheme.Opens) : Algebra ℂ Γ(X.scheme, U) :=
  (X.constants U).toAlgebra

instance (X : SmoothProjectiveVariety) : Nonempty (⊤ : X.scheme.Opens) :=
  ⟨⟨genericPoint X.scheme, by trivial⟩⟩

 
def functionFieldConstants (X : SmoothProjectiveVariety) : ℂ →+* X.scheme.functionField :=
  (X.scheme.germToFunctionField ⊤).hom.comp X.globalConstants

instance (X : SmoothProjectiveVariety) : Algebra ℂ X.scheme.functionField :=
  X.functionFieldConstants.toAlgebra

lemma germ_constants (X : SmoothProjectiveVariety) (U : X.scheme.Opens) [Nonempty U] (c : ℂ) :
    algebraMap Γ(X.scheme, U) X.scheme.functionField (algebraMap ℂ Γ(X.scheme, U) c) =
      algebraMap ℂ X.scheme.functionField c := by
  change X.scheme.presheaf.germ U (genericPoint X.scheme) _
    (X.scheme.presheaf.map (homOfLE (le_top (a := U))).op (X.globalConstants c)) =
      X.scheme.presheaf.germ ⊤ (genericPoint X.scheme) _ (X.globalConstants c)
  exact X.scheme.presheaf.germ_res_apply (homOfLE le_top) (genericPoint X.scheme) _ _

instance (X : SmoothProjectiveVariety) (U : X.scheme.Opens) [Nonempty U] :
    IsScalarTower ℂ Γ(X.scheme, U) X.scheme.functionField :=
  IsScalarTower.of_algebraMap_eq fun c => (X.germ_constants U c).symm

instance affineFiniteType (X : SmoothProjectiveVariety) (U : X.scheme.affineOpens) :
    Algebra.FiniteType ℂ Γ(X.scheme, U.1) := by
  change (X.constants U.1).FiniteType
  have hf := X.structural.finiteType_appLE (isAffineOpen_top _) U.2 (by simp)
  have he := RingHom.FiniteType.of_surjective
    (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv).2
  exact hf.comp he

instance functionFieldFinTrdeg (X : SmoothProjectiveVariety) :
    FinTrdeg ℂ X.scheme.functionField := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hx, -⟩ :=
    X.scheme.isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ (genericPoint X.scheme)) isOpen_univ
  let : Nonempty U := ⟨⟨genericPoint X.scheme, hx⟩⟩
  let : Algebra.FiniteType ℂ Γ(X.scheme, U) := X.affineFiniteType ⟨U, hU⟩
  let := functionField_isFractionRing_of_isAffineOpen X.scheme U hU
  let := Algebra.EssFiniteType.of_isLocalization X.scheme.functionField
    (nonZeroDivisors Γ(X.scheme, U))
  let := Algebra.EssFiniteType.comp ℂ Γ(X.scheme, U) X.scheme.functionField
  infer_instance

 

lemma exists_standardSmooth_affine (X : SmoothProjectiveVariety) :
    ∃ U : X.scheme.affineOpens, Nonempty U.1 ∧
      Algebra.IsStandardSmoothOfRelativeDimension X.dimension ℂ Γ(X.scheme, U.1) := by
  obtain ⟨U, hU, V, hV, hx, e, hf⟩ :=
    SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension
      (n := X.dimension) (f := X.structural) (genericPoint X.scheme)
  have hUt : U = ⊤ := by
    apply top_unique
    intro y hy
    have htt := e hx
    change X.structural (genericPoint X.scheme) ∈ U at htt
    simpa only [Subsingleton.elim y (X.structural (genericPoint X.scheme))] using htt
  subst U
  refine ⟨⟨V, hV⟩, ⟨⟨genericPoint X.scheme, hx⟩⟩, ?_⟩
  rw [← RingHom.isStandardSmoothOfRelativeDimension_algebraMap]
  exact RingHom.isStandardSmoothOfRelativeDimension_respectsIso.right
    (X.structural.appLE ⊤ V e).hom
    (Scheme.ΓSpecIso (CommRingCat.of ℂ)).symm.commRingCatIsoToRingEquiv hf

 

lemma rank_rationalDifferentials (X : SmoothProjectiveVariety) :
    Module.rank X.scheme.functionField (KaehlerDifferential ℂ X.scheme.functionField) =
      X.dimension := by
  obtain ⟨U, hU, hsm⟩ := X.exists_standardSmooth_affine
  let : Nonempty U.1 := hU
  let : Algebra.IsStandardSmoothOfRelativeDimension X.dimension ℂ Γ(X.scheme, U.1) := hsm
  let : Algebra.IsStandardSmooth ℂ Γ(X.scheme, U.1) :=
    Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth X.dimension
  let := functionField_isFractionRing_of_isAffineOpen X.scheme U.1 U.2
  let := Algebra.FormallyEtale.of_isLocalization (Rₘ := X.scheme.functionField)
    (nonZeroDivisors Γ(X.scheme, U.1))
  have he := (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale ℂ Γ(X.scheme, U.1)
    X.scheme.functionField).rank_eq
  rw [← he, Module.rank_baseChange,
    Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential X.dimension]
  simp

instance finite_rationalDifferentials (X : SmoothProjectiveVariety) :
    Module.Finite X.scheme.functionField (KaehlerDifferential ℂ X.scheme.functionField) :=
  Module.finite_of_rank_eq_nat X.rank_rationalDifferentials

lemma finrank_rationalDifferentials (X : SmoothProjectiveVariety) :
    Module.finrank X.scheme.functionField (KaehlerDifferential ℂ X.scheme.functionField) =
      X.dimension := by
  simp [Module.finrank, X.rank_rationalDifferentials]

 
abbrev RationalCanonical (X : SmoothProjectiveVariety) :=
  ⋀[X.scheme.functionField]^X.dimension (KaehlerDifferential ℂ X.scheme.functionField)

 
lemma finrank_rationalCanonical (X : SmoothProjectiveVariety) :
    Module.finrank X.scheme.functionField X.RationalCanonical = 1 := by
  rw [RationalCanonical, exteriorPower.finrank_eq, X.finrank_rationalDifferentials]
  exact Nat.choose_self _

 
abbrev RationalPluriform (X : SmoothProjectiveVariety) (m : ℕ) :=
  ⨂[X.scheme.functionField]^m X.RationalCanonical

instance (X : SmoothProjectiveVariety) (m : ℕ) : AddCommGroup (X.RationalPluriform m) :=
  Module.addCommMonoidToAddCommGroup X.scheme.functionField

 
lemma nonempty_pluriformEquiv (X : SmoothProjectiveVariety) (m : ℕ) :
    Nonempty (X.RationalPluriform m ≃ₗ[X.scheme.functionField] X.scheme.functionField) := by
  let e : X.RationalCanonical ≃ₗ[X.scheme.functionField] X.scheme.functionField :=
    LinearEquiv.ofFinrankEq _ _ (by simpa using X.finrank_rationalCanonical)
  exact ⟨(PiTensorProduct.congr fun _ : Fin m => e).trans
    (PiTensorProduct.constantBaseRingEquiv (Fin m) X.scheme.functionField).toLinearEquiv⟩

lemma finrank_rationalPluriform (X : SmoothProjectiveVariety) (m : ℕ) :
    Module.finrank X.scheme.functionField (X.RationalPluriform m) = 1 := by
  obtain ⟨e⟩ := X.nonempty_pluriformEquiv m
  simpa using e.finrank_eq

instance finite_rationalPluriform (X : SmoothProjectiveVariety) (m : ℕ) :
    Module.Finite X.scheme.functionField (X.RationalPluriform m) :=
  Module.finite_of_finrank_pos (by rw [X.finrank_rationalPluriform m]; decide)

instance nontrivial_rationalPluriform (X : SmoothProjectiveVariety) (m : ℕ) :
    Nontrivial (X.RationalPluriform m) :=
  (X.nonempty_pluriformEquiv m).some.toEquiv.nontrivial

 

def regularPluriformLattice (X : SmoothProjectiveVariety) (U : X.scheme.affineOpens)
    [Nonempty U.1] (m : ℕ) : Submodule Γ(X.scheme, U.1) (X.RationalPluriform m) :=
  Submodule.span Γ(X.scheme, U.1) <| Set.range fun a : Fin m → Fin X.dimension → Γ(X.scheme, U.1) =>
    PiTensorProduct.tprod X.scheme.functionField fun j =>
      exteriorPower.ιMulti X.scheme.functionField X.dimension fun i =>
        KaehlerDifferential.D ℂ X.scheme.functionField (algebraMap _ _ (a j i))

 

def IsCartierIdeal (X : SmoothProjectiveVariety) (I : X.scheme.IdealSheafData) : Prop :=
  ∀ x : X.scheme, ∃ (U : X.scheme.affineOpens), x ∈ U.1 ∧
    ∃ t : Γ(X.scheme, U.1), t ≠ 0 ∧ I.ideal U = Ideal.span {t}

 
lemma isCartierIdeal_one (X : SmoothProjectiveVariety) : X.IsCartierIdeal 1 := by
  intro x
  obtain ⟨_, ⟨U, hU, rfl⟩, hx, -⟩ :=
    X.scheme.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  let : Nonempty U := ⟨⟨x, hx⟩⟩
  refine ⟨⟨U, hU⟩, hx, 1, one_ne_zero, ?_⟩
  simp

 

structure ReducedSNCBoundary (X : SmoothProjectiveVariety) where
  count : ℕ
  components : Fin count → X.scheme.IdealSheafData
  cartier : ∀ i, X.IsCartierIdeal (components i)
  transverse : ∀ S : Finset (Fin count), S.Nonempty →
    IsEmpty ((S.sup components).subscheme) ∨
      (S.card ≤ X.dimension ∧ SmoothOfRelativeDimension (X.dimension - S.card)
        ((S.sup components).subschemeι ≫ X.structural))
  union_cartier : X.IsCartierIdeal (∏ i, components i)

namespace ReducedSNCBoundary

 
def empty (X : SmoothProjectiveVariety) : X.ReducedSNCBoundary where
  count := 0
  components := Fin.elim0
  cartier := fun i => i.elim0
  transverse := by
    intro S hS
    obtain ⟨i, hi⟩ := hS
    exact i.elim0
  union_cartier := by simpa using X.isCartierIdeal_one

 
def ideal {X : SmoothProjectiveVariety} (E : X.ReducedSNCBoundary) : X.scheme.IdealSheafData :=
  ∏ i, E.components i

 
def support {X : SmoothProjectiveVariety} (E : X.ReducedSNCBoundary) : Set X.scheme :=
  E.ideal.support

@[simp] lemma ideal_empty (X : SmoothProjectiveVariety) : (empty X).ideal = 1 := by
  change (∏ i : Fin 0, Fin.elim0 i) = (1 : X.scheme.IdealSheafData)
  exact Fin.prod_univ_zero _

@[simp] lemma support_empty (X : SmoothProjectiveVariety) : (empty X).support = ∅ := by
  simp [support]

 

def IsLogPluriform {X : SmoothProjectiveVariety} (E : X.ReducedSNCBoundary)
    (m : ℕ) (s : X.RationalPluriform m) : Prop :=
  ∀ (U : X.scheme.affineOpens) (_ : Nonempty U.1) (t : Γ(X.scheme, U.1)),
    t ≠ 0 → E.ideal.ideal U = Ideal.span {t} →
      (algebraMap Γ(X.scheme, U.1) X.scheme.functionField t)^m • s ∈
        X.regularPluriformLattice U m

lemma isLogPluriform_zero {X : SmoothProjectiveVariety} (E : X.ReducedSNCBoundary) (m : ℕ) :
    E.IsLogPluriform m 0 := by
  intro U hU t ht hI
  simp only [smul_zero, Submodule.zero_mem]

lemma isLogPluriform_add {X : SmoothProjectiveVariety} (E : X.ReducedSNCBoundary) (m : ℕ)
    {s r : X.RationalPluriform m} (hs : E.IsLogPluriform m s) (hr : E.IsLogPluriform m r) :
    E.IsLogPluriform m (s + r) := by
  intro U hU t ht hI
  simpa only [smul_add] using (X.regularPluriformLattice U m).add_mem
    (hs U hU t ht hI) (hr U hU t ht hI)

lemma isLogPluriform_smul {X : SmoothProjectiveVariety} (E : X.ReducedSNCBoundary) (m : ℕ)
    (c : ℂ) {s : X.RationalPluriform m} (hs : E.IsLogPluriform m s) :
    E.IsLogPluriform m (c • s) := by
  intro U hU t ht hI
  have h := (X.regularPluriformLattice U m).smul_mem
    (algebraMap ℂ Γ(X.scheme, U.1) c) (hs U hU t ht hI)
  rw [IsScalarTower.algebraMap_smul Γ(X.scheme, U.1)] at h
  rwa [smul_comm c] at h

 

def sections {X : SmoothProjectiveVariety} (E : X.ReducedSNCBoundary) (m : ℕ) :
    Submodule ℂ (X.RationalPluriform m) where
  carrier := E.IsLogPluriform m
  zero_mem' := E.isLogPluriform_zero m
  add_mem' := E.isLogPluriform_add m
  smul_mem' := E.isLogPluriform_smul m

 

def HasImageDimensionAtLeast {X : SmoothProjectiveVariety}
    (E : X.ReducedSNCBoundary) (k : ℕ) : Prop :=
  ∃ (m : ℕ), 0 < m ∧ ∃ s : X.RationalPluriform m,
    s ∈ E.sections m ∧ s ≠ 0 ∧ ∃ r : Fin k → X.scheme.functionField,
      AlgebraicIndependent ℂ r ∧ ∀ i, r i • s ∈ E.sections m

 

def kodaira {X : SmoothProjectiveVariety} (E : X.ReducedSNCBoundary) : WithBot ℕ∞ :=
  ⨆ (k : ℕ) (_ : E.HasImageDimensionAtLeast k), ((k : ℕ∞) : WithBot ℕ∞)

lemma imageDimension_le_transcendenceDegree {X : SmoothProjectiveVariety}
    (E : X.ReducedSNCBoundary) {k : ℕ} (hk : E.HasImageDimensionAtLeast k) :
    k ≤ (Algebra.trdeg ℂ X.scheme.functionField).toNat := by
  rcases hk with ⟨m, hm, s, hs, hn, r, hr, hmem⟩
  have h := Cardinal.toNat_le_toNat hr.cardinalMk_le_trdeg
    (trdeg_lt_aleph0 ℂ X.scheme.functionField)
  simpa using h

lemma kodaira_le_transcendenceDegree {X : SmoothProjectiveVariety}
    (E : X.ReducedSNCBoundary) :
    E.kodaira ≤ (((Algebra.trdeg ℂ X.scheme.functionField).toNat : ℕ∞) : WithBot ℕ∞) := by
  apply iSup_le
  intro k
  apply iSup_le
  intro hk
  exact_mod_cast E.imageDimension_le_transcendenceDegree hk

 
lemma kodaira_ne_top {X : SmoothProjectiveVariety} (E : X.ReducedSNCBoundary) :
    E.kodaira ≠ ⊤ := by
  apply ne_of_lt
  exact lt_of_le_of_lt E.kodaira_le_transcendenceDegree (by
    exact WithBot.coe_lt_coe.mpr (ENat.natCast_lt_top _))

lemma hasImageDimensionAtLeast_zero_iff {X : SmoothProjectiveVariety}
    (E : X.ReducedSNCBoundary) :
    E.HasImageDimensionAtLeast 0 ↔ ∃ (m : ℕ), 0 < m ∧
      ∃ s : X.RationalPluriform m, s ∈ E.sections m ∧ s ≠ 0 := by
  constructor
  · rintro ⟨m, hm, s, hs, hn, r, hr, h⟩
    exact ⟨m, hm, s, hs, hn⟩
  · rintro ⟨m, hm, s, hs, hn⟩
    exact ⟨m, hm, s, hs, hn, Fin.elim0, algebraicIndependent_empty_type, fun i => i.elim0⟩

 
theorem kodaira_eq_bot_iff {X : SmoothProjectiveVariety} (E : X.ReducedSNCBoundary) :
    E.kodaira = ⊥ ↔ ∀ (m : ℕ), 0 < m →
      ∀ s : X.RationalPluriform m, s ∈ E.sections m → s = 0 := by
  constructor
  · intro h m hm s hs
    by_contra hn
    have hzero := E.hasImageDimensionAtLeast_zero_iff.mpr ⟨m, hm, s, hs, hn⟩
    have hle : ((0 : ℕ∞) : WithBot ℕ∞) ≤ E.kodaira :=
      le_iSup_of_le 0 (le_iSup_of_le hzero le_rfl)
    rw [h] at hle
    exact WithBot.coe_ne_bot (le_bot_iff.mp hle)
  · intro h
    apply le_bot_iff.mp
    apply iSup_le
    intro k
    apply iSup_le
    rintro ⟨m, hm, s, hs, hn, r, hr, hmem⟩
    exact (hn (h m hm s hs)).elim

end ReducedSNCBoundary

 
structure ComplexPoint (X : SmoothProjectiveVariety) where
  hom : complexBase ⟶ X.scheme
  over_base : hom ≫ X.structural = 𝟙 complexBase

 
def complexBasePoint : complexBase := ⟨⊥, Ideal.isPrime_bot⟩

 
def ComplexPoint.point {X : SmoothProjectiveVariety} (y : X.ComplexPoint) : X.scheme :=
  y.hom complexBasePoint

 
def ReducedSNCBoundary.complement {X : SmoothProjectiveVariety} (E : X.ReducedSNCBoundary) :
    X.scheme.Opens := E.ideal.support.compl

 

structure BoundaryFibration (X Y : SmoothProjectiveVariety)
    (E : X.ReducedSNCBoundary) (D : Y.ReducedSNCBoundary) where
  hom : X.scheme ⟶ Y.scheme
  over_base : hom ≫ Y.structural = X.structural
  surjective : Surjective hom
  connected : ∀ y : Y.ComplexPoint, ConnectedSpace ↥(CategoryTheory.Limits.pullback hom y.hom)
  support : hom ⁻¹' D.support ⊆ E.support

 

structure StratumSmoothFibration (X Y : SmoothProjectiveVariety)
    (E : X.ReducedSNCBoundary) (D : Y.ReducedSNCBoundary)
    extends BoundaryFibration X Y E D where
  smooth : Smooth (hom.resLE D.complement (hom ⁻¹ᵁ D.complement) le_rfl)
  strata : ∀ (S : Finset (Fin E.count)), S.Nonempty →
    Smooth (((S.sup E.components).subschemeι ≫ hom).resLE D.complement
      (((S.sup E.components).subschemeι ≫ hom) ⁻¹ᵁ D.complement) le_rfl)

 

structure FiberModel {X Y : SmoothProjectiveVariety} {E : X.ReducedSNCBoundary}
    {D : Y.ReducedSNCBoundary} (f : BoundaryFibration X Y E D) (y : Y.ComplexPoint) where
  variety : SmoothProjectiveVariety
  inclusion : variety.scheme ⟶ X.scheme
  square : IsPullback inclusion variety.structural f.hom y.hom
  boundary : variety.ReducedSNCBoundary
  boundary_pullback : boundary.ideal = E.ideal.comap inclusion

 

def VeryGenerally (Y : SmoothProjectiveVariety) (P : Y.ComplexPoint → Prop) : Prop :=
  ∃ Z : ℕ → TopologicalSpace.Closeds Y.scheme,
    (∀ n, Z n ≠ ⊤) ∧ ∀ y : Y.ComplexPoint, (∀ n, y.point ∉ Z n) → P y

end SmoothProjectiveVariety

open SmoothProjectiveVariety

 

def ReverseInequalityStatement : Prop :=
  ∀ (X Y : SmoothProjectiveVariety) (E : X.ReducedSNCBoundary) (D : Y.ReducedSNCBoundary)
    (f : StratumSmoothFibration X Y E D),
    VeryGenerally Y fun y => y.point ∈ D.complement ∧
      Nonempty (FiberModel f.toBoundaryFibration y) ∧
      ∀ F : FiberModel f.toBoundaryFibration y,
        E.kodaira ≤ D.kodaira + F.boundary.kodaira ∧
        ((D.kodaira = ⊥ ∨ F.boundary.kodaira = ⊥) →
          ∀ (m : ℕ), 0 < m → ∀ s : X.RationalPluriform m, s ∈ E.sections m → s = 0)

 

def LogarithmicSubadditivityStatement : Prop :=
  ∀ (X Y : SmoothProjectiveVariety) (E : X.ReducedSNCBoundary) (D : Y.ReducedSNCBoundary)
    (f : BoundaryFibration X Y E D),
    VeryGenerally Y fun y => y.point ∈ D.complement ∧
      Nonempty (FiberModel f y) ∧ ∀ F : FiberModel f y,
        D.kodaira + F.boundary.kodaira ≤ E.kodaira

 
def LogarithmicAdditivityStatement : Prop :=
  ∀ (X Y : SmoothProjectiveVariety) (E : X.ReducedSNCBoundary) (D : Y.ReducedSNCBoundary)
    (f : StratumSmoothFibration X Y E D),
    VeryGenerally Y fun y => y.point ∈ D.complement ∧
      Nonempty (FiberModel f.toBoundaryFibration y) ∧
      ∀ F : FiberModel f.toBoundaryFibration y,
        E.kodaira = D.kodaira + F.boundary.kodaira

 

def MainTheoremStatement : Prop :=
  ReverseInequalityStatement ∧ LogarithmicSubadditivityStatement ∧ LogarithmicAdditivityStatement

end ReverseLogKodaira

namespace ReverseLogKodaira.SmoothProjectiveVariety

 

theorem appLE_constants {X Y : SmoothProjectiveVariety}
    (f : X.scheme ⟶ Y.scheme) (hf : f ≫ Y.structural = X.structural)
    (U : Y.scheme.Opens) (V : X.scheme.Opens) (e : V ≤ f ⁻¹ᵁ U) (c : ℂ) :
    f.appLE U V e (Y.constants U c) = X.constants V c := by
  have hY : Y.constants U = (Y.structural.appLE ⊤ U (by simp)).hom.comp
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom := rfl
  have hX : X.constants V = (X.structural.appLE ⊤ V (by simp)).hom.comp
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom := rfl
  rw [hY, hX]
  change (Y.structural.appLE ⊤ U (by simp) ≫ f.appLE U V e)
      ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv c) = _
  have h := Scheme.Hom.appLE_comp_appLE f Y.structural ⊤ U V (by simp) e
  have h' := congrArg (fun g : Γ(complexBase, ⊤) ⟶ Γ(X.scheme, V) =>
    g ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv c)) h
  change _ = (f ≫ Y.structural).appLE ⊤ V _ _ at h'
  rw [hf] at h'
  exact h'

end ReverseLogKodaira.SmoothProjectiveVariety

namespace ReverseLogKodaira.SmoothProjectiveVariety

lemma complexPoint_preimage_top {Y : SmoothProjectiveVariety} (y : Y.ComplexPoint)
    (U : Y.scheme.Opens) (hy : y.point ∈ U) : (⊤ : complexBase.Opens) ≤ y.hom ⁻¹ᵁ U := by
  intro z hz
  change y.hom z ∈ U
  rw [Subsingleton.elim z complexBasePoint]
  exact hy

 
def complexPointEvaluation {Y : SmoothProjectiveVariety} (y : Y.ComplexPoint)
    (U : Y.scheme.Opens) (hy : y.point ∈ U) : Γ(Y.scheme, U) →+* ℂ :=
  (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom.comp
    (y.hom.appLE U ⊤ (complexPoint_preimage_top y U hy)).hom

 

def chartToFunctionField {X F : SmoothProjectiveVariety}
    (i : F.scheme ⟶ X.scheme) (V : X.scheme.Opens) [Nonempty (i ⁻¹ᵁ V)] :
    Γ(X.scheme, V) →+* F.scheme.functionField :=
  (F.scheme.germToFunctionField (i ⁻¹ᵁ V)).hom.comp (i.app V).hom

end ReverseLogKodaira.SmoothProjectiveVariety

namespace ReverseLogKodaira.SmoothProjectiveVariety

lemma complexPointEvaluation_constants {Y : SmoothProjectiveVariety} (y : Y.ComplexPoint)
    (U : Y.scheme.Opens) (hy : y.point ∈ U) (c : ℂ) :
    complexPointEvaluation y U hy (Y.constants U c) = c := by
  have h := Scheme.Hom.appLE_comp_appLE y.hom Y.structural ⊤ U ⊤ (by simp)
    (complexPoint_preimage_top y U hy)
  rw [y.over_base] at h
  have h' := congrArg (fun g : Γ(complexBase, ⊤) ⟶ Γ(complexBase, ⊤) =>
    g ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv c)) h
  have hid : Scheme.Hom.appLE (𝟙 complexBase) ⊤ ⊤ (by simp) = 𝟙 Γ(complexBase, ⊤) := by
    change (𝟙 Γ(complexBase, ⊤)) ≫ complexBase.presheaf.map (𝟙 _) = _
    rw [CategoryTheory.Functor.map_id, Category.id_comp]
  rw [hid] at h'
  have hval : y.hom.appLE U ⊤ (complexPoint_preimage_top y U hy)
      (Y.constants U c) = (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv c := h'
  change (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom
    (y.hom.appLE U ⊤ (complexPoint_preimage_top y U hy) (Y.constants U c)) = c
  rw [hval]
  exact (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv_hom_id_apply c

lemma chartToFunctionField_constants {X F : SmoothProjectiveVariety}
    (i : F.scheme ⟶ X.scheme) (hi : i ≫ X.structural = F.structural)
    (V : X.scheme.Opens) [Nonempty (i ⁻¹ᵁ V)] (c : ℂ) :
    chartToFunctionField i V (X.constants V c) = algebraMap ℂ F.scheme.functionField c := by
  have h := appLE_constants i hi V (i ⁻¹ᵁ V) le_rfl c
  rw [Scheme.Hom.appLE_eq_app] at h
  change F.scheme.germToFunctionField (i ⁻¹ᵁ V) (i.app V (X.constants V c)) = _
  rw [h]
  exact F.germ_constants (i ⁻¹ᵁ V) c

end ReverseLogKodaira.SmoothProjectiveVariety

namespace ReverseLogKodaira.SmoothProjectiveVariety

theorem fiber_scalar_compatibility :
    (∀ (Y : SmoothProjectiveVariety) (y : Y.ComplexPoint)
      (U : Y.scheme.Opens) (hy : y.point ∈ U) (c : ℂ),
      complexPointEvaluation y U hy (Y.constants U c) = c) ∧
    (∀ (X F : SmoothProjectiveVariety) (i : F.scheme ⟶ X.scheme)
      (_hi : i ≫ X.structural = F.structural) (V : X.scheme.Opens)
      (_ : Nonempty (i ⁻¹ᵁ V)) (c : ℂ),
      chartToFunctionField i V (X.constants V c) = algebraMap ℂ F.scheme.functionField c) := by
  exact ⟨fun _ => complexPointEvaluation_constants,
    fun _ _ i hi V hV => @chartToFunctionField_constants _ _ i hi V hV⟩

end ReverseLogKodaira.SmoothProjectiveVariety

namespace ReverseLogKodaira.SmoothProjectiveVariety

 

theorem fiber_chart_base_scalar
    {X Y : SmoothProjectiveVariety} {E : X.ReducedSNCBoundary} {D : Y.ReducedSNCBoundary}
    (f : BoundaryFibration X Y E D) (y : Y.ComplexPoint) (F : FiberModel f y)
    (U : Y.scheme.Opens) (hy : y.point ∈ U) (V : X.scheme.Opens)
    (e : V ≤ f.hom ⁻¹ᵁ U) [Nonempty (F.inclusion ⁻¹ᵁ V)] (a : Γ(Y.scheme, U)) :
    chartToFunctionField F.inclusion V (f.hom.appLE U V e a) =
      algebraMap ℂ F.variety.scheme.functionField (complexPointEvaluation y U hy a) := by
  let W := F.inclusion ⁻¹ᵁ V
  have h₁ := Scheme.Hom.appLE_comp_appLE F.inclusion f.hom U V W e le_rfl
  have h₂ := Scheme.Hom.appLE_comp_appLE F.variety.structural y.hom U ⊤ W
    (complexPoint_preimage_top y U hy) (by simp)
  have hc : ∀ (g h : F.variety.scheme ⟶ Y.scheme) (hg : g = h)
      (eg : W ≤ g ⁻¹ᵁ U) (eh : W ≤ h ⁻¹ᵁ U),
      g.appLE U W eg = h.appLE U W eh := by
    intro g h hg eg eh
    subst h
    rfl
  have h := h₁.trans ((hc _ _ F.square.w _ _).trans h₂.symm)
  have hv := congrArg (fun g : Γ(Y.scheme, U) ⟶ Γ(F.variety.scheme, W) => g a) h
  have hid : (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv
      (complexPointEvaluation y U hy a) = y.hom.appLE U ⊤ (complexPoint_preimage_top y U hy) a :=
    (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom_inv_id_apply _
  have ha : F.inclusion.app V (f.hom.appLE U V e a) =
      F.variety.constants W (complexPointEvaluation y U hy a) := by
    rw [Scheme.Hom.appLE_eq_app] at hv
    change _ = F.variety.structural.appLE ⊤ W (by simp)
      ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv (complexPointEvaluation y U hy a))
    rw [hid]
    exact hv
  change F.variety.scheme.germToFunctionField W
    (F.inclusion.app V (f.hom.appLE U V e a)) = _
  rw [ha]
  exact F.variety.germ_constants W (complexPointEvaluation y U hy a)

end ReverseLogKodaira.SmoothProjectiveVariety

end
end

end OAI
