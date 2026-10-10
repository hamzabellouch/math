import Mathlib
import PrimeNumberTheoremAnd.SiegelZeros.HadamardSupport
import OAI.NumberTheory.SiegelZeros.Structure.DominantFunctionFieldHom

namespace OAI

namespace SiegelZeros

noncomputable section
attribute [local instance] WeightedTorusJets.Geometry.polynomialGradedAlgebra
open Module
open CategoryTheory _root_.AlgebraicGeometry _root_.OAI.SiegelZeros.AlgebraicGeometry
open CategoryTheory _root_.AlgebraicGeometry
open IsLocalRing
open _root_.AlgebraicGeometry TopologicalSpace CategoryTheory
open _root_.AlgebraicGeometry TopologicalSpace CategoryTheory
namespace AlgebraicGeometry.Scheme.Hom

theorem isIntegrallyClosed_stalk_normalization_of_field
    {K : Type*} [Field K] {Y : Scheme}
    (f : Spec (.of K) ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    (x : f.normalization) :
    IsIntegrallyClosed (f.normalization.presheaf.stalk x) := by
  classical
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, _⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open
      (show f.fromNormalization x ∈ (⊤ : Y.Opens) by simp) (⊤ : Y.Opens).isOpen
  have hpre : f ⁻¹ᵁ U = ⊤ := by
    obtain ⟨a, ha⟩ := f.toNormalization.denseRange.exists_mem_open
      (f.fromNormalization ⁻¹ᵁ U).isOpen ⟨x, hxU⟩
    change f.fromNormalization (f.toNormalization a) ∈ U at ha
    rw [← Scheme.Hom.comp_apply, f.toNormalization_fromNormalization] at ha
    apply top_unique
    intro b _
    change f b ∈ U
    have hba : b = a := Subsingleton.elim b a
    subst b
    exact ha
  have hfield : IsField Γ(Spec (.of K), f ⁻¹ᵁ U) := by
    rw [hpre]
    exact (Scheme.ΓSpecIso (.of K)).commRingCatIsoToRingEquiv.toMulEquiv.isField
      (Field.toIsField K)
  let : Field Γ(Spec (.of K), f ⁻¹ᵁ U) := hfield.toField
  let : Algebra Γ(Y, U) Γ(Spec (.of K), f ⁻¹ᵁ U) := (f.app U).hom.toAlgebra
  have : IsIntegrallyClosed (integralClosure Γ(Y, U) Γ(Spec (.of K), f ⁻¹ᵁ U)) :=
    IsIntegrallyClosed.of_isIntegrallyClosedIn _ Γ(Spec (.of K), f ⁻¹ᵁ U)
  have : IsIntegrallyClosed Γ(f.normalization, f.fromNormalization ⁻¹ᵁ U) :=
    IsIntegrallyClosed.of_equiv (f.normalizationObjIso hU).symm.commRingCatIsoToRingEquiv
  have : Nonempty (f.fromNormalization ⁻¹ᵁ U) := ⟨⟨x, hxU⟩⟩
  let : Algebra Γ(f.normalization, f.fromNormalization ⁻¹ᵁ U)
      (f.normalization.presheaf.stalk x) :=
    TopCat.Presheaf.algebra_section_stalk f.normalization.presheaf ⟨x, hxU⟩
  have hV := hU.preimage f.fromNormalization
  have := hV.isLocalization_stalk ⟨x, hxU⟩
  exact isIntegrallyClosed_of_isLocalization (f.normalization.presheaf.stalk x)
    (hV.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl
    (hV.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl_le_nonZeroDivisors

end AlgebraicGeometry.Scheme.Hom
namespace WeightedTorusJets

universe u

variable (Y : Scheme.{u}) [IsIntegral Y] [QuasiSeparatedSpace Y]

noncomputable def genericNormalization : Scheme.{u} :=
  (Y.fromSpecStalk (genericPoint Y)).normalization

noncomputable def genericNormalizationMap : genericNormalization Y ⟶ Y :=
  (Y.fromSpecStalk (genericPoint Y)).fromNormalization

instance genericNormalization_isIntegral : IsIntegral (genericNormalization Y) := by
  dsimp only [genericNormalization]
  infer_instance

instance genericNormalizationMap_isDominant : IsDominant (genericNormalizationMap Y) := by
  apply (IsDominant.comp_iff (Y.fromSpecStalk (genericPoint Y)).toNormalization
    (Y.fromSpecStalk (genericPoint Y)).fromNormalization).mp
  simpa only [Scheme.Hom.toNormalization_fromNormalization] using
    isDominant_fromSpecStalk_genericPoint Y

end WeightedTorusJets

namespace WeightedTorusJets

universe u

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]

instance dominantFunctionFieldHom_isIso (f : X ⟶ Y) [IsDominant f]
    [IsOpenImmersion f] : IsIso (dominantFunctionFieldHom f) := by
  unfold dominantFunctionFieldHom
  infer_instance

noncomputable def openImmersionFunctionFieldEquiv (f : X ⟶ Y) [IsDominant f]
    [IsOpenImmersion f] : Y.functionField ≃+* X.functionField :=
  (asIso (dominantFunctionFieldHom f)).commRingCatIsoToRingEquiv

end WeightedTorusJets

namespace WeightedTorusJets

universe u

noncomputable def schemeBaseToStalk {R : Type u} [CommRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) (x : X) : R →+* X.presheaf.stalk x :=
  ((StructureSheaf.toStalk R (f x)) ≫ f.stalkMap x).hom

noncomputable abbrev schemeBaseStalkAlgebra {R : Type u} [CommRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) (x : X) : Algebra R (X.presheaf.stalk x) :=
  (schemeBaseToStalk f x).toAlgebra

theorem schemeBaseToStalk_eq_global_germ {R : Type u} [CommRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) (x : X) :
    schemeBaseToStalk f x =
      (X.presheaf.germ ⊤ x (by simp)).hom.comp
        (((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ f.appTop).hom) := by
  change (((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫
    (Spec (CommRingCat.of R)).presheaf.germ ⊤ (f x) (by simp)) ≫ f.stalkMap x).hom = _
  rw [Category.assoc, f.germ_stalkMap]
  rfl

end WeightedTorusJets

namespace WeightedTorusJets

universe u

variable {k : Type u} [CommRing k] {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]

noncomputable def dominantFunctionFieldAlgHom (f : X ⟶ Y) [IsDominant f]
    (g : Y ⟶ Spec (CommRingCat.of k)) :
    let : Algebra k Y.functionField := schemeBaseStalkAlgebra g (genericPoint Y)
    let : Algebra k X.functionField := schemeBaseStalkAlgebra (f ≫ g) (genericPoint X)
    Y.functionField →ₐ[k] X.functionField := by
  let : Algebra k Y.functionField := schemeBaseStalkAlgebra g (genericPoint Y)
  let : Algebra k X.functionField := schemeBaseStalkAlgebra (f ≫ g) (genericPoint X)
  refine { (dominantFunctionFieldHom f).hom with commutes' := ?_ }
  intro c
  change dominantFunctionFieldHom f (schemeBaseToStalk g (genericPoint Y) c) =
    schemeBaseToStalk (f ≫ g) (genericPoint X) c
  rw [schemeBaseToStalk_eq_global_germ, schemeBaseToStalk_eq_global_germ]
  have hn := congrArg
    (fun h : Γ(Y, ⊤) ⟶ X.functionField ↦
      h (((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ g.appTop).hom c))
    (germToFunctionField_dominantFunctionFieldHom f)
  simpa only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply,
    CommRingCat.comp_apply] using hn

end WeightedTorusJets

namespace WeightedTorusJets

universe u

variable {k : Type u} [CommRing k] {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]

noncomputable def openImmersionFunctionFieldAlgEquiv (f : X ⟶ Y) [IsDominant f]
    [IsOpenImmersion f] (g : Y ⟶ Spec (CommRingCat.of k)) :
    let : Algebra k Y.functionField := schemeBaseStalkAlgebra g (genericPoint Y)
    let : Algebra k X.functionField := schemeBaseStalkAlgebra (f ≫ g) (genericPoint X)
    Y.functionField ≃ₐ[k] X.functionField := by
  let : Algebra k Y.functionField := schemeBaseStalkAlgebra g (genericPoint Y)
  let : Algebra k X.functionField := schemeBaseStalkAlgebra (f ≫ g) (genericPoint X)
  let e := openImmersionFunctionFieldEquiv f
  exact { e with
    commutes' := (dominantFunctionFieldAlgHom f g).commutes }

noncomputable def normalizationFunctionFieldAlgHom
    (f : X ⟶ Y) [IsDominant f] [IsOpenImmersion f]
    (g : Y ⟶ Spec (CommRingCat.of k)) :
    let : Algebra k X.functionField := schemeBaseStalkAlgebra (f ≫ g) (genericPoint X)
    let : Algebra k (genericNormalization Y).functionField :=
      schemeBaseStalkAlgebra (genericNormalizationMap Y ≫ g)
        (genericPoint (genericNormalization Y))
    X.functionField →ₐ[k] (genericNormalization Y).functionField := by
  let : Algebra k X.functionField := schemeBaseStalkAlgebra (f ≫ g) (genericPoint X)
  let : Algebra k (genericNormalization Y).functionField :=
    schemeBaseStalkAlgebra (genericNormalizationMap Y ≫ g)
      (genericPoint (genericNormalization Y))
  let : Algebra k Y.functionField := schemeBaseStalkAlgebra g (genericPoint Y)
  exact (dominantFunctionFieldAlgHom (genericNormalizationMap Y) g).comp
    (openImmersionFunctionFieldAlgEquiv f g).symm.toAlgHom

end WeightedTorusJets

namespace WeightedTorusJets

universe u

noncomputable instance affineFunctionFieldAlgebra (A : Type u) [CommRing A] [IsDomain A] :
    Algebra A (Spec (CommRingCat.of A)).functionField :=
  AlgebraicGeometry.instAlgebraCarrierFunctionFieldSpec (CommRingCat.of A)

theorem affineFunctionField_isScalarTower (k A : Type u) [CommRing k] [CommRing A]
    [IsDomain A] [Algebra k A] :
    let : Algebra k (Spec (CommRingCat.of A)).functionField :=
      schemeBaseStalkAlgebra (Spec.map (CommRingCat.ofHom (algebraMap k A)))
        (genericPoint (Spec (CommRingCat.of A)))
    IsScalarTower k A (Spec (CommRingCat.of A)).functionField := by
  let : Algebra k (Spec (CommRingCat.of A)).functionField :=
    schemeBaseStalkAlgebra (Spec.map (CommRingCat.ofHom (algebraMap k A)))
      (genericPoint (Spec (CommRingCat.of A)))
  apply IsScalarTower.of_algebraMap_eq'
  change schemeBaseToStalk (Spec.map (CommRingCat.ofHom (algebraMap k A)))
    (genericPoint (Spec (CommRingCat.of A))) = _
  rw [schemeBaseToStalk_eq_global_germ, ← Scheme.ΓSpecIso_inv_naturality]
  rfl

noncomputable def affineFractionFieldAlgEquiv (k A : Type u) [CommRing k] [CommRing A]
    [IsDomain A] [Algebra k A] :
    let : Algebra k (Spec (CommRingCat.of A)).functionField :=
      schemeBaseStalkAlgebra (Spec.map (CommRingCat.ofHom (algebraMap k A)))
        (genericPoint (Spec (CommRingCat.of A)))
    FractionRing A ≃ₐ[k] (Spec (CommRingCat.of A)).functionField := by
  let : Algebra k (Spec (CommRingCat.of A)).functionField :=
    schemeBaseStalkAlgebra (Spec.map (CommRingCat.ofHom (algebraMap k A)))
      (genericPoint (Spec (CommRingCat.of A)))
  have : IsScalarTower k A (Spec (CommRingCat.of A)).functionField :=
    affineFunctionField_isScalarTower k A
  have : IsFractionRing A (Spec (CommRingCat.of A)).functionField :=
    functionField_isFractionRing_of_affine (CommRingCat.of A)
  exact (FractionRing.algEquiv A (Spec (CommRingCat.of A)).functionField).restrictScalars k

end WeightedTorusJets

open CategoryTheory _root_.AlgebraicGeometry

namespace WeightedTorusJets

universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f]

theorem isReduced_schemeImage [AlgebraicGeometry.IsReduced X] :
    AlgebraicGeometry.IsReduced f.image := by
  constructor
  intro U
  constructor
  intro s hs
  apply f.image.IsSheaf.section_ext
  intro x hx
  obtain ⟨_, ⟨_, ⟨V, hV, rfl⟩, rfl⟩, hxV, hVU⟩ :=
    (Y.isBasis_affineOpens.of_isInducing f.imageι.isEmbedding.isInducing).exists_subset_of_mem_open hx U.isOpen
  refine ⟨f.imageι ⁻¹ᵁ V, hVU, hxV, ?_⟩
  apply f.toImage_app_injective ⟨V, hV⟩
  simp only [map_zero]
  exact ((hs.map (f.image.presheaf.map (homOfLE hVU).op).hom).map
    (f.toImage.app (f.imageι ⁻¹ᵁ V)).hom).eq_zero

theorem isIntegral_schemeImage [IsIntegral X] : IsIntegral f.image := by
  have : AlgebraicGeometry.IsReduced f.image := isReduced_schemeImage f
  have : IrreducibleSpace f.image := by
    rw [irreducibleSpace_def]
    convert!
      ((IrreducibleSpace.isIrreducible_univ X).image _
          f.toImage.continuous.continuousOn).closure
    simpa using f.toImage.denseRange.closure_range.symm
  exact isIntegral_of_irreducibleSpace_of_isReduced _

end WeightedTorusJets

open MvPolynomial HomogeneousLocalization

namespace WeightedTorusJets.Geometry

def affineProjEval {k A ι : Type*} [CommRing k] [CommRing A] [Algebra k A]
    (x : ι → A) : MvPolynomial (Option ι) k →ₐ[k] A :=
  aeval (Option.elim' 1 x)

abbrev affineProjChart (k ι : Type*) [CommRing k] :=
  Away (homogeneousSubmodule (Option ι) k) (X (none : Option ι))

def affineProjChartMap {k A ι : Type*} [CommRing k] [CommRing A] [Algebra k A]
    (x : ι → A) : affineProjChart k ι →+* A :=
  (IsLocalization.Away.lift (X (none : Option ι))
    (g := (affineProjEval (k := k) x).toRingHom) (by simp [affineProjEval])).comp
    (algebraMap (affineProjChart k ι) (Localization.Away (X (none : Option ι) : MvPolynomial (Option ι) k)))

theorem affineProjChartMap_mk
    {k A ι : Type*} [CommRing k] [CommRing A] [Algebra k A]
    (x : ι → A) (n : ℕ) (p : MvPolynomial (Option ι) k)
    (hp : p ∈ homogeneousSubmodule (Option ι) k (n • 1)) :
    affineProjChartMap (k := k) x (Away.mk (homogeneousSubmodule (Option ι) k)
      (isHomogeneous_X k (none : Option ι)) n p hp) = affineProjEval (k := k) x p := by
  change (IsLocalization.Away.lift (X (none : Option ι))
    (S := Localization.Away (X (none : Option ι) : MvPolynomial (Option ι) k))
    (g := (affineProjEval (k := k) x).toRingHom) (by simp [affineProjEval]))
    (Localization.mk p ⟨(X (none : Option ι)) ^ n, ⟨n, rfl⟩⟩) = _
  rw [Localization.mk_eq_mk', IsLocalization.Away.lift, IsLocalization.lift_mk']
  rw [Units.mul_inv_eq_iff_eq_mul]
  simp [IsUnit.coe_liftRight, affineProjEval]

theorem affineProjEval_mem_chartMap_range
    {k A ι : Type*} [CommRing k] [CommRing A] [Algebra k A]
    (x : ι → A) (p : MvPolynomial ι k) : aeval x p ∈ (affineProjChartMap (k := k) x).range := by
  have hc (c : k) : algebraMap k A c ∈ (affineProjChartMap (k := k) x).range := by
    refine ⟨Away.mk (homogeneousSubmodule (Option ι) k)
      (isHomogeneous_X k (none : Option ι)) 0 (C c) (by simp), ?_⟩
    rw [affineProjChartMap_mk]
    simp [affineProjEval]
  have hx (i : ι) : x i ∈ (affineProjChartMap (k := k) x).range := by
    refine ⟨Away.mk (homogeneousSubmodule (Option ι) k)
      (isHomogeneous_X k (none : Option ι)) 1 (X (some i)) (by simpa using isHomogeneous_X k (some i)), ?_⟩
    rw [affineProjChartMap_mk]
    simp [affineProjEval]
  induction p using MvPolynomial.induction_on with
  | C c => simpa using hc c
  | add p q hp hq => simpa using (affineProjChartMap (k := k) x).range.add_mem hp hq
  | mul_X p i hp => simpa using (affineProjChartMap (k := k) x).range.mul_mem hp (hx i)

theorem affineProjChartMap_surjective
    {k A ι : Type*} [CommRing k] [CommRing A] [Algebra k A]
    (x : ι → A) (hx : Function.Surjective (aeval (R := k) x)) :
    Function.Surjective (affineProjChartMap (k := k) x) := by
  intro a
  obtain ⟨p, rfl⟩ := hx a
  exact affineProjEval_mem_chartMap_range x p

theorem affineProjChartMap_fromZero
    {k A ι : Type*} [CommRing k] [CommRing A] [Algebra k A]
    (x : ι → A) (c : homogeneousSubmodule (Option ι) k 0) :
    affineProjChartMap (k := k) x
      (fromZeroRingHom (homogeneousSubmodule (Option ι) k)
        (Submonoid.powers (X (none : Option ι))) c) = affineProjEval (k := k) x c := by
  change (IsLocalization.Away.lift (X (none : Option ι))
    (S := Localization.Away (X (none : Option ι) : MvPolynomial (Option ι) k))
    (g := (affineProjEval (k := k) x).toRingHom) (by simp [affineProjEval]))
    (algebraMap (MvPolynomial (Option ι) k)
      (Localization.Away (X (none : Option ι))) c) = _
  exact IsLocalization.Away.lift_eq _ _ _

end WeightedTorusJets.Geometry

open CategoryTheory _root_.AlgebraicGeometry

namespace WeightedTorusJets

universe u

variable (k ι : Type u) [CommRing k]

noncomputable def polynomialDegreeZeroEquiv :
    k ≃ₐ[k] MvPolynomial.homogeneousSubmodule ι k 0 := by
  apply AlgEquiv.ofBijective (Algebra.ofId k (MvPolynomial.homogeneousSubmodule ι k 0))
  constructor
  · intro a b h
    apply MvPolynomial.C_injective
    exact congrArg Subtype.val h
  · rintro ⟨p, hp⟩
    refine ⟨p.coeff 0, Subtype.ext ?_⟩
    change MvPolynomial.C (p.coeff 0) = p
    exact (MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp
      ((MvPolynomial.totalDegree_zero_iff_isHomogeneous ι).mpr hp)).symm

theorem polynomial_finiteType_degreeZero [Finite ι] :
    Algebra.FiniteType (MvPolynomial.homogeneousSubmodule ι k 0) (MvPolynomial ι k) := by
  have : IsScalarTower k (MvPolynomial.homogeneousSubmodule ι k 0) (MvPolynomial ι k) :=
    IsScalarTower.of_algebraMap_eq (R := k)
      (S := MvPolynomial.homogeneousSubmodule ι k 0)
      (A := MvPolynomial ι k) fun _ ↦ rfl
  exact Algebra.FiniteType.of_restrictScalars_finiteType k
    (MvPolynomial.homogeneousSubmodule ι k 0) (MvPolynomial ι k)

noncomputable def polynomialProjToSpec :
    Proj (MvPolynomial.homogeneousSubmodule ι k) ⟶ Spec (CommRingCat.of k) :=
  Proj.toSpecZero (MvPolynomial.homogeneousSubmodule ι k) ≫
    Spec.map (CommRingCat.ofHom (algebraMap k (MvPolynomial.homogeneousSubmodule ι k 0)))

theorem polynomialProjToSpec_isProper [Finite ι] : IsProper (polynomialProjToSpec k ι) := by
  have : Algebra.FiniteType (MvPolynomial.homogeneousSubmodule ι k 0) (MvPolynomial ι k) :=
    polynomial_finiteType_degreeZero k ι
  have : IsIso (CommRingCat.ofHom
      (algebraMap k (MvPolynomial.homogeneousSubmodule ι k 0))) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr (polynomialDegreeZeroEquiv k ι).bijective
  dsimp only [polynomialProjToSpec]
  infer_instance

end WeightedTorusJets
namespace WeightedTorusJets.Geometry

open CategoryTheory _root_.AlgebraicGeometry

universe u

attribute [-instance] polynomialGradedAlgebra in
attribute [local instance] MvPolynomial.gradedAlgebra in

def affineIntoProj {k A ι : Type u} [CommRing k] [CommRing A] [Algebra k A]
    (x : ι → A) : Spec (CommRingCat.of A) ⟶ Proj (homogeneousSubmodule (Option ι) k) :=
  Spec.map (CommRingCat.ofHom (affineProjChartMap (k := k) x)) ≫
    Proj.awayι (homogeneousSubmodule (Option ι) k) (X (none : Option ι))
      (show (X (none : Option ι) : MvPolynomial (Option ι) k) ∈
        homogeneousSubmodule (Option ι) k 1 from isHomogeneous_X k (none : Option ι)) (by decide)

theorem affineIntoProj_isImmersion {k A ι : Type u}
    [CommRing k] [CommRing A] [Algebra k A]
    (x : ι → A) (hx : Function.Surjective (aeval (R := k) x)) :
    IsImmersion (affineIntoProj (k := k) x) := by
  have : IsClosedImmersion (Spec.map (CommRingCat.ofHom (affineProjChartMap (k := k) x))) :=
    IsClosedImmersion.spec_of_surjective _ (affineProjChartMap_surjective x hx)
  unfold affineIntoProj
  infer_instance

theorem affineIntoProj_toSpec {k A ι : Type u}
    [CommRing k] [CommRing A] [Algebra k A] (x : ι → A) :
    affineIntoProj (k := k) x ≫ polynomialProjToSpec k (Option ι) =
      Spec.map (CommRingCat.ofHom (algebraMap k A)) := by
  simp only [affineIntoProj, polynomialProjToSpec, Category.assoc,
    Proj.awayι_toSpecZero_assoc, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro c
  change affineProjChartMap (k := k) x
    (fromZeroRingHom (homogeneousSubmodule (Option ι) k) _
      (algebraMap k (homogeneousSubmodule (Option ι) k 0) c)) = algebraMap k A c
  rw [affineProjChartMap_fromZero]
  change affineProjEval (k := k) x (C c) = _
  simp [affineProjEval]

theorem exists_proper_immersion_of_finiteType
    (k A : Type u) [CommRing k] [CommRing A] [Algebra k A] [Algebra.FiniteType k A] :
    ∃ (Y : Scheme.{u}) (f : Spec (CommRingCat.of A) ⟶ Y)
      (g : Y ⟶ Spec (CommRingCat.of k)),
      IsImmersion f ∧ QuasiCompact f ∧ Scheme.IsSeparated Y ∧ IsProper g ∧
      f ≫ g = Spec.map (CommRingCat.ofHom (algebraMap k A)) := by
  obtain ⟨ι, hι, φ, hφ⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial'.mp
    (inferInstance : Algebra.FiniteType k A)
  let : Fintype ι := hι
  let x : ι → A := fun i => φ (X i)
  have hx : Function.Surjective (aeval (R := k) x) := by
    exact MvPolynomial.aeval_unique φ ▸ hφ
  exact ⟨Proj (homogeneousSubmodule (Option ι) k), affineIntoProj x,
    polynomialProjToSpec k (Option ι), affineIntoProj_isImmersion x hx,
    inferInstance, inferInstance, polynomialProjToSpec_isProper k (Option ι), affineIntoProj_toSpec x⟩

end WeightedTorusJets.Geometry

namespace WeightedTorusJets

universe u

instance schemeImage_isIntegral {X Y : Scheme.{u}} [IsIntegral X] (f : X ⟶ Y)
    [QuasiCompact f] : IsIntegral f.image := isIntegral_schemeImage f

instance schemeImage_isSeparated {X Y : Scheme.{u}} (f : X ⟶ Y) [Y.IsSeparated] :
    f.image.IsSeparated := by
  rw [Scheme.isSeparated_iff, ← CategoryTheory.Limits.terminal.comp_from f.imageι]
  infer_instance

theorem exists_normal_proper_model_of_finiteType_domain
    (k A : Type u) [Field k] [CharZero k] [CommRing A] [IsDomain A]
    [Algebra k A] [Algebra.FiniteType k A] :
    ∃ (N : Scheme.{u}) (hN : IsIntegral N),
      let : IsIntegral N := hN
      ∃ (p : N ⟶ Spec (CommRingCat.of k)),
        IsLocallyNoetherian N ∧ (∀ x : N, IsIntegrallyClosed (N.presheaf.stalk x)) ∧
        LocallyOfFiniteType p ∧ UniversallyClosed p ∧
        (let : Algebra k N.functionField := schemeBaseStalkAlgebra p (genericPoint N)
         Nonempty (FractionRing A →ₐ[k] N.functionField)) := by
  obtain ⟨Y, f, g, hf, hqc, hsep, hproper, hfg⟩ :=
    Geometry.exists_proper_immersion_of_finiteType k A
  let C := f.image
  let gC := f.imageι ≫ g
  let N := genericNormalization C
  let p := genericNormalizationMap C ≫ gC
  have : IsFinite (genericNormalizationMap C) := isFinite_genericNormalization k C gC
  have : IsLocallyNoetherian N := LocallyOfFiniteType.isLocallyNoetherian p
  have hnormal (x : N) : IsIntegrallyClosed (N.presheaf.stalk x) :=
    Scheme.Hom.isIntegrallyClosed_stalk_normalization_of_field
      (C.fromSpecStalk (genericPoint C)) x
  have hcomp : f.toImage ≫ gC = Spec.map (CommRingCat.ofHom (algebraMap k A)) := by
    simpa only [gC, ← Category.assoc, Scheme.Hom.toImage_imageι] using hfg
  let : Algebra k (Spec (CommRingCat.of A)).functionField :=
    schemeBaseStalkAlgebra (f.toImage ≫ gC) (genericPoint (Spec (CommRingCat.of A)))
  let : Algebra k N.functionField := schemeBaseStalkAlgebra p (genericPoint N)
  let e : FractionRing A ≃ₐ[k] (Spec (CommRingCat.of A)).functionField := by
    change @AlgEquiv k (FractionRing A) ((Spec (CommRingCat.of A)).functionField)
      _ _ _ _ (schemeBaseStalkAlgebra (f.toImage ≫ gC)
        (genericPoint (Spec (CommRingCat.of A))))
    rw [hcomp]
    exact affineFractionFieldAlgEquiv k A
  let φ : (Spec (CommRingCat.of A)).functionField →ₐ[k] N.functionField :=
    normalizationFunctionFieldAlgHom f.toImage gC
  exact ⟨N, inferInstance, p, inferInstance, hnormal, inferInstance, inferInstance,
    ⟨φ.comp e.toAlgHom⟩⟩

end WeightedTorusJets

open Polynomial IsLocalRing TensorProduct

end

end SiegelZeros

end OAI
