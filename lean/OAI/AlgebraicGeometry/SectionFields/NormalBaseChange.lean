import Mathlib
import OAI.AlgebraicGeometry.SectionFields.ScalarCharts

namespace OAI

/-! Normality and principal-divisor descent under finite Galois base change. -/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Order Polynomial
open scoped TensorProduct WithZero
universe u

namespace RelativeDenominators
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

 
lemma integrallyClosed_of_affine_open_immersion
    {X : Scheme.{u}} (hNormal : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (A : Type u) [CommRing A] [IsDomain A]
    (j : Spec (.of A) ⟶ X) [IsOpenImmersion j] : IsIntegrallyClosed A := by
  apply IsIntegrallyClosed.of_localization_maximal
  intro p hp hpmax
  let x : Spec (.of A) := (⟨p, inferInstance⟩ : PrimeSpectrum A)
  let := hNormal (j x)
  have hs : IsIntegrallyClosed ((Spec (.of A)).presheaf.stalk x) :=
    IsIntegrallyClosed.of_equiv (asIso (j.stalkMap x)).commRingCatIsoToRingEquiv
  exact IsIntegrallyClosed.of_equiv (h := hs)
    (StructureSheaf.stalkIso A (⟨p, inferInstance⟩ : PrimeSpectrum A)).toRingEquiv.symm

lemma integrallyClosed_spec_stalk (A : Type u) [CommRing A] [IsDomain A]
    [IsIntegrallyClosed A] (x : Spec (.of A)) :
    IsIntegrallyClosed ((Spec (.of A)).presheaf.stalk x) := by
  change PrimeSpectrum A at x
  let : IsIntegrallyClosed (Localization.AtPrime x.asIdeal) :=
    isIntegrallyClosed_of_isLocalization _ x.asIdeal.primeCompl
      x.asIdeal.primeCompl_le_nonZeroDivisors
  exact IsIntegrallyClosed.of_equiv (StructureSheaf.stalkIso A x).toRingEquiv

 
lemma scalarExtensionChart_range
    (K A L : Type u) [Field K] [CommRing A] [Field L]
    [Algebra K A] [Algebra K L]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of K))
    (j : Spec (.of A) ⟶ X)
    (hj : Spec.map (CommRingCat.ofHom (algebraMap K A)) = j ≫ f) :
    Set.range (scalarExtensionChart K A L f j hj) =
      pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap K L))) ⁻¹' Set.range j := by
  have hs : Set.range (pullbackSpecIso K A L).inv = Set.univ := by
    simp
  unfold scalarExtensionChart
  rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, hs,
    Set.image_univ, AlgebraicGeometry.Scheme.Pullback.range_map]
  simp

 

lemma scalarExtensionChart_normal_stalk
    (K A L : Type u) [Field K] [CommRing A] [IsDomain A] [Field L]
    [Algebra K A] [Algebra K L] [IsGalois K L] [Module.Finite K L]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of K)) [GeometricallyIntegral f]
    (hNormal : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (j : Spec (.of A) ⟶ X) [IsOpenImmersion j]
    (hj : Spec.map (CommRingCat.ofHom (algebraMap K A)) = j ≫ f)
    (x : Spec (.of (A ⊗[K] L))) :
    IsIntegrallyClosed ((pullback f (Spec.map (CommRingCat.ofHom (algebraMap K L)))).presheaf.stalk
      (scalarExtensionChart K A L f j hj x)) := by
  let := integrallyClosed_of_affine_open_immersion hNormal A j
  let := scalarExtensionChart_domain K A L f j hj
  let := tensor_isIntegrallyClosed_of_galois K A L (FractionRing A)
  let := integrallyClosed_spec_stalk (A ⊗[K] L) x
  exact IsIntegrallyClosed.of_equiv
    (asIso ((scalarExtensionChart K A L f j hj).stalkMap x)).commRingCatIsoToRingEquiv.symm

 

theorem galois_baseChange_normal
    (K L : Type u) [Field K] [Field L] [Algebra K L] [IsGalois K L]
    [Module.Finite K L] {X : Scheme.{u}} [IsIntegral X]
    (f : X ⟶ Spec (.of K)) [GeometricallyIntegral f]
    (hNormal : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (y : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap K L))) : Scheme)) :
    IsIntegrallyClosed ((pullback f
      (Spec.map (CommRingCat.ofHom (algebraMap K L)))).presheaf.stalk y) := by
  let z := pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap K L))) y
  let i := X.affineOpenCover.idx z
  let A := X.affineOpenCover.X i
  let j : Spec A ⟶ X := X.affineOpenCover.f i
  let : IsOpenImmersion j := X.affineOpenCover.map_prop i
  have hc : z ∈ Set.range j := X.affineOpenCover.covers z
  let : Nonempty (Spec A) := ⟨hc.choose⟩
  let : IsIntegral (Spec A) := isIntegral_of_isOpenImmersion j
  have hA : IsDomain A := (affine_isIntegral_iff A).mp inferInstance
  let := hA
  let b : CommRingCat.of K ⟶ A := (Spec.map_surjective (j ≫ f)).choose
  let : Algebra K A := b.hom.toAlgebra
  have hj : Spec.map (CommRingCat.ofHom (algebraMap K A)) = j ≫ f :=
    (Spec.map_surjective (j ≫ f)).choose_spec
  have hy : y ∈ Set.range (scalarExtensionChart K A L f j hj) := by
    rw [scalarExtensionChart_range]
    exact hc
  obtain ⟨x, hx⟩ := hy
  have hn := @scalarExtensionChart_normal_stalk K A L _ A.commRing hA _ _ _ _ _
    X f _ hNormal j _ hj x
  exact hx ▸ hn

end

attribute [local instance] Units.mulDistribMulActionRight
attribute [local instance 2000] CommRingCat.commRing

 

noncomputable def fieldAffineChartRing (X : Scheme.{u}) [IsIntegral X] : CommRingCat.{u} :=
  X.affineOpenCover.X (X.affineOpenCover.idx (genericPoint X))

noncomputable def fieldAffineChartMap (X : Scheme.{u}) [IsIntegral X] :
    Spec (fieldAffineChartRing X) ⟶ X :=
  X.affineOpenCover.f (X.affineOpenCover.idx (genericPoint X))

instance (X : Scheme.{u}) [IsIntegral X] : IsOpenImmersion (fieldAffineChartMap X) := by
  exact X.affineOpenCover.map_prop _

instance (X : Scheme.{u}) [IsIntegral X] : Nonempty (Spec (fieldAffineChartRing X)) := by
  obtain ⟨x, _⟩ := X.affineOpenCover.covers (genericPoint X)
  exact ⟨x⟩

instance fieldAffineChartRing_isDomain (X : Scheme.{u}) [IsIntegral X] : IsDomain (fieldAffineChartRing X) := by
  apply (affine_isIntegral_iff _).mp
  exact isIntegral_of_isOpenImmersion (fieldAffineChartMap X)

instance (X : Scheme.{u}) [IsIntegral X] : IsDominant (fieldAffineChartMap X) :=
  isDominant_of_openIntegral _

noncomputable def fieldAffineChartHom (K : Type u) [Field K]
    {X : Scheme.{u}} [IsIntegral X] (f : X ⟶ Spec (.of K)) :
    CommRingCat.of K ⟶ fieldAffineChartRing X :=
  (Spec.map_surjective (fieldAffineChartMap X ≫ f)).choose

lemma fieldAffineChartHom_spec (K : Type u) [Field K]
    {X : Scheme.{u}} [IsIntegral X] (f : X ⟶ Spec (.of K)) :
    Spec.map (fieldAffineChartHom K f) = fieldAffineChartMap X ≫ f :=
  (Spec.map_surjective (fieldAffineChartMap X ≫ f)).choose_spec

@[instance_reducible] noncomputable def fieldAffineChartAlgebra (K : Type u) [Field K]
    {X : Scheme.{u}} [IsIntegral X] (f : X ⟶ Spec (.of K)) :
    Algebra K (fieldAffineChartRing X) :=
  (fieldAffineChartHom K f).hom.toAlgebra

lemma fieldAffineChart_algebraMap_spec (K : Type u) [Field K]
    {X : Scheme.{u}} [IsIntegral X] (f : X ⟶ Spec (.of K)) :
    letI := fieldAffineChartAlgebra K f
    Spec.map (CommRingCat.ofHom (algebraMap K (fieldAffineChartRing X))) =
      fieldAffineChartMap X ≫ f :=
  fieldAffineChartHom_spec K f

 
@[instance_reducible] noncomputable def schemeBaseChangeGaloisAction
    (K L : Type u) [Field K] [Field L] [Algebra K L] [Module.Finite K L]
    {X : Scheme.{u}} [IsIntegral X]
    (f : X ⟶ Spec (.of K)) [GeometricallyIntegral f] :
    MulSemiringAction (Gal(L/K))
      (pullback f (Spec.map (CommRingCat.ofHom (algebraMap K L)))).functionField := by
  letI := fieldAffineChartAlgebra K f
  exact scalarExtensionGaloisAction K (fieldAffineChartRing X) L
    (FractionRing (fieldAffineChartRing X)) f (fieldAffineChartMap X)
      (fieldAffineChart_algebraMap_spec K f)

 

theorem same_divisor_descends_from_galois_extension
    (K L : Type u) [Field K] [Field L] [Algebra K L] [IsGalois K L]
    [Module.Finite K L] {X : Scheme.{u}} [IsIntegral X]
    (f : X ⟶ Spec (.of K)) [GeometricallyIntegral f] [IsProper f]
    (hNormal : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (u : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap K L)))).functionFieldˣ)
    (hdiv : letI := schemeBaseChangeGaloisAction K L f
      letI : IsNoetherian (pullback f
        (Spec.map (CommRingCat.ofHom (algebraMap K L)))) := {}
      ∀ σ : Gal(L/K), principalDivisor _ (σ • u) = principalDivisor _ u) :
    letI : IsNoetherian (pullback f
      (Spec.map (CommRingCat.ofHom (algebraMap K L)))) := {}
    ∃ v : X.functionFieldˣ,
      principalDivisor _ (Units.map (functionFieldPullback (pullback.fst f
        (Spec.map (CommRingCat.ofHom (algebraMap K L))))).toMonoidHom v) =
          principalDivisor _ u := by
  let := fieldAffineChartAlgebra K f
  let := fieldAffineChartRing_isDomain X
  have hmain := @same_divisor_descends_from_galois_baseChange K (fieldAffineChartRing X) L
    (FractionRing (fieldAffineChartRing X)) _ _ (fieldAffineChartRing_isDomain X)
    _ _ _ _ _ _ _ _ _ _ X _ f _ _ (fieldAffineChartMap X) _ _
      (fieldAffineChart_algebraMap_spec K f) (galois_baseChange_normal K L f hNormal) u
  exact hmain hdiv

end RelativeDenominators
end

end OAI
