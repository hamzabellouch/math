import Mathlib
import OAI.AlgebraicGeometry.SectionFields.AlgebraicFields
import OAI.AlgebraicGeometry.SectionFields.GenericFiber

namespace OAI

/-! Descent of principalizations from algebraic Galois extensions. -/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Order Polynomial
open scoped TensorProduct WithZero
universe u

namespace RelativeDenominators
open scoped TensorProduct

noncomputable def algebraicScalarExtensionFunctionFieldEquiv
    (K A L M : Type u) [Field K] [CommRing A] [IsDomain A] [Field L] [Field M]
    [Algebra K A] [Algebra K L] [Algebra K M] [Algebra A M] [IsScalarTower K A M]
    [IsFractionRing A M] [Algebra.IsAlgebraic K L]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of K)) [GeometricallyIntegral f]
    (j : Spec (.of A) ⟶ X) [IsOpenImmersion j]
    (hj : Spec.map (CommRingCat.ofHom (algebraMap K A)) = j ≫ f) :
    (M ⊗[K] L) ≃+* (pullback f (Spec.map (CommRingCat.ofHom (algebraMap K L)))).functionField := by
  letI := scalarExtensionChart_domain K A L f j hj
  letI := tensorFractionAlgebra K A L M
  letI := tensorAlgebraicFraction_isFractionRing K A L M
  letI : Algebra (A ⊗[K] L) (Spec (.of (A ⊗[K] L))).functionField :=
    AlgebraicGeometry.instAlgebraCarrierFunctionFieldSpec (.of (A ⊗[K] L))
  letI : IsFractionRing (A ⊗[K] L) (Spec (.of (A ⊗[K] L))).functionField :=
    functionField_isFractionRing_of_affine (.of (A ⊗[K] L))
  let jL := scalarExtensionChart K A L f j hj
  letI : IsDominant jL := isDominant_of_openIntegral jL
  exact (IsLocalization.algEquiv (nonZeroDivisors (A ⊗[K] L))
    (M ⊗[K] L) (Spec (.of (A ⊗[K] L))).functionField).toRingEquiv.trans
      (functionFieldOpenEquiv jL).symm


lemma algebraicScalarExtensionFunctionFieldEquiv_constant
    (K A L M : Type u) [Field K] [CommRing A] [IsDomain A] [Field L] [Field M]
    [Algebra K A] [Algebra K L] [Algebra K M] [Algebra A M] [IsScalarTower K A M]
    [IsFractionRing A M] [Algebra.IsAlgebraic K L]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of K)) [GeometricallyIntegral f]
    (j : Spec (.of A) ⟶ X) [IsOpenImmersion j]
    (hj : Spec.map (CommRingCat.ofHom (algebraMap K A)) = j ≫ f) (l : L) :
    algebraicScalarExtensionFunctionFieldEquiv K A L M f j hj ((1 : M) ⊗ₜ[K] l) =
      constantToFunctionField L (pullback.snd f
        (Spec.map (CommRingCat.ofHom (algebraMap K L)))) l := by
  let := scalarExtensionChart_domain K A L f j hj
  let := tensorFractionAlgebra K A L M
  let := tensorAlgebraicFraction_isFractionRing K A L M
  let : Algebra (A ⊗[K] L) (Spec (.of (A ⊗[K] L))).functionField :=
    AlgebraicGeometry.instAlgebraCarrierFunctionFieldSpec (.of (A ⊗[K] L))
  let : IsFractionRing (A ⊗[K] L) (Spec (.of (A ⊗[K] L))).functionField :=
    functionField_isFractionRing_of_affine (.of (A ⊗[K] L))
  let jL := scalarExtensionChart K A L f j hj
  let : IsDominant jL := isDominant_of_openIntegral jL
  apply (functionFieldOpenEquiv jL).injective
  change (functionFieldOpenEquiv jL)
    ((functionFieldOpenEquiv jL).symm
      ((IsLocalization.algEquiv (nonZeroDivisors (A ⊗[K] L))
        (M ⊗[K] L) (Spec (.of (A ⊗[K] L))).functionField) ((1 : M) ⊗ₜ[K] l))) = _
  rw [RingEquiv.apply_symm_apply]
  change _ = functionFieldPullback jL (constantToFunctionField L _ l)
  rw [functionFieldPullback_constant]
  change _ = constantToFunctionField L (scalarExtensionChart K A L f j hj ≫ _) l
  rw [scalarExtensionChart_snd]
  let : Algebra L (A ⊗[K] L) := Algebra.TensorProduct.rightAlgebra
  rw [constantToFunctionField_spec L (A ⊗[K] L)]
  have he : (1 : M) ⊗ₜ[K] l = algebraMap (A ⊗[K] L) (M ⊗[K] L) ((1 : A) ⊗ₜ[K] l) := by
    simp [RingHom.algebraMap_toAlgebra]
  rw [he, AlgEquiv.commutes]
  rfl


lemma algebraicScalarExtensionFunctionFieldEquiv_algebraMap
    (K A L M : Type u) [Field K] [CommRing A] [IsDomain A] [Field L] [Field M]
    [Algebra K A] [Algebra K L] [Algebra K M] [Algebra A M] [IsScalarTower K A M]
    [IsFractionRing A M] [Algebra.IsAlgebraic K L]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of K)) [GeometricallyIntegral f]
    (j : Spec (.of A) ⟶ X) [IsOpenImmersion j]
    (hj : Spec.map (CommRingCat.ofHom (algebraMap K A)) = j ≫ f) (a : A ⊗[K] L) :
    letI := scalarExtensionChart_domain K A L f j hj
    letI := tensorFractionAlgebra K A L M
    let jL := scalarExtensionChart K A L f j hj
    letI : IsDominant jL := isDominant_of_openIntegral jL
    functionFieldPullback jL (algebraicScalarExtensionFunctionFieldEquiv K A L M f j hj
      (algebraMap (A ⊗[K] L) (M ⊗[K] L) a)) =
        @algebraMap (A ⊗[K] L) (Spec (.of (A ⊗[K] L))).functionField _ _
          (AlgebraicGeometry.instAlgebraCarrierFunctionFieldSpec (.of (A ⊗[K] L))) a := by
  let := scalarExtensionChart_domain K A L f j hj
  let := tensorFractionAlgebra K A L M
  let := tensorAlgebraicFraction_isFractionRing K A L M
  let : Algebra (A ⊗[K] L) (Spec (.of (A ⊗[K] L))).functionField :=
    AlgebraicGeometry.instAlgebraCarrierFunctionFieldSpec (.of (A ⊗[K] L))
  let : IsFractionRing (A ⊗[K] L) (Spec (.of (A ⊗[K] L))).functionField :=
    functionField_isFractionRing_of_affine (.of (A ⊗[K] L))
  let jL := scalarExtensionChart K A L f j hj
  let : IsDominant jL := isDominant_of_openIntegral jL
  change (functionFieldOpenEquiv jL)
    ((functionFieldOpenEquiv jL).symm
      ((IsLocalization.algEquiv (nonZeroDivisors (A ⊗[K] L))
        (M ⊗[K] L) (Spec (.of (A ⊗[K] L))).functionField)
          (algebraMap (A ⊗[K] L) (M ⊗[K] L) a))) = _
  rw [RingEquiv.apply_symm_apply, AlgEquiv.commutes]

lemma algebraicScalarExtensionFunctionFieldEquiv_pullback
    (K A L M : Type u) [Field K] [CommRing A] [IsDomain A] [Field L] [Field M]
    [Algebra K A] [Algebra K L] [Algebra K M] [Algebra A M] [IsScalarTower K A M]
    [IsFractionRing A M] [Algebra.IsAlgebraic K L]
    {X : Scheme.{u}} [IsIntegral X] (f : X ⟶ Spec (.of K)) [GeometricallyIntegral f]
    (j : Spec (.of A) ⟶ X) [IsOpenImmersion j] [IsDominant j]
    (hj : Spec.map (CommRingCat.ofHom (algebraMap K A)) = j ≫ f) (m : M) :
    algebraicScalarExtensionFunctionFieldEquiv K A L M f j hj (m ⊗ₜ[K] (1 : L)) =
      functionFieldPullback (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap K L))))
        (chartFunctionFieldEquiv A M j m) := by
  let := scalarExtensionChart_domain K A L f j hj
  let := tensorFractionAlgebra K A L M
  let : Algebra (A ⊗[K] L) (Spec (.of (A ⊗[K] L))).functionField :=
    AlgebraicGeometry.instAlgebraCarrierFunctionFieldSpec (.of (A ⊗[K] L))
  let : Algebra A (Spec (.of A)).functionField :=
    AlgebraicGeometry.instAlgebraCarrierFunctionFieldSpec (.of A)
  let jL := scalarExtensionChart K A L f j hj
  let : IsDominant jL := isDominant_of_openIntegral jL
  let p := pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap K L)))
  let q := Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom :
    A →+* A ⊗[K] L))
  have hcomp : jL ≫ p = q ≫ j := scalarExtensionChart_fst K A L f j hj
  have : IsDominant (q ≫ j) := by rw [← hcomp]; infer_instance
  have : IsDominant q := IsDominant.of_comp_of_isOpenImmersion q j
  let e := algebraicScalarExtensionFunctionFieldEquiv K A L M f j hj
  let b := chartFunctionFieldEquiv A M j
  have he : e.toRingHom.comp Algebra.TensorProduct.includeLeftRingHom =
      (functionFieldPullback p).comp b.toRingHom := by
    apply IsLocalization.ringHom_ext (nonZeroDivisors A)
    ext a
    apply (functionFieldPullback jL).injective
    change functionFieldPullback jL (e (algebraMap A M a ⊗ₜ[K] (1 : L))) =
      functionFieldPullback jL (functionFieldPullback p (b (algebraMap A M a)))
    have hp (t : X.functionField) :
        functionFieldPullback jL (functionFieldPullback p t) =
          functionFieldPullback q (functionFieldPullback j t) := by
      change ((functionFieldPullback jL).comp (functionFieldPullback p)) t =
        ((functionFieldPullback q).comp (functionFieldPullback j)) t
      rw [← functionFieldPullback_comp, ← functionFieldPullback_comp]
      simp only [hcomp]
    rw [hp, chartFunctionFieldEquiv_algebraMap]
    rw [functionFieldPullback_spec_algebraMap]
    have ha : algebraMap A M a ⊗ₜ[K] (1 : L) =
        algebraMap (A ⊗[K] L) (M ⊗[K] L) (a ⊗ₜ[K] (1 : L)) := by
      simp [RingHom.algebraMap_toAlgebra]
    rw [ha]
    exact algebraicScalarExtensionFunctionFieldEquiv_algebraMap K A L M f j hj _
  exact RingHom.congr_fun he m


lemma algebraicScalarExtensionChart_normal_stalk
    (K A L : Type u) [Field K] [CommRing A] [IsDomain A] [Field L]
    [Algebra K A] [Algebra K L] [IsGalois K L] 
    {X : Scheme.{u}} (f : X ⟶ Spec (.of K)) [GeometricallyIntegral f]
    (hNormal : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (j : Spec (.of A) ⟶ X) [IsOpenImmersion j]
    (hj : Spec.map (CommRingCat.ofHom (algebraMap K A)) = j ≫ f)
    (x : Spec (.of (A ⊗[K] L))) :
    IsIntegrallyClosed ((pullback f (Spec.map (CommRingCat.ofHom (algebraMap K L)))).presheaf.stalk
      (scalarExtensionChart K A L f j hj x)) := by
  let := integrallyClosed_of_affine_open_immersion hNormal A j
  let := scalarExtensionChart_domain K A L f j hj
  let := tensor_isIntegrallyClosed_of_algebraic_galois K A L (FractionRing A)
  let := integrallyClosed_spec_stalk (A ⊗[K] L) x
  exact IsIntegrallyClosed.of_equiv
    (asIso ((scalarExtensionChart K A L f j hj).stalkMap x)).commRingCatIsoToRingEquiv.symm

 

theorem algebraic_galois_baseChange_normal
    (K L : Type u) [Field K] [Field L] [Algebra K L] [IsGalois K L]
    {X : Scheme.{u}} [IsIntegral X]
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
  have hn := @algebraicScalarExtensionChart_normal_stalk K A L _ A.commRing hA _ _ _ _
    X f _ hNormal j _ hj x
  exact hx ▸ hn

end RelativeDenominators

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace RelativeDenominators
section

noncomputable def scalarExtensionIntermediateMap
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of K)) (E : IntermediateField K L) :
    pullback f (Spec.map (CommRingCat.ofHom (algebraMap K L))) ⟶
      pullback f (Spec.map (CommRingCat.ofHom (algebraMap K E))) :=
  pullback.map _ _ _ _ (𝟙 X) (Spec.map (CommRingCat.ofHom E.val.toRingHom))
    (𝟙 (Spec (.of K))) (by simp) (by
      rw [Category.comp_id, ← Spec.map_comp]
      congr 1)

@[reassoc (attr := simp)]
lemma scalarExtensionIntermediateMap_fst
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of K)) (E : IntermediateField K L) :
    scalarExtensionIntermediateMap K L f E ≫ pullback.fst _ _ = pullback.fst _ _ := by
  dsimp only [scalarExtensionIntermediateMap, pullback.map]
  erw [pullback.lift_fst]
  simp

@[reassoc (attr := simp)]
lemma scalarExtensionIntermediateMap_snd
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of K)) (E : IntermediateField K L) :
    scalarExtensionIntermediateMap K L f E ≫ pullback.snd _ _ =
      pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom E.val.toRingHom) := by
  dsimp only [scalarExtensionIntermediateMap, pullback.map]
  erw [pullback.lift_snd]

lemma scalarExtensionIntermediateMap_isPullback
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of K)) (E : IntermediateField K L) :
    IsPullback (scalarExtensionIntermediateMap K L f E) (pullback.snd _ _)
      (pullback.snd _ _) (Spec.map (CommRingCat.ofHom E.val.toRingHom)) := by
  apply IsPullback.of_right (h₁₂ := pullback.fst f
    (Spec.map (CommRingCat.ofHom (algebraMap K E)))) _
    (scalarExtensionIntermediateMap_snd K L f E) (.of_hasPullback _ _)
  rw [scalarExtensionIntermediateMap_fst, ← Spec.map_comp]
  have he : CommRingCat.ofHom (algebraMap K E) ≫ CommRingCat.ofHom E.val.toRingHom =
      CommRingCat.ofHom (algebraMap K L) := by
    ext x
    exact E.val.commutes x
  rw [he]
  exact .of_hasPullback _ _

instance scalarExtensionIntermediateMap_flat
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of K)) (E : IntermediateField K L) :
    Flat (scalarExtensionIntermediateMap K L f E) := by
  exact MorphismProperty.of_isPullback (scalarExtensionIntermediateMap_isPullback K L f E).flip
    (inferInstance : Flat (Spec.map (CommRingCat.ofHom E.val.toRingHom)))

instance scalarExtensionIntermediateMap_surjective
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of K)) (E : IntermediateField K L) :
    Surjective (scalarExtensionIntermediateMap K L f E) := by
  exact MorphismProperty.of_isPullback (scalarExtensionIntermediateMap_isPullback K L f E).flip
    (inferInstance : Surjective (Spec.map (CommRingCat.ofHom E.val.toRingHom)))

open scoped TensorProduct

lemma scalarExtensionIntermediateMap_pullback_constant
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    {X : Scheme.{u}} [IsIntegral X]
    (f : X ⟶ Spec (.of K)) [GeometricallyIntegral f]
    (E : IntermediateField K L) (e : E) :
    functionFieldPullback (scalarExtensionIntermediateMap K L f E)
      (constantToFunctionField E (pullback.snd f
        (Spec.map (CommRingCat.ofHom (algebraMap K E)))) e) =
      constantToFunctionField L (pullback.snd f
        (Spec.map (CommRingCat.ofHom (algebraMap K L)))) (e : L) := by
  rw [functionFieldPullback_constant, scalarExtensionIntermediateMap_snd,
    constantToFunctionField_comp_spec]
  rfl

lemma scalarExtensionIntermediateMap_pullback_pullback
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    {X : Scheme.{u}} [IsIntegral X]
    (f : X ⟶ Spec (.of K)) [GeometricallyIntegral f]
    (E : IntermediateField K L) (x : X.functionField) :
    functionFieldPullback (scalarExtensionIntermediateMap K L f E)
      (functionFieldPullback (pullback.fst f
        (Spec.map (CommRingCat.ofHom (algebraMap K E)))) x) =
      functionFieldPullback (pullback.fst f
        (Spec.map (CommRingCat.ofHom (algebraMap K L)))) x := by
  rw [← RingHom.comp_apply, ← functionFieldPullback_comp]
  congr 1
  exact functionFieldPullback_congr _ _ (scalarExtensionIntermediateMap_fst K L f E)

 

lemma algebraicScalarExtensionFunctionFieldEquiv_intermediate
    (K A L M : Type u) [Field K] [CommRing A] [IsDomain A] [Field L] [Field M]
    [Algebra K A] [Algebra K L] [Algebra K M] [Algebra A M] [IsScalarTower K A M]
    [IsFractionRing A M] [Algebra.IsAlgebraic K L]
    {X : Scheme.{u}} [IsIntegral X]
    (f : X ⟶ Spec (.of K)) [GeometricallyIntegral f]
    (j : Spec (.of A) ⟶ X) [IsOpenImmersion j] [IsDominant j]
    (hj : Spec.map (CommRingCat.ofHom (algebraMap K A)) = j ≫ f)
    (E : IntermediateField K L) (t : M ⊗[K] E) :
    functionFieldPullback (scalarExtensionIntermediateMap K L f E)
      (algebraicScalarExtensionFunctionFieldEquiv K A E M f j hj t) =
    algebraicScalarExtensionFunctionFieldEquiv K A L M f j hj
      (tensorIntermediateInclusion K M L E t) := by
  let eL := algebraicScalarExtensionFunctionFieldEquiv K A L M f j hj
  let eE := algebraicScalarExtensionFunctionFieldEquiv K A E M f j hj
  have htL (m : M) (l : L) : eL (m ⊗ₜ[K] l) =
      functionFieldPullback (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap K L))))
        (chartFunctionFieldEquiv A M j m) *
      constantToFunctionField L (pullback.snd f
        (Spec.map (CommRingCat.ofHom (algebraMap K L)))) l := by
    rw [← algebraicScalarExtensionFunctionFieldEquiv_pullback K A L M f j hj m,
      ← algebraicScalarExtensionFunctionFieldEquiv_constant K A L M f j hj l, ← map_mul]
    simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rfl
  have htE (m : M) (e : E) : eE (m ⊗ₜ[K] e) =
      functionFieldPullback (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap K E))))
        (chartFunctionFieldEquiv A M j m) *
      constantToFunctionField E (pullback.snd f
        (Spec.map (CommRingCat.ofHom (algebraMap K E)))) e := by
    rw [← algebraicScalarExtensionFunctionFieldEquiv_pullback K A E M f j hj m,
      ← algebraicScalarExtensionFunctionFieldEquiv_constant K A E M f j hj e, ← map_mul]
    simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rfl
  change functionFieldPullback _ (eE t) = eL (tensorIntermediateInclusion K M L E t)
  induction t using TensorProduct.inductionOn with
  | tmul m e =>
      change functionFieldPullback _ (eE (m ⊗ₜ[K] e)) = eL (m ⊗ₜ[K] (e : L))
      rw [htE, htL, map_mul, scalarExtensionIntermediateMap_pullback_pullback,
        scalarExtensionIntermediateMap_pullback_constant]
  | add t t' h h' => simp only [map_add, h, h']

 

theorem rational_function_finiteGalois_field_of_definition
    (K L : Type u) [Field K] [Field L] [Algebra K L] [IsGalois K L]
    {X : Scheme.{u}} [IsIntegral X]
    (f : X ⟶ Spec (.of K)) [GeometricallyIntegral f]
    (u : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap K L)))).functionFieldˣ) :
    ∃ (E : FiniteGaloisIntermediateField K L)
      (v : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap K E)))).functionFieldˣ),
      Units.map (functionFieldPullback (scalarExtensionIntermediateMap K L f E.toIntermediateField)).toMonoidHom v = u := by
  let A := fieldAffineChartRing X
  let j := fieldAffineChartMap X
  let := fieldAffineChartAlgebra K f
  let M := FractionRing A
  have hj := fieldAffineChart_algebraMap_spec K f
  let eL := algebraicScalarExtensionFunctionFieldEquiv K A L M f j hj
  obtain ⟨E, y, hy⟩ := tensor_finiteGalois_field_of_definition K M L (eL.symm (u : _))
  let eE := algebraicScalarExtensionFunctionFieldEquiv K A E M f j hj
  have he : functionFieldPullback (scalarExtensionIntermediateMap K L f E.toIntermediateField)
      (eE y) = (u : _) := by
    rw [algebraicScalarExtensionFunctionFieldEquiv_intermediate]
    rw [hy, RingEquiv.apply_symm_apply]
  have hn : eE y ≠ 0 := by
    intro h
    rw [h, map_zero] at he
    exact u.ne_zero he.symm
  refine ⟨E, Units.mk0 (eE y) hn, ?_⟩
  apply Units.ext
  exact he

end

 

theorem principalization_descends_from_algebraic_galois_extension
    (K L : Type u) [Field K] [Field L] [Algebra K L] [IsGalois K L]
    {X : Scheme.{u}} [IsIntegral X] [IsNoetherian X]
    (f : X ⟶ Spec (.of K)) [GeometricallyIntegral f] [IsProper f]
    (hNormal : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (D : RationalWeilDivisor X) (hD : IsQCartier X D)
    (u : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap K L)))).functionFieldˣ)
    (hu : letI : IsNoetherian (pullback f
      (Spec.map (CommRingCat.ofHom (algebraMap K L)))) := {}
      rationalPrincipalDivisor _ u = pullbackQCartier hNormal (pullback.fst f
        (Spec.map (CommRingCat.ofHom (algebraMap K L)))) D hD) :
    ∃ v : X.functionFieldˣ, rationalPrincipalDivisor X v = D := by
  let XL := pullback f (Spec.map (CommRingCat.ofHom (algebraMap K L)))
  let πL := pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap K L)))
  let : IsNoetherian XL := {}
  have hNL := algebraic_galois_baseChange_normal K L f hNormal
  obtain ⟨E, v, hv⟩ := rational_function_finiteGalois_field_of_definition K L f u
  let XE := pullback f (Spec.map (CommRingCat.ofHom (algebraMap K E)))
  let πE := pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap K E)))
  let ρ := scalarExtensionIntermediateMap K L f E.toIntermediateField
  let : IsNoetherian XE := {}
  have hNE := galois_baseChange_normal K E f hNormal
  have hdiv : rationalPrincipalDivisor XE v = pullbackQCartier hNormal πE D hD := by
    apply pullbackQCartier_injective hNL hNE ρ _ _
      (isQCartier_principal XE v) (isQCartier_pullback hNormal πE D hD)
    calc
      _ = rationalPrincipalDivisor XL u := by
        rw [pullbackQCartier_principal hNE ρ, hv]
      _ = pullbackQCartier hNormal πL D hD := hu
      _ = pullbackQCartier hNormal (ρ ≫ πE) D hD := by
        congr 1
        exact (scalarExtensionIntermediateMap_fst K L f E.toIntermediateField).symm
      _ = _ := (pullbackQCartier_comp hNE hNormal ρ πE D hD _).symm
  exact principalization_descends_from_galois_extension K E f hNormal D hD v hdiv

attribute [local instance 2000] CommRingCat.commRing

instance functionFieldSpec_subsingleton (Z : Scheme.{u}) [IsIntegral Z] :
    Subsingleton (Spec Z.functionField) := by
  change Subsingleton (PrimeSpectrum Z.functionField)
  infer_instance

theorem rationalPrincipalDivisor_inv (X : Scheme) [IsIntegral X] [IsNoetherian X]
    (u : X.functionFieldˣ) :
    rationalPrincipalDivisor X u⁻¹ = -rationalPrincipalDivisor X u := by
  ext p
  simp [ord_inv X _ (Units.ne_zero u)]

 

theorem exists_divisible_linear_equivalence_witness
    {X Z : Scheme} [IsIntegral X] [IsIntegral Z] [IsNoetherian X] [IsNoetherian Z]
    (hNZ : ∀ z : Z, IsIntegrallyClosed (Z.presheaf.stalk z))
    (f : X ⟶ Z) [IsDominant f]
    (A : RationalWeilDivisor X) (D : RationalWeilDivisor Z) (hD : IsQCartier Z D)
    (hlinear : RationallyLinearlyEquivalent X A (pullbackQCartier hNZ f D hD))
    (p : ℕ) (hp : 0 < p) :
    ∃ a : ℕ, 0 < a ∧ p ∣ a ∧ ∃ φ : X.functionFieldˣ,
      (a : ℚ) • A + rationalPrincipalDivisor X φ =
        pullbackQCartier hNZ f ((a : ℚ) • D) (isQCartier_smul hD (a : ℚ)) := by
  obtain ⟨n, hn, w, hw⟩ := hlinear
  refine ⟨p * n, Nat.mul_pos hp hn, dvd_mul_right p n, (w⁻¹) ^ p, ?_⟩
  rw [rationalPrincipalDivisor_pow, rationalPrincipalDivisor_inv,
    pullbackQCartier_smul hNZ f hD]
  ext q
  have h := congrArg (fun d : RationalWeilDivisor X => d q) hw
  simp only [Finsupp.smul_apply, Finsupp.add_apply, Finsupp.neg_apply,
    Finsupp.sub_apply, smul_eq_mul, Nat.cast_mul] at h ⊢
  linear_combination (p : ℚ) * h

 

theorem relative_exact_presentation_of_geometricGenericFiber_principalization
    {X Z : Scheme.{u}} [IsIntegral X] [IsIntegral Z] [IsNoetherian X] [IsNoetherian Z]
    (hNX : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (hNZ : ∀ z : Z, IsIntegrallyClosed (Z.presheaf.stalk z))
    (f : X ⟶ Z) [IsDominant f] [IsIso f.c] [IsProper f]
    [GeometricallyIntegral (genericFiberToSpec f)]
    (L : Type u) [Field L] [Algebra Z.functionField L] [IsGalois Z.functionField L]
    (A : RationalWeilDivisor X) (hA : IsQCartier X A)
    (D : RationalWeilDivisor Z) (hD : IsQCartier Z D)
    (hlinear : RationallyLinearlyEquivalent X A (pullbackQCartier hNZ f D hD))
    (p : ℕ) (hp : 0 < p)
    (u : (pullback (genericFiberToSpec f) (Spec.map
      (CommRingCat.ofHom (algebraMap Z.functionField L)))).functionFieldˣ)
    (hu : letI : IsNoetherian (pullback (genericFiberToSpec f) (Spec.map
        (CommRingCat.ofHom (algebraMap Z.functionField L)))) := {}
      (p : ℚ) • pullbackQCartier (genericFiber_normal f hNX)
        (pullback.fst (genericFiberToSpec f) (Spec.map
          (CommRingCat.ofHom (algebraMap Z.functionField L))))
        (pullbackQCartier hNX (genericFiberι f) A hA)
        (isQCartier_pullback hNX (genericFiberι f) A hA) +
      rationalPrincipalDivisor _ u = 0) :
    ∃ (ψ : X.functionFieldˣ) (DZ : RationalWeilDivisor Z) (hDZ : IsQCartier Z DZ),
      RationallyLinearlyEquivalent Z DZ D ∧
      A + (p : ℚ)⁻¹ • rationalPrincipalDivisor X ψ = pullbackQCartier hNZ f DZ hDZ := by
  let F := genericFiber f
  let g := genericFiberToSpec f
  let FL := pullback g (Spec.map (CommRingCat.ofHom (algebraMap Z.functionField L)))
  let π := pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap Z.functionField L)))
  let : IsNoetherian FL := {}
  let AF := pullbackQCartier hNX (genericFiberι f) A hA
  have hAF : IsQCartier F AF := isQCartier_pullback hNX (genericFiberι f) A hA
  have hNF := genericFiber_normal f hNX
  have hu' : rationalPrincipalDivisor FL u =
      pullbackQCartier hNF π ((-(p : ℚ)) • AF) (isQCartier_smul hAF (-(p : ℚ))) := by
    rw [pullbackQCartier_smul hNF π hAF]
    simpa only [neg_smul] using (eq_neg_of_add_eq_zero_right hu)
  obtain ⟨v, hv⟩ := principalization_descends_from_algebraic_galois_extension
    Z.functionField L g hNF ((-(p : ℚ)) • AF) (isQCartier_smul hAF _) u hu'
  have hv' : (p : ℚ) • AF + rationalPrincipalDivisor F v = 0 := by
    rw [hv, neg_smul, add_neg_cancel]
  obtain ⟨a, ha, hpa, φ, hφ⟩ := exists_divisible_linear_equivalence_witness
    hNZ f A D hD hlinear p hp
  exact relative_exact_presentation_of_genericFiber_principalization
    hNX hNZ f A hA D hD p a hp ha hpa v hv' φ hφ

end RelativeDenominators

end

end OAI
