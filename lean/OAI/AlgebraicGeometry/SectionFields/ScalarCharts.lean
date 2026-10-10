import Mathlib
import OAI.AlgebraicGeometry.SectionFields.QCartier

namespace OAI

/-! Scalar-extension charts and descent through their function fields. -/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Order Polynomial
open scoped TensorProduct WithZero
universe u

namespace RelativeDenominators
open scoped TensorProduct

noncomputable def scalarExtensionChart
    (K A L : Type u) [Field K] [CommRing A] [Field L]
    [Algebra K A] [Algebra K L]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of K))
    (j : Spec (.of A) ⟶ X)
    (hj : Spec.map (CommRingCat.ofHom (algebraMap K A)) = j ≫ f) :
    Spec (.of (A ⊗[K] L)) ⟶ pullback f (Spec.map (CommRingCat.ofHom (algebraMap K L))) :=
  (pullbackSpecIso K A L).inv ≫
    pullback.map _ _ _ _ j (𝟙 _) (𝟙 _) (by simpa using hj) (by simp)

instance scalarExtensionChart_isOpenImmersion
    (K A L : Type u) [Field K] [CommRing A] [Field L]
    [Algebra K A] [Algebra K L]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of K))
    (j : Spec (.of A) ⟶ X) [IsOpenImmersion j]
    (hj : Spec.map (CommRingCat.ofHom (algebraMap K A)) = j ≫ f) :
    IsOpenImmersion (scalarExtensionChart K A L f j hj) := by
  unfold scalarExtensionChart
  infer_instance

lemma isDominant_of_openIntegral
    {X Y : Scheme} [IsIntegral X] [IsIntegral Y]
    (j : Y ⟶ X) [IsOpenImmersion j] : IsDominant j := by
  constructor
  exact j.isOpenEmbedding.isOpen_range.dense (Set.range_nonempty j)

lemma scalarExtensionChart_domain
    (K A L : Type u) [Field K] [CommRing A] [IsDomain A] [Field L]
    [Algebra K A] [Algebra K L]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of K)) [GeometricallyIntegral f]
    (j : Spec (.of A) ⟶ X) [IsOpenImmersion j]
    (hj : Spec.map (CommRingCat.ofHom (algebraMap K A)) = j ≫ f) :
    IsDomain (A ⊗[K] L) := by
  have : Nontrivial (A ⊗[K] L) :=
    (Algebra.TensorProduct.includeLeft_injective (R := K) (S := K) (A := A) (B := L)
      (algebraMap K L).injective).nontrivial
  have : IsIntegral (Spec (.of (A ⊗[K] L))) :=
    isIntegral_of_isOpenImmersion (scalarExtensionChart K A L f j hj)
  exact (AlgebraicGeometry.affine_isIntegral_iff (CommRingCat.of (A ⊗[K] L))).mp inferInstance


 

noncomputable def scalarExtensionFunctionFieldEquiv
    (K A L M : Type u) [Field K] [CommRing A] [IsDomain A] [Field L] [Field M]
    [Algebra K A] [Algebra K L] [Algebra K M] [Algebra A M] [IsScalarTower K A M]
    [IsFractionRing A M] [Module.Finite K L]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of K)) [GeometricallyIntegral f]
    (j : Spec (.of A) ⟶ X) [IsOpenImmersion j]
    (hj : Spec.map (CommRingCat.ofHom (algebraMap K A)) = j ≫ f) :
    (M ⊗[K] L) ≃+* (pullback f (Spec.map (CommRingCat.ofHom (algebraMap K L)))).functionField := by
  letI := scalarExtensionChart_domain K A L f j hj
  letI := tensorFractionAlgebra K A L M
  letI := tensorFraction_isFractionRing K A L M
  letI : Algebra (A ⊗[K] L) (Spec (.of (A ⊗[K] L))).functionField :=
    AlgebraicGeometry.instAlgebraCarrierFunctionFieldSpec (.of (A ⊗[K] L))
  letI : IsFractionRing (A ⊗[K] L) (Spec (.of (A ⊗[K] L))).functionField :=
    functionField_isFractionRing_of_affine (.of (A ⊗[K] L))
  let jL := scalarExtensionChart K A L f j hj
  letI : IsDominant jL := isDominant_of_openIntegral jL
  exact (IsLocalization.algEquiv (nonZeroDivisors (A ⊗[K] L))
    (M ⊗[K] L) (Spec (.of (A ⊗[K] L))).functionField).toRingEquiv.trans
      (functionFieldOpenEquiv jL).symm


@[reassoc (attr := simp)] lemma scalarExtensionChart_snd
    (K A L : Type u) [Field K] [CommRing A] [Field L]
    [Algebra K A] [Algebra K L]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of K))
    (j : Spec (.of A) ⟶ X)
    (hj : Spec.map (CommRingCat.ofHom (algebraMap K A)) = j ≫ f) :
    scalarExtensionChart K A L f j hj ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight :
        L →ₐ[K] A ⊗[K] L).toRingHom) := by
  dsimp only [scalarExtensionChart, pullback.map]
  rw [Category.assoc]
  erw [pullback.lift_snd]
  simp

@[reassoc (attr := simp)] lemma scalarExtensionChart_fst
    (K A L : Type u) [Field K] [CommRing A] [Field L]
    [Algebra K A] [Algebra K L]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of K))
    (j : Spec (.of A) ⟶ X)
    (hj : Spec.map (CommRingCat.ofHom (algebraMap K A)) = j ≫ f) :
    scalarExtensionChart K A L f j hj ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom :
        A →+* A ⊗[K] L)) ≫ j := by
  dsimp only [scalarExtensionChart, pullback.map]
  rw [Category.assoc]
  erw [pullback.lift_fst]
  simp

lemma scalarExtensionFunctionFieldEquiv_constant
    (K A L M : Type u) [Field K] [CommRing A] [IsDomain A] [Field L] [Field M]
    [Algebra K A] [Algebra K L] [Algebra K M] [Algebra A M] [IsScalarTower K A M]
    [IsFractionRing A M] [Module.Finite K L]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of K)) [GeometricallyIntegral f]
    (j : Spec (.of A) ⟶ X) [IsOpenImmersion j]
    (hj : Spec.map (CommRingCat.ofHom (algebraMap K A)) = j ≫ f) (l : L) :
    scalarExtensionFunctionFieldEquiv K A L M f j hj ((1 : M) ⊗ₜ[K] l) =
      constantToFunctionField L (pullback.snd f
        (Spec.map (CommRingCat.ofHom (algebraMap K L)))) l := by
  let := scalarExtensionChart_domain K A L f j hj
  let := tensorFractionAlgebra K A L M
  let := tensorFraction_isFractionRing K A L M
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


lemma scalarExtensionFunctionFieldEquiv_algebraMap
    (K A L M : Type u) [Field K] [CommRing A] [IsDomain A] [Field L] [Field M]
    [Algebra K A] [Algebra K L] [Algebra K M] [Algebra A M] [IsScalarTower K A M]
    [IsFractionRing A M] [Module.Finite K L]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of K)) [GeometricallyIntegral f]
    (j : Spec (.of A) ⟶ X) [IsOpenImmersion j]
    (hj : Spec.map (CommRingCat.ofHom (algebraMap K A)) = j ≫ f) (a : A ⊗[K] L) :
    letI := scalarExtensionChart_domain K A L f j hj
    letI := tensorFractionAlgebra K A L M
    let jL := scalarExtensionChart K A L f j hj
    letI : IsDominant jL := isDominant_of_openIntegral jL
    functionFieldPullback jL (scalarExtensionFunctionFieldEquiv K A L M f j hj
      (algebraMap (A ⊗[K] L) (M ⊗[K] L) a)) =
        @algebraMap (A ⊗[K] L) (Spec (.of (A ⊗[K] L))).functionField _ _
          (AlgebraicGeometry.instAlgebraCarrierFunctionFieldSpec (.of (A ⊗[K] L))) a := by
  let := scalarExtensionChart_domain K A L f j hj
  let := tensorFractionAlgebra K A L M
  let := tensorFraction_isFractionRing K A L M
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

lemma scalarExtensionFunctionFieldEquiv_pullback
    (K A L M : Type u) [Field K] [CommRing A] [IsDomain A] [Field L] [Field M]
    [Algebra K A] [Algebra K L] [Algebra K M] [Algebra A M] [IsScalarTower K A M]
    [IsFractionRing A M] [Module.Finite K L]
    {X : Scheme.{u}} [IsIntegral X] (f : X ⟶ Spec (.of K)) [GeometricallyIntegral f]
    (j : Spec (.of A) ⟶ X) [IsOpenImmersion j] [IsDominant j]
    (hj : Spec.map (CommRingCat.ofHom (algebraMap K A)) = j ≫ f) (m : M) :
    scalarExtensionFunctionFieldEquiv K A L M f j hj (m ⊗ₜ[K] (1 : L)) =
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
  let e := scalarExtensionFunctionFieldEquiv K A L M f j hj
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
    exact scalarExtensionFunctionFieldEquiv_algebraMap K A L M f j hj _
  exact RingHom.congr_fun he m


 

@[instance_reducible] noncomputable def transportRingAction
    {G R S : Type*} [Monoid G] [CommRing R] [CommRing S]
    [MulSemiringAction G R] (e : R ≃+* S) : MulSemiringAction G S where
  smul g s := e (g • e.symm s)
  smul_zero g := by
    change e (g • e.symm 0) = 0
    simp
  smul_add g x y := by
    change e (g • e.symm (x + y)) = e (g • e.symm x) + e (g • e.symm y)
    simp [smul_add]
  smul_one g := by
    change e (g • e.symm 1) = 1
    simp
  smul_mul g x y := by
    change e (g • e.symm (x * y)) = e (g • e.symm x) * e (g • e.symm y)
    simp [smul_mul']
  one_smul x := by
    change e ((1 : G) • e.symm x) = x
    simp
  mul_smul g h x := by
    change e ((g * h) • e.symm x) = e (g • e.symm (e (h • e.symm x)))
    simp [mul_smul]

noncomputable def scalarExtensionFunctionFieldEquivLeft
    (K A L M : Type u) [Field K] [CommRing A] [IsDomain A] [Field L] [Field M]
    [Algebra K A] [Algebra K L] [Algebra K M] [Algebra A M] [IsScalarTower K A M]
    [IsFractionRing A M] [Module.Finite K L]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of K)) [GeometricallyIntegral f]
    (j : Spec (.of A) ⟶ X) [IsOpenImmersion j]
    (hj : Spec.map (CommRingCat.ofHom (algebraMap K A)) = j ≫ f) :
    (L ⊗[K] M) ≃+* (pullback f (Spec.map (CommRingCat.ofHom (algebraMap K L)))).functionField :=
  (Algebra.TensorProduct.comm K L M).toRingEquiv.trans
    (scalarExtensionFunctionFieldEquiv K A L M f j hj)

 

@[instance_reducible] noncomputable def scalarExtensionGaloisAction
    (K A L M : Type u) [Field K] [CommRing A] [IsDomain A] [Field L] [Field M]
    [Algebra K A] [Algebra K L] [Algebra K M] [Algebra A M] [IsScalarTower K A M]
    [IsFractionRing A M] [Module.Finite K L]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of K)) [GeometricallyIntegral f]
    (j : Spec (.of A) ⟶ X) [IsOpenImmersion j]
    (hj : Spec.map (CommRingCat.ofHom (algebraMap K A)) = j ≫ f) :
    MulSemiringAction (Gal(L/K))
      (pullback f (Spec.map (CommRingCat.ofHom (algebraMap K L)))).functionField := by
  letI := tensorGaloisAction K L M
  exact transportRingAction (scalarExtensionFunctionFieldEquivLeft K A L M f j hj)

lemma scalarExtensionGaloisAction_constant
    (K A L M : Type u) [Field K] [CommRing A] [IsDomain A] [Field L] [Field M]
    [Algebra K A] [Algebra K L] [Algebra K M] [Algebra A M] [IsScalarTower K A M]
    [IsFractionRing A M] [Module.Finite K L]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of K)) [GeometricallyIntegral f]
    (j : Spec (.of A) ⟶ X) [IsOpenImmersion j]
    (hj : Spec.map (CommRingCat.ofHom (algebraMap K A)) = j ≫ f)
    (σ : Gal(L/K)) (l : L) :
    letI := scalarExtensionGaloisAction K A L M f j hj
    σ • constantToFunctionField L (pullback.snd f
      (Spec.map (CommRingCat.ofHom (algebraMap K L)))) l =
      constantToFunctionField L (pullback.snd f
        (Spec.map (CommRingCat.ofHom (algebraMap K L)))) (σ l) := by
  let e := scalarExtensionFunctionFieldEquivLeft K A L M f j hj
  have hc (c : L) : e (c ⊗ₜ[K] (1 : M)) = constantToFunctionField L
      (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap K L)))) c := by
    exact scalarExtensionFunctionFieldEquiv_constant K A L M f j hj c
  change e (Algebra.TensorProduct.map σ.toAlgHom (AlgHom.id K M)
    (e.symm (constantToFunctionField L _ l))) = _
  rw [← hc l, RingEquiv.symm_apply_apply]
  rw [Algebra.TensorProduct.map_tmul]
  exact hc (σ l)

attribute [local instance] Units.mulDistribMulActionRight

 

theorem scalarExtension_invariant_unit_descends
    (K A L M : Type u) [Field K] [CommRing A] [IsDomain A] [Field L] [Field M]
    [Algebra K A] [Algebra K L] [IsGalois K L] [Algebra K M]
    [Algebra A M] [IsScalarTower K A M] [IsFractionRing A M] [Module.Finite K L]
    {X : Scheme.{u}} [IsIntegral X]
    (f : X ⟶ Spec (.of K)) [GeometricallyIntegral f]
    (j : Spec (.of A) ⟶ X) [IsOpenImmersion j] [IsDominant j]
    (hj : Spec.map (CommRingCat.ofHom (algebraMap K A)) = j ≫ f)
    (u : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap K L)))).functionFieldˣ)
    (hu : letI := scalarExtensionGaloisAction K A L M f j hj
      ∀ σ : Gal(L/K), σ • u = u) :
    ∃ v : X.functionFieldˣ,
      functionFieldPullback (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap K L))))
        (v : X.functionField) = u := by
  let := scalarExtensionGaloisAction K A L M f j hj
  let e := scalarExtensionFunctionFieldEquivLeft K A L M f j hj
  let y := Units.map e.symm.toMonoidHom u
  have hy : ∀ σ : Gal(L/K),
      Algebra.TensorProduct.map σ.toAlgHom (AlgHom.id K M) (y : L ⊗[K] M) = y := by
    intro σ
    apply e.injective
    have h := congrArg (fun z : (pullback f
      (Spec.map (CommRingCat.ofHom (algebraMap K L)))).functionFieldˣ =>
      (z : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap K L)))).functionField)) (hu σ)
    change e (Algebra.TensorProduct.map σ.toAlgHom (AlgHom.id K M) (e.symm u)) = u at h
    change e (Algebra.TensorProduct.map σ.toAlgHom (AlgHom.id K M)
      (e.symm (u : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap K L)))).functionField))) =
        e (e.symm (u : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap K L)))).functionField))
    simpa only [RingEquiv.apply_symm_apply] using h
  obtain ⟨m, hm⟩ := tensor_invariant_unit_descends K L M y hy
  let b := chartFunctionFieldEquiv A M j
  refine ⟨Units.map b.toMonoidHom m, ?_⟩
  change functionFieldPullback _ (b (m : M)) = (u : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap K L)))).functionField)
  rw [← scalarExtensionFunctionFieldEquiv_pullback K A L M f j hj]
  have h := congrArg (fun z : (L ⊗[K] M)ˣ => e (z : L ⊗[K] M)) hm
  change e ((1 : L) ⊗ₜ[K] (m : M)) = e (e.symm
    (u : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap K L)))).functionField)) at h
  rw [RingEquiv.apply_symm_apply] at h
  exact h

 
lemma scalarExtensionGaloisAction_pullback
    (K A L M : Type u) [Field K] [CommRing A] [IsDomain A] [Field L] [Field M]
    [Algebra K A] [Algebra K L] [Algebra K M] [Algebra A M] [IsScalarTower K A M]
    [IsFractionRing A M] [Module.Finite K L]
    {X : Scheme.{u}} [IsIntegral X]
    (f : X ⟶ Spec (.of K)) [GeometricallyIntegral f]
    (j : Spec (.of A) ⟶ X) [IsOpenImmersion j] [IsDominant j]
    (hj : Spec.map (CommRingCat.ofHom (algebraMap K A)) = j ≫ f)
    (σ : Gal(L/K)) (x : X.functionField) :
    letI := scalarExtensionGaloisAction K A L M f j hj
    σ • functionFieldPullback (pullback.fst f
      (Spec.map (CommRingCat.ofHom (algebraMap K L)))) x =
      functionFieldPullback (pullback.fst f
        (Spec.map (CommRingCat.ofHom (algebraMap K L)))) x := by
  obtain ⟨m, rfl⟩ := (chartFunctionFieldEquiv A M j).surjective x
  let e := scalarExtensionFunctionFieldEquivLeft K A L M f j hj
  have hm : e ((1 : L) ⊗ₜ[K] m) = functionFieldPullback (pullback.fst f
      (Spec.map (CommRingCat.ofHom (algebraMap K L))))
        (chartFunctionFieldEquiv A M j m) :=
    scalarExtensionFunctionFieldEquiv_pullback K A L M f j hj m
  change e (Algebra.TensorProduct.map σ.toAlgHom (AlgHom.id K M)
    (e.symm (functionFieldPullback _ _))) = _
  rw [← hm, RingEquiv.symm_apply_apply]
  simp only [Algebra.TensorProduct.map_tmul, map_one, AlgHom.id_apply]

 

theorem same_divisor_descends_from_galois_baseChange
    (K A L M : Type u) [Field K] [CommRing A] [IsDomain A] [Field L] [Field M]
    [Algebra K A] [Algebra K L] [IsGalois K L] [Algebra K M]
    [Algebra A M] [IsScalarTower K A M] [IsFractionRing A M] [Module.Finite K L]
    {X : Scheme.{u}} [IsIntegral X]
    (f : X ⟶ Spec (.of K)) [GeometricallyIntegral f] [IsProper f]
    (j : Spec (.of A) ⟶ X) [IsOpenImmersion j] [IsDominant j]
    (hj : Spec.map (CommRingCat.ofHom (algebraMap K A)) = j ≫ f)
    (hNormal : ∀ x : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap K L))) : Scheme),
      IsIntegrallyClosed ((pullback f
        (Spec.map (CommRingCat.ofHom (algebraMap K L)))).presheaf.stalk x))
    (u : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap K L)))).functionFieldˣ)
    (hdiv : letI := scalarExtensionGaloisAction K A L M f j hj
      letI : IsNoetherian (pullback f
        (Spec.map (CommRingCat.ofHom (algebraMap K L)))) := {}
      ∀ σ : Gal(L/K), principalDivisor _ (σ • u) = principalDivisor _ u) :
    letI : IsNoetherian (pullback f
      (Spec.map (CommRingCat.ofHom (algebraMap K L)))) := {}
    ∃ v : X.functionFieldˣ,
      principalDivisor _ (Units.map (functionFieldPullback (pullback.fst f
        (Spec.map (CommRingCat.ofHom (algebraMap K L))))).toMonoidHom v) =
          principalDivisor _ u := by
  let := scalarExtensionGaloisAction K A L M f j hj
  let : IsNoetherian (pullback f
    (Spec.map (CommRingCat.ofHom (algebraMap K L)))) := {}
  obtain ⟨c, hc, hcu⟩ := invariant_rescaling_of_conjugate_divisor_eq K L
    (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap K L)))) hNormal
    (scalarExtensionGaloisAction_constant K A L M f j hj) u hdiv
  obtain ⟨v, hv⟩ := scalarExtension_invariant_unit_descends K A L M f j hj _ hc
  refine ⟨v, ?_⟩
  have he : Units.map (functionFieldPullback (pullback.fst f
      (Spec.map (CommRingCat.ofHom (algebraMap K L))))).toMonoidHom v =
      u / Units.map (constantToFunctionField L (pullback.snd f
        (Spec.map (CommRingCat.ofHom (algebraMap K L))))).toMonoidHom c :=
    Units.ext hv
  rw [he]
  exact hcu

end RelativeDenominators
end

end OAI
