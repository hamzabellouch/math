import Mathlib
import OAI.AlgebraicGeometry.SectionFields.NormalDivisors
import OAI.AlgebraicGeometry.SectionFields.TensorAlgebra

namespace OAI

/-! Constants and function fields under geometric integrality and open charts. -/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Order Polynomial
open scoped TensorProduct WithZero
universe u

namespace RelativeDenominators

 

theorem global_constants_surjective_of_geometricallyIntegral
    (K : Type u) [Field K] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) [UniversallyClosed f] [GeometricallyIntegral f] :
    Function.Surjective (((Scheme.ΓSpecIso (.of K)).inv ≫ f.appTop).hom) := by
  let : IsIntegral X := GeometricallyIntegral.isIntegral_of_subsingleton f
  let : CompactSpace X := (quasiCompact_iff_compactSpace f).mp inferInstance
  let A := Γ(X, ⊤)
  let : Field A := (isField_of_universallyClosed K f).toField
  let F : CommRingCat.of K ⟶ A := (Scheme.ΓSpecIso (.of K)).inv ≫ f.appTop
  let : Algebra K A := F.hom.toAlgebra
  have hintegral : F.hom.IsIntegral := by
    apply RingHom.isIntegral_respectsIso.2
      (e := (Scheme.ΓSpecIso (.of K)).symm.commRingCatIsoToRingEquiv)
    exact isIntegral_appTop_of_universallyClosed f
  let : Algebra.IsIntegral K A := ⟨hintegral⟩
  let g : Spec A ⟶ Spec (.of K) := Spec.map F
  have hfactor : X.toSpecΓ ≫ g = f := by
    dsimp [g, F]
    rw [Spec.map_comp, ← Category.assoc, ← Scheme.toSpecΓ_naturality]
    rw [Category.assoc, ← Scheme.isoSpec_Spec_inv]
    simp
  let P := pullback g g
  let q : pullback X.toSpecΓ (pullback.fst g g) ⟶ P :=
    pullback.snd X.toSpecΓ (pullback.fst g g)
  let e : pullback X.toSpecΓ (pullback.fst g g) ≅ pullback f g :=
    pullbackRightPullbackFstIso g g X.toSpecΓ ≪≫ pullback.congrHom hfactor rfl
  let : IsIntegral (pullback X.toSpecΓ (pullback.fst g g)) :=
    IsIntegral.of_isIso e.inv
  let : IsSchemeTheoreticallyDominant X.toSpecΓ :=
    IsSchemeTheoreticallyDominant.of_isDominant _
  let : IsReduced P := IsSchemeTheoreticallyDominant.isReduced q
  have hP : IsIrreducible (Set.univ : Set P) := by
    have h := (IrreducibleSpace.isIrreducible_univ (pullback X.toSpecΓ (pullback.fst g g) : Scheme)).image
      q q.continuous.continuousOn
    simpa only [Set.image_univ, q.denseRange.closure_range] using h.closure
  let : IrreducibleSpace P := (irreducibleSpace_def P).mpr hP
  let : IsIntegral P := isIntegral_of_irreducibleSpace_of_isReduced P
  let : IsIntegral (Spec (.of (A ⊗[K] A))) :=
    IsIntegral.of_isIso (pullbackSpecIso K A A).hom
  let : IsDomain (A ⊗[K] A) := (affine_isIntegral_iff (.of (A ⊗[K] A))).mp inferInstance
  exact algebraMap_surjective_of_isAlgebraic_tensorSelf_domain K A

 

noncomputable def constantToFunctionField
    (K : Type u) [Field K] {X : Scheme.{u}} [IsIntegral X]
    (f : X ⟶ Spec (.of K)) : K →+* X.functionField :=
  (X.germToFunctionField ⊤).hom.comp
    (((Scheme.ΓSpecIso (.of K)).inv ≫ f.appTop).hom)

 

theorem rational_function_constant_of_divisor_zero
    (K : Type u) [Field K] {X : Scheme.{u}} [IsIntegral X] [IsNoetherian X]
    (f : X ⟶ Spec (.of K)) [UniversallyClosed f] [GeometricallyIntegral f]
    (hNormal : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (u : X.functionFieldˣ) (hdiv : principalDivisor X u = 0) :
    ∃ c : Kˣ, constantToFunctionField K f (c : K) = (u : X.functionField) := by
  obtain ⟨s, hs⟩ := rational_function_eq_global_unit_of_divisor_zero X hNormal u hdiv
  obtain ⟨c, hc⟩ := global_constants_surjective_of_geometricallyIntegral K f (s : Γ(X, ⊤))
  have hc0 : c ≠ 0 := by
    intro h
    apply Units.ne_zero s
    rw [← hc, h, map_zero]
  refine ⟨Units.mk0 c hc0, ?_⟩
  change X.germToFunctionField ⊤
    (((Scheme.ΓSpecIso (.of K)).inv ≫ f.appTop) c) = (u : X.functionField)
  rw [hc]
  exact hs

 

theorem functionFieldPullback_bijective_of_open
    {X Y : Scheme} [IsIntegral X] [IsIntegral Y]
    (j : Y ⟶ X) [IsOpenImmersion j] [IsDominant j] :
    Function.Bijective (functionFieldPullback j) := by
  let e := X.presheaf.stalkCongr
    (Inseparable.of_eq (genericPoint_eq_of_dominant j))
  have he : X.presheaf.stalkSpecializes
      (specializes_of_eq (genericPoint_eq_of_dominant j)) = e.inv := rfl
  have : IsIso (X.presheaf.stalkSpecializes
      (specializes_of_eq (genericPoint_eq_of_dominant j))) := by rw [he]; infer_instance
  exact ConcreteCategory.bijective_of_isIso
    (X.presheaf.stalkSpecializes
      (specializes_of_eq (genericPoint_eq_of_dominant j)) ≫ j.stalkMap (genericPoint Y))

noncomputable def functionFieldOpenEquiv
    {X Y : Scheme} [IsIntegral X] [IsIntegral Y]
    (j : Y ⟶ X) [IsOpenImmersion j] [IsDominant j] :
    X.functionField ≃+* Y.functionField :=
  RingEquiv.ofBijective (functionFieldPullback j) (functionFieldPullback_bijective_of_open j)

 

noncomputable def chartFunctionFieldEquiv
    (A M : Type u) [CommRing A] [IsDomain A] [Field M]
    [Algebra A M] [IsFractionRing A M]
    {X : Scheme.{u}} [IsIntegral X]
    (j : Spec (.of A) ⟶ X) [IsOpenImmersion j] [IsDominant j] :
    M ≃+* X.functionField := by
  letI : Algebra A (Spec (.of A)).functionField :=
    AlgebraicGeometry.instAlgebraCarrierFunctionFieldSpec (.of A)
  letI : IsFractionRing A (Spec (.of A)).functionField :=
    functionField_isFractionRing_of_affine (.of A)
  exact (IsLocalization.algEquiv (nonZeroDivisors A) M
    (Spec (.of A)).functionField).toRingEquiv.trans (functionFieldOpenEquiv j).symm

lemma chartFunctionFieldEquiv_algebraMap
    (A M : Type u) [CommRing A] [IsDomain A] [Field M]
    [Algebra A M] [IsFractionRing A M]
    {X : Scheme.{u}} [IsIntegral X]
    (j : Spec (.of A) ⟶ X) [IsOpenImmersion j] [IsDominant j] (a : A) :
    functionFieldPullback j (chartFunctionFieldEquiv A M j (algebraMap A M a)) =
      @algebraMap A (Spec (.of A)).functionField _ _
        (AlgebraicGeometry.instAlgebraCarrierFunctionFieldSpec (.of A)) a := by
  let : Algebra A (Spec (.of A)).functionField :=
    AlgebraicGeometry.instAlgebraCarrierFunctionFieldSpec (.of A)
  let : IsFractionRing A (Spec (.of A)).functionField :=
    functionField_isFractionRing_of_affine (.of A)
  change (functionFieldOpenEquiv j)
    ((functionFieldOpenEquiv j).symm
      ((IsLocalization.algEquiv (nonZeroDivisors A) M
        (Spec (.of A)).functionField) (algebraMap A M a))) = _
  rw [RingEquiv.apply_symm_apply, AlgEquiv.commutes]

lemma functionFieldPullback_comp
    {X Y Z : Scheme} [IsIntegral X] [IsIntegral Y] [IsIntegral Z]
    (f : X ⟶ Y) (g : Y ⟶ Z) [IsDominant f] [IsDominant g] :
    functionFieldPullback (f ≫ g) = (functionFieldPullback f).comp (functionFieldPullback g) := by
  change (Z.presheaf.stalkSpecializes _ ≫ (f ≫ g).stalkMap _).hom =
    ((Z.presheaf.stalkSpecializes _ ≫ g.stalkMap _) ≫
      (Y.presheaf.stalkSpecializes _ ≫ f.stalkMap _)).hom
  congr 1
  rw [Scheme.Hom.stalkMap_comp, Category.assoc, ← Category.assoc (g.stalkMap _),
    ← g.stalkSpecializes_stalkMap]
  simp only [← Category.assoc, TopCat.Presheaf.stalkSpecializes_comp]
  simp only [Category.assoc]
  rfl

lemma functionFieldPullback_constant
    (K : Type u) [Field K] {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Spec (.of K)) (j : Y ⟶ X) [IsDominant j] (c : K) :
    functionFieldPullback j (constantToFunctionField K f c) =
      constantToFunctionField K (j ≫ f) c := by
  unfold constantToFunctionField
  simp only [RingHom.comp_apply]
  rw [functionFieldPullback_germ]
  change Y.germToFunctionField ⊤ (j.appTop (((Scheme.ΓSpecIso (.of K)).inv ≫ f.appTop) c)) = _
  rw [Scheme.Hom.comp_appTop]
  rfl

lemma constantToFunctionField_spec
    (K A : Type u) [Field K] [CommRing A] [IsDomain A] [Algebra K A] (c : K) :
    constantToFunctionField K (Spec.map (CommRingCat.ofHom (algebraMap K A))) c =
      @algebraMap A (Spec (.of A)).functionField _ _
        (AlgebraicGeometry.instAlgebraCarrierFunctionFieldSpec (.of A))
          (algebraMap K A c) := by
  unfold constantToFunctionField
  rw [← Scheme.ΓSpecIso_inv_naturality]
  rfl

lemma functionFieldPullback_spec_algebraMap
    (A B : Type u) [CommRing A] [IsDomain A] [CommRing B] [IsDomain B]
    (h : A →+* B) [IsDominant (Spec.map (CommRingCat.ofHom h))] (a : A) :
    functionFieldPullback (Spec.map (CommRingCat.ofHom h))
      (@algebraMap A (Spec (.of A)).functionField _ _
        (AlgebraicGeometry.instAlgebraCarrierFunctionFieldSpec (.of A)) a) =
        @algebraMap B (Spec (.of B)).functionField _ _
        (AlgebraicGeometry.instAlgebraCarrierFunctionFieldSpec (.of B)) (h a) := by
  change functionFieldPullback (Spec.map (CommRingCat.ofHom h))
    ((Spec (.of A)).germToFunctionField ⊤ ((Scheme.ΓSpecIso (.of A)).inv a)) = _
  rw [functionFieldPullback_germ]
  change (Spec (.of B)).germToFunctionField ⊤
    (((Scheme.ΓSpecIso (.of A)).inv ≫ (Spec.map (CommRingCat.ofHom h)).appTop) a) = _
  rw [← Scheme.ΓSpecIso_inv_naturality]
  rfl

end RelativeDenominators
end

end OAI
