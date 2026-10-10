import Mathlib
import OAI.AlgebraicGeometry.SectionFields.NormalBaseChange

namespace OAI

/-! Functorial Cartier pullback and the geometric Galois action. -/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Order Polynomial
open scoped TensorProduct WithZero
universe u

namespace RelativeDenominators
section

 

theorem pullbackQCartier_comp
    {X Y Z : Scheme} [IsIntegral X] [IsIntegral Y] [IsIntegral Z]
    [IsNoetherian X] [IsNoetherian Y] [IsNoetherian Z]
    (hNY : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y))
    (hNZ : ∀ z : Z, IsIntegrallyClosed (Z.presheaf.stalk z))
    (g : X ⟶ Y) (f : Y ⟶ Z) [IsDominant g] [IsDominant f]
    (D : RationalWeilDivisor Z) (hD : IsQCartier Z D)
    (hE : IsQCartier Y (pullbackQCartier hNZ f D hD)) :
    pullbackQCartier hNY g (pullbackQCartier hNZ f D hD) hE =
      pullbackQCartier hNZ (g ≫ f) D hD := by
  ext p
  let c := hD.data
  let z := f (g p.1)
  let v := Units.map (functionFieldPullback f).toMonoidHom (c.equation z)
  have hloc : ∀ q : PrimeDivisor Y, q.1 ∈ f ⁻¹ᵁ c.chart z →
      (c.index : ℚ) * pullbackQCartier hNZ f D hD q =
        (Y.ord (v : Y.functionField) q.1 : ℚ) := by
    intro q hq
    rw [pullbackQCartier_apply_of_local hNZ f D hD c.index c.index_pos
      (c.chart z) (c.equation z) (c.ord_eq z) q hq]
    have hn : (c.index : ℚ) ≠ 0 := by exact_mod_cast c.index_pos.ne'
    field_simp
    rfl
  rw [pullbackQCartier_apply_of_local hNY g _ hE c.index c.index_pos
    (f ⁻¹ᵁ c.chart z) v hloc p (c.mem_chart z),
    pullbackQCartier_apply_of_local hNZ (g ≫ f) D hD c.index c.index_pos
      (c.chart z) (c.equation z) (c.ord_eq z) p (c.mem_chart z)]
  dsimp only [v, Units.coe_map, MonoidHom.coe_coe]
  rw [functionFieldPullback_comp, RingHom.comp_apply]
  rfl

 

theorem principalDivisor_eq_of_over_base
    {X Z : Scheme} [IsIntegral X] [IsIntegral Z]
    [IsNoetherian X] [IsNoetherian Z]
    (hNX : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (hNZ : ∀ z : Z, IsIntegrallyClosed (Z.presheaf.stalk z))
    (f : X ⟶ Z) (g : X ⟶ X) [IsDominant f] [IsDominant g]
    (hgf : g ≫ f = f) (D : RationalWeilDivisor Z) (hD : IsQCartier Z D)
    (u : X.functionFieldˣ)
    (hu : rationalPrincipalDivisor X u = pullbackQCartier hNZ f D hD) :
    principalDivisor X (Units.map (functionFieldPullback g).toMonoidHom u) =
      principalDivisor X u := by
  have he : rationalPrincipalDivisor X
      (Units.map (functionFieldPullback g).toMonoidHom u) = rationalPrincipalDivisor X u := by
    calc
      _ = pullbackQCartier hNX g (rationalPrincipalDivisor X u)
          (isQCartier_principal X u) := (pullbackQCartier_principal hNX g u _).symm
      _ = pullbackQCartier hNX g (pullbackQCartier hNZ f D hD)
          (isQCartier_pullback hNZ f D hD) := by congr 1
      _ = pullbackQCartier hNZ (g ≫ f) D hD := pullbackQCartier_comp hNX hNZ g f D hD _
      _ = pullbackQCartier hNZ f D hD := by congr 1
      _ = rationalPrincipalDivisor X u := hu.symm
  ext p
  have hp := DFunLike.congr_fun he p
  change (principalDivisor X (Units.map (functionFieldPullback g).toMonoidHom u) p : ℚ) =
    (principalDivisor X u p : ℚ) at hp
  exact_mod_cast hp

open scoped TensorProduct

 

noncomputable def scalarExtensionAutomorphism
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of K)) (σ : Gal(L/K)) :
    pullback f (Spec.map (CommRingCat.ofHom (algebraMap K L))) ⟶
      pullback f (Spec.map (CommRingCat.ofHom (algebraMap K L))) :=
  pullback.map _ _ _ _ (𝟙 X) (Spec.map (CommRingCat.ofHom σ.toRingHom))
    (𝟙 (Spec (.of K))) (by simp) (by
      rw [Category.comp_id, ← Spec.map_comp]
      congr 1
      ext x
      exact (σ.commutes x).symm)

instance scalarExtensionAutomorphism_isIso
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of K)) (σ : Gal(L/K)) :
    IsIso (scalarExtensionAutomorphism K L f σ) := by
  let : IsIso (CommRingCat.ofHom σ.toRingHom) :=
    inferInstanceAs (IsIso σ.toRingEquiv.toCommRingCatIso.hom)
  unfold scalarExtensionAutomorphism
  infer_instance

@[reassoc (attr := simp)] lemma scalarExtensionAutomorphism_fst
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of K)) (σ : Gal(L/K)) :
    scalarExtensionAutomorphism K L f σ ≫ pullback.fst _ _ = pullback.fst _ _ := by
  dsimp only [scalarExtensionAutomorphism, pullback.map]
  erw [pullback.lift_fst]
  simp

@[reassoc (attr := simp)] lemma scalarExtensionAutomorphism_snd
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of K)) (σ : Gal(L/K)) :
    scalarExtensionAutomorphism K L f σ ≫ pullback.snd _ _ =
      pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom σ.toRingHom) := by
  dsimp only [scalarExtensionAutomorphism, pullback.map]
  erw [pullback.lift_snd]

lemma constantToFunctionField_comp_spec
    (K L : Type u) [Field K] [Field L]
    {X : Scheme.{u}} [IsIntegral X] (f : X ⟶ Spec (.of L))
    (h : K →+* L) (c : K) :
    constantToFunctionField K (f ≫ Spec.map (CommRingCat.ofHom h)) c =
      constantToFunctionField L f (h c) := by
  unfold constantToFunctionField
  rw [Scheme.Hom.comp_appTop, ← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality]
  rfl

lemma scalarExtensionAutomorphism_pullback_constant
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of K)) [GeometricallyIntegral f]
    (σ : Gal(L/K)) (l : L) :
    functionFieldPullback (scalarExtensionAutomorphism K L f σ)
      (constantToFunctionField L (pullback.snd f
        (Spec.map (CommRingCat.ofHom (algebraMap K L)))) l) =
      constantToFunctionField L (pullback.snd f
        (Spec.map (CommRingCat.ofHom (algebraMap K L)))) (σ l) := by
  rw [functionFieldPullback_constant, scalarExtensionAutomorphism_snd,
    constantToFunctionField_comp_spec]
  rfl

lemma functionFieldPullback_congr
    {X Y : Scheme} [IsIntegral X] [IsIntegral Y]
    (f g : X ⟶ Y) [IsDominant f] [IsDominant g] (h : f = g) :
    functionFieldPullback f = functionFieldPullback g := by
  subst h
  rfl

lemma scalarExtensionAutomorphism_pullback_pullback
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    {X : Scheme.{u}} [IsIntegral X]
    (f : X ⟶ Spec (.of K)) [GeometricallyIntegral f]
    (σ : Gal(L/K)) (x : X.functionField) :
    functionFieldPullback (scalarExtensionAutomorphism K L f σ)
      (functionFieldPullback (pullback.fst f
        (Spec.map (CommRingCat.ofHom (algebraMap K L)))) x) =
      functionFieldPullback (pullback.fst f
        (Spec.map (CommRingCat.ofHom (algebraMap K L)))) x := by
  rw [← RingHom.comp_apply, ← functionFieldPullback_comp]
  congr 1
  exact functionFieldPullback_congr _ _ (scalarExtensionAutomorphism_fst K L f σ)

end

open scoped TensorProduct

 

theorem scalarExtensionGaloisAction_eq_pullback
    (K A L M : Type u) [Field K] [CommRing A] [IsDomain A] [Field L] [Field M]
    [Algebra K A] [Algebra K L] [Algebra K M] [Algebra A M] [IsScalarTower K A M]
    [IsFractionRing A M] [Module.Finite K L]
    {X : Scheme.{u}} [IsIntegral X]
    (f : X ⟶ Spec (.of K)) [GeometricallyIntegral f]
    (j : Spec (.of A) ⟶ X) [IsOpenImmersion j] [IsDominant j]
    (hj : Spec.map (CommRingCat.ofHom (algebraMap K A)) = j ≫ f)
    (σ : Gal(L/K))
    (x : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap K L)))).functionField) :
    letI := scalarExtensionGaloisAction K A L M f j hj
    σ • x = functionFieldPullback (scalarExtensionAutomorphism K L f σ) x := by
  let e := scalarExtensionFunctionFieldEquivLeft K A L M f j hj
  let π := pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap K L)))
  let C := constantToFunctionField L (pullback.snd f
    (Spec.map (CommRingCat.ofHom (algebraMap K L))))
  let b := chartFunctionFieldEquiv A M j
  have hc (l : L) : e (l ⊗ₜ[K] (1 : M)) = C l :=
    scalarExtensionFunctionFieldEquiv_constant K A L M f j hj l
  have hm (m : M) : e ((1 : L) ⊗ₜ[K] m) = functionFieldPullback π (b m) :=
    scalarExtensionFunctionFieldEquiv_pullback K A L M f j hj m
  have ht (l : L) (m : M) : e (l ⊗ₜ[K] m) = C l * functionFieldPullback π (b m) := by
    rw [← hc l, ← hm m, ← map_mul]
    simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  change e (Algebra.TensorProduct.map σ.toAlgHom (AlgHom.id K M) (e.symm x)) = _
  obtain ⟨t, rfl⟩ := e.surjective x
  rw [RingEquiv.symm_apply_apply]
  induction t using TensorProduct.inductionOn with
  | tmul l m =>
      rw [Algebra.TensorProduct.map_tmul]
      change e (σ l ⊗ₜ[K] m) = _
      rw [ht, ht, map_mul, scalarExtensionAutomorphism_pullback_constant,
        scalarExtensionAutomorphism_pullback_pullback]
  | add t t' h h' => simp only [map_add, h, h']

lemma schemeBaseChangeGaloisAction_eq_pullback
    (K L : Type u) [Field K] [Field L] [Algebra K L] [Module.Finite K L]
    {X : Scheme.{u}} [IsIntegral X]
    (f : X ⟶ Spec (.of K)) [GeometricallyIntegral f]
    (σ : Gal(L/K))
    (x : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap K L)))).functionField) :
    letI := schemeBaseChangeGaloisAction K L f
    σ • x = functionFieldPullback (scalarExtensionAutomorphism K L f σ) x := by
  let := fieldAffineChartAlgebra K f
  exact @scalarExtensionGaloisAction_eq_pullback K (fieldAffineChartRing X) L
    (FractionRing (fieldAffineChartRing X)) _ _ (fieldAffineChartRing_isDomain X)
    _ _ _ _ _ _ _ _ _ X _ f _ (fieldAffineChartMap X) _ _
    (fieldAffineChart_algebraMap_spec K f) σ x

end RelativeDenominators
end

end OAI
