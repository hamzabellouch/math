import Mathlib
import OAI.AlgebraicGeometry.NumericalDimension.CartierIntersection

namespace OAI

/-! Normalization Rings. -/

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace NumericalDimensionOne
open AlgebraicGeometry CategoryTheory
variable {C Y : Scheme} [IsIntegral C] [IsIntegral Y]
  [IsLocallyNoetherian C] [IsLocallyNoetherian Y]
  [StalkwiseNormal C] [StalkwiseNormal Y] [CompactSpace Y] [CompactSpace C]
omit [StalkwiseNormal C] in

theorem IsPulledCartierRepresentative.exists_effective_local_orders
    (f : C ⟶ Y) {D : WeilDivisor Y} {E : WeilDivisor C}
    (hE : IsPulledCartierRepresentative f D E)
    (hη : f (genericPoint C) ∉ divisorSupport D) :
    ∃ t : C.functionField, t ≠ 0 ∧ ∀ (p : PrimeDivisor C)
      (b : CartierStalkEquation D (f p.1)),
      f.stalkMap p.1 b.regular ≠ 0 ∧
      (principalWeilDivisor t + E) p =
        C.ord (algebraMap (C.presheaf.stalk p.1) C.functionField
          (f.stalkMap p.1 b.regular)) p.1 := by
  obtain ⟨U, _, hηU, g, hg, hDg, hEloc⟩ := hE
  have hone : principalWeilDivisor (1 : Y.functionField) = 0 := by
    ext p
    simp only [principalWeilDivisor_apply, order_one, Finsupp.zero_apply]
  have hnonvan : f (genericPoint C) ∈ sectionNonvanishing D 1 := by
    simpa only [sectionNonvanishing, hone, zero_add, divisorComplement,
      TopologicalSpace.Opens.mem_mk, Set.mem_compl_iff] using hη
  obtain ⟨a, ha, hea⟩ := section_unit_stalk one_ne_zero hg hDg hηU hnonvan
  have hea' : algebraMap (Y.presheaf.stalk (f (genericPoint C))) Y.functionField a = g := by
    simpa only [one_mul] using hea
  let t : C.functionField := f.stalkMap (genericPoint C) a
  have ht : t ≠ 0 := (ha.map (f.stalkMap (genericPoint C)).hom).ne_zero
  refine ⟨t, ht, ?_⟩
  intro p b
  obtain ⟨v, hv, hev⟩ := local_equation_ratio_unit b.nonzero hg b.equation hDg
    (image_generic_mem f b.mem_openSet) hηU
  obtain ⟨V, _, hpV, h, hh, hDh, w, hw, hew, heword⟩ := hEloc p.1
  have heord : E p = C.ord (f.stalkMap (genericPoint C) v) p.1 := by
    apply (heword p hpV).trans
    exact (curve_equation_order_eq f b.nonzero hh hg b.equation hDh
      v w hw hev hew p b.mem_openSet hpV).symm
  let hsp : genericPoint C ⤳ p.1 := (genericPoint_spec C).specializes trivial
  have heq : a * v =
      Y.presheaf.stalkSpecializes (f.base.hom.map_specializes hsp) b.regular := by
    apply IsFractionRing.injective (Y.presheaf.stalk (f (genericPoint C))) Y.functionField
    rw [map_mul, hea', hev, algebraMap_stalkSpecializes, b.regular_eq]
    exact mul_div_cancel₀ _ hg
  have hfield : t * f.stalkMap (genericPoint C) v =
      algebraMap (C.presheaf.stalk p.1) C.functionField
        (f.stalkMap p.1 b.regular) := by
    rw [show t = f.stalkMap (genericPoint C) a from rfl, ← map_mul, heq,
      f.stalkSpecializes_stalkMap_apply (genericPoint C) p.1 hsp b.regular]
    rfl
  have hn : f.stalkMap (genericPoint C) v ≠ 0 :=
    (hv.map (f.stalkMap (genericPoint C)).hom).ne_zero
  have hn' : f.stalkMap p.1 b.regular ≠ 0 := by
    intro hz
    have := hfield
    rw [hz, map_zero] at this
    exact mul_ne_zero ht hn this
  refine ⟨hn', ?_⟩
  change C.ord t p.1 + E p = _
  rw [heord, ← C.ord_mul ht hn, hfield]
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace NumericalDimensionOne
open AlgebraicGeometry CategoryTheory
variable {C Y : Scheme} [IsIntegral C] [IsIntegral Y]
  [IsLocallyNoetherian C] [IsLocallyNoetherian Y] [StalkwiseNormal Y]
  [CompactSpace C] [CompactSpace Y]
variable (sC : C ⟶ Spec (.of ℂ)) [SmoothOfRelativeDimension 1 sC] [IsProper sC]
include sC in

theorem properCurveDegree_eq_local_orders (f : C ⟶ Y)
    (D : cartierDivisors (X := Y))
    (hη : f (genericPoint C) ∉ divisorSupport D.1)
    (b : ∀ p : PrimeDivisor C, CartierStalkEquation D.1 (f p.1)) :
    properCurveDegree f D = ∑ᶠ p : PrimeDivisor C,
      ((Ring.ord (C.presheaf.stalk p.1) (f.stalkMap p.1 (b p).regular)).toNat : ℤ) := by
  classical
  let E := Classical.choose (exists_pulledCartierRepresentative f D.1 D.2)
  have hE := Classical.choose_spec (exists_pulledCartierRepresentative f D.1 D.2)
  obtain ⟨t, _, ht⟩ := hE.exists_effective_local_orders f hη
  let F := principalWeilDivisor t + E
  have hF : ∀ p : PrimeDivisor C, F p =
      ((Ring.ord (C.presheaf.stalk p.1) (f.stalkMap p.1 (b p).regular)).toNat : ℤ) := by
    intro p
    exact (ht p (b p)).2.trans
      (NumericalDimensionOneCurveAux.scheme_order_of_stalk_element p.1 p.2 _ (ht p (b p)).1)
  have hsum : complexWeilDegree F = complexWeilDegree E := by
    change (principalWeilDivisor t + E).sum (fun _ a => a) = _
    rw [Finsupp.sum_add_index (fun _ _ => rfl) (fun _ _ _ _ => rfl)]
    change complexWeilDegree (principalWeilDivisor t) + complexWeilDegree E = _
    rw [proper_principal_degree_zero sC, zero_add]
  rw [properCurveDegree_eq sC f D E hE, ← hsum]
  calc
    complexWeilDegree F = ∑ᶠ p, F p := by
      symm
      exact finsum_eq_sum_of_support_subset F (by
        intro p hp
        exact Finsupp.mem_support_iff.mpr hp)
    _ = _ := finsum_congr hF
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace NumericalDimensionOne

theorem fractionField_finite_of_finite (A B K : Type*)
    [CommRing A] [IsDomain A] [CommRing B] [IsDomain B] [Field K]
    [Algebra A B] [FaithfulSMul A B] [Module.Finite A B]
    [Algebra B K] [IsFractionRing B K]
    [Algebra A K] [IsScalarTower A B K]
    [Algebra (FractionRing A) K] [IsScalarTower A (FractionRing A) K] :
    Module.Finite (FractionRing A) K := by
  let F := FractionRing A
  let T := B ⊗[A] F
  let : Algebra F T := Algebra.TensorProduct.rightAlgebra
  have hinj : Function.Injective (algebraMap A B) := FaithfulSMul.algebraMap_injective A B
  have hM : Algebra.algebraMapSubmonoid B A⁰ ≤ B⁰ := by
    rintro x ⟨y, hy, rfl⟩
    exact mem_nonZeroDivisors_iff_ne_zero.mpr
      ((map_ne_zero_iff _ hinj).mpr (mem_nonZeroDivisors_iff_ne_zero.mp hy))
  let : IsDomain T := IsLocalization.isDomain_of_le_nonZeroDivisors T hM
  let : Module.Finite F T := Module.Finite.of_isLocalization A B A⁰
  let : IsArtinianRing T := .of_finite F T
  let : Field T := (IsArtinianRing.isField_of_isDomain T).toField
  have hBT : Function.Injective (algebraMap B T) := IsLocalization.injective T hM
  let : IsFractionRing B T := IsLocalization.of_le (Algebra.algebraMapSubmonoid B A⁰) B⁰ hM
    fun x hx => isUnit_iff_ne_zero.mpr ((map_ne_zero_iff _ hBT).mpr
      (mem_nonZeroDivisors_iff_ne_zero.mp hx))
  let : IsLocalization (Algebra.algebraMapSubmonoid B A⁰) K :=
    IsLocalization.isLocalization_of_algEquiv _ (IsLocalization.algEquiv B⁰ T K)
  exact Module.Finite.of_isLocalization A B A⁰

theorem finite_integralClosure_of_finiteType (k R K : Type*)
    [Field k] [CharZero k] [CommRing R] [IsDomain R]
    [Algebra k R] [Algebra.FiniteType k R]
    [Field K] [Algebra R K] [IsFractionRing R K] :
    Module.Finite R (integralClosure R K) := by
  classical
  obtain ⟨n, g, hg, hfin⟩ := exists_finite_inj_algHom_of_fg k R
  let A := MvPolynomial (Fin n) k
  let : Algebra A R := g.toRingHom.toAlgebra
  have : Module.Finite A R := hfin
  have : FaithfulSMul A R := (faithfulSMul_iff_algebraMap_injective A R).mpr hg
  let : Algebra A K := ((algebraMap R K).comp g.toRingHom).toAlgebra
  have : IsScalarTower A R K := IsScalarTower.of_algebraMap_eq' rfl
  have : FaithfulSMul A K := (faithfulSMul_iff_algebraMap_injective A K).mpr
    ((IsFractionRing.injective R K).comp hg)
  let : Algebra (FractionRing A) K := FractionRing.liftAlgebra A K
  have : IsScalarTower A (FractionRing A) K := FractionRing.isScalarTower_liftAlgebra A K
  have : Module.Finite (FractionRing A) K := fractionField_finite_of_finite A R K
  let C := integralClosure R K
  let : Algebra A C := ((algebraMap R C).comp g.toRingHom).toAlgebra
  have : IsScalarTower A R C := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower A C K := IsScalarTower.to₁₃₄ A R C K
  have : Algebra.IsIntegral A C := Algebra.IsIntegral.trans R
  have : IsIntegralClosure C A K := IsIntegralClosure.of_isIntegrallyClosedIn
  have : Module.Finite A C := IsIntegralClosure.finite A (FractionRing A) K C
  exact Module.Finite.of_restrictScalars_finite A R C
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne
section GenericNormalization
universe u
variable {k : Type u} [Field k] [CharZero k]
variable {X : Scheme.{u}} [AlgebraicGeometry.IsIntegral X]

lemma genericStalk_preimage_eq_top (U : X.Opens) [Nonempty U] :
    (X.fromSpecStalk (genericPoint X)) ⁻¹ᵁ U = ⊤ := by
  apply top_unique
  intro t _
  change (X.fromSpecStalk (genericPoint X)) t ∈ U
  have ht : t = IsLocalRing.closedPoint X.functionField :=
    Subsingleton.elim (α := PrimeSpectrum X.functionField) _ _
  rw [ht, Scheme.fromSpecStalk_closedPoint]
  exact ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr
    (by simpa using (show Nonempty U from inferInstance))

noncomputable def genericSectionsIso (U : X.Opens) [Nonempty U] :
    Γ(Spec X.functionField, (X.fromSpecStalk (genericPoint X)) ⁻¹ᵁ U) ≅ X.functionField :=
  (Spec X.functionField).presheaf.mapIso
    (eqToIso (genericStalk_preimage_eq_top U).symm).op ≪≫ Scheme.ΓSpecIso _

lemma genericSectionsIso_app (U : X.Opens) [Nonempty U] :
    (X.fromSpecStalk (genericPoint X)).app U ≫ (genericSectionsIso U).hom =
      X.germToFunctionField U := by
  have hx : genericPoint X ∈ U :=
    ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr
      (by simpa using (show Nonempty U from inferInstance))
  let V := Spec X.functionField
  let r := V.presheaf.map (homOfLE (show
    (X.fromSpecStalk (genericPoint X)) ⁻¹ᵁ U ≤ ⊤ from le_top)).op
  let t := V.presheaf.map
    (eqToHom (genericStalk_preimage_eq_top U).symm).op
  have hrt : r ≫ t = 𝟙 (Γ(V, ⊤)) := by
    dsimp only [r, t]
    rw [← Functor.map_comp, ← op_comp]
    have h : eqToHom (genericStalk_preimage_eq_top U).symm ≫
        homOfLE (show (X.fromSpecStalk (genericPoint X)) ⁻¹ᵁ U ≤ ⊤ from le_top) =
        𝟙 (⊤ : V.Opens) := Subsingleton.elim _ _
    rw [h, op_id, CategoryTheory.Functor.map_id]
  rw [Scheme.fromSpecStalk_app hx]
  change (X.presheaf.germ U (genericPoint X) hx ≫
    (Scheme.ΓSpecIso X.functionField).inv ≫ r) ≫
    t ≫ (Scheme.ΓSpecIso X.functionField).hom = X.germToFunctionField U
  simp only [Category.assoc, ← Category.assoc r t, hrt, Category.id_comp,
    Iso.inv_hom_id, Category.comp_id]

lemma genericSections_isFractionRing (U : X.Opens) (hU : IsAffineOpen U) [Nonempty U] :
    let := ((X.fromSpecStalk (genericPoint X)).app U).hom.toAlgebra
    IsFractionRing Γ(X, U)
      Γ(Spec X.functionField, (X.fromSpecStalk (genericPoint X)) ⁻¹ᵁ U) := by
  let := ((X.fromSpecStalk (genericPoint X)).app U).hom.toAlgebra
  have := functionField_isFractionRing_of_isAffineOpen X U hU
  let e : Γ(Spec X.functionField, (X.fromSpecStalk (genericPoint X)) ⁻¹ᵁ U) ≃ₐ[Γ(X,U)]
      X.functionField :=
    { Iso.commRingCatIsoToRingEquiv (genericSectionsIso U) with
      commutes' := fun a => congrArg (fun f : Γ(X,U) ⟶ X.functionField => f.hom a)
        (genericSectionsIso_app U) }
  exact IsLocalization.isLocalization_of_algEquiv _ e.symm

theorem finite_genericNormalization [QuasiSeparatedSpace X]
    (sX : X ⟶ Spec (.of k)) [LocallyOfFiniteType sX] :
    AlgebraicGeometry.IsFinite (X.fromSpecStalk (genericPoint X)).fromNormalization := by
  let f := X.fromSpecStalk (genericPoint X)
  refine { finite_app := ?_ }
  intro U hU
  by_cases hne : Nonempty U
  · let := hne
    let R := Γ(X,U)
    let K := Γ(Spec X.functionField, f ⁻¹ᵁ U)
    let : Algebra R K := (f.app U).hom.toAlgebra
    let e : K ≃+* X.functionField := Iso.commRingCatIsoToRingEquiv (genericSectionsIso U)
    let : Field K := (e.toMulEquiv.isField (Field.toIsField X.functionField)).toField
    let : IsFractionRing R K := genericSections_isFractionRing U hU
    let : Algebra k R :=
      ((sX.appLE ⊤ U (by simp)).hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom).toAlgebra
    have : Algebra.FiniteType k R :=
      (sX.finiteType_appLE (isAffineOpen_top _) hU (by simp)).comp
        (RingHom.FiniteType.of_surjective _ (ConcreteCategory.bijective_of_isIso
          (Scheme.ΓSpecIso (.of k)).inv).2)
    have : Module.Finite R (integralClosure R K) :=
      finite_integralClosure_of_finiteType k R K
    rw [f.fromNormalization_app hU]
    exact RingHom.Finite.comp (RingHom.Finite.of_surjective _
      (ConcreteCategory.bijective_of_isIso (f.normalizationObjIso hU).inv).2)
      (RingHom.finite_algebraMap.mpr inferInstance)
  · have hbot : U = ⊥ := by
      apply le_antisymm _ bot_le
      intro x hx
      exact (hne ⟨⟨x, hx⟩⟩).elim
    subst U
    have : Subsingleton Γ(f.normalization, f.fromNormalization ⁻¹ᵁ ⊥) :=
      (f.fromNormalization.app ⊥).hom.codomain_trivial
    exact RingHom.Finite.of_surjective _ (Function.surjective_to_subsingleton _)
end GenericNormalization
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne
open AlgebraicGeometry CategoryTheory TopologicalSpace
variable {X : Scheme} [IsIntegral X] [QuasiSeparatedSpace X]

local instance genericPointMap_quasiCompact :
    QuasiCompact (X.fromSpecStalk (genericPoint X)) := by
  have : NoetherianSpace (Spec X.functionField) := inferInstance
  exact quasiCompact_of_noetherianSpace_source _
omit [QuasiSeparatedSpace X] in

theorem genericNormalization_stalk
    (x : (X.fromSpecStalk (genericPoint X)).normalization) :
    IsDomain ((X.fromSpecStalk (genericPoint X)).normalization.presheaf.stalk x) ∧
    IsIntegrallyClosed ((X.fromSpecStalk (genericPoint X)).normalization.presheaf.stalk x) := by
  let f := X.fromSpecStalk (genericPoint X)
  let N := f.normalization
  obtain ⟨U, hU, hxU, _⟩ := exists_isAffineOpen_mem_and_subset
    (show f.fromNormalization x ∈ (⊤ : X.Opens) from trivial)
  let : Nonempty U := ⟨⟨f.fromNormalization x, hxU⟩⟩
  let R := Γ(X, U)
  let K := Γ(Spec X.functionField, f ⁻¹ᵁ U)
  let : Algebra R K := (f.app U).hom.toAlgebra
  let eK : K ≃+* X.functionField := Iso.commRingCatIsoToRingEquiv (genericSectionsIso U)
  let : Field K := (eK.toMulEquiv.isField (Field.toIsField X.functionField)).toField
  let C := integralClosure R K
  let : IsIntegrallyClosed C := IsIntegrallyClosed.of_isIntegrallyClosedIn C K
  let V := f.fromNormalization ⁻¹ᵁ U
  have hV : IsAffineOpen V := hU.preimage f.fromNormalization
  let e : Γ(N,V) ≃+* C := Iso.commRingCatIsoToRingEquiv (f.normalizationObjIso hU)
  let : IsDomain Γ(N,V) := e.injective.isDomain e.toRingHom
  let : IsIntegrallyClosed Γ(N,V) := IsIntegrallyClosed.of_equiv e.symm
  let y : V := ⟨x, hxU⟩
  let := TopCat.Presheaf.algebra_section_stalk N.presheaf y
  let := hV.isLocalization_stalk y
  have hd := IsLocalization.isDomain_of_le_nonZeroDivisors (N.presheaf.stalk x)
    (hV.primeIdealOf y).asIdeal.primeCompl_le_nonZeroDivisors
  have hn := isIntegrallyClosed_of_isLocalization (N.presheaf.stalk x)
    (hV.primeIdealOf y).asIdeal.primeCompl
    (hV.primeIdealOf y).asIdeal.primeCompl_le_nonZeroDivisors
  exact ⟨hd, hn⟩

omit [QuasiSeparatedSpace X] in

theorem integral_genericNormalization :
    IsIntegral (X.fromSpecStalk (genericPoint X)).normalization := by
  let f := X.fromSpecStalk (genericPoint X)
  have (x : f.normalization) : _root_.IsReduced (f.normalization.presheaf.stalk x) := by
    have := (genericNormalization_stalk x).1
    infer_instance
  let : IsReduced f.normalization := isReduced_of_isReduced_stalk _
  have : IrreducibleSpace f.normalization :=
    { isPreirreducible_univ := by
        rw [← f.toNormalization.denseRange.closure_eq, ← Set.image_univ]
        exact (PreirreducibleSpace.isPreirreducible_univ.image f.toNormalization
          f.toNormalization.continuous.continuousOn).closure
      toNonempty := Nonempty.map f.toNormalization inferInstance }
  exact isIntegral_of_irreducibleSpace_of_isReduced _
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne
open AlgebraicGeometry CategoryTheory TopologicalSpace
variable {X Y : Scheme} [IsIntegral X] [IsIntegral Y]

theorem dominantFunctionFieldMap_bijective_of_preimmersion (f : X ⟶ Y)
    [IsDominant f] [IsPreimmersion f] :
    Function.Bijective (dominantFunctionFieldMap f) := by
  refine ⟨(dominantFunctionFieldMap f).injective, ?_⟩
  exact (f.stalkMap_surjective (genericPoint X)).comp
    (ConcreteCategory.bijective_of_isIso
      (Y.presheaf.stalkCongr (Inseparable.of_eq (dominant_genericPoint f).symm)).hom).2

instance dominant_genericPointMap : IsDominant (X.fromSpecStalk (genericPoint X)) := by
  constructor
  rw [denseRange_iff_closure_range, ← Set.univ_subset_iff, ← genericPoint_spec X]
  apply closure_mono
  rintro y rfl
  exact ⟨IsLocalRing.closedPoint X.functionField, Scheme.fromSpecStalk_closedPoint⟩

attribute [local instance] genericPointMap_quasiCompact

instance genericNormalization_isIntegral :
    IsIntegral (X.fromSpecStalk (genericPoint X)).normalization := integral_genericNormalization
instance dominant_fromGenericNormalization :
    IsDominant (X.fromSpecStalk (genericPoint X)).fromNormalization := by
  let f := X.fromSpecStalk (genericPoint X)
  have : IsDominant (f.toNormalization ≫ f.fromNormalization) := by
    simpa only [Scheme.Hom.toNormalization_fromNormalization] using (inferInstance : IsDominant f)
  exact IsDominant.of_comp f.toNormalization f.fromNormalization

theorem genericNormalization_bijective_functionField :
    Function.Bijective
      (dominantFunctionFieldMap (X.fromSpecStalk (genericPoint X)).fromNormalization) := by
  let f := X.fromSpecStalk (genericPoint X)
  refine ⟨(dominantFunctionFieldMap f.fromNormalization).injective, ?_⟩
  intro a
  obtain ⟨b,hb⟩ := (dominantFunctionFieldMap_bijective_of_preimmersion f).2
    (dominantFunctionFieldMap f.toNormalization a)
  refine ⟨b,(dominantFunctionFieldMap f.toNormalization).injective ?_⟩
  rw [← dominantFunctionFieldMap_comp_apply]
  change dominantFunctionFieldMap (f.toNormalization ≫ f.fromNormalization) b = _
  simpa only [Scheme.Hom.toNormalization_fromNormalization] using hb
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

noncomputable def genericNormalizationSectionsEquiv (U : X.Opens)
    (hU : IsAffineOpen U) [Nonempty U] :
    letI := ((X.fromSpecStalk (genericPoint X)).fromNormalization.app U).hom.toAlgebra
    Γ((X.fromSpecStalk (genericPoint X)).normalization,
      (X.fromSpecStalk (genericPoint X)).fromNormalization ⁻¹ᵁ U) ≃ₐ[Γ(X,U)]
        integralClosure Γ(X,U) X.functionField := by
  let f := X.fromSpecStalk (genericPoint X)
  let N := f.normalization
  let V := f.fromNormalization ⁻¹ᵁ U
  let R := Γ(X,U)
  let K := Γ(Spec X.functionField, f ⁻¹ᵁ U)
  let := (f.app U).hom.toAlgebra
  let := (f.fromNormalization.app U).hom.toAlgebra
  let eK : K ≃ₐ[R] X.functionField :=
    { Iso.commRingCatIsoToRingEquiv (genericSectionsIso U) with
      commutes' := fun a => congrArg (fun g : R ⟶ X.functionField => g.hom a)
        (genericSectionsIso_app U) }
  let eN : Γ(N,V) ≃ₐ[R] integralClosure R K :=
    { Iso.commRingCatIsoToRingEquiv (f.normalizationObjIso hU) with
      commutes' := fun a => by
        change ((f.fromNormalization.app U ≫ (f.normalizationObjIso hU).hom).hom a) = _
        rw [f.fromNormalization_app hU]
        simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
        rfl }
  exact eN.trans ((eK.subalgebraMap (integralClosure R K)).trans
    (Subalgebra.equivOfEq _ _ (integralClosure_map_algEquiv eK)))
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne
open AlgebraicGeometry CategoryTheory
variable {X Y : Scheme} (f : Y ⟶ X) (U : X.Opens) (hU : IsAffineOpen U)
  (hV : IsAffineOpen (f ⁻¹ᵁ U)) (x : U)

noncomputable def affineFiberEquiv :
    letI := (f.app U).hom.toAlgebra
    {y : Y // f y = x.1} ≃ (hU.primeIdealOf x).asIdeal.primesOver Γ(Y,f ⁻¹ᵁ U) := by
  let : Algebra Γ(X,U) Γ(Y,f ⁻¹ᵁ U) := (f.app U).hom.toAlgebra
  let toFun : {y : Y // f y = x.1} →
      (hU.primeIdealOf x).asIdeal.primesOver Γ(Y,f ⁻¹ᵁ U) := fun y => by
    have hy : y.1 ∈ f ⁻¹ᵁ U := by
      change f y.1 ∈ U
      rw [y.2]
      exact x.2
    refine ⟨(hV.primeIdealOf ⟨y.1,hy⟩).asIdeal, inferInstance, ⟨?_⟩⟩
    have he := IsAffineOpen.comap_primeIdealOf_appLE U hU (f ⁻¹ᵁ U) hV le_rfl hy
    change (hU.primeIdealOf x).asIdeal =
      (hV.primeIdealOf ⟨y.1,hy⟩).asIdeal.comap (f.app U).hom
    have he' : (⟨f y.1,hy⟩ : U) = x := Subtype.ext y.2
    rw [Scheme.Hom.appLE_eq_app, he'] at he
    exact (congrArg PrimeSpectrum.asIdeal he).symm
  let invFun : (hU.primeIdealOf x).asIdeal.primesOver Γ(Y,f ⁻¹ᵁ U) →
      {y : Y // f y = x.1} := fun q => by
    let y := hV.isoSpec.inv (⟨q.1,q.2.1⟩ : PrimeSpectrum Γ(Y,f ⁻¹ᵁ U))
    refine ⟨y.1, ?_⟩
    have he := IsAffineOpen.comap_primeIdealOf_appLE U hU (f ⁻¹ᵁ U) hV le_rfl y.2
    have hqy : hV.primeIdealOf y = ⟨q.1,q.2.1⟩ := by
      change hV.isoSpec.hom (hV.isoSpec.inv _) = _
      exact (Scheme.homeoOfIso hV.isoSpec).apply_symm_apply _
    have hyeta : (⟨y.1,y.2⟩ : f ⁻¹ᵁ U) = y := rfl
    rw [hyeta, hqy, Scheme.Hom.appLE_eq_app] at he
    have hf : hU.primeIdealOf ⟨f y.1,y.2⟩ = hU.primeIdealOf x :=
      he.symm.trans (PrimeSpectrum.ext (q.1.over_def _).symm)
    exact (hU.fromSpec_primeIdealOf ⟨f y.1,y.2⟩).symm.trans
      ((congrArg hU.fromSpec hf).trans (hU.fromSpec_primeIdealOf x))
  refine ⟨toFun,invFun,?_,?_⟩
  · intro y
    apply Subtype.ext
    exact hV.fromSpec_primeIdealOf ⟨y.1, by
      change f y.1 ∈ U
      rw [y.2]
      exact x.2⟩
  · intro q
    apply Subtype.ext
    change (hV.primeIdealOf (hV.isoSpec.inv _)).asIdeal = q.1
    change (hV.isoSpec.hom (hV.isoSpec.inv _)).asIdeal = q.1
    exact congrArg PrimeSpectrum.asIdeal ((Scheme.homeoOfIso hV.isoSpec).apply_symm_apply _)
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne
variable {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
  [Algebra A B] [Algebra A C]

noncomputable def primesOverAlgEquiv (p : Ideal A) (e : B ≃ₐ[A] C) :
    p.primesOver C ≃ p.primesOver B := by
  refine
    { toFun := fun q => ⟨q.1.comap e.toRingHom, inferInstance, ⟨?_⟩⟩
      invFun := fun q => ⟨q.1.comap e.symm.toRingHom, inferInstance, ⟨?_⟩⟩
      left_inv := ?_
      right_inv := ?_ }
  · change p = (q.1.comap e.toRingHom).comap (algebraMap A B)
    rw [Ideal.comap_comap]
    have he : e.toRingHom.comp (algebraMap A B) = algebraMap A C := by
      ext a
      exact e.commutes a
    rw [he]
    exact q.1.over_def p
  · change p = (q.1.comap e.symm.toRingHom).comap (algebraMap A C)
    rw [Ideal.comap_comap]
    have he : e.symm.toRingHom.comp (algebraMap A C) = algebraMap A B := by
      ext a
      exact e.symm.commutes a
    rw [he]
    exact q.1.over_def p
  · intro q
    apply Subtype.ext
    ext c
    change e (e.symm c) ∈ q.1 ↔ c ∈ q.1
    rw [e.apply_symm_apply]
  · intro q
    apply Subtype.ext
    ext b
    change e.symm (e b) ∈ q.1 ↔ b ∈ q.1
    rw [e.symm_apply_apply]

lemma primesOverAlgEquiv_asIdeal (p : Ideal A) (e : B ≃ₐ[A] C)
    (q : p.primesOver C) :
    (primesOverAlgEquiv p e q).1 = q.1.comap e.toRingHom := by
  rfl
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne
open scoped nonZeroDivisors
variable (A R K : Type*) [CommRing A] [CommRing R] [Field K]
  [Algebra A R] [Algebra A K] [Algebra R K] [IsScalarTower A R K]

def integralClosureBaseMap : integralClosure A K →+* integralClosure R K :=
  { toFun := fun x => ⟨x.1,x.2.tower_top⟩
    map_one' := rfl
    map_zero' := rfl
    map_mul' := fun _ _ => rfl
    map_add' := fun _ _ => rfl }
lemma integralClosureBaseMap_tower :
    letI := (integralClosureBaseMap A R K).toAlgebra
    IsScalarTower A (integralClosure A K) (integralClosure R K) := by
  let : Algebra (integralClosure A K) (integralClosure R K) :=
    (integralClosureBaseMap A R K).toAlgebra
  exact IsScalarTower.of_algebraMap_eq (fun _ => rfl)
lemma integralClosureBaseMap_isLocalization [IsDomain A] [IsFractionRing A K]
    (M : Submonoid A) (hM : M ≤ A⁰) [IsLocalization M R] :
    letI := (integralClosureBaseMap A R K).toAlgebra
    IsLocalization (Algebra.algebraMapSubmonoid (integralClosure A K) M)
      (integralClosure R K) := by
  let : Algebra (integralClosure A K) (integralClosure R K) :=
    (integralClosureBaseMap A R K).toAlgebra
  have : IsScalarTower (integralClosure A K) (integralClosure R K) K :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have : IsScalarTower A (integralClosure A K) (integralClosure R K) :=
    integralClosureBaseMap_tower A R K
  have hunit : Algebra.algebraMapSubmonoid K M ≤ IsUnit.submonoid K := by
    rintro _ ⟨x,hx,rfl⟩
    exact isUnit_iff_ne_zero.mpr ((map_ne_zero_iff _ (IsFractionRing.injective A K)).mpr
      (mem_nonZeroDivisors_iff_ne_zero.mp (hM hx)))
  let : IsLocalization (Algebra.algebraMapSubmonoid K M) K := IsLocalization.self hunit
  exact IsLocalization.integralClosure M
end NumericalDimensionOne

end OAI
