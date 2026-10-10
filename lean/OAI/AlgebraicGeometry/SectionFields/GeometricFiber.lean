import Mathlib
import OAI.AlgebraicGeometry.SectionFields.AlgebraicDescent
import OAI.AlgebraicGeometry.SectionFields.TensorDomains

namespace OAI

/-! Geometric integrality of contraction fibres and exact presentations. -/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Order Polynomial
open scoped TensorProduct WithZero
universe u

namespace RelativeDenominators
section
attribute [local instance 2000] CommRingCat.commRing
open scoped TensorProduct

 

theorem scalarExtensionChart_domain_of_relatively_closed
    (K A L : Type u) [Field K] [CharZero K] [CommRing A] [IsDomain A] [Field L]
    [Algebra K A] [Algebra K L]
    {X : Scheme.{u}} [IsIntegral X] (f : X ⟶ Spec (.of K))
    (h : letI := (constantToFunctionField K f).toAlgebra
      IsIntegrallyClosedIn K X.functionField)
    (j : Spec (.of A) ⟶ X) [IsOpenImmersion j] [IsDominant j]
    (hj : Spec.map (CommRingCat.ofHom (algebraMap K A)) = j ≫ f) :
    IsDomain (A ⊗[K] L) := by
  let := (constantToFunctionField K f).toAlgebra
  let : IsIntegrallyClosedIn K X.functionField := h
  let : Algebra A (Spec (.of A)).functionField :=
    AlgebraicGeometry.instAlgebraCarrierFunctionFieldSpec (.of A)
  let : IsFractionRing A (Spec (.of A)).functionField :=
    functionField_isFractionRing_of_affine (.of A)
  let e : A →ₐ[K] X.functionField :=
    { toRingHom := (functionFieldOpenEquiv j).symm.toRingHom.comp
        (algebraMap A (Spec (.of A)).functionField)
      commutes' := by
        intro a
        apply (functionFieldPullback j).injective
        change (functionFieldOpenEquiv j)
          ((functionFieldOpenEquiv j).symm (algebraMap A (Spec (.of A)).functionField
            (algebraMap K A a))) = functionFieldPullback j (constantToFunctionField K f a)
        rw [RingEquiv.apply_symm_apply, functionFieldPullback_constant, ← hj,
          constantToFunctionField_spec] }
  have he : Function.Injective e :=
    (functionFieldOpenEquiv j).symm.injective.comp
      (IsFractionRing.injective A (Spec (.of A)).functionField)
  let t := Algebra.TensorProduct.map e (AlgHom.id K L)
  have ht : Function.Injective t := by
    change Function.Injective (LinearMap.rTensor L e.toLinearMap)
    exact Module.Flat.rTensor_preserves_injective_linearMap _ he
  let : IsDomain (X.functionField ⊗[K] L) :=
    tensor_domain_of_relatively_closed K X.functionField L
  exact ht.isDomain t.toRingHom

 

theorem geometricallyIntegral_of_functionField_relatively_closed
    (K : Type u) [Field K] [CharZero K]
    {X : Scheme.{u}} [IsIntegral X] (f : X ⟶ Spec (.of K))
    (h : letI := (constantToFunctionField K f).toAlgebra
      IsIntegrallyClosedIn K X.functionField) : GeometricallyIntegral f := by
  let : ObjectProperty.IsClosedUnderIsomorphisms (C := Scheme.{u}) IsIntegral :=
    ⟨fun e _ => IsIntegral.of_isIso e.hom⟩
  constructor
  rw [geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms]
  intro L _ _
  let g := Spec.map (CommRingCat.ofHom (algebraMap K L))
  let P := pullback f g
  let p : P ⟶ X := pullback.fst f g
  have hchart (A : CommRingCat.{u}) (j : Spec A ⟶ X)
      [IsOpenImmersion j] [Nonempty (Spec A)] [Algebra K A]
      (hj : Spec.map (CommRingCat.ofHom (algebraMap K A)) = j ≫ f) :
      IsDomain (A ⊗[K] L) := by
    let : IsIntegral (Spec A) := isIntegral_of_isOpenImmersion j
    let : IsDomain A := (affine_isIntegral_iff A).mp inferInstance
    let : IsDominant j := isDominant_of_openIntegral j
    exact scalarExtensionChart_domain_of_relatively_closed K A L f h j hj
  let (y : P) : _root_.IsReduced (P.presheaf.stalk y) := by
    let i := X.affineOpenCover.idx (p y)
    let A := X.affineOpenCover.X i
    let j : Spec A ⟶ X := X.affineOpenCover.f i
    let : IsOpenImmersion j := X.affineOpenCover.map_prop i
    have hc : p y ∈ Set.range j := X.affineOpenCover.covers (p y)
    let : Nonempty (Spec A) := ⟨hc.choose⟩
    let k := (Spec.map_surjective (j ≫ f)).choose
    let := k.hom.toAlgebra
    have hj : Spec.map (CommRingCat.ofHom (algebraMap K A)) = j ≫ f :=
      (Spec.map_surjective (j ≫ f)).choose_spec
    let : IsDomain (A ⊗[K] L) := hchart A j hj
    let jl := scalarExtensionChart K A L f j hj
    have hy : y ∈ Set.range jl := by
      rw [scalarExtensionChart_range]
      exact hc
    obtain ⟨y', hy'⟩ := hy
    have hr : _root_.IsReduced (P.presheaf.stalk (jl y')) :=
      isReduced_of_injective (jl.stalkMap y').hom
        (ConcreteCategory.bijective_of_isIso (jl.stalkMap y')).1
    rw [hy'] at hr
    exact hr
  let : AlgebraicGeometry.IsReduced P := isReduced_of_isReduced_stalk P
  let := fieldAffineChartAlgebra K f
  let : IsDomain (fieldAffineChartRing X ⊗[K] L) :=
    scalarExtensionChart_domain_of_relatively_closed K (fieldAffineChartRing X) L f h
      (fieldAffineChartMap X) (fieldAffineChart_algebraMap_spec K f)
  let jl := scalarExtensionChart K (fieldAffineChartRing X) L f
    (fieldAffineChartMap X) (fieldAffineChart_algebraMap_spec K f)
  have hd : DenseRange jl := by
    change Dense (Set.range jl)
    rw [scalarExtensionChart_range]
    exact (fieldAffineChartMap X).denseRange.preimage p.isOpenMap
  have hi : IsIrreducible (Set.range jl) := by
    simpa only [Set.image_univ] using
      (IrreducibleSpace.isIrreducible_univ (Spec (.of (fieldAffineChartRing X ⊗[K] L)))).image
        jl jl.continuous.continuousOn
  let : IrreducibleSpace P := (irreducibleSpace_def _).mpr (by
    change IsIrreducible (Set.univ : Set P)
    rw [← hd.closure_range]
    exact hi.closure)
  exact isIntegral_of_irreducibleSpace_of_isReduced P

end

section
attribute [local instance 2000] CommRingCat.commRing

 

noncomputable def genericPointStalkMap
    {X Z : Scheme} [IsIntegral Z] (f : X ⟶ Z)
    (x : X) (hx : f x = genericPoint Z) : Z.functionField →+* X.presheaf.stalk x :=
  ((Z.presheaf.stalkCongr (Inseparable.of_eq hx)).inv ≫ f.stalkMap x).hom

lemma genericPointStalkMap_compat
    {X Z : Scheme} [IsIntegral X] [IsIntegral Z]
    (f : X ⟶ Z) [IsDominant f] (x : X) (hx : f x = genericPoint Z)
    (a : Z.functionField) :
    algebraMap (X.presheaf.stalk x) X.functionField (genericPointStalkMap f x hx a) =
      functionFieldPullback f a := by
  let e := Z.presheaf.stalkCongr (Inseparable.of_eq hx)
  have he : Z.presheaf.stalkSpecializes ((genericPoint_spec Z).specializes (y := f x) trivial) =
      e.hom := rfl
  have ha : algebraMap (Z.presheaf.stalk (f x)) Z.functionField (e.inv a) = a := by
    change Z.presheaf.stalkSpecializes _ (e.inv a) = a
    rw [he]
    exact congrArg (fun h => h a) e.inv_hom_id
  calc
    _ = algebraMap (X.presheaf.stalk x) X.functionField (f.stalkMap x (e.inv a)) := rfl
    _ = functionFieldPullback f
        (algebraMap (Z.presheaf.stalk (f x)) Z.functionField (e.inv a)) :=
      (functionFieldPullback_stalk f x (e.inv a)).symm
    _ = _ := congrArg (functionFieldPullback f) ha

 

theorem integral_rational_stalk_unit_over_generic
    {X Z : Scheme} [IsIntegral X] [IsIntegral Z]
    (hNX : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (f : X ⟶ Z) [IsDominant f]
    (u : X.functionFieldˣ)
    (hu : letI := (functionFieldPullback f).toAlgebra
      IsIntegral Z.functionField (u : X.functionField))
    (x : X) (hx : f x = genericPoint Z) :
    ∃ s : (X.presheaf.stalk x)ˣ,
      algebraMap (X.presheaf.stalk x) X.functionField (s : X.presheaf.stalk x) =
        (u : X.functionField) := by
  let := (functionFieldPullback f).toAlgebra
  let := (genericPointStalkMap f x hx).toAlgebra
  let : IsScalarTower Z.functionField (X.presheaf.stalk x) X.functionField :=
    IsScalarTower.of_algebraMap_eq fun a => (genericPointStalkMap_compat f x hx a).symm
  let := hNX x
  obtain ⟨s, hs⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral
    (hu.tower_top (A := X.presheaf.stalk x))
  obtain ⟨t, ht⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral
    (hu.inv.tower_top (A := X.presheaf.stalk x))
  have hmul : s * t = 1 := by
    apply IsFractionRing.injective (X.presheaf.stalk x) X.functionField
    rw [map_mul, hs, ht, map_one, mul_inv_cancel₀ (Units.ne_zero u)]
  exact ⟨Units.mkOfMulEqOne s t hmul, hs⟩

 

theorem contraction_functionField_integrallyClosedIn
    {X Z : Scheme} [IsIntegral X] [IsIntegral Z] [IsNoetherian X]
    (hNX : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (f : X ⟶ Z) [IsDominant f] [IsIso f.c] :
    letI := (functionFieldPullback f).toAlgebra
    IsIntegrallyClosedIn Z.functionField X.functionField := by
  let := (functionFieldPullback f).toAlgebra
  apply isIntegrallyClosedIn_iff.mpr
  refine ⟨(functionFieldPullback f).injective, ?_⟩
  intro v hv
  by_cases h0 : v = 0
  · exact ⟨0, by simp [h0]⟩
  let u : X.functionFieldˣ := Units.mk0 v h0
  have hvert : IsVerticalDivisor f (principalDivisor X u) := by
    intro p hp hgen
    obtain ⟨s, hs⟩ := integral_rational_stalk_unit_over_generic hNX f u hv p.1 hgen
    apply hp
    change X.ord (u : X.functionField) p.1 = 0
    apply (X.ord_eq_iff p.2 (Units.ne_zero u)).mpr
    let : Ring.KrullDimLE 1 (X.presheaf.stalk p.1) := krullDimLE_of_coheight_le p.2.le
    change Ring.ordFrac (X.presheaf.stalk p.1) (u : X.functionField) = 1
    rw [← hs]
    exact Ring.ordFrac_of_isUnit s.isUnit
  obtain ⟨w, hw⟩ := rational_function_descends_of_vertical_divisor hNX f u hvert
  exact ⟨(w : Z.functionField), hw⟩


instance fromSpecStalk_generic_dominant (Z : Scheme.{u}) [IsIntegral Z] :
    IsDominant (Z.fromSpecStalk (genericPoint Z)) := by
  constructor
  intro x
  rw [range_fromSpecStalk_generic, (genericPoint_spec Z).def]
  trivial

lemma functionFieldPullback_fromSpecStalk_generic (Z : Scheme.{u}) [IsIntegral Z] :
    functionFieldPullback (Z.fromSpecStalk (genericPoint Z)) =
      constantToFunctionField Z.functionField (𝟙 (Spec Z.functionField)) := by
  ext z
  obtain ⟨U, hU, s, rfl⟩ := Z.presheaf.exists_germ_eq z
  let : Nonempty U := ⟨⟨genericPoint Z, hU⟩⟩
  change functionFieldPullback (Z.fromSpecStalk (genericPoint Z)) (Z.germToFunctionField U s) = _
  rw [functionFieldPullback_germ, Scheme.fromSpecStalk_app hU]
  unfold constantToFunctionField
  simp only [Scheme.Hom.id_appTop, RingHom.comp_apply]
  change ((Spec Z.functionField).presheaf.map (homOfLE le_top).op ≫
    (Spec Z.functionField).germToFunctionField _)
      ((Scheme.ΓSpecIso Z.functionField).inv (Z.presheaf.germ U (genericPoint Z) hU s)) = _
  rw [TopCat.Presheaf.germ_res]
  rfl

 

lemma genericFiber_constant_compat
    {X Z : Scheme.{u}} [IsIntegral X] [IsIntegral Z]
    (f : X ⟶ Z) [IsDominant f] (z : Z.functionField) :
    constantToFunctionField Z.functionField (genericFiberToSpec f) z =
      genericFiberFunctionFieldEquiv f (functionFieldPullback f z) := by
  let η := Z.fromSpecStalk (genericPoint Z)
  let q := genericFiberToSpec f
  let : Subsingleton (Spec Z.functionField) :=
    inferInstanceAs (Subsingleton (PrimeSpectrum Z.functionField))
  let : IsDominant q := ⟨(Function.surjective_to_subsingleton q).denseRange⟩
  have hp : genericFiberι f ≫ f = q ≫ η := pullback.condition
  have heq : (functionFieldPullback (genericFiberι f)).comp (functionFieldPullback f) =
      (functionFieldPullback q).comp (functionFieldPullback η) := by
    rw [← functionFieldPullback_comp, ← functionFieldPullback_comp]
    congr 1
  calc
    constantToFunctionField Z.functionField (genericFiberToSpec f) z =
        functionFieldPullback q (constantToFunctionField Z.functionField
          (𝟙 (Spec Z.functionField)) z) := by
      rw [functionFieldPullback_constant]
      simp [q]
    _ = functionFieldPullback q (functionFieldPullback η z) := by
      rw [functionFieldPullback_fromSpecStalk_generic]
    _ = genericFiberFunctionFieldEquiv f (functionFieldPullback f z) :=
      (RingHom.congr_fun heq z).symm

 

theorem contraction_genericFiber_geometricallyIntegral
    {X Z : Scheme.{u}} [IsIntegral X] [IsIntegral Z] [IsNoetherian X]
    [CharZero Z.functionField]
    (hNX : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (f : X ⟶ Z) [IsDominant f] [IsIso f.c] :
    GeometricallyIntegral (genericFiberToSpec f) := by
  apply geometricallyIntegral_of_functionField_relatively_closed Z.functionField
  let := (constantToFunctionField Z.functionField (genericFiberToSpec f)).toAlgebra
  let := (functionFieldPullback f).toAlgebra
  let := contraction_functionField_integrallyClosedIn hNX f
  let e : X.functionField ≃ₐ[Z.functionField] (genericFiber f).functionField :=
    { genericFiberFunctionFieldEquiv f with
      commutes' := fun z => (genericFiber_constant_compat f z).symm }
  apply isIntegrallyClosedIn_iff.mpr
  refine ⟨(algebraMap Z.functionField (genericFiber f).functionField).injective, ?_⟩
  intro z hz
  obtain ⟨a, ha⟩ := IsIntegrallyClosedIn.algebraMap_eq_of_integral
    (hz.map e.symm.toAlgHom)
  refine ⟨a, ?_⟩
  apply e.symm.injective
  simpa using ha

end

section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

 

theorem contraction_exact_presentation_of_geometricGenericFiber_principalization
    {X Z : Scheme.{u}} [IsIntegral X] [IsIntegral Z] [IsNoetherian X] [IsNoetherian Z]
    (hNX : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (hNZ : ∀ z : Z, IsIntegrallyClosed (Z.presheaf.stalk z))
    (f : X ⟶ Z) [IsDominant f] [IsIso f.c] [IsProper f]
    [CharZero Z.functionField]
    (L : Type u) [Field L] [Algebra Z.functionField L] [IsGalois Z.functionField L]
    (A : RationalWeilDivisor X) (hA : IsQCartier X A)
    (D : RationalWeilDivisor Z) (hD : IsQCartier Z D)
    (hlinear : RationallyLinearlyEquivalent X A (pullbackQCartier hNZ f D hD))
    (p : ℕ) (hp : 0 < p)
    :
    letI := contraction_genericFiber_geometricallyIntegral hNX f
    ∀ (u : (pullback (genericFiberToSpec f) (Spec.map
      (CommRingCat.ofHom (algebraMap Z.functionField L)))).functionFieldˣ)
    (_ : letI : IsNoetherian (pullback (genericFiberToSpec f) (Spec.map
        (CommRingCat.ofHom (algebraMap Z.functionField L)))) := {}
      (p : ℚ) • pullbackQCartier (genericFiber_normal f hNX)
        (pullback.fst (genericFiberToSpec f) (Spec.map
          (CommRingCat.ofHom (algebraMap Z.functionField L))))
        (pullbackQCartier hNX (genericFiberι f) A hA)
        (isQCartier_pullback hNX (genericFiberι f) A hA) +
      rationalPrincipalDivisor _ u = 0),
    ∃ (ψ : X.functionFieldˣ) (DZ : RationalWeilDivisor Z) (hDZ : IsQCartier Z DZ),
      RationallyLinearlyEquivalent Z DZ D ∧
      A + (p : ℚ)⁻¹ • rationalPrincipalDivisor X ψ = pullbackQCartier hNZ f DZ hDZ := by
  let := contraction_genericFiber_geometricallyIntegral hNX f
  intro u hu
  exact relative_exact_presentation_of_geometricGenericFiber_principalization
    hNX hNZ f L A hA D hD hlinear p hp u hu

end

 

theorem complex_contraction_exact_presentation_of_geometricGenericFiber_principalization
    {X Z : Scheme.{0}} [IsIntegral X] [IsIntegral Z] [IsNoetherian X] [IsNoetherian Z]
    (hNX : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (hNZ : ∀ z : Z, IsIntegrallyClosed (Z.presheaf.stalk z))
    (f : X ⟶ Z) [IsDominant f] [IsIso f.c] [IsProper f]
    (z : Z ⟶ Spec (.of ℂ))
    (A : RationalWeilDivisor X) (hA : IsQCartier X A)
    (D : RationalWeilDivisor Z) (hD : IsQCartier Z D)
    (hlinear : RationallyLinearlyEquivalent X A (pullbackQCartier hNZ f D hD))
    (p : ℕ) (hp : 0 < p)
    :
    letI := (constantToFunctionField ℂ z).toAlgebra
    letI := Algebra.charZero_of_charZero ℂ Z.functionField
    letI := contraction_genericFiber_geometricallyIntegral hNX f
    ∀ (u : (pullback (genericFiberToSpec f) (Spec.map
      (CommRingCat.ofHom (algebraMap Z.functionField (AlgebraicClosure Z.functionField))))).functionFieldˣ)
    (_ : letI : IsNoetherian (pullback (genericFiberToSpec f) (Spec.map
        (CommRingCat.ofHom (algebraMap Z.functionField (AlgebraicClosure Z.functionField))))) := {}
      (p : ℚ) • pullbackQCartier (genericFiber_normal f hNX)
        (pullback.fst (genericFiberToSpec f) (Spec.map
          (CommRingCat.ofHom (algebraMap Z.functionField (AlgebraicClosure Z.functionField)))))
        (pullbackQCartier hNX (genericFiberι f) A hA)
        (isQCartier_pullback hNX (genericFiberι f) A hA) +
      rationalPrincipalDivisor _ u = 0),
    ∃ (ψ : X.functionFieldˣ) (DZ : RationalWeilDivisor Z) (hDZ : IsQCartier Z DZ),
      RationallyLinearlyEquivalent Z DZ D ∧
      A + (p : ℚ)⁻¹ • rationalPrincipalDivisor X ψ = pullbackQCartier hNZ f DZ hDZ := by
  let := (constantToFunctionField ℂ z).toAlgebra
  let := Algebra.charZero_of_charZero ℂ Z.functionField
  exact contraction_exact_presentation_of_geometricGenericFiber_principalization
    hNX hNZ f (AlgebraicClosure Z.functionField) A hA D hD hlinear p hp

end RelativeDenominators
end

end OAI
