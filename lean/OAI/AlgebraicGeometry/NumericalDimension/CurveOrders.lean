import Mathlib
import OAI.AlgebraicGeometry.NumericalDimension.ProjectiveCurves

namespace OAI

/-! Curve Orders. -/

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace NumericalDimensionOneCurveAux
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u

theorem isClosed_point_of_curve_coheight {C : Scheme.{u}} [IsIntegral C]
    (hdim : ∀ x : C, Order.coheight x ≤ 1) {x : C}
    (hx : x ≠ genericPoint C) : IsClosed ({x} : Set C) := by
  apply isClosed_of_closure_subset
  intro y hy
  have hxy : x ⤳ y := specializes_iff_mem_closure.mpr hy
  by_contra hyx
  have hyx' : y ≠ x := by simpa using hyx
  have hxylt : y < x := lt_iff_le_not_ge.mpr ⟨hxy, fun h => hyx' (Specializes.antisymm (show y ⤳ x from h) hxy).eq⟩
  have hxηlt : x < genericPoint C := lt_iff_le_not_ge.mpr
    ⟨genericPoint_specializes x, fun h => hx (Specializes.antisymm (show x ⤳ genericPoint C from h)
      (genericPoint_specializes x)).eq⟩
  have h1 : (1 : ℕ∞) ≤ Order.coheight x := by
    calc
      (1 : ℕ∞) = 0 + 1 := by simp
      _ ≤ Order.coheight (genericPoint C) + 1 := add_le_add (show (0 : ℕ∞) ≤ Order.coheight (genericPoint C) from bot_le) le_rfl
      _ ≤ Order.coheight x := Order.coheight_add_one_le hxηlt
  have hcontra : (2 : ℕ∞) ≤ 1 := by
    calc
      (2 : ℕ∞) = 1 + 1 := by norm_num
      _ ≤ Order.coheight x + 1 := add_le_add h1 le_rfl
      _ ≤ Order.coheight y := Order.coheight_add_one_le hxylt
      _ ≤ 1 := hdim y
  norm_num at hcontra

theorem finite_closed_of_curve_coheight {C : Scheme.{u}} [IsIntegral C]
    [NoetherianSpace C] (hdim : ∀ x : C, Order.coheight x ≤ 1)
    {Z : Set C} (hZ : IsClosed Z) (hη : genericPoint C ∉ Z) : Z.Finite := by
  obtain ⟨T, hT, hc, hi, heq⟩ :=
    NoetherianSpace.exists_finite_set_isClosed_irreducible hZ
  rw [heq]
  apply hT.sUnion
  intro t ht
  obtain ⟨x, hx⟩ := QuasiSober.sober (hi t ht) (hc t ht)
  have hxη : x ≠ genericPoint C := by
    intro he
    apply hη
    rw [heq]
    exact Set.mem_sUnion.mpr ⟨t, ht, he ▸ hx.mem⟩
  have hcpoint := isClosed_point_of_curve_coheight hdim hxη
  rw [← hx, hcpoint.closure_eq]
  exact Set.finite_singleton _

theorem finite_of_proper_dominant_from_smooth_curve
    {k : Type u} [Field k] {C Y : Scheme.{u}} [IsIntegral C] [IsIntegral Y]
    [NoetherianSpace C] [Nontrivial Y]
    (sC : C ⟶ Spec (.of k)) [SmoothOfRelativeDimension 1 sC]
    (f : C ⟶ Y) [IsProper f] [IsDominant f] : IsFinite f := by
  have hdim := coheight_le_of_smooth_dimension sC 1
  have hgen : f (genericPoint C) = genericPoint Y := by
    apply ((genericPoint_spec Y).eq _).symm
    simpa only [Set.image_univ, f.denseRange.closure_range] using
      (genericPoint_spec C).image f.continuous
  have hnotclosed : ¬ IsClosed ({genericPoint Y} : Set Y) := by
    intro h
    have hEq : ({genericPoint Y} : Set Y) = Set.univ :=
      h.closure_eq.symm.trans (genericPoint_spec Y)
    have hall : ∀ y : Y, y = genericPoint Y := fun y => by
      have : y ∈ ({genericPoint Y} : Set Y) := hEq.symm ▸ Set.mem_univ y
      exact this
    obtain ⟨a, b, hab⟩ := exists_pair_ne Y
    exact hab ((hall a).trans (hall b).symm)
  let : LocallyQuasiFinite f := LocallyQuasiFinite.of_finite_preimage_singleton f fun y => by
    by_cases hy : y = genericPoint Y
    · apply (Set.finite_singleton (genericPoint C)).subset
      intro x hx
      by_contra hxη
      have hc := isClosed_point_of_curve_coheight hdim (by simpa using hxη)
      apply hnotclosed
      have h := f.isClosedMap _ hc
      have hxy : f x = genericPoint Y := hx.trans hy
      simpa only [Set.image_singleton, hxy] using h
    · have hclosed : IsClosed (f ⁻¹' closure {y}) := isClosed_closure.preimage f.continuous
      have hnot : genericPoint C ∉ f ⁻¹' closure {y} := by
        intro h
        have hp : y ⤳ genericPoint Y := specializes_iff_mem_closure.mpr (hgen ▸ h)
        exact hy (Specializes.antisymm hp (genericPoint_specializes y)).eq
      exact (finite_closed_of_curve_coheight hdim hclosed hnot).subset
        (Set.preimage_mono subset_closure)
  exact IsFinite.of_isProper_of_locallyQuasiFinite f

end NumericalDimensionOneCurveAux

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace NumericalDimensionOneCurveAux
open AlgebraicGeometry CategoryTheory TopologicalSpace

noncomputable def curveFieldScalar {C : Scheme} [IsIntegral C]
    (sC : C ⟶ Spec (.of ℂ)) : ℂ →+* C.functionField :=
  (Spec.preimage (C.fromSpecStalk (genericPoint C) ≫ sC)).hom

noncomputable def curveFunctionPolynomial {C : Scheme} [IsIntegral C]
    (sC : C ⟶ Spec (.of ℂ)) (a : C.functionField) : Polynomial ℂ →+* C.functionField :=
  Polynomial.eval₂RingHom (curveFieldScalar sC) a

noncomputable def genericCurveFunctionMap {C : Scheme} [IsIntegral C]
    (sC : C ⟶ Spec (.of ℂ)) (a : C.functionField) :
    Spec C.functionField ⟶ complexProjectiveSpace 1 :=
  Spec.map (CommRingCat.ofHom (curveFunctionPolynomial sC a)) ≫ complexAffineChart

theorem transcendental_of_not_constant
    {k K : Type*} [Field k] [IsAlgClosed k] [Field K] [Algebra k K]
    {a : K} (ha : a ∉ Set.range (algebraMap k K)) : Transcendental k a := by
  intro h
  have hbot : algebraicClosure k K = ⊥ :=
    IntermediateField.eq_bot_of_isAlgClosed_of_isAlgebraic _
  have hm : a ∈ algebraicClosure k K := mem_algebraicClosure_iff.mpr h
  rw [hbot] at hm
  exact ha hm

theorem genericCurveFunctionMap_over {C : Scheme} [IsIntegral C]
    (sC : C ⟶ Spec (.of ℂ)) (a : C.functionField) :
    genericCurveFunctionMap sC a ≫ complexProjectiveSpaceMap 1 =
      C.fromSpecStalk (genericPoint C) ≫ sC := by
  erw [genericCurveFunctionMap, Category.assoc, complexAffineChart_over, ← Spec.map_comp]
  have h : CommRingCat.ofHom (Polynomial.C : ℂ →+* Polynomial ℂ) ≫
      CommRingCat.ofHom (curveFunctionPolynomial sC a) =
      Spec.preimage (C.fromSpecStalk (genericPoint C) ≫ sC) := by
    ext c
    simp [curveFunctionPolynomial, curveFieldScalar]
  exact (congrArg Spec.map h).trans (Spec.map_preimage _)

theorem genericCurveFunctionMap_dominant {C : Scheme} [IsIntegral C]
    (sC : C ⟶ Spec (.of ℂ)) {a : C.functionField}
    (ha : a ∉ Set.range (curveFieldScalar sC)) :
    IsDominant (genericCurveFunctionMap sC a) := by
  let : Algebra ℂ C.functionField := (curveFieldScalar sC).toAlgebra
  have ht : Transcendental ℂ a := transcendental_of_not_constant ha
  have hinj : Function.Injective (curveFunctionPolynomial sC a) :=
    transcendental_iff_injective.mp ht
  let : IsDominant (Spec.map (CommRingCat.ofHom (curveFunctionPolynomial sC a))) := by
    constructor
    apply (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).mpr
    exact ((RingHom.injective_iff_ker_eq_bot _).mp hinj).le.trans bot_le
  let : IsIntegral (complexProjectiveSpace 1) := complexProjectiveLine_integral
  let : IsOpenImmersion complexAffineChart := complexAffineChart_isOpenImmersion
  let : IsDominant complexAffineChart :=
    ⟨complexAffineChart.isOpenEmbedding.isOpen_range.dense (Set.range_nonempty _)⟩
  exact ⟨complexAffineChart.denseRange.comp
    (Spec.map (CommRingCat.ofHom (curveFunctionPolynomial sC a))).denseRange
    complexAffineChart.continuous⟩

theorem exists_finite_curveFunctionMap {C : Scheme} [IsIntegral C]
    [NoetherianSpace C] (sC : C ⟶ Spec (.of ℂ))
    [SmoothOfRelativeDimension 1 sC] [IsProper sC] {a : C.functionField}
    (ha : a ∉ Set.range (curveFieldScalar sC)) :
    ∃ f : C ⟶ complexProjectiveSpace 1,
      C.fromSpecStalk (genericPoint C) ≫ f = genericCurveFunctionMap sC a ∧
      f ≫ complexProjectiveSpaceMap 1 = sC ∧ IsDominant f ∧ IsFinite f := by
  let : IsProper (complexProjectiveSpaceMap 1) := complexProjectiveSpace_isProper 1
  obtain ⟨f, hf, hfover⟩ := exists_extension_from_functionField_of_smooth_curve sC
    (complexProjectiveSpaceMap 1) (genericCurveFunctionMap sC a)
    (genericCurveFunctionMap_over sC a)
  let : IsIntegral (complexProjectiveSpace 1) := complexProjectiveLine_integral
  let : Nontrivial (complexProjectiveSpace 1) := complexProjectiveLine_nontrivial
  let : IsProper (f ≫ complexProjectiveSpaceMap 1) := hfover.symm ▸ inferInstance
  let : IsProper f := IsProper.of_comp f (complexProjectiveSpaceMap 1)
  let : IsDominant (C.fromSpecStalk (genericPoint C) ≫ f) :=
    hf.symm ▸ genericCurveFunctionMap_dominant sC ha
  let : IsDominant f := IsDominant.of_comp (C.fromSpecStalk (genericPoint C)) f
  exact ⟨f, hf, hfover, inferInstance,
    finite_of_proper_dominant_from_smooth_curve sC f⟩

end NumericalDimensionOneCurveAux

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace NumericalDimensionOneCurveAux

theorem exists_affine_finite_chart
    {C Y : Scheme} [IsIntegral C] {R : CommRingCat}
    (f : C ⟶ Y) [IsFinite f] (i : Spec R ⟶ Y) [IsOpenImmersion i]
    (ρ : R ⟶ C.functionField)
    (hρ : C.fromSpecStalk (genericPoint C) ≫ f = Spec.map ρ ≫ i) :
    ∃ (U : C.Opens) (hU : IsAffineOpen U) (hη : genericPoint C ∈ U)
      (α : R ⟶ Γ(C, U)),
      U = f ⁻¹ᵁ i.opensRange ∧ α.hom.Finite ∧
      α ≫ C.presheaf.germ U (genericPoint C) hη = ρ ∧
      Spec.map α ≫ i = hU.fromSpec ≫ f := by
  let V : Y.Opens := i.opensRange
  let U : C.Opens := f ⁻¹ᵁ V
  have hV : IsAffineOpen V := isAffineOpen_opensRange i
  have hU : IsAffineOpen U := hV.preimage f
  have hη : genericPoint C ∈ U := by
    have h := congrArg (fun a : Spec C.functionField ⟶ Y =>
      a (IsLocalRing.closedPoint C.functionField)) hρ
    change f (C.fromSpecStalk (genericPoint C)
      (IsLocalRing.closedPoint C.functionField)) =
      i (Spec.map ρ (IsLocalRing.closedPoint C.functionField)) at h
    rw [Scheme.fromSpecStalk_closedPoint] at h
    exact ⟨_, h.symm⟩
  let e : V.toScheme ≅ Spec R := IsOpenImmersion.isoOfRangeEq V.ι i (by
    rw [V.range_ι, Scheme.Hom.coe_opensRange])
  let r : U.toScheme ⟶ Spec R := (f ∣_ V) ≫ e.hom
  have hr : r ≫ i = U.ι ≫ f := by
    dsimp [r, e]
    rw [Category.assoc, IsOpenImmersion.isoOfRangeEq_hom_fac, morphismRestrict_ι]
  let α : R ⟶ Γ(C, U) := Spec.preimage (hU.isoSpec.inv ≫ r)
  have hα : Spec.map α = hU.isoSpec.inv ≫ r := Spec.map_preimage _
  have hfα : α.hom.Finite := by
    apply (IsFinite.SpecMap_iff α).mp
    rw [hα]
    dsimp [r]
    infer_instance
  have hαi : Spec.map α ≫ i = hU.fromSpec ≫ f := by
    rw [hα, Category.assoc, hr, ← Category.assoc, IsAffineOpen.isoSpec_inv_ι]
  refine ⟨U, hU, hη, α, rfl, hfα, ?_, hαi⟩
  apply Spec.map_injective
  apply (cancel_mono i).mp
  rw [Spec.map_comp, Category.assoc, hαi]
  have hgincl : Spec.map (C.presheaf.germ U (genericPoint C) hη) ≫ hU.fromSpec =
      C.fromSpecStalk (genericPoint C) := by
    rw [← U.fromSpecStalkOfMem_toSpecΓ, ← hU.isoSpec_hom,
      Category.assoc, IsAffineOpen.isoSpec_hom_fromSpec,
      U.fromSpecStalkOfMem_ι]
  rw [← Category.assoc, hgincl, hρ]

end NumericalDimensionOneCurveAux

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace NumericalDimensionOneCurveAux
open AlgebraicGeometry CategoryTheory TopologicalSpace

attribute [local instance] complexAffineChart_isOpenImmersion

theorem exists_finite_polynomial_presentation {C : Scheme} [IsIntegral C]
    [NoetherianSpace C] (sC : C ⟶ Spec (.of ℂ))
    [SmoothOfRelativeDimension 1 sC] [IsProper sC] {a : C.functionField}
    (ha : a ∉ Set.range (curveFieldScalar sC)) :
    ∃ (f : C ⟶ complexProjectiveSpace 1) (U : C.Opens) (hU : IsAffineOpen U)
      (hη : genericPoint C ∈ U) (α : .of (Polynomial ℂ) ⟶ Γ(C, U)),
      C.fromSpecStalk (genericPoint C) ≫ f = genericCurveFunctionMap sC a ∧
      U = f ⁻¹ᵁ complexAffineChart.opensRange ∧
      α.hom.Finite ∧ Function.Injective α.hom ∧
      α ≫ C.presheaf.germ U (genericPoint C) hη =
        CommRingCat.ofHom (curveFunctionPolynomial sC a) ∧
      Spec.map α ≫ complexAffineChart = hU.fromSpec ≫ f := by
  obtain ⟨f, hf, _hfover, _hfdom, hffin⟩ := exists_finite_curveFunctionMap sC ha
  let := hffin
  let := complexAffineChart_isOpenImmersion
  obtain ⟨U, hU, hη, α, hUf, hαfin, hαg, hαf⟩ :=
    exists_affine_finite_chart f complexAffineChart
      (CommRingCat.ofHom (curveFunctionPolynomial sC a)) hf
  refine ⟨f, U, hU, hη, α, hf, hUf, hαfin, ?_, hαg, hαf⟩
  let : Algebra ℂ C.functionField := (curveFieldScalar sC).toAlgebra
  have hi : Function.Injective (curveFunctionPolynomial sC a) :=
    transcendental_iff_injective.mp (transcendental_of_not_constant ha)
  intro p q hpq
  apply hi
  have h := congrArg (fun β : .of (Polynomial ℂ) ⟶ C.functionField => β p) hαg
  have h' := congrArg (fun β : .of (Polynomial ℂ) ⟶ C.functionField => β q) hαg
  change C.presheaf.germ U (genericPoint C) hη (α p) = _ at h
  change C.presheaf.germ U (genericPoint C) hη (α q) = _ at h'
  exact h.symm.trans ((congrArg (C.presheaf.germ U (genericPoint C) hη) hpq).trans h')

end NumericalDimensionOneCurveAux

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace NumericalDimensionOneCurveAux

theorem mem_affine_chart_of_local_factor
    {C Y : Scheme} [IsIntegral C] [Y.IsSeparated] {R : CommRingCat}
    (f : C ⟶ Y) (i : Spec R ⟶ Y) (ρ : R ⟶ C.functionField)
    (hρ : C.fromSpecStalk (genericPoint C) ≫ f = Spec.map ρ ≫ i)
    (x : C) (β : R ⟶ C.presheaf.stalk x)
    (hβ : β ≫ CommRingCat.ofHom
      (algebraMap (C.presheaf.stalk x) C.functionField) = ρ) :
    f x ∈ Set.range i := by
  let j := Spec.map (CommRingCat.ofHom
    (algebraMap (C.presheaf.stalk x) C.functionField))
  let : IsDominant j := by
    constructor
    apply (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).mpr
    exact ((RingHom.injective_iff_ker_eq_bot _).mp
      (IsFractionRing.injective (C.presheaf.stalk x) C.functionField)).le.trans bot_le
  have heq : C.fromSpecStalk x ≫ f = Spec.map β ≫ i := by
    apply ext_of_isDominant j
    have hj : j ≫ C.fromSpecStalk x = C.fromSpecStalk (genericPoint C) :=
      C.SpecMap_stalkSpecializes_fromSpecStalk (genericPoint_specializes x)
    rw [← Category.assoc, hj, hρ]
    dsimp [j]
    rw [← Category.assoc, ← Spec.map_comp]
    exact congrArg (fun a => Spec.map a ≫ i) hβ.symm
  have hp := congrArg (fun g : Spec (C.presheaf.stalk x) ⟶ Y =>
    g (IsLocalRing.closedPoint (C.presheaf.stalk x))) heq
  change f (C.fromSpecStalk x (IsLocalRing.closedPoint (C.presheaf.stalk x))) =
    i (Spec.map β (IsLocalRing.closedPoint (C.presheaf.stalk x))) at hp
  rw [Scheme.fromSpecStalk_closedPoint] at hp
  exact ⟨_, hp.symm⟩

end NumericalDimensionOneCurveAux

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace NumericalDimensionOneCurveAux
open AlgebraicGeometry CategoryTheory TopologicalSpace

attribute [local instance] complexAffineChart_isOpenImmersion

noncomputable def curveStalkScalar {C : Scheme} (sC : C ⟶ Spec (.of ℂ)) (x : C) :
    ℂ →+* C.presheaf.stalk x := (Spec.preimage (C.fromSpecStalk x ≫ sC)).hom

lemma curveStalkScalar_comp_field {C : Scheme} [IsIntegral C]
    (sC : C ⟶ Spec (.of ℂ)) (x : C) :
    (algebraMap (C.presheaf.stalk x) C.functionField).comp (curveStalkScalar sC x) =
      curveFieldScalar sC := by
  have h : Spec.preimage (C.fromSpecStalk x ≫ sC) ≫
      C.presheaf.stalkSpecializes (genericPoint_specializes x) =
      Spec.preimage (C.fromSpecStalk (genericPoint C) ≫ sC) := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_preimage, Spec.map_preimage, ← Category.assoc]
    exact congrArg (fun g => g ≫ sC)
      (C.SpecMap_stalkSpecializes_fromSpecStalk (genericPoint_specializes x))
  exact congrArg CommRingCat.Hom.hom h

theorem curveFunction_mem_chart_of_regular {C : Scheme} [IsIntegral C]
    (sC : C ⟶ Spec (.of ℂ)) (a : C.functionField)
    (f : C ⟶ complexProjectiveSpace 1)
    (hf : C.fromSpecStalk (genericPoint C) ≫ f = genericCurveFunctionMap sC a)
    (x : C) (b : C.presheaf.stalk x)
    (hb : algebraMap (C.presheaf.stalk x) C.functionField b = a) :
    f x ∈ complexAffineChart.opensRange := by
  let : (complexProjectiveSpace 1).IsSeparated := by
    have := complexProjectiveSpace_isProper 1
    constructor
    rw [← Limits.terminal.comp_from (complexProjectiveSpaceMap 1)]
    infer_instance
  let β : .of (Polynomial ℂ) ⟶ C.presheaf.stalk x :=
    CommRingCat.ofHom (Polynomial.eval₂RingHom (curveStalkScalar sC x) b)
  apply mem_affine_chart_of_local_factor f complexAffineChart
    (CommRingCat.ofHom (curveFunctionPolynomial sC a)) hf x β
  apply CommRingCat.hom_ext
  apply Polynomial.ringHom_ext
  · intro c
    change algebraMap (C.presheaf.stalk x) C.functionField
      (Polynomial.eval₂RingHom (curveStalkScalar sC x) b (Polynomial.C c)) =
      Polynomial.eval₂RingHom (curveFieldScalar sC) a (Polynomial.C c)
    simp only [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C]
    exact congrArg (fun g : ℂ →+* C.functionField => g c) (curveStalkScalar_comp_field sC x)
  · change algebraMap (C.presheaf.stalk x) C.functionField
      (Polynomial.eval₂RingHom (curveStalkScalar sC x) b Polynomial.X) =
      Polynomial.eval₂RingHom (curveFieldScalar sC) a Polynomial.X
    simpa using hb

end NumericalDimensionOneCurveAux

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace NumericalDimensionOneCurveAux
variable {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X]

lemma order_one (x : X) : X.ord (1 : X.functionField) x = 0 := by
  have h := X.ord_mul (x := x) (f := (1 : X.functionField)) (g := 1) one_ne_zero one_ne_zero
  simp only [mul_one] at h
  omega

lemma order_neg (f : X.functionField) (x : X) : X.ord (-f) x = X.ord f x := by
  have hneg : X.ord (-1 : X.functionField) x = 0 := by
    have h := X.ord_mul (x := x) (f := (-1 : X.functionField)) (g := -1)
      (neg_ne_zero.mpr one_ne_zero) (neg_ne_zero.mpr one_ne_zero)
    simp only [neg_mul_neg, one_mul, order_one] at h
    omega
  by_cases hf : f = 0
  · simp [hf]
  rw [← neg_one_mul, X.ord_mul (neg_ne_zero.mpr one_ne_zero) hf, hneg, zero_add]

lemma order_inv (f : X.functionField) (hf : f ≠ 0) (x : X) :
    X.ord f⁻¹ x = - X.ord f x := by
  have h := X.ord_mul (x := x) hf (inv_ne_zero hf)
  rw [mul_inv_cancel₀ hf, order_one] at h
  omega

lemma order_div (f g : X.functionField) (hf : f ≠ 0) (hg : g ≠ 0) (x : X) :
    X.ord (f / g) x = X.ord f x - X.ord g x := by
  rw [div_eq_mul_inv, X.ord_mul hf (inv_ne_zero hg), order_inv g hg]
  rfl

lemma order_nonnegative_iff_local {x : X} (hx : Order.coheight x = 1)
    [IsDiscreteValuationRing (X.presheaf.stalk x)] (f : X.functionField) (hf : f ≠ 0) :
    0 ≤ X.ord f x ↔ ∃ a : X.presheaf.stalk x,
      algebraMap (X.presheaf.stalk x) X.functionField a = f := by
  rw [X.le_ord_iff hx hf]
  change 1 ≤ Ring.ordFrac (X.presheaf.stalk x) f ↔ _
  rw [Ring.ordFrac_eq_valuation_inv, one_le_inv₀
    (WithZero.pos_iff_ne_zero.mpr ((map_ne_zero _).mpr hf))]
  constructor
  · intro h
    obtain ⟨n, d, hnd⟩ :=
      IsDedekindDomain.HeightOneSpectrum.exists_primeCompl_mul_eq_of_integer
        (IsDiscreteValuationRing.maximalIdeal (X.presheaf.stalk x)) f h
    have hd : IsUnit (d : X.presheaf.stalk x) := by
      simpa [IsDiscreteValuationRing.maximalIdeal, IsLocalRing.mem_maximalIdeal,
        mem_nonunits_iff] using d.2
    obtain ⟨u, hu⟩ := hd
    refine ⟨n * ↑(u⁻¹), ?_⟩
    rw [map_mul, ← hnd, ← hu, mul_assoc, ← map_mul]
    simp
  · rintro ⟨a, rfl⟩
    exact (IsDiscreteValuationRing.maximalIdeal (X.presheaf.stalk x)).valuation_le_one a

lemma order_add_one_of_negative {x : X} [IsDiscreteValuationRing (X.presheaf.stalk x)]
    {f : X.functionField} (h : X.ord f x < 0) : X.ord (f + 1) x = X.ord f x := by
  have hf : f ≠ 0 := by intro he; simp [he] at h
  have hf1 : f + 1 ≠ 0 := by
    intro he
    have he' : f = -1 := by linear_combination he
    rw [he', order_neg, order_one] at h
    omega
  have h1 := X.ord_add (x := x) hf1
  have hf' : f + 1 + -1 ≠ 0 := by simpa using hf
  have h2 := X.ord_add (x := x) hf'
  simp only [order_one, order_neg] at h1 h2
  simpa only [add_neg_cancel_right] using (show X.ord (f + 1) x = X.ord f x by
    simp only [add_neg_cancel_right] at h2
    omega)
end NumericalDimensionOneCurveAux

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace NumericalDimensionOneCurveAux

theorem inertiaDegree_one_of_algClosed_residue
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] [Module.Finite R S]
    (p : Ideal R) [p.IsPrime] [IsAlgClosed p.ResidueField]
    (q : Ideal S) [q.IsPrime] [q.LiesOver p] : q.inertiaDeg R = 1 := by
  let := Localization.AtPrime.algebraOfLiesOver p q
  rw [Ideal.inertiaDeg_eq p q]
  exact Module.finrank_of_bijective_algebraMap IsAlgClosed.algebraMap_bijective_of_isIntegral

theorem sum_local_order_eq_finrank
    {R S : Type*} [CommRing R] [IsDomain R] [CommRing S] [Algebra R S]
    [Module.Finite R S] [Module.Flat R S]
    (t : R) (p : Ideal R) [p.IsPrime] [IsAlgClosed p.ResidueField]
    (hp : p = Ideal.span {t}) [Fintype (p.primesOver S)] :
    (∑ q : p.primesOver S,
      (Ring.ord (Localization.AtPrime q.1)
        (algebraMap R (Localization.AtPrime q.1) t)).toNat) = Module.finrank R S := by
  have h := Ideal.sum_ramification_inertia_eq_finrank p S
  convert h using 1
  apply Finset.sum_congr rfl
  intro q _
  rw [inertiaDegree_one_of_algClosed_residue p q.1, mul_one,
    Ideal.ramificationIdx_eq p q.1]
  have hmap : Ideal.map (algebraMap R (Localization.AtPrime q.1)) p =
      Ideal.span {algebraMap R (Localization.AtPrime q.1) t} := by
    exact (congrArg (Ideal.map (algebraMap R (Localization.AtPrime q.1))) hp).trans
      (by rw [Ideal.map_span, Set.image_singleton])
  rw [hmap]
  rfl

noncomputable def polynomialPoint {k : Type*} [Field k] (c : k) : Ideal (Polynomial k) :=
  Ideal.span {Polynomial.X - Polynomial.C c}

instance polynomialPoint_isMaximal {k : Type*} [Field k] (c : k) :
    (polynomialPoint c).IsMaximal := by
  exact PrincipalIdealRing.isMaximal_of_irreducible (Polynomial.irreducible_X_sub_C c)

noncomputable def polynomialPoint_residueFieldEquiv {k : Type*} [Field k] (c : k) :
    k ≃+* (polynomialPoint c).ResidueField := by
  exact (Polynomial.quotientSpanXSubCAlgEquiv c).symm.toRingEquiv |>.trans
    (RingEquiv.ofBijective (algebraMap (Polynomial k ⧸ polynomialPoint c)
      (polynomialPoint c).ResidueField)
      (Ideal.bijective_algebraMap_quotient_residueField (polynomialPoint c)))

instance polynomialPoint_residueField_algClosed {k : Type*} [Field k] [IsAlgClosed k]
    (c : k) : IsAlgClosed (polynomialPoint c).ResidueField := by
  exact IsAlgClosed.of_ringEquiv k _ (polynomialPoint_residueFieldEquiv c)

theorem polynomial_fiber_order_eq_rank
    {k S : Type*} [Field k] [IsAlgClosed k] [CommRing S] [IsDomain S]
    [Algebra (Polynomial k) S] [Module.Finite (Polynomial k) S]
    (hi : Function.Injective (algebraMap (Polynomial k) S)) (c : k)
    [Fintype ((polynomialPoint c).primesOver S)] :
    (∑ q : (polynomialPoint c).primesOver S,
      (Ring.ord (Localization.AtPrime q.1)
        (algebraMap (Polynomial k) (Localization.AtPrime q.1)
          (Polynomial.X - Polynomial.C c))).toNat) = Module.finrank (Polynomial k) S := by
  let : Module.IsTorsionFree (Polynomial k) S :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr hi
  exact sum_local_order_eq_finrank (Polynomial.X - Polynomial.C c)
    (polynomialPoint c) rfl

end NumericalDimensionOneCurveAux

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace NumericalDimensionOneCurveAux

theorem ringOrder_equiv {R S : Type*} [CommRing R] [CommRing S]
    (e : R ≃+* S) (a : R) : Ring.ord S (e a) = Ring.ord R a := by
  rw [Ring.ord, Ring.ord, Module.length_quotient, Module.length_quotient]
  simpa only [Ideal.comap_symm, Ideal.map_span, Set.image_singleton] using
    Ideal.coheight_comap_of_surjective e.symm e.symm.surjective (Ideal.span {a})

theorem scheme_order_of_stalk_element {C : Scheme} [IsIntegral C]
    [IsLocallyNoetherian C] (x : C) (hx : Order.coheight x = 1)
    (a : C.presheaf.stalk x) (ha : a ≠ 0) :
    C.ord (algebraMap (C.presheaf.stalk x) C.functionField a) x =
      ((Ring.ord (C.presheaf.stalk x) a).toNat : ℤ) := by
  let : Ring.KrullDimLE 1 (C.presheaf.stalk x) := krullDimLE_of_coheight_le hx.le
  have ha' : algebraMap (C.presheaf.stalk x) C.functionField a ≠ 0 := by
    simpa only [map_zero] using (IsFractionRing.injective (C.presheaf.stalk x) C.functionField).ne ha
  apply (C.ord_eq_iff hx ha').mpr
  change Ring.ordFrac (C.presheaf.stalk x) _ = _
  rw [Ring.ordFrac_eq_ord _ ha]
  exact Ring.ordMonoidWithZeroHom_eq_coe (C.presheaf.stalk x) (mem_nonZeroDivisors_of_ne_zero ha)
    (ENat.natCast_toNat (Ring.ord_ne_top (mem_nonZeroDivisors_of_ne_zero ha))).symm

theorem scheme_order_on_affine_chart {C : Scheme} [IsIntegral C]
    [IsLocallyNoetherian C] {U : C.Opens} [Nonempty U] (hU : IsAffineOpen U)
    (x : U) (hx : Order.coheight (x : C) = 1) (t : Γ(C, U)) (ht : t ≠ 0) :
    C.ord (C.germToFunctionField U t) x =
      ((Ring.ord (Localization.AtPrime (hU.primeIdealOf x).asIdeal)
        (algebraMap Γ(C, U) (Localization.AtPrime (hU.primeIdealOf x).asIdeal) t)).toNat : ℤ) := by
  let := C.presheaf.algebra_section_stalk x
  let := hU.isLocalization_stalk x
  let e := IsLocalization.algEquiv (hU.primeIdealOf x).asIdeal.primeCompl
    (Localization.AtPrime (hU.primeIdealOf x).asIdeal) (C.presheaf.stalk x)
  have ht' : (C.presheaf.germ U (x : C) x.2).hom t ≠ 0 := by
    simpa only [map_zero] using (germ_injective_of_isIntegral C x x.2).ne ht
  have ho := scheme_order_of_stalk_element (C := C) (x : C) hx ((C.presheaf.germ U (x : C) x.2).hom t) ht'
  rw [C.algebraMap_germ_eq_germToFunctionField x.2 t] at ho
  apply ho.trans
  have he := ringOrder_equiv e.toRingEquiv
    (algebraMap Γ(C, U) (Localization.AtPrime (hU.primeIdealOf x).asIdeal) t)
  have hc : e.toRingEquiv
      (algebraMap Γ(C, U) (Localization.AtPrime (hU.primeIdealOf x).asIdeal) t) =
      (C.presheaf.germ U (x : C) x.2).hom t := e.commutes t
  rw [hc] at he
  exact congrArg (fun n : ℕ∞ => (n.toNat : ℤ)) he

end NumericalDimensionOneCurveAux

end OAI
