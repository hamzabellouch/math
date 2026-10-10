import Mathlib
import OAI.AlgebraicGeometry.NumericalDimension.CurveProjection

namespace OAI

/-! Polynomial Charts. -/

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne
open HomogeneousLocalization
attribute [local instance] MvPolynomial.gradedAlgebra

variable (k : Type*) [CommRing k]

abbrev planeGrading := MvPolynomial.homogeneousSubmodule (Fin 2) k
abbrev planeChart := HomogeneousLocalization.Away (planeGrading k) (MvPolynomial.X 1)

noncomputable def planeConstants : k →+* planeGrading k 0 where
  toFun c := ⟨MvPolynomial.C c, MvPolynomial.isHomogeneous_C _ c⟩
  map_one' := Subtype.ext (map_one MvPolynomial.C)
  map_zero' := Subtype.ext (map_zero MvPolynomial.C)
  map_add' a b := Subtype.ext (map_add MvPolynomial.C a b)
  map_mul' a b := Subtype.ext (map_mul MvPolynomial.C a b)

noncomputable def planeDehom : MvPolynomial (Fin 2) k →+* Polynomial k :=
  MvPolynomial.eval₂Hom Polynomial.C (fun i => if i = 0 then Polynomial.X else 1)

noncomputable def planeChartEval : planeChart k →+* Polynomial k :=
  (Localization.awayLift (planeDehom k) (MvPolynomial.X 1)
    (isUnit_iff_exists_inv.mpr ⟨1, by simp [planeDehom]⟩)).comp
      (algebraMap (planeChart k) (Localization.Away (MvPolynomial.X (1 : Fin 2) :
        MvPolynomial (Fin 2) k)))

noncomputable def planeChartCoordinate : planeChart k :=
  HomogeneousLocalization.Away.mk (planeGrading k)
    (MvPolynomial.isHomogeneous_X k 1) 1 (MvPolynomial.X 0)
    (by simpa using MvPolynomial.isHomogeneous_X k (0 : Fin 2))

noncomputable def planeChartInv : Polynomial k →+* planeChart k :=
  Polynomial.eval₂RingHom
    ((HomogeneousLocalization.fromZeroRingHom (planeGrading k) _).comp (planeConstants k))
    (planeChartCoordinate k)

theorem planeConstants_surjective : Function.Surjective (planeConstants k) := by
  intro p
  refine ⟨p.val.coeff 0, Subtype.ext ?_⟩
  exact ((MvPolynomial.totalDegree_eq_zero_iff_eq_C).mp
    ((MvPolynomial.totalDegree_zero_iff_isHomogeneous (Fin 2)).mpr p.property)).symm

theorem planeChartEval_mk (n : ℕ) (p : MvPolynomial (Fin 2) k)
    (hp : p ∈ planeGrading k (n • 1)) :
    planeChartEval k (HomogeneousLocalization.Away.mk (planeGrading k)
      (MvPolynomial.isHomogeneous_X k 1) n p hp) = planeDehom k p := by
  change (Localization.awayLift (planeDehom k) (MvPolynomial.X 1)
    (isUnit_iff_exists_inv.mpr ⟨1, by simp [planeDehom]⟩))
    (Localization.mk p ⟨MvPolynomial.X (1 : Fin 2) ^ n, n, rfl⟩) = _
  simpa using Localization.awayLift_mk (planeDehom k) (MvPolynomial.X 1) p 1
    (by simp [planeDehom]) n

theorem planeChartEval_constants (c : k) :
    planeChartEval k (HomogeneousLocalization.fromZeroRingHom (planeGrading k) _
      (planeConstants k c)) = Polynomial.C c := by
  change planeChartEval k (HomogeneousLocalization.Away.mk (planeGrading k)
    (MvPolynomial.isHomogeneous_X k 1) 0 (MvPolynomial.C c)
    (by change (MvPolynomial.C c).IsHomogeneous 0; exact MvPolynomial.isHomogeneous_C _ c)) = _
  rw [planeChartEval_mk]
  simp [planeDehom]

theorem planeChartEval_coordinate :
    planeChartEval k (planeChartCoordinate k) = Polynomial.X := by
  rw [planeChartCoordinate, planeChartEval_mk]
  simp [planeDehom]

theorem planeChartEval_inv : (planeChartEval k).comp (planeChartInv k) = RingHom.id _ := by
  apply Polynomial.ringHom_ext
  · intro c
    simp [planeChartInv, planeChartEval_constants]
  · simp [planeChartInv, planeChartEval_coordinate]

theorem planeGrading_adjoin_X :
    Algebra.adjoin (planeGrading k 0) (Set.range (MvPolynomial.X : Fin 2 →
      MvPolynomial (Fin 2) k)) = ⊤ := by
  apply top_unique
  intro p hp
  clear hp
  induction p using MvPolynomial.induction_on with
  | C c => exact (Algebra.adjoin _ _).algebraMap_mem (planeConstants k c)
  | add p q hp hq => exact (Algebra.adjoin _ _).add_mem hp hq
  | mul_X p i hp =>
    exact (Algebra.adjoin _ _).mul_mem hp (Algebra.subset_adjoin ⟨i, rfl⟩)

theorem planeChart_monomial (a : ℕ) (ai : Fin 2 → ℕ)
    (hai : ∑ i, ai i • (1 : ℕ) = a • 1) :
    HomogeneousLocalization.Away.mk (planeGrading k)
        (MvPolynomial.isHomogeneous_X k 1) a (∏ i, MvPolynomial.X i ^ ai i)
        (hai ▸ SetLike.prod_pow_mem_graded _ _ _ _
          (fun i _ => MvPolynomial.isHomogeneous_X k i)) =
      planeChartCoordinate k ^ ai 0 := by
  have ha : a = ai 0 + ai 1 := by simpa [Fin.sum_univ_two] using hai.symm
  apply HomogeneousLocalization.val_injective
  rw [HomogeneousLocalization.val_pow]
  change (Localization.mk (∏ i, MvPolynomial.X i ^ ai i)
    ⟨(MvPolynomial.X (1 : Fin 2) : MvPolynomial (Fin 2) k) ^ a, a, rfl⟩ :
      Localization.Away (MvPolynomial.X (1 : Fin 2) : MvPolynomial (Fin 2) k)) =
    (Localization.mk (MvPolynomial.X (0 : Fin 2))
      ⟨(MvPolynomial.X (1 : Fin 2) : MvPolynomial (Fin 2) k) ^ 1, 1, rfl⟩ :
        Localization.Away (MvPolynomial.X (1 : Fin 2) : MvPolynomial (Fin 2) k)) ^ ai 0
  rw [Localization.mk_pow, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  simp only [ha, Fin.prod_univ_two, OneMemClass.coe_one, one_mul, pow_one,
    SubmonoidClass.coe_pow, pow_add]
  ring

theorem planeChartInv_bijective : Function.Bijective (planeChartInv k) := by
  constructor
  · exact Function.HasLeftInverse.injective ⟨planeChartEval k,
      fun p => congrArg (fun f : Polynomial k →+* Polynomial k => f p) (planeChartEval_inv k)⟩
  · intro x
    have hspan := HomogeneousLocalization.Away.span_mk_prod_pow_eq_top
      (MvPolynomial.isHomogeneous_X k 1) (MvPolynomial.X : Fin 2 → MvPolynomial (Fin 2) k)
      (planeGrading_adjoin_X k) (fun _ => 1)
      (fun i => MvPolynomial.isHomogeneous_X k i)
    have hx : x ∈ Submodule.span (planeGrading k 0)
        { (HomogeneousLocalization.Away.mk (planeGrading k)
          (MvPolynomial.isHomogeneous_X k 1) a (∏ i, MvPolynomial.X i ^ ai i)
          (hai ▸ SetLike.prod_pow_mem_graded _ _ _ _
            (fun i _ => MvPolynomial.isHomogeneous_X k i)) : planeChart k) |
            (a : ℕ) (ai : Fin 2 → ℕ) (hai : ∑ i, ai i • (1 : ℕ) = a • 1) } := by
      rw [hspan]
      trivial
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨a, ai, hai, rfl⟩ := hy
      refine ⟨Polynomial.X ^ ai 0, ?_⟩
      simpa [planeChartInv] using (planeChart_monomial k a ai hai).symm
    | zero => exact ⟨0, map_zero _⟩
    | add y z _ _ hy hz =>
      obtain ⟨p, rfl⟩ := hy
      obtain ⟨q, rfl⟩ := hz
      exact ⟨p + q, map_add _ _ _⟩
    | smul c y _ hy =>
      obtain ⟨p, rfl⟩ := hy
      obtain ⟨c, rfl⟩ := planeConstants_surjective k c
      refine ⟨Polynomial.C c * p, ?_⟩
      simp [planeChartInv, Algebra.smul_def, HomogeneousLocalization.algebraMap_eq]

end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne

variable {A σ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (G : ℕ → σ) [GradedRing G]

theorem proj_integral [IsDomain A] (hG : HomogeneousIdeal.irrelevant G ≠ ⊥) :
    IsIntegral (Proj G) := by
  let η : ProjectiveSpectrum G := ⟨⊥, Ideal.isPrime_bot,
    fun h => hG (le_antisymm h bot_le)⟩
  have hη : IsGenericPoint η Set.univ := by
    apply Set.Subset.antisymm (Set.subset_univ _)
    intro y _
    exact (ProjectiveSpectrum.le_iff_mem_closure G η y).mp (show (⊥ : HomogeneousIdeal G) ≤ y.asHomogeneousIdeal from bot_le)
  let : IrreducibleSpace (Proj G) := (irreducibleSpace_def _).mpr hη.isIrreducible
  let : ∀ x : Proj G, _root_.IsReduced ((Proj G).presheaf.stalk x) := fun x => by
    let : x.asHomogeneousIdeal.toIdeal.IsPrime := x.isPrime
    let H := HomogeneousLocalization.AtPrime G x.asHomogeneousIdeal.toIdeal
    let : _root_.IsReduced H := isReduced_of_injective
      (algebraMap H (Localization.AtPrime x.asHomogeneousIdeal.toIdeal))
      (HomogeneousLocalization.val_injective _)
    exact isReduced_of_injective (Proj.stalkIso' G x) (Proj.stalkIso' G x).injective
  let : IsReduced (Proj G) := isReduced_of_isReduced_stalk _
  exact isIntegral_of_irreducibleSpace_of_isReduced _

end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne
open AlgebraicGeometry CategoryTheory
attribute [local instance] MvPolynomial.gradedAlgebra

theorem planeXone_mem (k : Type*) [CommRing k] :
    (MvPolynomial.X 1 : MvPolynomial (Fin 2) k) ∈ planeGrading k 1 :=
  MvPolynomial.isHomogeneous_X k 1

noncomputable def complexAffineChart : Spec (.of (Polynomial ℂ)) ⟶ complexProjectiveSpace 1 :=
  Spec.map (CommRingCat.ofHom (planeChartEval ℂ)) ≫
    Proj.awayι (planeGrading ℂ) (MvPolynomial.X 1)
      (planeXone_mem ℂ) (by decide : 0 < (1 : ℕ))

theorem planeChartEval_bijective (k : Type*) [CommRing k] :
    Function.Bijective (planeChartEval k) := by
  have hleft : Function.LeftInverse (planeChartEval k) (planeChartInv k) :=
    fun p => congrArg (fun f : Polynomial k →+* Polynomial k => f p) (planeChartEval_inv k)
  refine ⟨?_, hleft.surjective⟩
  intro x y h
  obtain ⟨p, rfl⟩ := (planeChartInv_bijective k).2 x
  obtain ⟨q, rfl⟩ := (planeChartInv_bijective k).2 y
  rw [hleft p, hleft q] at h
  exact congrArg (planeChartInv k) h

theorem complexAffineChart_isOpenImmersion : IsOpenImmersion complexAffineChart := by
  let e := RingEquiv.ofBijective (planeChartEval ℂ) (planeChartEval_bijective ℂ)
  let : IsIso (CommRingCat.ofHom (planeChartEval ℂ)) := e.toCommRingCatIso.isIso_hom
  let : IsIso (Spec.map (CommRingCat.ofHom (planeChartEval ℂ))) := inferInstance
  exact IsOpenImmersion.comp _ (Proj.awayι (planeGrading ℂ) (MvPolynomial.X 1)
    (planeXone_mem ℂ) (by decide : 0 < (1 : ℕ)))

theorem planeAffineChart_toSpec (k : Type*) [CommRing k] :
    (Spec.map (CommRingCat.ofHom (planeChartEval k)) ≫
      Proj.awayι (planeGrading k) (MvPolynomial.X 1) (planeXone_mem k)
        (by decide : 0 < (1 : ℕ))) ≫
      (Proj.toSpecZero (planeGrading k) ≫ Spec.map (CommRingCat.ofHom (planeConstants k))) =
    Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* Polynomial k)) := by
  rw [Category.assoc, Proj.awayι_toSpecZero_assoc, ← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact RingHom.ext (planeChartEval_constants k)

@[reassoc]
theorem complexAffineChart_over :
    complexAffineChart ≫ complexProjectiveSpaceMap 1 =
      Spec.map (CommRingCat.ofHom (Polynomial.C : ℂ →+* Polynomial ℂ)) := by
  exact planeAffineChart_toSpec ℂ

theorem complexProjectiveLine_integral : IsIntegral (complexProjectiveSpace 1) := by
  apply proj_integral
  intro h
  have hX := HomogeneousIdeal.mem_irrelevant_of_mem (planeGrading ℂ)
    (by decide : 0 < (1 : ℕ)) (MvPolynomial.isHomogeneous_X ℂ (1 : Fin 2))
  rw [h] at hX
  change MvPolynomial.X (1 : Fin 2) = (0 : MvPolynomial (Fin 2) ℂ) at hX
  exact (MvPolynomial.X_ne_zero (1 : Fin 2)) hX

theorem complexProjectiveLine_nontrivial : Nontrivial (complexProjectiveSpace 1) := by
  let : IsOpenImmersion complexAffineChart := complexAffineChart_isOpenImmersion
  have hi := complexAffineChart.isOpenEmbedding.injective
  let p : PrimeSpectrum (Polynomial ℂ) := ⟨⊥, Ideal.isPrime_bot⟩
  let q : PrimeSpectrum (Polynomial ℂ) :=
    ⟨RingHom.ker (Polynomial.evalRingHom (0 : ℂ)), RingHom.ker_isPrime _⟩
  have hpq : p ≠ q := by
    intro h
    have hX : Polynomial.X ∈ q.asIdeal := by simp [q]
    rw [← h] at hX
    change (Polynomial.X : Polynomial ℂ) = 0 at hX
    exact Polynomial.X_ne_zero hX
  exact ⟨⟨complexAffineChart p, complexAffineChart q, fun h => hpq (hi h)⟩⟩

end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne
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

end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne

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

end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne
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

end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne

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

end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne
open AlgebraicGeometry CategoryTheory TopologicalSpace
attribute [local instance] complexAffineChart_isOpenImmersion
structure PolynomialCurveChart {C : Scheme} [IsIntegral C]
    (sC : C ⟶ Spec (.of ℂ)) (a : C.functionField) where
  U : C.Opens
  affine : IsAffineOpen U
  generic_mem : genericPoint C ∈ U
  poly : Polynomial ℂ →+* Γ(C,U)
  finite : poly.Finite
  germ_poly : (C.presheaf.germ U (genericPoint C) generic_mem).hom.comp poly = curveFunctionPolynomial sC a
  over_base : Spec.map (CommRingCat.ofHom poly) ≫ Spec.map (CommRingCat.ofHom Polynomial.C) = affine.fromSpec ≫ sC
  mem_of_regular : ∀ x : C, (∃ b : C.presheaf.stalk x,
      algebraMap (C.presheaf.stalk x) C.functionField b = a) → x ∈ U

lemma exists_polynomialCurveChart {C : Scheme} [IsIntegral C] [NoetherianSpace C]
    (sC : C ⟶ Spec (.of ℂ)) [SmoothOfRelativeDimension 1 sC] [IsProper sC]
    (a : C.functionField) (ha : a ∉ Set.range (curveFieldScalar sC)) :
    Nonempty (PolynomialCurveChart sC a) := by
  obtain ⟨f,hf,hfover,hfd,hfin⟩ := exists_finite_curveFunctionMap sC ha
  let : IsFinite f := hfin
  obtain ⟨U,hU,hη,α,hUeq,hαfin,hαg,hαi⟩ := exists_affine_finite_chart f
    complexAffineChart (CommRingCat.ofHom (curveFunctionPolynomial sC a)) hf
  refine ⟨⟨U,hU,hη,α.hom,hαfin,congrArg CommRingCat.Hom.hom hαg,?_,?_⟩⟩
  · change Spec.map α ≫ Spec.map (CommRingCat.ofHom Polynomial.C) = hU.fromSpec ≫ sC
    have h := congrArg (fun g => g ≫ complexProjectiveSpaceMap 1) hαi
    simpa only [Category.assoc, complexAffineChart_over, hfover] using h
  · intro x hx
    obtain ⟨b,hb⟩ := hx
    rw [hUeq]
    exact curveFunction_mem_chart_of_regular sC a f hf x b hb

lemma polynomialCurveChart_cover {C : Scheme} [IsIntegral C]
    (sC : C ⟶ Spec (.of ℂ)) [SmoothOfRelativeDimension 1 sC]
    (a : C.functionField) (A : PolynomialCurveChart sC a)
    (B : PolynomialCurveChart sC a⁻¹) : A.U ⊔ B.U = ⊤ := by
  apply top_unique
  intro x _
  let : ValuationRing (C.presheaf.stalk x) := valuationRing_stalk_of_smooth_curve sC x
  rcases ValuationRing.isInteger_or_isInteger (C.presheaf.stalk x) a with ha | ha
  · exact Or.inl (A.mem_of_regular x ha)
  · exact Or.inr (B.mem_of_regular x ha)

lemma PolynomialCurveChart.normal {C : Scheme} [IsIntegral C]
    (sC : C ⟶ Spec (.of ℂ)) [SmoothOfRelativeDimension 1 sC]
    (a : C.functionField) (A : PolynomialCurveChart sC a) :
    IsIntegrallyClosed Γ(C,A.U) := by
  let : Nonempty A.U := ⟨⟨genericPoint C,A.generic_mem⟩⟩
  let : Smooth sC := SmoothOfRelativeDimension.smooth 1 sC
  obtain ⟨φ,hφ⟩ := Spec.map_surjective (A.affine.fromSpec ≫ sC)
  have hs : Smooth (Spec.map φ) := hφ ▸ inferInstance
  have hs' : φ.hom.Smooth := (HasRingHomProperty.Spec_iff (P := @Smooth)).mp hs
  let : Algebra ℂ Γ(C,A.U) := φ.hom.toAlgebra
  let : Algebra.Smooth ℂ Γ(C,A.U) := hs'
  exact isIntegrallyClosed_of_smooth_field_domain ℂ Γ(C,A.U)
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne
lemma exists_pow_mul_integer_of_integral_inverse
    {k B K : Type*} [CommRing k] [CommRing B] [IsDomain B] [IsIntegrallyClosed B]
    [Field K] [Algebra B K] [IsFractionRing B K]
    (c : k →+* B) (s : B) (hs : s ≠ 0) (x : K)
    (hx : (Polynomial.eval₂RingHom ((algebraMap B K).comp c)
      (algebraMap B K s)⁻¹).IsIntegralElem x) :
    ∃ n : ℕ, ∃ b : B, algebraMap B K b = (algebraMap B K s)^n * x := by
  let L := Localization.Away s
  have hsK : algebraMap B K s ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective B K)).mpr hs
  let ℓ : L →+* K := IsLocalization.Away.lift s (isUnit_iff_ne_zero.mpr hsK)
  let : Algebra L K := ℓ.toAlgebra
  let : IsScalarTower B L K := IsScalarTower.of_algebraMap_eq'
    (IsLocalization.Away.lift_comp (S := L) s (isUnit_iff_ne_zero.mpr hsK)).symm
  have hi : ℓ (IsLocalization.Away.invSelf s : L) = (algebraMap B K s)⁻¹ := by
    have h := congrArg ℓ (IsLocalization.Away.mul_invSelf (S := L) s)
    simp only [map_mul, map_one, IsLocalization.Away.lift_eq, ℓ] at h
    apply (mul_left_cancel₀ hsK)
    rw [h, mul_inv_cancel₀ hsK]
  let φ : Polynomial k →+* L := Polynomial.eval₂RingHom
    ((algebraMap B L).comp c) (IsLocalization.Away.invSelf s)
  have hφ : ℓ.comp φ = Polynomial.eval₂RingHom ((algebraMap B K).comp c)
      (algebraMap B K s)⁻¹ := by
    apply Polynomial.ringHom_ext
    · intro a
      simp only [RingHom.comp_apply, φ, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C]
      exact IsLocalization.Away.lift_eq (S := L) s (isUnit_iff_ne_zero.mpr hsK) (c a)
    · simp only [RingHom.comp_apply, φ, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]
      exact hi
  have hix : IsIntegral L x := RingHom.IsIntegralElem.of_comp (hφ.symm ▸ hx)
  obtain ⟨m,hm⟩ := hix.exists_multiple_integral_of_isLocalization (Submonoid.powers s) x
  obtain ⟨n,hn⟩ := m.2
  obtain ⟨b,hb⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hm
  refine ⟨n,b,?_⟩
  rw [hb]
  rw [Submonoid.smul_def, Algebra.smul_def]
  rw [← hn, map_pow]
end NumericalDimensionOne

end OAI
