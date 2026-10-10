import Mathlib
import OAI.AlgebraicGeometry.NumericalDimension.CurveCoordinates
import OAI.AlgebraicGeometry.NumericalDimension.RationalDegrees

namespace OAI

/-! Relative Ampleness. -/

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne
open AlgebraicGeometry CategoryTheory TopologicalSpace
lemma PolynomialCurveChart.fromSpec_germ {C : Scheme} [IsIntegral C]
    {sC : C ⟶ Spec (.of ℂ)} {a : C.functionField} (A : PolynomialCurveChart sC a) :
    Spec.map (CommRingCat.ofHom A.germ) ≫ A.affine.fromSpec = C.fromSpecStalk (genericPoint C) := by
  change Spec.map (C.presheaf.germ A.U (genericPoint C) A.generic_mem) ≫ A.affine.fromSpec = _
  rw [← A.U.fromSpecStalkOfMem_toSpecΓ, ← A.affine.isoSpec_hom,
    Category.assoc, IsAffineOpen.isoSpec_hom_fromSpec,
    A.U.fromSpecStalkOfMem_ι]
lemma PolynomialCurveChart.projective_generic {C : Scheme} [IsIntegral C]
    {sC : C ⟶ Spec (.of ℂ)} {a : C.functionField} (A : PolynomialCurveChart sC a)
    {N : ℕ} (x : Fin (N+1) → Γ(C,A.U)) (i : Fin (N+1)) (hi : x i = 1) :
    Spec.map (CommRingCat.ofHom A.germ) ≫ projectiveAffineMap A.scalar x i hi =
      projectiveFieldMap (curveFieldScalar sC) (fun k => A.germ (x k)) i
        (by rw [hi,map_one]; exact one_ne_zero) := by
  rw [projectiveAffineMap_naturality, A.germ_scalar]
  exact (projectiveFieldMap_eq_affine _ _ i (by rw [hi,map_one])).symm
lemma PolynomialCurveChart.extension_agrees {C : Scheme} [IsIntegral C]
    {sC : C ⟶ Spec (.of ℂ)} {a : C.functionField} (A : PolynomialCurveChart sC a)
    {N : ℕ} (x : Fin (N+1) → Γ(C,A.U)) (i : Fin (N+1)) (hi : x i = 1)
    (f : C ⟶ complexProjectiveSpace N)
    (hf : C.fromSpecStalk (genericPoint C) ≫ f =
      projectiveFieldMap (curveFieldScalar sC) (fun k => A.germ (x k)) i
        (by rw [hi,map_one]; exact one_ne_zero)) :
    A.affine.fromSpec ≫ f = projectiveAffineMap A.scalar x i hi := by
  let : Nonempty A.U := ⟨⟨genericPoint C,A.generic_mem⟩⟩
  let : (complexProjectiveSpace N).IsSeparated := by
    have := complexProjectiveSpace_isProper N
    constructor
    rw [← Limits.terminal.comp_from (complexProjectiveSpaceMap N)]
    infer_instance
  let e := Spec.map (CommRingCat.ofHom A.germ)
  let : IsDominant e := by
    constructor
    apply (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).mpr
    exact ((RingHom.injective_iff_ker_eq_bot _).mp
      (germ_injective_of_isIntegral C (genericPoint C) A.generic_mem)).le.trans bot_le
  apply ext_of_isDominant e
  change Spec.map (CommRingCat.ofHom A.germ) ≫ (A.affine.fromSpec ≫ f) = _
  rw [← Category.assoc,A.fromSpec_germ,hf,A.projective_generic]
lemma exists_curveCoordinateMap {C : Scheme} [IsIntegral C]
    (sC : C ⟶ Spec (.of ℂ)) [SmoothOfRelativeDimension 1 sC]
    {a : C.functionField} (ha : a ≠ 0)
    (A : PolynomialCurveChart sC a) (B : PolynomialCurveChart sC a⁻¹)
    (z : ProjectiveCurveCoordinates A B) :
    ∃ f : C ⟶ complexProjectiveSpace z.N,
      f ≫ complexProjectiveSpaceMap z.N = sC ∧
      A.affine.fromSpec ≫ f = projectiveAffineMap A.scalar z.x z.i z.xi ∧
      B.affine.fromSpec ≫ f = projectiveAffineMap B.scalar z.y z.j z.yj := by
  let : IsProper (complexProjectiveSpaceMap z.N) := complexProjectiveSpace_isProper z.N
  have hxi : A.germ (z.x z.i) = 1 := by rw [z.xi,map_one]
  have hyj : B.germ (z.y z.j) = 1 := by rw [z.yj,map_one]
  let g := projectiveFieldMap (curveFieldScalar sC) (fun k => A.germ (z.x k)) z.i
    (hxi ▸ one_ne_zero)
  have hgover : g ≫ complexProjectiveSpaceMap z.N = C.fromSpecStalk (genericPoint C) ≫ sC := by
    rw [projectiveFieldMap_over]
    exact Spec.map_preimage _
  obtain ⟨f,hf,hfover⟩ := exists_extension_from_functionField_of_smooth_curve sC
    (complexProjectiveSpaceMap z.N) g hgover
  refine ⟨f,hfover,A.extension_agrees z.x z.i z.xi f hf,?_⟩
  apply B.extension_agrees z.y z.j z.yj f
  rw [hf]
  have hz : (fun k => B.germ (z.y k)) = fun k => (a⁻¹)^z.d * A.germ (z.x k) :=
    funext z.compatible
  have hn : (a⁻¹)^z.d ≠ 0 := pow_ne_zero _ (inv_ne_zero ha)
  have hi' : B.germ (z.y z.i) ≠ 0 := by rw [z.compatible,hxi,mul_one]; exact hn
  rw [← projectiveFieldMap_independent (curveFieldScalar sC) _ z.i z.j hi'
    (hyj ▸ one_ne_zero)]
  have he : projectiveFieldMap (curveFieldScalar sC) (fun k => B.germ (z.y k)) z.i hi' =
      projectiveFieldMap (curveFieldScalar sC) (fun k => (a⁻¹)^z.d * A.germ (z.x k)) z.i
        (mul_ne_zero hn (hxi ▸ one_ne_zero)) := by
    congr 1
  rw [he]
  exact (projectiveFieldMap_scaling _ _ z.i (hxi ▸ one_ne_zero) _ hn).symm
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne
open AlgebraicGeometry CategoryTheory TopologicalSpace
lemma PolynomialCurveChart.basicOpen_le_inverse_chart {C : Scheme} [IsIntegral C]
    {sC : C ⟶ Spec (.of ℂ)} {a : C.functionField} (ha : a ≠ 0)
    (A : PolynomialCurveChart sC a) (B : PolynomialCurveChart sC a⁻¹) :
    C.basicOpen (B.poly Polynomial.X) ≤ A.U := by
  intro p hp
  have hpB : p ∈ B.U := (C.basicOpen_le (B.poly Polynomial.X)) hp
  have hu := (C.mem_basicOpen (B.poly Polynomial.X) p hpB).mp hp
  obtain ⟨u,hu⟩ := hu
  let g := algebraMap (C.presheaf.stalk p) C.functionField
  let : Nonempty B.U := ⟨⟨genericPoint C,B.generic_mem⟩⟩
  have hgu : g u.val = a⁻¹ := by
    rw [hu]
    change algebraMap (C.presheaf.stalk p) C.functionField
      (C.presheaf.germ B.U p hpB (B.poly Polynomial.X)) = _
    rw [C.algebraMap_germ_eq_germToFunctionField]
    exact B.germ_X
  apply A.mem_of_regular p
  refine ⟨(u⁻¹).val,?_⟩
  apply mul_right_cancel₀ (inv_ne_zero ha)
  change g (u⁻¹).val * a⁻¹ = a * a⁻¹
  rw [← hgu,← map_mul,Units.inv_mul,map_one,hgu,mul_inv_cancel₀ ha]
lemma PolynomialCurveChart.inverse_chart_fromSpec {C : Scheme} [IsIntegral C]
    {sC : C ⟶ Spec (.of ℂ)} {a : C.functionField} (ha : a ≠ 0)
    (A : PolynomialCurveChart sC a) (B : PolynomialCurveChart sC a⁻¹)
    (d : ℕ) (hd : 0 < d) (q : Spec Γ(C,B.U))
    (hq : q ∈ PrimeSpectrum.basicOpen ((B.poly Polynomial.X)^d)) :
    B.affine.fromSpec q ∈ A.U := by
  apply A.basicOpen_le_inverse_chart ha B
  change q ∈ B.affine.fromSpec ⁻¹ᵁ C.basicOpen (B.poly Polynomial.X)
  rw [B.affine.fromSpec_preimage_basicOpen]
  change B.poly Polynomial.X ∉ q.asIdeal
  intro hs
  exact hq (q.asIdeal.pow_mem_of_mem hs d hd)
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne
open AlgebraicGeometry CategoryTheory TopologicalSpace
lemma stalkMap_surjective_of_affine_immersion {X Y : Scheme} (f : X ⟶ Y)
    {U : X.Opens} (hU : IsAffineOpen U) [IsImmersion (hU.fromSpec ≫ f)]
    (p : X) (hp : p ∈ U) : Function.Surjective (f.stalkMap p) := by
  have hp' : p ∈ Set.range hU.fromSpec := hU.range_fromSpec.symm ▸ hp
  obtain ⟨q,rfl⟩ := hp'
  have hs := (hU.fromSpec ≫ f).stalkMap_surjective q
  rw [Scheme.Hom.stalkMap_comp] at hs
  change Function.Surjective ((hU.fromSpec.stalkMap q) ∘ (f.stalkMap (hU.fromSpec q))) at hs
  exact hs.of_comp_left (ConcreteCategory.bijective_of_isIso (hU.fromSpec.stalkMap q)).1
lemma isClosedImmersion_of_proper_two_charts {X Y : Scheme} (f : X ⟶ Y) [IsProper f]
    {U V : X.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hcover : U ⊔ V = ⊤)
    [IsImmersion (hU.fromSpec ≫ f)] [IsImmersion (hV.fromSpec ≫ f)]
    (W : Y.Opens) (hW : f ⁻¹ᵁ W = U) : IsClosedImmersion f := by
  have hc (p : X) : p ∈ U ∨ p ∈ V := by
    change p ∈ U ⊔ V
    rw [hcover]
    trivial
  let : SurjectiveOnStalks f := ⟨fun p => by
    rcases hc p with hp | hp
    · exact stalkMap_surjective_of_affine_immersion f hU p hp
    · exact stalkMap_surjective_of_affine_immersion f hV p hp⟩
  have hinj : Function.Injective f := by
    intro p q hpq
    have hmem : p ∈ U ↔ q ∈ U := by
      rw [← hW]
      change f p ∈ W ↔ f q ∈ W
      rw [hpq]
    have hlocal {T : X.Opens} (hT : IsAffineOpen T) [IsImmersion (hT.fromSpec ≫ f)]
        (hp : p ∈ T) (hq : q ∈ T) : p = q := by
      obtain ⟨p',rfl⟩ := (show p ∈ Set.range hT.fromSpec from hT.range_fromSpec.symm ▸ hp)
      obtain ⟨q',rfl⟩ := (show q ∈ Set.range hT.fromSpec from hT.range_fromSpec.symm ▸ hq)
      exact congrArg hT.fromSpec ((hT.fromSpec ≫ f).isEmbedding.injective hpq)
    by_cases hp : p ∈ U
    · exact hlocal hU hp (hmem.mp hp)
    · exact hlocal hV ((hc p).resolve_left hp) ((hc q).resolve_left (mt hmem.mpr hp))
  exact ⟨.of_continuous_injective_isClosedMap f.continuous hinj f.isClosedMap⟩
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne
open AlgebraicGeometry CategoryTheory TopologicalSpace
lemma exists_nonconstant_curveFunction {C : Scheme} [IsIntegral C]
    (sC : C ⟶ Spec (.of ℂ)) [SmoothOfRelativeDimension 1 sC] :
    ∃ a : C.functionField, a ∉ Set.range (curveFieldScalar sC) := by
  let : Smooth sC := SmoothOfRelativeDimension.smooth 1 sC
  let : JacobsonSpace C := LocallyOfFiniteType.jacobsonSpace sC
  obtain ⟨p, _, hp⟩ := nonempty_inter_closedPoints
    (Set.univ_nonempty : (Set.univ : Set C).Nonempty) isClosed_univ.isLocallyClosed
  have hd : ringKrullDim (C.presheaf.stalk p) = 1 := by
    rw [ringKrullDim_stalk_eq_coheight, coheight_eq_of_smooth_closed sC 1 p hp]
    norm_num
  have hnf : ¬ IsField (C.presheaf.stalk p) :=
    (ringKrullDim_eq_one_iff_of_isLocalRing_isDomain.mp hd).1
  let : IsLocallyNoetherian C := LocallyOfFiniteType.isLocallyNoetherian sC
  let : IsIntegrallyClosed (C.presheaf.stalk p) := integrallyClosed_stalk_of_smooth_field sC p
  let : Ring.KrullDimLE 1 (C.presheaf.stalk p) := Ring.krullDimLE_iff.mpr hd.le
  let : Ring.DimensionLEOne (C.presheaf.stalk p) :=
    ⟨fun {I} hI hprime => Ring.krullDimLE_one_iff_of_noZeroDivisors.mp inferInstance I hI hprime⟩
  let : IsDedekindDomain (C.presheaf.stalk p) := { }
  let : IsDiscreteValuationRing (C.presheaf.stalk p) :=
    ((IsDiscreteValuationRing.TFAE (C.presheaf.stalk p) hnf).out 3 1).mp
      (show IsDedekindDomain (C.presheaf.stalk p) from inferInstance)
  obtain ⟨a, ha⟩ := IsDiscreteValuationRing.exists_irreducible (C.presheaf.stalk p)
  refine ⟨algebraMap (C.presheaf.stalk p) C.functionField a, ?_⟩
  rintro ⟨c,hc⟩
  have he : curveStalkScalar sC p c = a := by
    apply IsFractionRing.injective (C.presheaf.stalk p) C.functionField
    exact (RingHom.congr_fun (curveStalkScalar_comp_field sC p) c).trans hc
  have hc0 : c ≠ 0 := by
    intro h
    have : a = 0 := by rw [← he, h, map_zero]
    exact ha.ne_zero this
  exact ha.not_isUnit (he ▸ (isUnit_iff_ne_zero.mpr hc0).map (curveStalkScalar sC p))
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne
open AlgebraicGeometry CategoryTheory TopologicalSpace
attribute [local instance] MvPolynomial.gradedAlgebra
lemma curveCoordinateMap_preimage {C : Scheme} [IsIntegral C]
    (sC : C ⟶ Spec (.of ℂ)) [SmoothOfRelativeDimension 1 sC]
    {a : C.functionField} (ha : a ≠ 0)
    (A : PolynomialCurveChart sC a) (B : PolynomialCurveChart sC a⁻¹)
    (z : ProjectiveCurveCoordinates A B) (f : C ⟶ complexProjectiveSpace z.N)
    (hfA : A.affine.fromSpec ≫ f = projectiveAffineMap A.scalar z.x z.i z.xi)
    (hfB : B.affine.fromSpec ≫ f = projectiveAffineMap B.scalar z.y z.j z.yj) :
    f ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (z.N+1)) ℂ)
      (MvPolynomial.X z.i) = A.U := by
  ext p
  constructor
  · intro hp
    by_cases hA : p ∈ A.U
    · exact hA
    have hB : p ∈ B.U := by
      have : p ∈ A.U ⊔ B.U := by rw [polynomialCurveChart_cover sC a A B]; trivial
      exact this.resolve_left hA
    obtain ⟨q,rfl⟩ := (show p ∈ Set.range B.affine.fromSpec from B.affine.range_fromSpec.symm ▸ hB)
    change q ∈ (B.affine.fromSpec ≫ f) ⁻¹ᵁ _ at hp
    rw [hfB,projectiveAffineMap_preimage,z.yi] at hp
    exact A.inverse_chart_fromSpec ha B z.d z.positive q hp
  · intro hp
    obtain ⟨q,rfl⟩ := (show p ∈ Set.range A.affine.fromSpec from A.affine.range_fromSpec.symm ▸ hp)
    change q ∈ (A.affine.fromSpec ≫ f) ⁻¹ᵁ _
    rw [hfA,projectiveAffineMap_preimage,z.xi,PrimeSpectrum.basicOpen_one]
    trivial
lemma exists_closedImmersion_of_smooth_proper_curve {C : Scheme} [IsIntegral C]
    (sC : C ⟶ Spec (.of ℂ)) [SmoothOfRelativeDimension 1 sC] [IsProper sC] :
    ∃ N : ℕ, ∃ f : C ⟶ complexProjectiveSpace N,
      IsClosedImmersion f ∧ f ≫ complexProjectiveSpaceMap N = sC := by
  let : IsNoetherian C := {
    __ := LocallyOfFiniteType.isLocallyNoetherian sC
    __ := QuasiCompact.compactSpace_of_compactSpace sC }
  obtain ⟨a,ha⟩ := exists_nonconstant_curveFunction sC
  have ha0 : a ≠ 0 := by rintro rfl; exact ha ⟨0,map_zero _⟩
  obtain ⟨A⟩ := exists_polynomialCurveChart sC a ha
  obtain ⟨B⟩ := exists_polynomialCurveChart sC a⁻¹ (nonconstant_inv (curveFieldScalar sC) ha)
  obtain ⟨z⟩ := exists_projectiveCurveCoordinates ha0 A B
  obtain ⟨f,hfover,hfA,hfB⟩ := exists_curveCoordinateMap sC ha0 A B z
  let : IsProper (complexProjectiveSpaceMap z.N) := complexProjectiveSpace_isProper z.N
  let : IsProper (f ≫ complexProjectiveSpaceMap z.N) := hfover.symm ▸ inferInstance
  let : IsProper f := IsProper.of_comp f (complexProjectiveSpaceMap z.N)
  let : IsImmersion (A.affine.fromSpec ≫ f) := hfA.symm ▸
    projectiveAffineMap_immersion A.scalar z.x z.i z.xi z.surjective_x
  let : IsImmersion (B.affine.fromSpec ≫ f) := hfB.symm ▸
    projectiveAffineMap_immersion B.scalar z.y z.j z.yj z.surjective_y
  exact ⟨z.N,f,isClosedImmersion_of_proper_two_charts f A.affine B.affine
    (polynomialCurveChart_cover sC a A B) _
    (curveCoordinateMap_preimage sC ha0 A B z f hfA hfB),hfover⟩
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne
open AlgebraicGeometry CategoryTheory TopologicalSpace
noncomputable def properSmoothCurveVariety {C : Scheme} [IsIntegral C]
    (sC : C ⟶ Spec (.of ℂ)) [SmoothOfRelativeDimension 1 sC] [IsProper sC] :
    ComplexProjectiveVariety where
  scheme := C
  structureMap := sC
  integral := inferInstance
  connected := inferInstance
  projective := exists_closedImmersion_of_smooth_proper_curve sC
noncomputable def surfacePrimeCurveOn (X : ComplexProjectiveVariety)
    (hX : IsSmoothNfold X 2) (p : PrimeDivisor X.scheme) : CurveOn X := by
  let : SmoothOfRelativeDimension 2 X.structureMap := hX
  let C := (pointClosure p.1).fromSpecStalk (genericPoint (pointClosure p.1))
  let : IsIntegral C.normalization := integral_genericNormalization
  let : SmoothOfRelativeDimension 1
      (C.fromNormalization ≫ pointClosureι p.1 ≫ X.structureMap) :=
    surface_prime_normalization_smooth X.structureMap p.1 p.2
  let : IsProper (C.fromNormalization ≫ pointClosureι p.1 ≫ X.structureMap) :=
    surface_prime_normalization_proper X.structureMap p.1
  exact ⟨properSmoothCurveVariety (C.fromNormalization ≫ pointClosureι p.1 ≫ X.structureMap),
    (by change SmoothOfRelativeDimension 1 (C.fromNormalization ≫ pointClosureι p.1 ≫ X.structureMap); infer_instance),
    C.fromNormalization ≫ pointClosureι p.1, rfl⟩
lemma surfaceCartierPrimeDegree_eq_cartierCurveDegree (X : ComplexProjectiveVariety)
    [StalkwiseNormal X.scheme] (hX : IsSmoothNfold X 2)
    (D : cartierDivisors (X := X.scheme)) (p : PrimeDivisor X.scheme) :
    @surfaceCartierPrimeDegree X.scheme _ _ _ X.structureMap hX _ D p =
      cartierCurveDegree D (surfacePrimeCurveOn X hX p) := by
  rfl
lemma surfaceIntersection_nonneg_of_nef_effective (X : ComplexProjectiveVariety)
    [StalkwiseNormal X.scheme] (hX : IsSmoothNfold X 2)
    (D E : cartierDivisors (X := X.scheme)) (hD : IsNefCartier X D)
    (hE : 0 ≤ E.1) :
    0 ≤ @surfaceIntersection X.scheme _ _ _ X.structureMap hX _ E D := by
  classical
  change 0 ≤ E.1.sum (fun p n => n * _)
  apply Finset.sum_nonneg
  intro p _
  have hdeg := hD (surfacePrimeCurveOn X hX p)
  rw [← surfaceCartierPrimeDegree_eq_cartierCurveDegree X hX D p] at hdeg
  exact mul_nonneg (hE p) hdeg
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne
open AlgebraicGeometry CategoryTheory
lemma order_stalk_positive_iff {C : Scheme} [IsIntegral C] [IsLocallyNoetherian C]
    [StalkwiseNormal C] (p : PrimeDivisor C) (a : C.presheaf.stalk p.1) (ha : a ≠ 0) :
    0 < C.ord (algebraMap (C.presheaf.stalk p.1) C.functionField a) p.1 ↔ ¬ IsUnit a := by
  let : IsDiscreteValuationRing (C.presheaf.stalk p.1) := dvr_at_prime_divisor p
  have ha' : algebraMap (C.presheaf.stalk p.1) C.functionField a ≠ 0 :=
    by simpa only [map_zero] using
      (IsFractionRing.injective (C.presheaf.stalk p.1) C.functionField).ne ha
  have hn : 0 ≤ C.ord (algebraMap (C.presheaf.stalk p.1) C.functionField a) p.1 := by
    rw [NumericalDimensionOneCurveAux.scheme_order_of_stalk_element p.1 p.2 a ha]
    positivity
  have he : C.ord (algebraMap (C.presheaf.stalk p.1) C.functionField a) p.1 = 0 ↔ IsUnit a := by
    rw [C.ord_eq_iff p.2 ha']
    exact Ring.isUnit_iff_ordFrac_one_of_isDiscreteValuationRing.symm
  exact ⟨fun h hu => (ne_of_gt h) (he.mpr hu), fun h => lt_of_le_of_ne hn (Ne.symm (mt he.mp h))⟩
lemma CartierStalkEquation.not_isUnit_of_mem_support {X : Scheme} [IsIntegral X]
    [IsLocallyNoetherian X] [StalkwiseNormal X] [CompactSpace X]
    {D : WeilDivisor X} {x : X} (a : CartierStalkEquation D x)
    (hx : x ∈ divisorSupport D) : ¬ IsUnit a.regular := by
  intro hu
  have h := section_nonvanishing_of_local_unit one_ne_zero a.nonzero a.equation
    a.mem_openSet a.regular hu (by rw [one_mul]; exact a.regular_eq)
  have hone : principalWeilDivisor (1 : X.functionField) = 0 := by
    ext p
    simp only [principalWeilDivisor_apply, order_one, Finsupp.zero_apply]
  change x ∈ divisorComplement (principalWeilDivisor (1 : X.functionField) + D) at h
  rw [hone,zero_add] at h
  exact h hx
lemma complexWeilDegree_positive_of_effective {X : Scheme} (D : WeilDivisor X)
    (hD : ∀ p, 0 ≤ D p) (p : PrimeDivisor X) (hp : 0 < D p) :
    0 < complexWeilDegree D := by
  classical
  exact Finset.sum_pos' (fun q _ => hD q)
    ⟨p,Finsupp.mem_support_iff.mpr (ne_of_gt hp),hp⟩
lemma cartierCurveDegree_positive_of_effective_meeting {X : ComplexProjectiveVariety}
    [StalkwiseNormal X.scheme] (D : cartierDivisors (X := X.scheme)) (C : CurveOn X)
    (heff : ∀ p, 0 ≤ D.1 p) (hη : C.morphism (genericPoint C.curve.scheme) ∉ divisorSupport D.1)
    (p : PrimeDivisor C.curve.scheme) (hp : C.morphism p.1 ∈ divisorSupport D.1) :
    0 < cartierCurveDegree D C := by
  classical
  let E := pulledCartierRepresentative C D.1 D.2
  obtain ⟨t,ht,htord⟩ := (pulledCartierRepresentative_spec C D.1 D.2).exists_effective_local_orders
    C.morphism hη
  let F := principalWeilDivisor t + E
  have hF (q : PrimeDivisor C.curve.scheme) : 0 ≤ F q := by
    obtain ⟨b⟩ := exists_cartierStalkEquation D.2 heff (C.morphism q.1)
    obtain ⟨hb,ho⟩ := htord q b
    rw [show F q = _ from ho,NumericalDimensionOneCurveAux.scheme_order_of_stalk_element q.1 q.2 _ hb]
    positivity
  obtain ⟨b⟩ := exists_cartierStalkEquation D.2 heff (C.morphism p.1)
  obtain ⟨hb,ho⟩ := htord p b
  have hpF : 0 < F p := by
    rw [show F p = _ from ho,order_stalk_positive_iff p _ hb]
    exact fun hu => b.not_isUnit_of_mem_support hp ((isUnit_map_iff (C.morphism.stalkMap p.1).hom _).mp hu)
  have hpos := complexWeilDegree_positive_of_effective F hF p hpF
  unfold F complexWeilDegree at hpos
  rw [Finsupp.sum_add_index (fun _ _ => rfl) (fun _ _ _ _ => rfl)] at hpos
  change 0 < complexWeilDegree (principalWeilDivisor t) + cartierCurveDegree D C at hpos
  rw [principal_degree_zero C.curve C.smooth t,zero_add] at hpos
  exact hpos
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne
open AlgebraicGeometry CategoryTheory TopologicalSpace
lemma primeDivisor_ne_generic {C : Scheme} [IsIntegral C] (p : PrimeDivisor C) :
    p.1 ≠ genericPoint C := by
  intro h
  have hm : IsMax (genericPoint C) := fun _ _ => genericPoint_specializes _
  have hz := Order.coheight_eq_zero.mpr hm
  rw [← h,p.2] at hz
  exact one_ne_zero hz
lemma CurveOn.isClosed_prime_image {X : ComplexProjectiveVariety} (C : CurveOn X)
    (p : PrimeDivisor C.curve.scheme) : IsClosed ({C.morphism p.1} : Set X.scheme) := by
  let : SmoothOfRelativeDimension 1 C.curve.structureMap := C.smooth
  let : IsProper (C.morphism ≫ X.structureMap) := C.overComplex.symm ▸ inferInstance
  let : IsProper C.morphism := IsProper.of_comp C.morphism X.structureMap
  have hc := isClosed_point_of_curve_coheight
    (coheight_le_of_smooth_dimension C.curve.structureMap 1) (primeDivisor_ne_generic p)
  simpa only [Set.image_singleton] using C.morphism.isClosedMap {p.1} hc
lemma cartierCurveDegree_principal {X : ComplexProjectiveVariety} [StalkwiseNormal X.scheme]
    (C : CurveOn X) (a : X.scheme.functionField) (ha : a ≠ 0)
    (hD : IsCartierDivisor (principalWeilDivisor a)) :
    cartierCurveDegree ⟨principalWeilDivisor a,hD⟩ C = 0 := by
  change complexWeilDegree (pulledCartierRepresentative C (principalWeilDivisor a) hD) = 0
  rw [pulledCartierRepresentative_degree_eq C
    (pulledCartierRepresentative_spec C (principalWeilDivisor a) hD) (isPulledCartierRepresentative_principal C.morphism a ha)]
  rfl
lemma cartierCurveDegree_positive_of_ample {X : ComplexProjectiveVariety}
    [StalkwiseNormal X.scheme] (D : cartierDivisors (X := X.scheme))
    (hD : IsAmpleDivisor D.1) (C : CurveOn X) (p : PrimeDivisor C.curve.scheme)
    (hp : C.morphism (genericPoint C.curve.scheme) ≠ C.morphism p.1) :
    0 < cartierCurveDegree D C := by
  let U : X.scheme.Opens := ⟨({C.morphism p.1} : Set X.scheme)ᶜ,
    (C.isClosed_prime_image p).isOpen_compl⟩
  obtain ⟨m,hm,s,hs,hsec,_,hη,hU⟩ :=
    hD.2 (C.morphism (genericPoint C.curve.scheme)) U hp
  have hsD : IsCartierDivisor (principalWeilDivisor s) := by
    intro x
    obtain ⟨V,hV,hx,_⟩ := exists_isAffineOpen_mem_and_subset
      (show x ∈ (⊤ : X.scheme.Opens) from trivial)
    exact ⟨V,hV,hx,s,hs,fun _ _ => rfl⟩
  let P : cartierDivisors (X := X.scheme) := ⟨principalWeilDivisor s,hsD⟩
  have heff : ∀ q, 0 ≤ (P + m • D).1 q := (hsec.resolve_left hs)
  have hpoint : C.morphism p.1 ∈ divisorSupport (P + m • D).1 := by
    by_contra h
    have : C.morphism p.1 ∈ U := hU h
    exact this rfl
  have hpos := cartierCurveDegree_positive_of_effective_meeting (P + m • D) C heff hη p hpoint
  rw [cartierCurveDegree_add,cartierCurveDegree_principal C s hs hsD,zero_add] at hpos
  have he := map_nsmul (cartierCurveDegreeHom C) m D
  change cartierCurveDegree (m • D) C = m • cartierCurveDegree D C at he
  rw [he,nsmul_eq_mul] at hpos
  exact pos_of_mul_pos_right hpos (by positivity)
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne
open AlgebraicGeometry CategoryTheory
lemma qCartierCurveDegree_positive_of_ample {X : ComplexProjectiveVariety}
    [StalkwiseNormal X.scheme] {D : QWeilDivisor X.scheme}
    (hD : IsQCartierDivisor D) (hA : IsAmpleQDivisor D) (C : CurveOn X)
    (c : PrimeDivisor C.curve.scheme)
    (hc : C.morphism (genericPoint C.curve.scheme) ≠ C.morphism c.1) :
    0 < qCartierCurveDegree D hD C := by
  obtain ⟨m,hm,A,hAmp,hAD⟩ := hA
  rw [qCartierCurveDegree_eq_multiple _ (⟨m,hm,⟨A,hAmp.1⟩,hAD⟩ : CartierMultiple D)]
  exact div_pos (by exact_mod_cast cartierCurveDegree_positive_of_ample ⟨A,hAmp.1⟩ hAmp C c hc)
    (by exact_mod_cast hm)
lemma IsRelativelyAmpleQ.curveDegree_pos
    {X Y : ComplexProjectiveVariety} [StalkwiseNormal X.scheme]
    (f : X.scheme ⟶ Y.scheme) [IsDominant f] {D : QWeilDivisor X.scheme}
    (hD : IsQCartierDivisor D) (hA : IsRelativelyAmpleQ f D)
    (C : CurveOn X) (hC : IsCurveContracted f C)
    (c : PrimeDivisor C.curve.scheme)
    (hc : C.morphism (genericPoint C.curve.scheme) ≠ C.morphism c.1) :
    0 < qCartierCurveDegree D hD C := by
  obtain ⟨A,_hA,E,hE,hAmp⟩ := hA
  let M : CartierMultiple (rationalWeilDivisor E) := ⟨1,by omega,⟨E,hE.isCartier⟩,by simp⟩
  have hsum := ((chooseCartierMultiple hD).add M).isQCartier
  have hz : qCartierCurveDegree (rationalWeilDivisor E) M.isQCartier C = 0 := by
    rw [qCartierCurveDegree_eq_multiple _ M]
    change (cartierCurveDegree ⟨E,hE.isCartier⟩ C : ℚ) / 1 = 0
    rw [cartierCurveDegree_pullback_contracted f _ hE C hC,Int.cast_zero,zero_div]
  have h := qCartierCurveDegree_positive_of_ample hsum hAmp C c hc
  rw [qCartierCurveDegree_add hD M.isQCartier, hz,add_zero] at h
  exact h

lemma canonical_difference_negative_on_curve
    {W X Y R : ComplexProjectiveVariety}
    [StalkwiseNormal W.scheme] [StalkwiseNormal X.scheme]
    (p : W.scheme ⟶ X.scheme) (q : W.scheme ⟶ Y.scheme)
    [IsDominant p] [IsDominant q]
    (hp : p ≫ X.structureMap = W.structureMap)
    (f : X.scheme ⟶ R.scheme) [IsDominant f] (g : Y.scheme ⟶ R.scheme)
    (hcomm : p ≫ f = q ≫ g)
    {D : QWeilDivisor X.scheme} {E : QWeilDivisor Y.scheme}
    {P Q : QWeilDivisor W.scheme} (hD : IsQCartierDivisor D)
    (hP : IsQCartierPullback p D P) (hQ : IsQCartierPullback q E Q)
    (hs : IsQCartierDivisor (P-Q)) (hnegative : IsRelativelyAmpleQ f (-D))
    (C : CurveOn W) (hC : IsCurveContracted q C)
    (c : PrimeDivisor C.curve.scheme)
    (hc : p (C.morphism (genericPoint C.curve.scheme)) ≠ p (C.morphism c.1)) :
    qCartierCurveDegree (P-Q) hs C < 0 := by
  have hcontract : IsCurveContracted f (C.comp p hp) := by
    obtain ⟨y,hy⟩ := hC
    refine ⟨g y,?_⟩
    intro x
    change (p ≫ f) (C.morphism x) = g y
    rw [hcomm]
    change g (q (C.morphism x)) = g y
    rw [hy x]
  have hn : IsQCartierDivisor (-D) := by
    simpa only [neg_one_smul] using ((chooseCartierMultiple hD).smul (-1)).isQCartier
  have h := hnegative.curveDegree_pos f hn (C.comp p hp) hcontract c hc
  rw [qCartierCurveDegree_neg hD hn,neg_pos] at h
  rw [qCartierCurveDegree_sub hP.isQCartier hQ.isQCartier,
    qCartierCurveDegree_pullback p hp hD hP,
    qCartierCurveDegree_pullback_contracted q hQ C hC,sub_zero]
  exact h
end NumericalDimensionOne

end OAI
