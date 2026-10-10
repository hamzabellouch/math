import Mathlib
import OAI.AlgebraicGeometry.NumericalDimension.FactorialDivisors

namespace OAI

/-! Surface Intersection. -/

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne

lemma length_sup_span_eq_ord_quotient {R : Type*} [CommRing R]
    (I : Ideal R) (b : R) :
    Module.length R (R ⧸ (I ⊔ Ideal.span {b})) =
      Ring.ord (R ⧸ I) (Ideal.Quotient.mk I b) := by
  let J : Ideal (R ⧸ I) := (Ideal.span {b}).map (Ideal.Quotient.mk I)
  have ht : IsScalarTower R (R ⧸ I) ((R ⧸ I) ⧸ J) :=
    IsScalarTower.of_algebraMap_eq' rfl
  have he := (DoubleQuot.quotQuotEquivQuotSupₐ R I (Ideal.span {b})).toLinearEquiv.length_eq
  rw [← he, Module.length_eq_of_surjective (R := R ⧸ I) Ideal.Quotient.mk_surjective]
  rw [Ideal.map_span, Set.image_singleton]
  rfl

open AlgebraicGeometry CategoryTheory TopologicalSpace
variable {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X]
  [StalkwiseNormal X] [CompactSpace X]

omit [IsIntegral X] [IsLocallyNoetherian X] [StalkwiseNormal X] [CompactSpace X] in

lemma primeDivisor_effective (p : PrimeDivisor X) :
    ∀ q, 0 ≤ (Finsupp.single p (1 : ℤ)) q := by
  intro q
  classical
  simp only [Finsupp.single_apply]
  split_ifs <;> omega

lemma primeCartierStalkIdeal (p : PrimeDivisor X) (z : pointClosure p.1)
    [UniqueFactorizationMonoid (X.presheaf.stalk (pointClosureι p.1 z))]
    (hP : IsCartierDivisor (Finsupp.single p 1)) :
    effectiveCartierStalkIdeal hP (primeDivisor_effective p) (pointClosureι p.1 z) =
      generizationPrime (pointClosure_specializes p.1 z) := by
  classical
  let y := pointClosureι p.1 z
  let h := pointClosure_specializes p.1 z
  have hp := generizationPrime_height h p.2
  obtain ⟨a,ha⟩ := UniqueFactorizationMonoid.isPrincipal_of_height_eq_one hp
  have ha0 : a ≠ 0 := by
    intro he
    exact (generizationPrime h).ne_bot_of_height_eq_one hp
      (by simpa only [he, Ideal.span_singleton_zero] using ha)
  let f := algebraMap (X.presheaf.stalk y) X.functionField a
  have hf : f ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr ha0
  have he (q : PrimeDivisor X) (hq : q.1 ⤳ y) :
      Finsupp.single p (1 : ℤ) q = X.ord f q.1 := by
    simpa only [Finsupp.single_apply, Subtype.ext_iff] using
      (order_stalk_generator h hq p.2 q.2 a ha).symm
  obtain ⟨U,_hU,hy,heq⟩ := affine_equation_of_generization_orders
    (Finsupp.single p 1) y f he
  let eqn : CartierStalkEquation (Finsupp.single p 1) y :=
    ⟨U,hy,f,hf,heq,a,rfl⟩
  exact (effectiveCartierStalkIdeal_eq hP (primeDivisor_effective p) eqn).trans ha.symm

theorem primeCurveMultiplicity_eq_ord (p : PrimeDivisor X) (z : pointClosure p.1)
    [UniqueFactorizationMonoid (X.presheaf.stalk (pointClosureι p.1 z))]
    (hP : IsCartierDivisor (Finsupp.single p 1))
    {D : WeilDivisor X} (hD : IsCartierDivisor D) (hDeff : ∀ q, 0 ≤ D q)
    (b : CartierStalkEquation D (pointClosureι p.1 z)) :
    effectiveCartierMultiplicity hP hD (primeDivisor_effective p) hDeff
        (pointClosureι p.1 z) =
      Ring.ord ((pointClosure p.1).presheaf.stalk z)
        ((pointClosureι p.1).stalkMap z b.regular) := by
  rw [effectiveCartierMultiplicity, primeCartierStalkIdeal p z hP,
    effectiveCartierStalkIdeal_eq hD hDeff b, length_sup_span_eq_ord_quotient]
  exact (ringOrder_equiv (pointClosure_stalkEquiv p.1 z) _).symm
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne
open AlgebraicGeometry CategoryTheory
variable {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X]
  [StalkwiseNormal X] [CompactSpace X]

omit [CompactSpace X] in

lemma primeCurve_equation_ne_zero (p : PrimeDivisor X) (z : pointClosure p.1)
    {D : WeilDivisor X} (hDp : D p = 0)
    (b : CartierStalkEquation D (pointClosureι p.1 z)) :
    (pointClosureι p.1).stalkMap z b.regular ≠ 0 := by
  let h := pointClosure_specializes p.1 z
  let R := X.presheaf.stalk (pointClosureι p.1 z)
  let S := X.presheaf.stalk p.1
  let := stalkGenerizationAlgebra h
  have := functionField_stalkGenerization_tower h
  have : IsDiscreteValuationRing S := dvr_at_prime_divisor p
  let v := (X.presheaf.stalkSpecializes h).hom b.regular
  have hv : algebraMap S X.functionField v = b.function := by
    change algebraMap S X.functionField (algebraMap R S b.regular) = b.function
    rw [← IsScalarTower.algebraMap_apply R S X.functionField, b.regular_eq]
  have ho : X.ord b.function p.1 = 0 := by
    rw [← b.equation p (h.mem_open b.openSet.isOpen b.mem_openSet), hDp]
  have hu : IsUnit v := by
    rw [Ring.isUnit_iff_ordFrac_one_of_isDiscreteValuationRing (K := X.functionField), hv]
    exact (X.ord_eq_iff p.2 b.nonzero).mp ho
  have hn : b.regular ∉ generizationPrime h := IsLocalRing.notMem_maximalIdeal.mpr hu
  intro hb
  apply hn
  rw [← pointClosure_stalk_ker p.1 z]
  exact hb

theorem primeCurveMultiplicity_eq_normalizedBranches
    (sX : X ⟶ Spec (.of ℂ)) [LocallyOfFiniteType sX]
    (p : PrimeDivisor X) (z : pointClosure p.1)
    (hz : IsClosed ({z} : Set (pointClosure p.1)))
    (hdim : Order.coheight z ≤ 1)
    [UniqueFactorizationMonoid (X.presheaf.stalk (pointClosureι p.1 z))]
    (hP : IsCartierDivisor (Finsupp.single p 1))
    {D : WeilDivisor X} (hD : IsCartierDivisor D) (hDeff : ∀ q, 0 ≤ D q)
    (hDp : D p = 0) (b : CartierStalkEquation D (pointClosureι p.1 z)) :
    let a := (pointClosureι p.1).stalkMap z b.regular
    effectiveCartierMultiplicity hP hD (primeDivisor_effective p) hDeff
        (pointClosureι p.1 z) =
      ∑ᶠ q : NormalizedStalkBranches z a,
        Ring.ord (Localization.AtPrime (q.asIdeal.comap (Ideal.Quotient.mk
          (Ideal.span {algebraMap ((pointClosure p.1).presheaf.stalk z)
            (integralClosure ((pointClosure p.1).presheaf.stalk z)
              (pointClosure p.1).functionField) a}))))
          (algebraMap ((pointClosure p.1).presheaf.stalk z) _ a) := by
  dsimp only
  have : IsLocallyNoetherian (pointClosure p.1) :=
    LocallyOfFiniteType.isLocallyNoetherian (pointClosureι p.1)
  apply Eq.trans (primeCurveMultiplicity_eq_ord p z hP hD hDeff b)
  exact localOrder_eq_normalizedBranches (pointClosureι p.1 ≫ sX) z hz hdim
    ((pointClosureι p.1).stalkMap z b.regular) (primeCurve_equation_ne_zero p z hDp b)
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne
open AlgebraicGeometry CategoryTheory
variable {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X] [StalkwiseNormal X]
variable (sX : X ⟶ Spec (.of ℂ)) [SmoothOfRelativeDimension 2 sX] [IsProper sX]

noncomputable def surfaceCartierPrimeDegree (D : cartierDivisors (X := X))
    (p : PrimeDivisor X) : ℤ := by
  let C := (pointClosure p.1).fromSpecStalk (genericPoint (pointClosure p.1))
  have : IsIntegral C.normalization := integral_genericNormalization
  have : SmoothOfRelativeDimension 1
      (C.fromNormalization ≫ pointClosureι p.1 ≫ sX) :=
    surface_prime_normalization_smooth sX p.1 p.2
  have : IsProper (C.fromNormalization ≫ pointClosureι p.1 ≫ sX) :=
    surface_prime_normalization_proper sX p.1
  have : IsLocallyNoetherian C.normalization :=
    LocallyOfFiniteType.isLocallyNoetherian (C.fromNormalization ≫ pointClosureι p.1 ≫ sX)
  have : CompactSpace C.normalization :=
    QuasiCompact.compactSpace_of_compactSpace (C.fromNormalization ≫ pointClosureι p.1 ≫ sX)
  exact properCurveDegree (C.fromNormalization ≫ pointClosureι p.1) D

lemma surfaceCartierPrimeDegree_add (D E : cartierDivisors (X := X)) (p : PrimeDivisor X) :
    surfaceCartierPrimeDegree sX (D + E) p =
      surfaceCartierPrimeDegree sX D p + surfaceCartierPrimeDegree sX E p := by
  let C := (pointClosure p.1).fromSpecStalk (genericPoint (pointClosure p.1))
  have : IsIntegral C.normalization := integral_genericNormalization
  have : SmoothOfRelativeDimension 1
      (C.fromNormalization ≫ pointClosureι p.1 ≫ sX) :=
    surface_prime_normalization_smooth sX p.1 p.2
  have : IsProper (C.fromNormalization ≫ pointClosureι p.1 ≫ sX) :=
    surface_prime_normalization_proper sX p.1
  have : IsLocallyNoetherian C.normalization :=
    LocallyOfFiniteType.isLocallyNoetherian (C.fromNormalization ≫ pointClosureι p.1 ≫ sX)
  have : CompactSpace C.normalization :=
    QuasiCompact.compactSpace_of_compactSpace (C.fromNormalization ≫ pointClosureι p.1 ≫ sX)
  exact properCurveDegree_add (C.fromNormalization ≫ pointClosureι p.1 ≫ sX) _ D E
lemma surfaceCartierPrimeDegree_zero (p : PrimeDivisor X) :
    surfaceCartierPrimeDegree sX 0 p = 0 := by
  let C := (pointClosure p.1).fromSpecStalk (genericPoint (pointClosure p.1))
  have : IsIntegral C.normalization := integral_genericNormalization
  have : SmoothOfRelativeDimension 1
      (C.fromNormalization ≫ pointClosureι p.1 ≫ sX) :=
    surface_prime_normalization_smooth sX p.1 p.2
  have : IsProper (C.fromNormalization ≫ pointClosureι p.1 ≫ sX) :=
    surface_prime_normalization_proper sX p.1
  have : IsLocallyNoetherian C.normalization :=
    LocallyOfFiniteType.isLocallyNoetherian (C.fromNormalization ≫ pointClosureι p.1 ≫ sX)
  have : CompactSpace C.normalization :=
    QuasiCompact.compactSpace_of_compactSpace (C.fromNormalization ≫ pointClosureι p.1 ≫ sX)
  exact properCurveDegree_zero (C.fromNormalization ≫ pointClosureι p.1 ≫ sX) _

noncomputable def surfaceIntersection (D E : cartierDivisors (X := X)) : ℤ :=
  D.1.sum fun p a => a * surfaceCartierPrimeDegree sX E p

lemma surfaceIntersection_add_left (D E F : cartierDivisors (X := X)) :
    surfaceIntersection sX (D + E) F =
      surfaceIntersection sX D F + surfaceIntersection sX E F := by
  classical
  exact Finsupp.sum_add_index (fun _ _ => zero_mul _) (fun _ _ a b => add_mul a b _)
lemma surfaceIntersection_add_right (D E F : cartierDivisors (X := X)) :
    surfaceIntersection sX D (E + F) =
      surfaceIntersection sX D E + surfaceIntersection sX D F := by
  classical
  simp only [surfaceIntersection, surfaceCartierPrimeDegree_add, mul_add,
    Finsupp.sum_add]
lemma surfaceIntersection_zero_left (D : cartierDivisors (X := X)) :
    surfaceIntersection sX 0 D = 0 := by
  rfl
lemma surfaceIntersection_zero_right (D : cartierDivisors (X := X)) :
    surfaceIntersection sX D 0 = 0 := by
  simp only [surfaceIntersection, surfaceCartierPrimeDegree_zero, mul_zero,
    Finsupp.sum, Finset.sum_const_zero]
noncomputable def surfaceIntersectionHom :
    cartierDivisors (X := X) →+ cartierDivisors (X := X) →+ ℤ where
  toFun D := { toFun := surfaceIntersection sX D
               map_zero' := surfaceIntersection_zero_right sX D
               map_add' := surfaceIntersection_add_right sX D }
  map_zero' := by ext D; exact surfaceIntersection_zero_left sX D
  map_add' D E := by ext F; exact surfaceIntersection_add_left sX D E F
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne
open AlgebraicGeometry CategoryTheory
lemma pointClosure_generic {X : Scheme} (p : X) :
    pointClosureι p (genericPoint (pointClosure p)) = p := by
  have hg := (genericPoint_spec (pointClosure p)).image (pointClosureι p).continuous
  rw [Set.image_univ, pointClosure_range, closure_closure] at hg
  exact hg.eq isGenericPoint_closure
lemma prime_point_outside_support {X : Scheme} (D : WeilDivisor X) (p : PrimeDivisor X)
    (hp : D p = 0) : p.1 ∉ divisorSupport D := by
  intro h
  obtain ⟨q,hq,hpq⟩ := Set.mem_iUnion₂.mp h
  have hsp := specializes_iff_mem_closure.mpr hpq
  have he : q = p := Subtype.ext
    (eq_of_specializes_of_equal_finite_coheight hsp q.2 p.2)
  subst q
  exact Finsupp.mem_support_iff.mp hq hp
variable {C Y : Scheme} [IsIntegral C] [IsIntegral Y]
  [IsLocallyNoetherian C] [IsLocallyNoetherian Y] [StalkwiseNormal Y]
  [CompactSpace C] [CompactSpace Y]
lemma finite_support_pulled_orders
    (sC : C ⟶ Spec (.of ℂ)) [SmoothOfRelativeDimension 1 sC]
    (f : C ⟶ Y) (D : cartierDivisors (X := Y))
    (hη : f (genericPoint C) ∉ divisorSupport D.1)
    (b : ∀ p : PrimeDivisor C, CartierStalkEquation D.1 (f p.1)) :
    Function.HasFiniteSupport (fun p : PrimeDivisor C =>
      ((Ring.ord (C.presheaf.stalk p.1) (f.stalkMap p.1 (b p).regular)).toNat : ℤ)) := by
  classical
  obtain ⟨E,hE⟩ := exists_pulledCartierRepresentative f D.1 D.2
  obtain ⟨t,_,ht⟩ := hE.exists_effective_local_orders f hη
  let F := principalWeilDivisor t + E
  have hF : ∀ p : PrimeDivisor C, F p =
      ((Ring.ord (C.presheaf.stalk p.1) (f.stalkMap p.1 (b p).regular)).toNat : ℤ) := by
    intro p
    exact (ht p (b p)).2.trans
      (NumericalDimensionOneCurveAux.scheme_order_of_stalk_element p.1 p.2 _ (ht p (b p)).1)
  exact (funext hF) ▸ F.hasFiniteSupport
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne
open AlgebraicGeometry CategoryTheory
lemma fiber_composite_stalk_element {C Y X : Scheme} (f : C ⟶ Y) (g : Y ⟶ X)
    (b : ∀ z : Y, X.presheaf.stalk (g z))
    (x : Y) (y : {y : C // f y = x}) :
    fiberStalkMap f x y (g.stalkMap x (b x)) =
      (f ≫ g).stalkMap y.1 (b (f y.1)) := by
  obtain ⟨y,rfl⟩ := y
  rw [fiberStalkMap_self, Scheme.Hom.stalkMap_comp]
  rfl
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne
open AlgebraicGeometry CategoryTheory
variable {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X] [StalkwiseNormal X]
variable (sX : X ⟶ Spec (.of ℂ)) [SmoothOfRelativeDimension 2 sX] [IsProper sX]

theorem surfacePrimeDegree_eq_multiplicities
    (D : cartierDivisors (X := X)) (hDeff : ∀ q, 0 ≤ D.1 q)
    (p : PrimeDivisor X) (hDp : D.1 p = 0)
    (hP : IsCartierDivisor (Finsupp.single p 1)) :
    surfaceCartierPrimeDegree sX D p =
      ∑ᶠ z : ClosedCurvePoint (pointClosure p.1),
        ((effectiveCartierMultiplicity hP D.2 (primeDivisor_effective p) hDeff
          (pointClosureι p.1 z.1)).toNat : ℤ) := by
  classical
  let C := pointClosure p.1
  let ι := pointClosureι p.1
  let N := (C.fromSpecStalk (genericPoint C)).normalization
  let ν := (C.fromSpecStalk (genericPoint C)).fromNormalization
  have : IsIntegral N := integral_genericNormalization
  have : IsLocallyNoetherian C := LocallyOfFiniteType.isLocallyNoetherian ι
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  have : CompactSpace C := QuasiCompact.compactSpace_of_compactSpace ι
  have : AlgebraicGeometry.IsNoetherian C := ⟨⟩
  have : AlgebraicGeometry.IsFinite ν := finite_genericNormalization (ι ≫ sX)
  let sN := ν ≫ ι ≫ sX
  have : SmoothOfRelativeDimension 1 sN := surface_prime_normalization_smooth sX p.1 p.2
  have : IsProper sN := surface_prime_normalization_proper sX p.1
  have : IsLocallyNoetherian N := LocallyOfFiniteType.isLocallyNoetherian sN
  have : CompactSpace N := QuasiCompact.compactSpace_of_compactSpace sN
  let g := ν ≫ ι
  let b (z : C) := Classical.choice (exists_cartierStalkEquation D.2 hDeff (ι z))
  let bN (q : PrimeDivisor N) : CartierStalkEquation D.1 (g q.1) := b (ν q.1)
  have hη : g (genericPoint N) ∉ divisorSupport D.1 := by
    change ι (ν (genericPoint N)) ∉ divisorSupport D.1
    rw [dominant_genericPoint ν]
    rw [pointClosure_generic]
    exact prime_point_outside_support D.1 p hDp
  let w (q : PrimeDivisor N) : ℤ :=
    (Ring.ord (N.presheaf.stalk q.1) (g.stalkMap q.1 (bN q).regular)).toNat
  have hw : Function.HasFiniteSupport w := finite_support_pulled_orders sN g D hη bN
  change properCurveDegree g D = _
  rw [properCurveDegree_eq_local_orders sN g D hη bN]
  change (∑ᶠ q, w q) = _
  rw [← finsum_fiberwise (finiteCurvePrimeImage sN ν) w hw]
  apply finsum_congr
  intro z
  have : UniqueFactorizationMonoid (X.presheaf.stalk (ι z.1)) :=
    factorial_stalk_of_smooth_surface sX (ι z.1)
  rw [primeCurveMultiplicity_eq_ord p z.1 hP D.2 hDeff (b z.1)]
  rw [localOrder_int_eq_normalizationFiber (ι ≫ sX) z.1 z.2
    (surface_pointClosure_coheight sX p.1 p.2 z.1) _
    (primeCurve_equation_ne_zero p z.1 hDp (b z.1))]
  let e := finiteCurvePrimeFiberEquiv sN ν z
  rw [← finsum_comp_equiv e]
  apply finsum_congr
  intro q
  have he := fiber_composite_stalk_element ν ι (fun y => (b y).regular) z.1 (e q)
  exact congrArg (fun a : N.presheaf.stalk (e q).1 =>
    ((Ring.ord (N.presheaf.stalk (e q).1) a).toNat : ℤ)) he.symm
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne
lemma finsum_comp_injective_supported {α β M : Type*} [AddCommMonoid M]
    (f : α → β) (hf : Function.Injective f) (w : β → M)
    (hs : Function.support w ⊆ Set.range f) :
    (∑ᶠ x, w (f x)) = ∑ᶠ y, w y := by
  classical
  rw [← finsum_mem_range hf, finsum_mem_def]
  apply finsum_congr
  intro y
  by_cases hy : y ∈ Set.range f
  · exact Set.indicator_of_mem hy _
  · rw [Set.indicator_of_notMem hy]
    exact (not_ne_iff.mp (fun h => hy (hs h))).symm
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne
open AlgebraicGeometry CategoryTheory
variable {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X] [StalkwiseNormal X]
  [CompactSpace X]

lemma prime_multiplicity_support (hdim : ∀ x : X, Order.coheight x ≤ 2)
    (D : cartierDivisors (X := X)) (hDeff : ∀ q, 0 ≤ D.1 q)
    (p : PrimeDivisor X) (hDp : D.1 p = 0)
    (hP : IsCartierDivisor (Finsupp.single p 1)) :
    Function.support (fun x : X =>
      ((effectiveCartierMultiplicity hP D.2 (primeDivisor_effective p) hDeff x).toNat : ℤ)) ⊆
        Set.range (fun z : ClosedCurvePoint (pointClosure p.1) => pointClosureι p.1 z.1) := by
  classical
  intro x hx
  have hmem : x ∈ divisorSupport (Finsupp.single p 1) ∩ divisorSupport D.1 := by
    by_contra hn
    exact hx (congrArg (fun n : ℕ∞ => (n.toNat : ℤ))
      (effectiveCartierMultiplicity_eq_zero hP D.2 (primeDivisor_effective p) hDeff hn))
  have hxp : x ∈ closure ({p.1} : Set X) := by
    obtain ⟨q,hq,hxq⟩ := Set.mem_iUnion₂.mp hmem.1
    have hqp : q = p := by simpa only [Finsupp.support_single p one_ne_zero,
      Finset.mem_singleton] using hq
    exact hqp ▸ hxq
  obtain ⟨q,hq,hxq⟩ := Set.mem_iUnion₂.mp hmem.2
  have hpq : p ≠ q := by
    rintro rfl
    exact Finsupp.mem_support_iff.mp hq hDp
  have hc : IsClosed ({x} : Set X) := closed_point_of_distinct_prime_intersection
    hdim p q hpq x hxp hxq
  have hxr : x ∈ Set.range (pointClosureι p.1) := by rwa [pointClosure_range]
  obtain ⟨z,rfl⟩ := hxr
  have hz : IsClosed ({z} : Set (pointClosure p.1)) := by
    have he : (pointClosureι p.1) ⁻¹' {pointClosureι p.1 z} = {z} := by
      ext y
      exact (pointClosureι p.1).isClosedEmbedding.injective.eq_iff
    rw [← he]
    exact hc.preimage (pointClosureι p.1).continuous
  exact ⟨⟨z,hz⟩,rfl⟩
lemma prime_multiplicities_finsum (hdim : ∀ x : X, Order.coheight x ≤ 2)
    (D : cartierDivisors (X := X)) (hDeff : ∀ q, 0 ≤ D.1 q)
    (p : PrimeDivisor X) (hDp : D.1 p = 0)
    (hP : IsCartierDivisor (Finsupp.single p 1)) :
    (∑ᶠ z : ClosedCurvePoint (pointClosure p.1),
      ((effectiveCartierMultiplicity hP D.2 (primeDivisor_effective p) hDeff
        (pointClosureι p.1 z.1)).toNat : ℤ)) =
      ∑ᶠ x : X,
        ((effectiveCartierMultiplicity hP D.2 (primeDivisor_effective p) hDeff x).toNat : ℤ) := by
  apply finsum_comp_injective_supported
    (fun z : ClosedCurvePoint (pointClosure p.1) => pointClosureι p.1 z.1)
    (w := fun x : X =>
      ((effectiveCartierMultiplicity hP D.2 (primeDivisor_effective p) hDeff x).toNat : ℤ))
  · intro z w h
    exact Subtype.ext ((pointClosureι p.1).isClosedEmbedding.injective h)
  · exact prime_multiplicity_support hdim D hDeff p hDp hP
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne
open AlgebraicGeometry CategoryTheory
variable {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X] [StalkwiseNormal X]
variable (sX : X ⟶ Spec (.of ℂ)) [SmoothOfRelativeDimension 2 sX] [IsProper sX]

noncomputable def smoothSurfaceWeilCartier :
    WeilDivisor X →+ cartierDivisors (X := X) where
  toFun D := ⟨D, by
    have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
    exact isCartierDivisor_smooth_surface sX D⟩
  map_zero' := rfl
  map_add' _ _ := rfl
noncomputable def smoothSurfacePrimeCartier (p : PrimeDivisor X) :
    cartierDivisors (X := X) := smoothSurfaceWeilCartier sX (Finsupp.single p 1)

theorem surfacePrimePrime_comm (p q : PrimeDivisor X) :
    surfaceCartierPrimeDegree sX (smoothSurfacePrimeCartier sX q) p =
      surfaceCartierPrimeDegree sX (smoothSurfacePrimeCartier sX p) q := by
  classical
  by_cases hpq : p = q
  · subst q
    rfl
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  let P := smoothSurfacePrimeCartier sX p
  let Q := smoothSurfacePrimeCartier sX q
  have hP : IsCartierDivisor (Finsupp.single p 1) := P.2
  have hQ : IsCartierDivisor (Finsupp.single q 1) := Q.2
  have hQp : Q.1 p = 0 := Finsupp.single_eq_of_ne hpq
  have hPq : P.1 q = 0 := Finsupp.single_eq_of_ne (Ne.symm hpq)
  have hd := coheight_le_of_smooth_dimension sX 2
  have h1 := (surfacePrimeDegree_eq_multiplicities sX Q
    (primeDivisor_effective q) p hQp hP).trans
    (prime_multiplicities_finsum hd Q (primeDivisor_effective q) p hQp hP)
  have h2 := (surfacePrimeDegree_eq_multiplicities sX P
    (primeDivisor_effective p) q hPq hQ).trans
    (prime_multiplicities_finsum hd P (primeDivisor_effective p) q hPq hQ)
  apply h1.trans
  apply Eq.trans _ h2.symm
  exact finsum_congr (fun x => congrArg (fun n : ℕ∞ => (n.toNat : ℤ))
    (effectiveCartierMultiplicity_comm hP hQ
      (primeDivisor_effective p) (primeDivisor_effective q) x))
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne
lemma finsupp_bilinear_comm {α : Type*}
    (B : (α →₀ ℤ) →+ (α →₀ ℤ) →+ ℤ)
    (hs : ∀ p q, B (Finsupp.single p 1) (Finsupp.single q 1) =
      B (Finsupp.single q 1) (Finsupp.single p 1))
    (D E : α →₀ ℤ) : B D E = B E D := by
  classical
  induction D using Finsupp.induction_linear with
  | zero => simp
  | add D F hD hF => simp only [map_add, AddMonoidHom.add_apply, hD, hF]
  | single p n =>
    induction E using Finsupp.induction_linear with
    | zero => simp
    | add E F hE hF => simp only [map_add, AddMonoidHom.add_apply, hE, hF]
    | single q m =>
      have hn : Finsupp.single p n = n • Finsupp.single p (1 : ℤ) := by
        simp only [Finsupp.smul_single, zsmul_eq_mul, mul_one, Int.cast_id]
      have hm : Finsupp.single q m = m • Finsupp.single q (1 : ℤ) := by
        simp only [Finsupp.smul_single, zsmul_eq_mul, mul_one, Int.cast_id]
      rw [hn, hm]
      simp only [map_zsmul, AddMonoidHom.zsmul_apply, zsmul_eq_mul]
      rw [hs p q]
      ring
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne
open AlgebraicGeometry CategoryTheory
variable {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X] [StalkwiseNormal X]
variable (sX : X ⟶ Spec (.of ℂ)) [SmoothOfRelativeDimension 2 sX] [IsProper sX]
lemma surfaceIntersection_prime_left (p : PrimeDivisor X)
    (D : cartierDivisors (X := X)) :
    surfaceIntersection sX (smoothSurfacePrimeCartier sX p) D =
      surfaceCartierPrimeDegree sX D p := by
  change (Finsupp.single p (1 : ℤ)).sum
    (fun q n => n * surfaceCartierPrimeDegree sX D q) = _
  rw [Finsupp.sum_single_index (by simp only [zero_mul]), one_mul]

theorem surfaceIntersection_comm (D E : cartierDivisors (X := X)) :
    surfaceIntersection sX D E = surfaceIntersection sX E D := by
  let H := smoothSurfaceWeilCartier sX
  let B := ((surfaceIntersectionHom sX).comp H).compl₂ H
  have hs (p q : PrimeDivisor X) :
      B (Finsupp.single p 1) (Finsupp.single q 1) =
        B (Finsupp.single q 1) (Finsupp.single p 1) := by
    change surfaceIntersection sX (smoothSurfacePrimeCartier sX p)
      (smoothSurfacePrimeCartier sX q) =
        surfaceIntersection sX (smoothSurfacePrimeCartier sX q)
          (smoothSurfacePrimeCartier sX p)
    rw [surfaceIntersection_prime_left, surfaceIntersection_prime_left]
    exact surfacePrimePrime_comm sX p q
  exact finsupp_bilinear_comm B hs D.1 E.1
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne
open AlgebraicGeometry CategoryTheory
variable {C Y : Scheme} [IsIntegral C] [IsIntegral Y]
  [IsLocallyNoetherian C] [IsLocallyNoetherian Y] [StalkwiseNormal Y]
  [CompactSpace Y]
omit [StalkwiseNormal Y] in
lemma isPulledCartierRepresentative_principal (f : C ⟶ Y)
    (a : Y.functionField) (ha : a ≠ 0) :
    IsPulledCartierRepresentative f (principalWeilDivisor a) 0 := by
  obtain ⟨U,hU,hyU,_⟩ := exists_isAffineOpen_mem_and_subset
    (show f (genericPoint C) ∈ (⊤ : Y.Opens) from trivial)
  refine ⟨U,hU,hyU,a,ha,fun _ _ => rfl,?_⟩
  intro x
  obtain ⟨V,hV,hxV,_⟩ := exists_isAffineOpen_mem_and_subset
    (show f x ∈ (⊤ : Y.Opens) from trivial)
  refine ⟨V,hV,hxV,a,ha,fun _ _ => rfl,1,isUnit_one,?_,?_⟩
  · simp only [map_one, div_self ha]
  · intro p _
    simp only [Finsupp.zero_apply, map_one, order_one]
lemma properCurveDegree_principal [CompactSpace C]
    (sC : C ⟶ Spec (.of ℂ)) [SmoothOfRelativeDimension 1 sC] [IsProper sC]
    (f : C ⟶ Y) (a : Y.functionField) (ha : a ≠ 0)
    (hD : IsCartierDivisor (principalWeilDivisor a)) :
    properCurveDegree f ⟨principalWeilDivisor a,hD⟩ = 0 := by
  rw [properCurveDegree_eq sC f _ 0 (isPulledCartierRepresentative_principal f a ha)]
  rfl
end NumericalDimensionOne

end OAI
