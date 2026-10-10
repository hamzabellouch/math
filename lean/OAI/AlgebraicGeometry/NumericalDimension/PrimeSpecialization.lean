import Mathlib
import OAI.AlgebraicGeometry.NumericalDimension.IntersectionLengths
import OAI.AlgebraicGeometry.NumericalDimension.SmoothParameters

namespace OAI

/-! Prime Specialization. -/

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne
open AlgebraicGeometry CategoryTheory

theorem maximal_comap_of_finiteType {A B : Type*} [CommRing A] [CommRing B]
    [IsJacobsonRing A] (f : A →+* B) (hf : f.FiniteType)
    (p : Ideal B) [p.IsMaximal] : (p.comap f).IsMaximal := by
  let : Field (B ⧸ p) := Ideal.Quotient.field p
  let φ := (Ideal.Quotient.mk p).comp f
  have hφ : φ.FiniteType := (RingHom.FiniteType.of_surjective _ Ideal.Quotient.mk_surjective).comp hf
  have hfin : φ.Finite := RingHom.finite_iff_finiteType_of_isJacobsonRing.mpr hφ
  have hi : φ.IsIntegral := by
    let : Algebra A (B ⧸ p) := φ.toAlgebra
    have : Module.Finite A (B ⧸ p) := hfin
    exact Algebra.IsIntegral.isIntegral
  have hm := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal φ hi (⊥ : Ideal (B ⧸ p))
  change ((⊥ : Ideal (B ⧸ p)).comap ((Ideal.Quotient.mk p).comp f)).IsMaximal at hm
  rw [← Ideal.comap_comap, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker] at hm
  exact hm

universe u

theorem coheight_eq_of_smooth_closed
    {k : Type u} [Field k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) (n : ℕ)
    [SmoothOfRelativeDimension n sX] (x : X) (hx : IsClosed ({x} : Set X)) :
    Order.coheight x = n := by
  apply le_antisymm (coheight_le_of_smooth_dimension sX n x)
  obtain ⟨U, hU, hxU, hs⟩ := exists_standard_smooth_chart sX n x
  obtain ⟨g, _, hg⟩ := hs.exists_etale_mvPolynomial
  let A := MvPolynomial (Fin n) k
  let B := Γ(X,U)
  let : Algebra A B := g.toAlgebra
  have : Algebra.Etale A B := hg
  let p := (hU.primeIdealOf ⟨x,hxU⟩).asIdeal
  have : p.IsMaximal := hU.primeIdealOf_isMaximal_of_isClosed ⟨x,hxU⟩ hx
  let q := p.comap g
  have : q.IsMaximal := maximal_comap_of_finiteType g
    (RingHom.finiteType_algebraMap.mpr (inferInstance : Algebra.FiniteType A B)) p
  have : p.LiesOver q := ⟨rfl⟩
  have : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing A B
  have hh : q.height ≤ p.height := by
    rw [Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown q p]
    exact le_self_add
  rw [polynomial_maximal_height k n q] at hh
  have he : p.height = Order.coheight x := by
    let y : U := ⟨x,hxU⟩
    let := TopCat.Presheaf.algebra_section_stalk X.presheaf y
    let := hU.isLocalization_stalk y
    have h := IsLocalization.AtPrime.ringKrullDim_eq_height (hU.primeIdealOf y).asIdeal
      (A := X.presheaf.stalk x)
    rw [ringKrullDim_stalk_eq_coheight] at h
    exact WithBot.coe_injective h.symm
  exact he ▸ hh
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne
open AlgebraicGeometry CategoryTheory TopologicalSpace
variable {X Y : Scheme} (f : X ⟶ Y) [QuasiCompact f]

theorem schemeTheoreticallyDominant_toImage :
    IsSchemeTheoreticallyDominant f.toImage := by
  constructor
  apply Scheme.IdealSheafData.ext_of_iSup_eq_top
    (fun U : Y.affineOpens => ⟨f.imageι ⁻¹ᵁ U.1, U.2.preimage _⟩)
  · rw [← Scheme.Hom.preimage_iSup, iSup_affineOpens_eq_top, Scheme.Hom.preimage_top]
  · intro U
    rw [Scheme.Hom.ker_apply, Scheme.IdealSheafData.ideal_bot]
    exact (RingHom.injective_iff_ker_eq_bot _).mp (f.toImage_app_injective U)

theorem reduced_image [IsReduced X] : IsReduced f.image := by
  let := schemeTheoreticallyDominant_toImage f
  exact IsSchemeTheoreticallyDominant.isReduced f.toImage

theorem integral_image [IsIntegral X] : IsIntegral f.image := by
  let := reduced_image f
  have : IrreducibleSpace f.image :=
    { isPreirreducible_univ := by
        rw [← f.toImage.denseRange.closure_eq, ← Set.image_univ]
        exact (PreirreducibleSpace.isPreirreducible_univ.image f.toImage
          f.toImage.continuous.continuousOn).closure
      toNonempty := Nonempty.map f.toImage inferInstance }
  exact isIntegral_of_irreducibleSpace_of_isReduced _
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne
open AlgebraicGeometry CategoryTheory TopologicalSpace
variable {X : Scheme}

noncomputable def pointClosure (x : X) : Scheme := (X.fromSpecResidueField x).image
noncomputable def pointClosureι (x : X) : pointClosure x ⟶ X :=
  (X.fromSpecResidueField x).imageι

instance pointClosure_integral (x : X) : IsIntegral (pointClosure x) := by
  have : QuasiCompact (X.fromSpecResidueField x) := quasiCompact_of_noetherianSpace_source _
  exact integral_image (X.fromSpecResidueField x)
instance pointClosure_closedImmersion (x : X) : IsClosedImmersion (pointClosureι x) := by
  change IsClosedImmersion (X.fromSpecResidueField x).imageι
  infer_instance
lemma pointClosure_range (x : X) :
    Set.range (pointClosureι x) = closure ({x} : Set X) := by
  change Set.range (X.fromSpecResidueField x).ker.subschemeι = _
  rw [Scheme.IdealSheafData.range_subschemeι, Scheme.Hom.support_ker,
    Scheme.range_fromSpecResidueField]
lemma pointClosure_nontrivial (x : X) (hx : ¬ IsClosed ({x} : Set X)) :
    Nontrivial (pointClosure x) := by
  classical
  by_contra hn
  have : Subsingleton (pointClosure x) := not_nontrivial_iff_subsingleton.mp hn
  have hmem : x ∈ Set.range (pointClosureι x) := by
    rw [pointClosure_range]
    exact subset_closure (Set.mem_singleton _)
  obtain ⟨z,hz⟩ := hmem
  have he : Set.range (pointClosureι x) = {x} := by
    ext y
    constructor
    · rintro ⟨t,rfl⟩
      rw [Subsingleton.elim t z, hz]
      rfl
    · rintro rfl
      exact ⟨z,hz⟩
  exact hx (he ▸ (pointClosureι x).isClosedEmbedding.isClosed_range)
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u
variable {k : Type u} [Field k] [IsAlgClosed k] [CharZero k]
variable {X : Scheme.{u}} (sX : X ⟶ Spec (.of k))
variable [SmoothOfRelativeDimension 2 sX] [IsProper sX]
variable (p : X) (hp : Order.coheight p = 1)

include sX hp in
omit [IsProper sX] [IsAlgClosed k] [CharZero k] in

theorem surface_pointClosure_nontrivial : Nontrivial (pointClosure p) := by
  apply pointClosure_nontrivial
  intro hc
  have h := coheight_eq_of_smooth_closed sX 2 p hc
  rw [hp] at h
  norm_num at h

include sX hp in
omit [IsProper sX] [IsAlgClosed k] [CharZero k] in

theorem surface_pointClosure_coheight (x : pointClosure p) : Order.coheight x ≤ 1 := by
  have : Nonempty X := ⟨p⟩
  apply coheight_le_one_of_bounded_embedding (pointClosureι p)
    (strictMono_of_locallyQuasiFinite _) p _ hp (coheight_le_of_smooth_dimension sX 2) x
  intro y
  apply specializes_iff_mem_closure.mpr
  rw [← pointClosure_range p]
  exact ⟨y,rfl⟩

include hp in

theorem surface_prime_normalization_smooth :
    SmoothOfRelativeDimension 1
      (( (pointClosure p).fromSpecStalk (genericPoint (pointClosure p))).fromNormalization ≫
        pointClosureι p ≫ sX) := by
  have : Nontrivial (pointClosure p) := surface_pointClosure_nontrivial sX p hp
  have : IsProper (pointClosureι p ≫ sX) := inferInstance
  have : IsLocallyNoetherian (pointClosure p) :=
    LocallyOfFiniteType.isLocallyNoetherian (pointClosureι p ≫ sX)
  have : CompactSpace (pointClosure p) :=
    QuasiCompact.compactSpace_of_compactSpace (pointClosureι p ≫ sX)
  have : AlgebraicGeometry.IsNoetherian (pointClosure p) := ⟨⟩
  exact smooth_genericNormalization (pointClosureι p ≫ sX)
    (surface_pointClosure_coheight sX p hp)

omit [IsAlgClosed k] [SmoothOfRelativeDimension 2 sX] in

theorem surface_prime_normalization_proper :
    IsProper
      (((pointClosure p).fromSpecStalk (genericPoint (pointClosure p))).fromNormalization ≫
        pointClosureι p ≫ sX) := by
  have : IsProper (pointClosureι p ≫ sX) := inferInstance
  have : IsLocallyNoetherian (pointClosure p) :=
    LocallyOfFiniteType.isLocallyNoetherian (pointClosureι p ≫ sX)
  have : CompactSpace (pointClosure p) :=
    QuasiCompact.compactSpace_of_compactSpace (pointClosureι p ≫ sX)
  have : AlgebraicGeometry.IsNoetherian (pointClosure p) := ⟨⟩
  exact proper_genericNormalization (pointClosureι p ≫ sX)
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne
open AlgebraicGeometry CategoryTheory
lemma isClosed_point_of_isClosed_image {C X : Scheme} (f : C ⟶ X)
    [LocallyQuasiFinite f] (y : C) (hy : IsClosed ({f y} : Set X)) :
    IsClosed ({y} : Set C) := by
  apply isClosed_of_subset_discrete_closed (t := f ⁻¹' {f y}) _
    (f.isDiscrete_preimage_singleton (f y)) (hy.preimage f.continuous)
  rintro _ rfl
  rfl

variable {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X]
  [Nontrivial X] [QuasiSeparatedSpace X]

theorem localOrder_eq_normalizedSchemeOrders (sX : X ⟶ Spec (.of ℂ))
    [LocallyOfFiniteType sX] (hd : ∀ x : X, Order.coheight x ≤ 1)
    (x : X) (hx : IsClosed ({x} : Set X))
    (a : X.presheaf.stalk x) (ha : a ≠ 0) :
    let N := (X.fromSpecStalk (genericPoint X)).normalization
    let f := (X.fromSpecStalk (genericPoint X)).fromNormalization
    letI : AlgebraicGeometry.IsFinite f := finite_genericNormalization sX
    letI : IsLocallyNoetherian N := LocallyOfFiniteType.isLocallyNoetherian f
    ((Ring.ord (X.presheaf.stalk x) a).toNat : ℤ) =
      ∑ᶠ y : {y : N // f y = x},
        N.ord (algebraMap (N.presheaf.stalk y.1) N.functionField
          (fiberStalkMap f x y a)) y.1 := by
  let N := (X.fromSpecStalk (genericPoint X)).normalization
  let f := (X.fromSpecStalk (genericPoint X)).fromNormalization
  have : AlgebraicGeometry.IsFinite f := finite_genericNormalization sX
  have : IsIntegral N := integral_genericNormalization
  have : SmoothOfRelativeDimension 1 (f ≫ sX) := smooth_genericNormalization sX hd
  have : IsLocallyNoetherian N := LocallyOfFiniteType.isLocallyNoetherian (f ≫ sX)
  apply (localOrder_int_eq_normalizationFiber sX x hx (hd x) a ha).trans
  apply finsum_congr
  intro y
  have hyclosed : IsClosed ({y.1} : Set N) :=
    isClosed_point_of_isClosed_image f y.1 (y.2.symm ▸ hx)
  have hyheight : Order.coheight y.1 = 1 :=
    coheight_eq_of_smooth_closed (f ≫ sX) 1 y.1 hyclosed
  have hn : fiberStalkMap f x y a ≠ 0 := by
    let : Algebra (X.presheaf.stalk x) (N.presheaf.stalk y.1) :=
      (fiberStalkMap f x y).toAlgebra
    let hf := genericNormalization_bijective_functionField (X := X)
    let : Algebra (N.presheaf.stalk y.1) X.functionField :=
      (birationalStalkToField f hf y.1).toAlgebra
    have : IsScalarTower (X.presheaf.stalk x) (N.presheaf.stalk y.1) X.functionField :=
      birationalFiberStalk_tower f hf x y
    intro hz
    apply ha
    apply IsFractionRing.injective (X.presheaf.stalk x) X.functionField
    rw [map_zero, IsScalarTower.algebraMap_apply (X.presheaf.stalk x)
      (N.presheaf.stalk y.1) X.functionField]
    change algebraMap (N.presheaf.stalk y.1) X.functionField (fiberStalkMap f x y a) = 0
    rw [hz, map_zero]
  exact (scheme_order_of_stalk_element y.1 hyheight _ hn).symm
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne

theorem finsum_fiberwise {α β M : Type*} [AddCommMonoid M]
    (f : α → β) (w : α → M) (hw : Function.HasFiniteSupport w) :
    (∑ᶠ x : β, ∑ᶠ y : {y : α // f y = x}, w y.1) = ∑ᶠ y, w y := by
  classical
  let s := hw.toFinset
  have hinner (x : β) : (∑ᶠ y : {y : α // f y = x}, w y.1) =
      ∑ y ∈ s with f y = x, w y := by
    rw [finsum_subtype_eq_finsum_cond]
    apply finsum_cond_eq_sum_of_cond_iff
    intro y hy
    simp only [Finset.mem_filter]
    exact ⟨fun h => ⟨hw.mem_toFinset.mpr hy, h⟩, And.right⟩
  simp_rw [hinner]
  rw [finsum_eq_sum_of_support_subset _ (s.support_of_fiberwise_sum_subset_image w f),
    Finset.sum_fiberwise_of_maps_to (t := s.image f) _ w]
  · exact (finsum_eq_sum w hw).symm
  · intro y hy
    exact Finset.mem_image.mpr ⟨y,hy,rfl⟩
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne
open AlgebraicGeometry CategoryTheory
abbrev ClosedCurvePoint (X : Scheme) := {x : X // IsClosed ({x} : Set X)}
variable {C X : Scheme} (sC : C ⟶ Spec (.of ℂ)) [SmoothOfRelativeDimension 1 sC]
include sC in
lemma curvePrime_isClosed (p : PrimeDivisor C) : IsClosed ({p.1} : Set C) := by
  exact isClosed_point_of_max_coheight (coheight_le_of_smooth_dimension sC 1) p.1 p.2

noncomputable def finiteCurvePrimeImage (f : C ⟶ X) [IsFinite f]
    (p : PrimeDivisor C) : ClosedCurvePoint X :=
  ⟨f p.1, by simpa only [Set.image_singleton] using
    f.isClosedMap {p.1} (curvePrime_isClosed sC p)⟩

noncomputable def finiteCurvePrimeFiberEquiv (f : C ⟶ X) [IsFinite f]
    (x : ClosedCurvePoint X) :
    {p : PrimeDivisor C // finiteCurvePrimeImage sC f p = x} ≃
      {y : C // f y = x.1} := by
  refine
    { toFun := fun p => ⟨p.1.1, congrArg Subtype.val p.2⟩
      invFun := fun y => ⟨⟨y.1, ?_⟩, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · exact coheight_eq_of_smooth_closed sC 1 y.1
      (isClosed_point_of_isClosed_image f y.1 (y.2.symm ▸ x.2))
  · exact Subtype.ext y.2
  · intro p
    rfl
  · intro y
    rfl
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne
open AlgebraicGeometry CategoryTheory
universe u
section StalkGenerization
variable {X : Scheme.{u}}

@[instance_reducible]
noncomputable def stalkGenerizationAlgebra {x y : X} (h : x ⤳ y) :
    Algebra (X.presheaf.stalk y) (X.presheaf.stalk x) :=
  (X.presheaf.stalkSpecializes h).hom.toAlgebra

lemma open_stalk_generization_tower {x y : X} (h : x ⤳ y)
    (U : X.Opens) (hy : y ∈ U) :
    letI := TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨y, hy⟩
    letI := TopCat.Presheaf.algebra_section_stalk X.presheaf
      ⟨x, h.mem_open U.isOpen hy⟩
    letI := stalkGenerizationAlgebra h
    IsScalarTower Γ(X, U) (X.presheaf.stalk y) (X.presheaf.stalk x) := by
  let := TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨y, hy⟩
  let := TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨x, h.mem_open U.isOpen hy⟩
  let := stalkGenerizationAlgebra h
  apply IsScalarTower.of_algebraMap_eq
  intro a
  exact (congrArg (fun f : Γ(X, U) ⟶ X.presheaf.stalk x => f a)
    (X.presheaf.germ_stalkSpecializes hy h)).symm

end StalkGenerization
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne
open AlgebraicGeometry CategoryTheory
universe u
variable {X : Scheme.{u}}

lemma functionField_stalkGenerization_tower [IrreducibleSpace X]
    {x y : X} (h : x ⤳ y) :
    letI := stalkGenerizationAlgebra h
    IsScalarTower (X.presheaf.stalk y) (X.presheaf.stalk x) X.functionField := by
  let := stalkGenerizationAlgebra h
  apply IsScalarTower.of_algebraMap_eq'
  change (X.presheaf.stalkSpecializes
    ((genericPoint_spec X).specializes (show y ∈ Set.univ from trivial))).hom =
    ((X.presheaf.stalkSpecializes
      ((genericPoint_spec X).specializes (show x ∈ Set.univ from trivial))).hom).comp
      (X.presheaf.stalkSpecializes h).hom
  exact congrArg CommRingCat.Hom.hom
    (X.presheaf.stalkSpecializes_comp
      ((genericPoint_spec X).specializes (show x ∈ Set.univ from trivial)) h).symm

theorem isLocalization_stalkGenerization [IsIntegral X]
    {x y : X} (h : x ⤳ y) :
    letI := stalkGenerizationAlgebra h
    IsLocalization.AtPrime (X.presheaf.stalk x)
      ((IsLocalRing.maximalIdeal (X.presheaf.stalk x)).comap
        (X.presheaf.stalkSpecializes h).hom) := by
  let := stalkGenerizationAlgebra h
  obtain ⟨U, hU, hy, _⟩ := exists_isAffineOpen_mem_and_subset
    (show y ∈ (⊤ : X.Opens) from trivial)
  let := TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨y, hy⟩
  let := TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨x, h.mem_open U.isOpen hy⟩
  let := open_stalk_generization_tower h U hy
  let := hU.isLocalization_stalk ⟨x, h.mem_open U.isOpen hy⟩
  let := functionField_stalkGenerization_tower h
  apply LocalizationTower.atPrime_of_localized_base
    (hU.primeIdealOf ⟨x, h.mem_open U.isOpen hy⟩).asIdeal.primeCompl
  intro a b he
  apply IsFractionRing.injective (X.presheaf.stalk y) X.functionField
  rw [IsScalarTower.algebraMap_apply (X.presheaf.stalk y) (X.presheaf.stalk x)
    X.functionField, IsScalarTower.algebraMap_apply (X.presheaf.stalk y)
    (X.presheaf.stalk x) X.functionField, he]
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne
open AlgebraicGeometry CategoryTheory
universe u
variable {X : Scheme.{u}}

noncomputable def generizationPrime {x y : X} (h : x ⤳ y) :
    Ideal (X.presheaf.stalk y) :=
  (IsLocalRing.maximalIdeal (X.presheaf.stalk x)).comap
    (X.presheaf.stalkSpecializes h).hom

instance generizationPrime_isPrime {x y : X} (h : x ⤳ y) :
    (generizationPrime h).IsPrime := Ideal.comap_isPrime _ _

lemma generizationPrime_height [IsIntegral X] {x y : X} (h : x ⤳ y)
    (hx : Order.coheight x = 1) : (generizationPrime h).height = 1 := by
  let := stalkGenerizationAlgebra h
  let : IsLocalization.AtPrime (X.presheaf.stalk x) (generizationPrime h) :=
    isLocalization_stalkGenerization h
  have hd := IsLocalization.AtPrime.ringKrullDim_eq_height
    (generizationPrime h) (X.presheaf.stalk x)
  rw [ringKrullDim_stalk_eq_coheight, hx] at hd
  exact WithBot.coe_injective hd.symm

lemma generizationPrime_affine {x y : X} (h : x ⤳ y) {U : X.Opens}
    (hU : IsAffineOpen U) (hy : y ∈ U) :
    (generizationPrime h).comap (X.presheaf.germ U y hy).hom =
      (hU.primeIdealOf ⟨x, h.mem_open U.isOpen hy⟩).asIdeal := by
  rw [generizationPrime, Ideal.comap_comap]
  have he := congrArg CommRingCat.Hom.hom (X.presheaf.germ_stalkSpecializes hy h)
  change (X.presheaf.stalkSpecializes h).hom.comp (X.presheaf.germ U y hy).hom =
    (X.presheaf.germ U x (h.mem_open U.isOpen hy)).hom at he
  rw [he]
  exact (congrArg PrimeSpectrum.asIdeal
    (hU.primeIdealOf_eq_map_closedPoint ⟨x, h.mem_open U.isOpen hy⟩)).symm

lemma generizationPrime_injective {x z y : X} (hxy : x ⤳ y) (hzy : z ⤳ y)
    (he : generizationPrime hxy = generizationPrime hzy) : x = z := by
  obtain ⟨U, hU, hy, _⟩ := exists_isAffineOpen_mem_and_subset
    (show y ∈ (⊤ : X.Opens) from trivial)
  have he' := congrArg (Ideal.comap (X.presheaf.germ U y hy).hom) he
  rw [generizationPrime_affine hxy hU hy, generizationPrime_affine hzy hU hy] at he'
  have hp := PrimeSpectrum.ext he'
  have hh := congrArg hU.fromSpec hp
  simpa only [hU.fromSpec_primeIdealOf] using hh
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne
namespace FactorialUniformizers
variable {A : Type*} [CommRing A] [hdom : IsDomain A] [IsNoetherianRing A]
omit hdom in

theorem order_generator (p q : Ideal A) [p.IsPrime] [q.IsPrime]
    (hp : p.height = 1) (hq : q.height = 1) (a : A) (ha : p = Ideal.span {a}) :
    Ring.ord (Localization.AtPrime q) (algebraMap A (Localization.AtPrime q) a) =
      if p = q then 1 else 0 := by
  classical
  by_cases he : p = q
  · subst q
    simp only [ite_true]
    have hm : Ideal.span {algebraMap A (Localization.AtPrime p) a} =
        IsLocalRing.maximalIdeal (Localization.AtPrime p) := by
      rw [← Localization.AtPrime.map_eq_maximalIdeal]
      conv_rhs => arg 2; rw [ha]
      rw [Ideal.map_span, Set.image_singleton]
    rw [Ring.ord, hm]
    have : IsSimpleModule (Localization.AtPrime p)
        (Localization.AtPrime p ⧸ IsLocalRing.maximalIdeal (Localization.AtPrime p)) :=
      isSimpleModule_iff_isCoatom.mpr
        (Ideal.isMaximal_def.mp (IsLocalRing.maximalIdeal.isMaximal _))
    exact Module.length_eq_one _ _
  · simp only [ite_eq_right he]
    apply Ring.ord_of_isUnit
    apply IsLocalization.map_units (Localization.AtPrime q) (M := q.primeCompl) ⟨a, ?_⟩
    intro hmem
    have hle : p ≤ q := by
      rw [ha]
      exact q.span_singleton_le_iff_mem.mpr hmem
    exact he (Ideal.eq_of_le_of_height_le p hle (by rw [hp, hq]))
end FactorialUniformizers
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne
open AlgebraicGeometry CategoryTheory
universe u
variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]

open scoped Classical in

theorem order_stalk_generator {x y z : X} (hxy : x ⤳ y) (hzy : z ⤳ y)
    (hx : Order.coheight x = 1) (hz : Order.coheight z = 1)
    (a : X.presheaf.stalk y) (ha : generizationPrime hxy = Ideal.span {a}) :
    X.ord (algebraMap (X.presheaf.stalk y) X.functionField a) z =
      if x = z then 1 else 0 := by
  classical
  let := stalkGenerizationAlgebra hzy
  let : IsLocalization.AtPrime (X.presheaf.stalk z) (generizationPrime hzy) :=
    isLocalization_stalkGenerization hzy
  let := functionField_stalkGenerization_tower hzy
  have ha0 : a ≠ 0 := by
    intro he
    have hp := (generizationPrime hxy).ne_bot_of_height_eq_one
      (generizationPrime_height hxy hx)
    exact hp (by simpa only [he, Ideal.span_singleton_zero] using ha)
  have hay : algebraMap (X.presheaf.stalk y) X.functionField a ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr ha0
  have haz : algebraMap (X.presheaf.stalk y) (X.presheaf.stalk z) a ≠ 0 := by
    intro he
    apply hay
    rw [IsScalarTower.algebraMap_apply (X.presheaf.stalk y) (X.presheaf.stalk z)
      X.functionField, he, map_zero]
  have ho := scheme_order_of_stalk_element z hz
    (algebraMap (X.presheaf.stalk y) (X.presheaf.stalk z) a) haz
  rw [← IsScalarTower.algebraMap_apply] at ho
  let e := IsLocalization.algEquiv (generizationPrime hzy).primeCompl
    (Localization.AtPrime (generizationPrime hzy)) (X.presheaf.stalk z)
  have he := ringOrder_equiv e.toRingEquiv
    (algebraMap (X.presheaf.stalk y) (Localization.AtPrime (generizationPrime hzy)) a)
  have hec : e.toRingEquiv
      (algebraMap (X.presheaf.stalk y) (Localization.AtPrime (generizationPrime hzy)) a) =
      algebraMap (X.presheaf.stalk y) (X.presheaf.stalk z) a := e.commutes a
  rw [hec, FactorialUniformizers.order_generator (generizationPrime hxy)
    (generizationPrime hzy) (generizationPrime_height hxy hx)
    (generizationPrime_height hzy hz) a ha] at he
  rw [he] at ho
  have hp : generizationPrime hxy = generizationPrime hzy ↔ x = z := by
    constructor
    · exact generizationPrime_injective hxy hzy
    · rintro rfl; rfl
  simpa only [hp, apply_ite ENat.toNat, ENat.toNat_one, ENat.toNat_zero,
    Int.cast_ofNat, Nat.cast_ite, Nat.cast_one, Nat.cast_zero] using ho
end NumericalDimensionOne

end OAI
