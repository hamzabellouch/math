import Mathlib
import OAI.AlgebraicGeometry.NumericalDimension.ProjectiveCoordinates

namespace OAI

/-! Surface Square. -/

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne
open AlgebraicGeometry CategoryTheory HomogeneousLocalization TopologicalSpace
attribute [local instance] MvPolynomial.gradedAlgebra
lemma projective_coordinate_cover (N : ℕ) :
    (⨆ i : Fin (N+1), Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N+1)) ℂ)
      (MvPolynomial.X i)) = ⊤ := by
  let A := MvPolynomial.homogeneousSubmodule (Fin (N+1)) ℂ
  let : IsScalarTower ℂ (A 0) (MvPolynomial (Fin (N+1)) ℂ) :=
    IsScalarTower.of_algebraMap_eq (R := ℂ) (S := A 0) (A := MvPolynomial (Fin (N+1)) ℂ) fun _ => rfl
  apply Proj.iSup_basicOpen_eq_top' _ _ (fun i => ⟨1,projectiveVariable_mem i⟩)
  rw [← Algebra.adjoin_adjoin_of_tower ℂ, MvPolynomial.adjoin_range_X]
  exact Algebra.adjoin_univ _ _
lemma projectiveAffineMap_coords_injective {R : Type} [CommRing R] {N : ℕ}
    (c d : ℂ →+* R) (x y : Fin (N+1) → R) (i : Fin (N+1))
    (hx : x i = 1) (hy : y i = 1)
    (h : projectiveAffineMap c x i hx = projectiveAffineMap d y i hy) :
    c = d ∧ x = y := by
  unfold projectiveAffineMap at h
  have hh := Spec.map_injective ((cancel_mono (Proj.awayι _ _ _ _)).mp h)
  have hr := congrArg CommRingCat.Hom.hom hh
  constructor
  · apply RingHom.ext
    intro a
    have he := DFunLike.congr_fun hr (projectiveChartConstants i a)
    exact (projectiveChartRingHom_constants c x i hx a).symm.trans
      (he.trans (projectiveChartRingHom_constants d y i hy a))
  · funext j
    have he := DFunLike.congr_fun hr (projectiveChartRatio i j)
    simpa only [CommRingCat.hom_ofHom,projectiveChartRingHom_ratio] using he
lemma projectiveAffineMap_preimage_homogeneous {R : Type} [CommRing R] {N : ℕ}
    (c : ℂ →+* R) (x : Fin (N+1) → R) (i : Fin (N+1)) (hi : x i = 1)
    (d : ℕ) (hd : 0 < d) (P : MvPolynomial (Fin (N+1)) ℂ) (hP : P.IsHomogeneous d) :
    projectiveAffineMap c x i hi ⁻¹ᵁ Proj.basicOpen
      (MvPolynomial.homogeneousSubmodule (Fin (N+1)) ℂ) P =
        PrimeSpectrum.basicOpen (MvPolynomial.eval₂Hom c x P) := by
  change (Spec.map (CommRingCat.ofHom (projectiveChartRingHom c x i hi)) ≫
    Proj.awayι _ (MvPolynomial.X i) (projectiveVariable_mem i) (by decide : 0 < 1)) ⁻¹ᵁ
    Proj.basicOpen _ P = _
  rw [Scheme.Hom.comp_preimage,
    Proj.awayι_preimage_basicOpen _ (projectiveVariable_mem i) (by decide : 0 < 1) hP hd]
  have he : projectiveChartRingHom c x i hi
      (Away.isLocalizationElem (projectiveVariable_mem i) hP) = MvPolynomial.eval₂Hom c x P := by
    change projectiveChartRingHom c x i hi (Away.mk _ _ d (P ^ 1) _) = _
    rw [projectiveChartRingHom_mk,map_pow,pow_one]
  ext p
  change projectiveChartRingHom c x i hi _ ∉ p.asIdeal ↔ MvPolynomial.eval₂Hom c x P ∉ p.asIdeal
  rw [he]
lemma projectiveField_coordinates {K : Type} [Field K] {N : ℕ}
    (u : Spec (.of K) ⟶ complexProjectiveSpace N) :
    ∃ (i : Fin (N+1)) (c : ℂ →+* K) (x : Fin (N+1) → K) (hi : x i = 1),
      u = projectiveAffineMap c x i hi := by
  let z : Spec (.of K) := IsLocalRing.closedPoint K
  obtain ⟨i,hi⟩ := Opens.mem_iSup.mp ((projective_coordinate_cover N).ge
    (show u z ∈ (⊤ : (complexProjectiveSpace N).Opens) from trivial))
  let a := Proj.awayι (MvPolynomial.homogeneousSubmodule (Fin (N+1)) ℂ)
    (MvPolynomial.X i) (projectiveVariable_mem i) (by decide : 0 < 1)
  have hr : Set.range u ⊆ Set.range a := by
    rintro _ ⟨p,rfl⟩
    change u p ∈ a.opensRange
    rw [Proj.opensRange_awayι]
    rw [Subsingleton.elim p z]
    exact hi
  let v := IsOpenImmersion.lift a u hr
  have hv : v ≫ a = u := IsOpenImmersion.lift_fac a u hr
  obtain ⟨ψ,hψ⟩ := Spec.map_surjective v
  let c := ψ.hom.comp (projectiveChartConstants i)
  let x (j : Fin (N+1)) := ψ.hom (projectiveChartRatio i j)
  have hxi : x i = 1 := by dsimp only [x]; rw [projectiveChartRatio_self,map_one]
  refine ⟨i,c,x,hxi,?_⟩
  rw [← hv,← hψ]
  unfold projectiveAffineMap
  congr 1
  exact congrArg (fun h => Spec.map (CommRingCat.ofHom h))
    (projectiveChart_hom_reconstruct i ψ.hom).symm
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne
open AlgebraicGeometry CategoryTheory HomogeneousLocalization TopologicalSpace
attribute [local instance] MvPolynomial.gradedAlgebra
lemma projectiveLocal_coordinatesAt {R : Type} [CommRing R] [IsLocalRing R] {N : ℕ}
    (u : Spec (.of R) ⟶ complexProjectiveSpace N) (i : Fin (N+1))
    (hi : u (IsLocalRing.closedPoint R) ∈ Proj.basicOpen
      (MvPolynomial.homogeneousSubmodule (Fin (N+1)) ℂ) (MvPolynomial.X i)) :
    ∃ (c : ℂ →+* R) (t : Fin (N+1) → R) (ht : t i = 1),
      u = projectiveAffineMap c t i ht := by
  let a := Proj.awayι (MvPolynomial.homogeneousSubmodule (Fin (N+1)) ℂ)
    (MvPolynomial.X i) (projectiveVariable_mem i) (by decide : 0 < 1)
  have hr : Set.range u ⊆ Set.range a := by
    rintro _ ⟨p,rfl⟩
    change u p ∈ a.opensRange
    rw [Proj.opensRange_awayι]
    exact ((IsLocalRing.specializes_closedPoint p).map u.continuous).mem_open
      (Proj.basicOpen _ _).isOpen hi
  let v := IsOpenImmersion.lift a u hr
  have hv : v ≫ a = u := IsOpenImmersion.lift_fac a u hr
  obtain ⟨ψ,hψ⟩ := Spec.map_surjective v
  let c := ψ.hom.comp (projectiveChartConstants i)
  let t (j : Fin (N+1)) := ψ.hom (projectiveChartRatio i j)
  have hti : t i = 1 := by dsimp only [t]; rw [projectiveChartRatio_self,map_one]
  refine ⟨c,t,hti,?_⟩
  rw [← hv,← hψ]
  unfold projectiveAffineMap
  congr 1
  exact congrArg (fun h => Spec.map (CommRingCat.ofHom h))
    (projectiveChart_hom_reconstruct i ψ.hom).symm
lemma projective_generic_coordinate_ne_zero {X : Scheme} [IsIntegral X] {N : ℕ}
    (f : X ⟶ complexProjectiveSpace N)
    (c : ℂ →+* X.functionField) (t : Fin (N+1) → X.functionField)
    (i₀ : Fin (N+1)) (ht : t i₀ = 1)
    (hg : X.fromSpecStalk (genericPoint X) ≫ f = projectiveAffineMap c t i₀ ht)
    (p : X) (i : Fin (N+1))
    (hi : f p ∈ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N+1)) ℂ) (MvPolynomial.X i)) :
    t i ≠ 0 := by
  have hη : f (genericPoint X) ∈ Proj.basicOpen
      (MvPolynomial.homogeneousSubmodule (Fin (N+1)) ℂ) (MvPolynomial.X i) :=
    ((genericPoint_specializes p).map f.continuous).mem_open (Proj.basicOpen _ _).isOpen hi
  have hm : IsLocalRing.closedPoint X.functionField ∈
      projectiveAffineMap c t i₀ ht ⁻¹ᵁ Proj.basicOpen
        (MvPolynomial.homogeneousSubmodule (Fin (N+1)) ℂ) (MvPolynomial.X i) := by
    rw [← hg]
    change f (X.fromSpecStalk (genericPoint X) (IsLocalRing.closedPoint X.functionField)) ∈
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N+1)) ℂ) (MvPolynomial.X i)
    rw [Scheme.fromSpecStalk_closedPoint]
    exact hη
  rw [projectiveAffineMap_preimage] at hm
  change t i ∉ IsLocalRing.maximalIdeal X.functionField at hm
  simpa only [IsLocalRing.maximalIdeal_eq_bot,Ideal.mem_bot] using hm
lemma projective_stalk_coordinates {X : Scheme} [IsIntegral X] {N : ℕ}
    (f : X ⟶ complexProjectiveSpace N)
    (c : ℂ →+* X.functionField) (t : Fin (N+1) → X.functionField)
    (i₀ : Fin (N+1)) (ht : t i₀ = 1)
    (hg : X.fromSpecStalk (genericPoint X) ≫ f = projectiveAffineMap c t i₀ ht)
    (p : X) (i : Fin (N+1))
    (hi : f p ∈ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N+1)) ℂ) (MvPolynomial.X i)) :
    ∃ (b : ℂ →+* X.presheaf.stalk p) (x : Fin (N+1) → X.presheaf.stalk p),
      x i = 1 ∧ (algebraMap (X.presheaf.stalk p) X.functionField).comp b = c ∧
      (∀ j, algebraMap (X.presheaf.stalk p) X.functionField (x j) = t j / t i) ∧
      (∀ j, IsUnit (x j) ↔ f p ∈ Proj.basicOpen
        (MvPolynomial.homogeneousSubmodule (Fin (N+1)) ℂ) (MvPolynomial.X j)) := by
  let hlr : IsLocalRing (X.presheaf.stalk p) := X.toLocallyRingedSpace.isLocalRing p
  have hne := projective_generic_coordinate_ne_zero f c t i₀ ht hg p i hi
  have hlocal : (X.fromSpecStalk p ≫ f) (IsLocalRing.closedPoint (X.presheaf.stalk p)) ∈
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N+1)) ℂ) (MvPolynomial.X i) := by
    change f (X.fromSpecStalk p (IsLocalRing.closedPoint (X.presheaf.stalk p))) ∈ _
    rw [Scheme.fromSpecStalk_closedPoint]
    exact hi
  obtain ⟨b,x,hx,hmap⟩ := @projectiveLocal_coordinatesAt (X.presheaf.stalk p) inferInstance hlr N (X.fromSpecStalk p ≫ f) i hlocal
  let a := algebraMap (X.presheaf.stalk p) X.functionField
  have hmapη : projectiveAffineMap (a.comp b) (fun j => a (x j)) i
      (by rw [hx,map_one]) = X.fromSpecStalk (genericPoint X) ≫ f := by
    rw [← projectiveAffineMap_naturality b x i hx a,← hmap,← Category.assoc]
    rw [show Spec.map (CommRingCat.ofHom a) ≫ X.fromSpecStalk p =
        X.fromSpecStalk (genericPoint X) from
      X.SpecMap_stalkSpecializes_fromSpecStalk (genericPoint_specializes p)]
  have hnorm : (t i)⁻¹ * t i = 1 := inv_mul_cancel₀ hne
  have hnormmap : projectiveAffineMap c (fun j => (t i)⁻¹ * t j) i hnorm =
      X.fromSpecStalk (genericPoint X) ≫ f := by
    rw [← projectiveFieldMap_eq_affine,projectiveFieldMap_scaling c t i hne _ (inv_ne_zero hne),
      projectiveFieldMap_independent c t i i₀ hne (by rw [ht]; exact one_ne_zero),
      projectiveFieldMap_eq_affine c t i₀ ht,← hg]
  obtain ⟨hb,heq⟩ := projectiveAffineMap_coords_injective (a.comp b) c
    (fun j => a (x j)) (fun j => (t i)⁻¹ * t j) i (by rw [hx,map_one]) hnorm
    (hmapη.trans hnormmap.symm)
  refine ⟨b,x,hx,hb,?_,?_⟩
  · intro j
    rw [congrFun heq j,div_eq_mul_inv,mul_comm]
  · intro j
    have hm := congrArg (fun u : Spec (X.presheaf.stalk p) ⟶ complexProjectiveSpace N =>
      u ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N+1)) ℂ)
        (MvPolynomial.X j)) hmap
    rw [projectiveAffineMap_preimage] at hm
    have hp := congrArg (fun U : (Spec (X.presheaf.stalk p)).Opens =>
      IsLocalRing.closedPoint (X.presheaf.stalk p) ∈ U) hm
    change (f (X.fromSpecStalk p (IsLocalRing.closedPoint (X.presheaf.stalk p))) ∈
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N+1)) ℂ) (MvPolynomial.X j)) =
        (x j ∉ IsLocalRing.maximalIdeal (X.presheaf.stalk p)) at hp
    rw [Scheme.fromSpecStalk_closedPoint] at hp
    rw [hp,IsLocalRing.mem_maximalIdeal,mem_nonunits_iff,not_not]
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne
open AlgebraicGeometry CategoryTheory
lemma finite_support_selection {α ι : Type*} [Finite ι] (F : ι → α →₀ ℤ)
    (i : α → ι) : (Function.support (fun a => F (i a) a)).Finite := by
  apply (Set.finite_iUnion (fun j => (F j).hasFiniteSupport)).subset
  intro a ha
  exact Set.mem_iUnion.mpr ⟨i a,ha⟩
noncomputable def selectedOrdDivisor {X : Scheme} [IsIntegral X]
    [IsLocallyNoetherian X] [StalkwiseNormal X] [CompactSpace X]
    {ι : Type*} [Finite ι] (g : ι → X.functionField) (i : X → ι) : WeilDivisor X :=
  Finsupp.ofSupportFinite (fun p : PrimeDivisor X => principalWeilDivisor (g (i p.1)) p)
    (finite_support_selection (fun j => principalWeilDivisor (g j)) (fun p => i p.1))
lemma selectedOrdDivisor_apply {X : Scheme} [IsIntegral X]
    [IsLocallyNoetherian X] [StalkwiseNormal X] [CompactSpace X]
    {ι : Type*} [Finite ι] (g : ι → X.functionField) (i : X → ι) (p : PrimeDivisor X) :
    selectedOrdDivisor g i p = X.ord (g (i p.1)) p.1 := by
  unfold selectedOrdDivisor
  rw [Finsupp.ofSupportFinite_coe,principalWeilDivisor_apply]
lemma exists_cartierDivisor_of_local_orders {X : Scheme} [IsIntegral X]
    [IsLocallyNoetherian X] [StalkwiseNormal X] [CompactSpace X]
    {ι : Type*} [Finite ι] (U : ι → X.Opens) (hcover : ∀ x : X, ∃ i, x ∈ U i)
    (g : ι → X.functionField) (hg : ∀ i, g i ≠ 0)
    (hcompat : ∀ i j (p : PrimeDivisor X), p.1 ∈ U i → p.1 ∈ U j →
      X.ord (g i) p.1 = X.ord (g j) p.1) :
    ∃ D : WeilDivisor X, IsCartierDivisor D ∧
      ∀ i (p : PrimeDivisor X), p.1 ∈ U i → D p = X.ord (g i) p.1 := by
  classical
  choose i hi using hcover
  let D : WeilDivisor X := selectedOrdDivisor g i
  have he (j : ι) (p : PrimeDivisor X) (hp : p.1 ∈ U j) : D p = X.ord (g j) p.1 := by
    rw [show D p = X.ord (g (i p.1)) p.1 from selectedOrdDivisor_apply g i p]
    exact hcompat (i p.1) j p (hi p.1) hp
  refine ⟨D,?_,he⟩
  intro x
  obtain ⟨V,hV,hxV,hVU⟩ := exists_isAffineOpen_mem_and_subset (hi x)
  exact ⟨V,hV,hxV,g (i x),hg (i x),fun p hp => he (i x) p (hVU hp)⟩
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne
open AlgebraicGeometry CategoryTheory HomogeneousLocalization TopologicalSpace
attribute [local instance] MvPolynomial.gradedAlgebra
lemma exists_projective_hyperplane_divisor {X : Scheme} [IsIntegral X]
    [IsLocallyNoetherian X] [StalkwiseNormal X] [CompactSpace X] {N : ℕ}
    (f : X ⟶ complexProjectiveSpace N)
    (c : ℂ →+* X.functionField) (t : Fin (N+1) → X.functionField)
    (i₀ : Fin (N+1)) (ht : t i₀ = 1)
    (hg : X.fromSpecStalk (genericPoint X) ≫ f = projectiveAffineMap c t i₀ ht) :
    ∃ D : WeilDivisor X, IsCartierDivisor D ∧ ∀ i (p : PrimeDivisor X),
      f p.1 ∈ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N+1)) ℂ)
        (MvPolynomial.X i) → D p = X.ord (t i)⁻¹ p.1 := by
  classical
  let U (i : Fin (N+1)) := f ⁻¹ᵁ Proj.basicOpen
    (MvPolynomial.homogeneousSubmodule (Fin (N+1)) ℂ) (MvPolynomial.X i)
  have hcov (x : X) : ∃ i, x ∈ U i := by
    obtain ⟨i,hi⟩ := Opens.mem_iSup.mp ((projective_coordinate_cover N).ge
      (show f x ∈ (⊤ : (complexProjectiveSpace N).Opens) from trivial))
    exact ⟨i,hi⟩
  let g (i : Fin (N+1)) := if t i = 0 then 1 else (t i)⁻¹
  have hgn (i : Fin (N+1)) : g i ≠ 0 := by
    dsimp only [g]; split_ifs with h
    · exact one_ne_zero
    · exact inv_ne_zero h
  have he (i : Fin (N+1)) (x : X) (hx : x ∈ U i) : g i = (t i)⁻¹ := by
    exact ite_eq_right (projective_generic_coordinate_ne_zero f c t i₀ ht hg x i hx)
  obtain ⟨D,hD,hEq⟩ := exists_cartierDivisor_of_local_orders U hcov g hgn (by
    intro i j p hpi hpj
    rw [he i p.1 hpi,he j p.1 hpj]
    have hi := projective_generic_coordinate_ne_zero f c t i₀ ht hg p.1 i hpi
    have hj := projective_generic_coordinate_ne_zero f c t i₀ ht hg p.1 j hpj
    obtain ⟨b,x,_,_,hxe,hxu⟩ := projective_stalk_coordinates f c t i₀ ht hg p.1 i hpi
    have ho := order_stalk_unit p ((hxu j).mpr hpj)
    rw [hxe j,order_div hj hi] at ho
    rw [order_inv _ hi,order_inv _ hj]
    omega)
  refine ⟨D,hD,?_⟩
  intro i p hp
  rw [hEq i p hp,he i p.1 hp]
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne
open AlgebraicGeometry CategoryTheory HomogeneousLocalization TopologicalSpace
attribute [local instance] MvPolynomial.gradedAlgebra
lemma projective_stalk_coordinates_full {X : Scheme} [IsIntegral X] {N : ℕ}
    (f : X ⟶ complexProjectiveSpace N)
    (c : ℂ →+* X.functionField) (t : Fin (N+1) → X.functionField)
    (i₀ : Fin (N+1)) (ht : t i₀ = 1)
    (hg : X.fromSpecStalk (genericPoint X) ≫ f = projectiveAffineMap c t i₀ ht)
    (p : X) (i : Fin (N+1))
    (hi : f p ∈ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N+1)) ℂ) (MvPolynomial.X i)) :
    ∃ (b : ℂ →+* X.presheaf.stalk p) (x : Fin (N+1) → X.presheaf.stalk p) (hx : x i = 1), (algebraMap (X.presheaf.stalk p) X.functionField).comp b = c ∧
      (∀ j, algebraMap (X.presheaf.stalk p) X.functionField (x j) = t j / t i) ∧
      X.fromSpecStalk p ≫ f = projectiveAffineMap b x i hx := by
  let hlr : IsLocalRing (X.presheaf.stalk p) := X.toLocallyRingedSpace.isLocalRing p
  have hne := projective_generic_coordinate_ne_zero f c t i₀ ht hg p i hi
  have hlocal : (X.fromSpecStalk p ≫ f) (IsLocalRing.closedPoint (X.presheaf.stalk p)) ∈
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N+1)) ℂ) (MvPolynomial.X i) := by
    change f (X.fromSpecStalk p (IsLocalRing.closedPoint (X.presheaf.stalk p))) ∈ _
    rw [Scheme.fromSpecStalk_closedPoint]
    exact hi
  obtain ⟨b,x,hx,hmap⟩ := @projectiveLocal_coordinatesAt (X.presheaf.stalk p) inferInstance hlr N (X.fromSpecStalk p ≫ f) i hlocal
  let a := algebraMap (X.presheaf.stalk p) X.functionField
  have hmapη : projectiveAffineMap (a.comp b) (fun j => a (x j)) i
      (by rw [hx,map_one]) = X.fromSpecStalk (genericPoint X) ≫ f := by
    rw [← projectiveAffineMap_naturality b x i hx a,← hmap,← Category.assoc]
    rw [show Spec.map (CommRingCat.ofHom a) ≫ X.fromSpecStalk p =
        X.fromSpecStalk (genericPoint X) from
      X.SpecMap_stalkSpecializes_fromSpecStalk (genericPoint_specializes p)]
  have hnorm : (t i)⁻¹ * t i = 1 := inv_mul_cancel₀ hne
  have hnormmap : projectiveAffineMap c (fun j => (t i)⁻¹ * t j) i hnorm =
      X.fromSpecStalk (genericPoint X) ≫ f := by
    rw [← projectiveFieldMap_eq_affine,projectiveFieldMap_scaling c t i hne _ (inv_ne_zero hne),
      projectiveFieldMap_independent c t i i₀ hne (by rw [ht]; exact one_ne_zero),
      projectiveFieldMap_eq_affine c t i₀ ht,← hg]
  obtain ⟨hb,heq⟩ := projectiveAffineMap_coords_injective (a.comp b) c
    (fun j => a (x j)) (fun j => (t i)⁻¹ * t j) i (by rw [hx,map_one]) hnorm
    (hmapη.trans hnormmap.symm)
  refine ⟨b,x,hx,hb,?_,?_⟩
  · intro j
    rw [congrFun heq j,div_eq_mul_inv,mul_comm]
  · exact hmap
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne
open AlgebraicGeometry CategoryTheory HomogeneousLocalization TopologicalSpace
attribute [local instance] MvPolynomial.gradedAlgebra
lemma projective_homogeneous_stalk_value {X : Scheme} [IsIntegral X] {N : ℕ}
    (f : X ⟶ complexProjectiveSpace N)
    (c : ℂ →+* X.functionField) (t : Fin (N+1) → X.functionField)
    (i₀ : Fin (N+1)) (ht : t i₀ = 1)
    (hg : X.fromSpecStalk (genericPoint X) ≫ f = projectiveAffineMap c t i₀ ht)
    (p : X) (i : Fin (N+1))
    (hi : f p ∈ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N+1)) ℂ) (MvPolynomial.X i))
    (d : ℕ) (hd : 0 < d) (P : MvPolynomial (Fin (N+1)) ℂ) (hP : P.IsHomogeneous d) :
    ∃ a : X.presheaf.stalk p,
      algebraMap (X.presheaf.stalk p) X.functionField a = MvPolynomial.eval₂Hom c t P / (t i)^d ∧
      (IsUnit a ↔ f p ∈ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N+1)) ℂ) P) := by
  obtain ⟨b,x,hx,hb,hxe,hmap⟩ := projective_stalk_coordinates_full f c t i₀ ht hg p i hi
  refine ⟨MvPolynomial.eval₂Hom b x P,?_,?_⟩
  · rw [MvPolynomial.map_eval₂Hom,hb]
    have he : (fun j => algebraMap (X.presheaf.stalk p) X.functionField (x j)) =
        (fun j => (t i)⁻¹ * t j) := by
      funext j
      rw [hxe j,div_eq_mul_inv,mul_comm]
    rw [he,eval₂_homogeneous_scaling c t _ hP]
    rw [div_eq_mul_inv,inv_pow,mul_comm]
  · have hm := congrArg (fun u : Spec (X.presheaf.stalk p) ⟶ complexProjectiveSpace N =>
      u ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N+1)) ℂ) P) hmap
    rw [projectiveAffineMap_preimage_homogeneous b x i hx d hd P hP] at hm
    have hp := congrArg (fun U : (Spec (X.presheaf.stalk p)).Opens =>
      IsLocalRing.closedPoint (X.presheaf.stalk p) ∈ U) hm
    change (f (X.fromSpecStalk p (IsLocalRing.closedPoint (X.presheaf.stalk p))) ∈
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N+1)) ℂ) P) =
        (MvPolynomial.eval₂Hom b x P ∉ IsLocalRing.maximalIdeal (X.presheaf.stalk p)) at hp
    rw [Scheme.fromSpecStalk_closedPoint] at hp
    rw [hp,IsLocalRing.mem_maximalIdeal,mem_nonunits_iff,not_not]
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne
open AlgebraicGeometry CategoryTheory HomogeneousLocalization TopologicalSpace
attribute [local instance] MvPolynomial.gradedAlgebra
lemma projective_hyperplane_section {X : Scheme} [IsIntegral X]
    [IsLocallyNoetherian X] [StalkwiseNormal X] [CompactSpace X] {N : ℕ}
    (f : X ⟶ complexProjectiveSpace N)
    (c : ℂ →+* X.functionField) (t : Fin (N+1) → X.functionField)
    (i₀ : Fin (N+1)) (ht : t i₀ = 1)
    (hg : X.fromSpecStalk (genericPoint X) ≫ f = projectiveAffineMap c t i₀ ht)
    (D : WeilDivisor X)
    (hD : ∀ i (p : PrimeDivisor X), f p.1 ∈
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N+1)) ℂ) (MvPolynomial.X i) →
      D p = X.ord (t i)⁻¹ p.1)
    (d : ℕ) (hd : 0 < d) (P : MvPolynomial (Fin (N+1)) ℂ) (hP : P.IsHomogeneous d)
    (hEv : MvPolynomial.eval₂Hom c t P ≠ 0) :
    IsDivisorSection (d • D) (MvPolynomial.eval₂Hom c t P) ∧
      sectionNonvanishing (d • D) (MvPolynomial.eval₂Hom c t P) =
        f ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N+1)) ℂ) P := by
  let U (i : Fin (N+1)) := f ⁻¹ᵁ Proj.basicOpen
    (MvPolynomial.homogeneousSubmodule (Fin (N+1)) ℂ) (MvPolynomial.X i)
  have hcov (x : X) : ∃ i, x ∈ U i := by
    obtain ⟨i,hi⟩ := Opens.mem_iSup.mp ((projective_coordinate_cover N).ge
      (show f x ∈ (⊤ : (complexProjectiveSpace N).Opens) from trivial))
    exact ⟨i,hi⟩
  have hlocal (i : Fin (N+1)) (hne : t i ≠ 0) (p : PrimeDivisor X) (hp : p.1 ∈ U i) :
      (d • D) p = X.ord ((t i)⁻¹ ^ d) p.1 := by
    rw [Finsupp.smul_apply,nsmul_eq_mul,hD i p hp,order_pow _ (inv_ne_zero hne)]
  constructor
  · apply Or.inr
    intro p
    obtain ⟨i,hi⟩ := hcov p.1
    have hne := projective_generic_coordinate_ne_zero f c t i₀ ht hg p.1 i hi
    obtain ⟨a,ha,_⟩ := projective_homogeneous_stalk_value f c t i₀ ht hg p.1 i hi d hd P hP
    have hreg := (ord_nonnegative_iff_regular p _ (div_ne_zero hEv (pow_ne_zero d hne))).mpr ⟨a,ha⟩
    rw [div_eq_mul_inv,← inv_pow,X.ord_mul hEv (pow_ne_zero d (inv_ne_zero hne)),
      ← hlocal i hne p hi] at hreg
    exact hreg
  · ext p
    obtain ⟨i,hi⟩ := hcov p
    have hne := projective_generic_coordinate_ne_zero f c t i₀ ht hg p i hi
    have hgpow := pow_ne_zero d (inv_ne_zero hne)
    obtain ⟨a,ha,hu⟩ := projective_homogeneous_stalk_value f c t i₀ ht hg p i hi d hd P hP
    have hae : algebraMap (X.presheaf.stalk p) X.functionField a =
        MvPolynomial.eval₂Hom c t P * (t i)⁻¹ ^ d := by rw [ha,div_eq_mul_inv,inv_pow]
    constructor
    · intro hp
      obtain ⟨b,hb,hbe⟩ := section_unit_stalk hEv hgpow (hlocal i hne) hi hp
      have hab : a = b := (IsFractionRing.injective (X.presheaf.stalk p) X.functionField)
        (hae.trans hbe.symm)
      exact hu.mp (hab ▸ hb)
    · intro hp
      exact section_nonvanishing_of_local_unit hEv hgpow (hlocal i hne) hi a (hu.mpr hp) hae
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne
open AlgebraicGeometry CategoryTheory HomogeneousLocalization TopologicalSpace
attribute [local instance] MvPolynomial.gradedAlgebra
lemma projective_homogeneous_basis {X : Scheme} {N : ℕ}
    (f : X ⟶ complexProjectiveSpace N) [IsClosedImmersion f]
    (x : X) (U : X.Opens) (hx : x ∈ U) :
    ∃ (d : ℕ) (_hd : 0 < d) (P : MvPolynomial (Fin (N+1)) ℂ), P.IsHomogeneous d ∧
      IsAffineOpen (f ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N+1)) ℂ) P) ∧
      f x ∈ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N+1)) ℂ) P ∧
      f ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N+1)) ℂ) P ≤ U := by
  classical
  let hAffine : IsAffineHom f := inferInstance
  let A := MvPolynomial.homogeneousSubmodule (Fin (N+1)) ℂ
  obtain ⟨V,hV,hUV⟩ := f.isClosedEmbedding.isInducing.isOpen_iff.mp U.isOpen
  have hxV : f x ∈ V := by
    change x ∈ f ⁻¹' V
    rw [hUV]
    exact hx
  obtain ⟨_,⟨P,rfl⟩,hxP,hPV⟩ :=
    (ProjectiveSpectrum.isTopologicalBasis_basic_opens A).exists_subset_of_mem_open hxV hV
  change f x ∈ Proj.basicOpen A P at hxP
  rw [Proj.basicOpen_eq_iSup_proj] at hxP
  obtain ⟨d,hxd⟩ := Opens.mem_iSup.mp hxP
  let Q := GradedRing.proj A d P
  have hQ : Q.IsHomogeneous d := by
    change Q ∈ A d
    rw [show Q = GradedRing.proj A d P from rfl,GradedRing.proj_apply]
    exact SetLike.coe_mem _
  obtain ⟨i,hxi⟩ := Opens.mem_iSup.mp ((projective_coordinate_cover N).ge
    (show f x ∈ (⊤ : (complexProjectiveSpace N).Opens) from trivial))
  have hh := hQ.mul (MvPolynomial.isHomogeneous_X ℂ i)
  have hOpen : IsAffineOpen (Proj.basicOpen A (Q * MvPolynomial.X i)) :=
    Proj.isAffineOpen_basicOpen A _ hh (Nat.zero_lt_succ _)
  have hPre : IsAffineOpen (f ⁻¹ᵁ Proj.basicOpen A (Q * MvPolynomial.X i)) :=
    @IsAffineOpen.preimage X (complexProjectiveSpace N) _ hOpen f hAffine
  refine ⟨d+1,Nat.zero_lt_succ _,Q * MvPolynomial.X i,hh,hPre,?_,?_⟩
  · rw [Proj.basicOpen_mul]
    exact ⟨hxd,hxi⟩
  · intro y hy
    have hyQ : f y ∈ Proj.basicOpen A Q := by
      rw [Proj.basicOpen_mul] at hy
      exact hy.1
    have hyP : f y ∈ Proj.basicOpen A P := by
      rw [Proj.basicOpen_eq_iSup_proj]
      exact Opens.mem_iSup.mpr ⟨d,hyQ⟩
    have hyV : y ∈ f ⁻¹' V := hPV hyP
    rwa [hUV] at hyV
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne
open AlgebraicGeometry CategoryTheory HomogeneousLocalization TopologicalSpace
attribute [local instance] MvPolynomial.gradedAlgebra
lemma exists_ampleDivisor_of_projective (X : ComplexProjectiveVariety)
    [StalkwiseNormal X.scheme] : ∃ D : WeilDivisor X.scheme, IsAmpleDivisor D := by
  obtain ⟨N,f,hf,_⟩ := X.projective
  let := hf
  obtain ⟨i₀,c,t,ht,hg⟩ := projectiveField_coordinates (X.scheme.fromSpecStalk (genericPoint X.scheme) ≫ f)
  obtain ⟨D,hD,hDl⟩ := exists_projective_hyperplane_divisor f c t i₀ ht hg
  refine ⟨D,hD,?_⟩
  intro x U hx
  obtain ⟨d,hd,P,hP,hAff,hxP,hU⟩ := projective_homogeneous_basis f x U hx
  obtain ⟨i,hi⟩ := Opens.mem_iSup.mp ((projective_coordinate_cover N).ge
    (show f x ∈ (⊤ : (complexProjectiveSpace N).Opens) from trivial))
  obtain ⟨a,ha,hu⟩ := projective_homogeneous_stalk_value f c t i₀ ht hg x i hi d hd P hP
  have hev : MvPolynomial.eval₂Hom c t P ≠ 0 := by
    intro hz
    have hn := ((hu.mpr hxP).map (algebraMap (X.scheme.presheaf.stalk x) X.scheme.functionField)).ne_zero
    apply hn
    rw [ha,hz,zero_div]
  obtain ⟨hsec,he⟩ := projective_hyperplane_section f c t i₀ ht hg D hDl d hd P hP hev
  exact ⟨d,hd,_,hev,hsec,he.symm ▸ hAff,he.symm ▸ hxP,he.symm ▸ hU⟩
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne
open AlgebraicGeometry CategoryTheory TopologicalSpace

lemma surface_fixed_square (X : ComplexProjectiveVariety)
    (hX : IsSmoothNfold X 2) :
    letI := smoothNormal X hX
    ∀ {Y : Scheme} [IsIntegral Y] [IsLocallyNoetherian Y]
    (f : X.scheme ⟶ Y) [IsDominant f] [IsProper f] (_hf : IsBirationalMorphism f)
    (e : PrimeDivisor X.scheme)
    (_he : ∀ x ∈ closure ({e.1} : Set X.scheme), f x = f e.1)
    {ι : Type*} (D : ι → WeilDivisor Y) (P : ι → WeilDivisor X.scheme)
    (_hP : ∀ j, IsCartierPullback f (D j) (P j)) (k : ι → ℕ) (_hk : ∀ j, 0 < k j)
    (S : ι → letI := schemeFieldAlgebra (.of ℂ) X.structureMap; Submodule ℂ X.scheme.functionField)
    (hS : ∀ j, ∀ s ∈ S j, IsDivisorSection (P j) s)
    (hne : ∀ j, ∃ s ∈ S j, s ≠ 0)
    (Z : ι → Finset Y) (_hZ : ∀ j z, z ∈ Z j → IsClosed ({z} : Set Y))
    (_hgen : ∀ j x, f x ∉ Z j → ∃ s ∈ S j, s ≠ 0 ∧ x ∈ sectionNonvanishing (P j) s)
    (c : ℝ) (_hc : 0 < c)
    (_hcoeff : ∀ j, c * (k j : ℝ) ≤ (fixedPart (P j) (S j) (hS j) (hne j) e : ℝ)),
    letI : SmoothOfRelativeDimension 2 X.structureMap := hX
    ∃ ε : ℝ, 0 < ε ∧ ∀ j,
      ε * (k j : ℝ)^2 ≤ (surfaceIntersection X.structureMap
        (smoothSurfaceWeilCartier X.structureMap (P j))
        (smoothSurfaceWeilCartier X.structureMap (P j)) : ℝ) := by
  let : StalkwiseNormal X.scheme := smoothNormal X hX
  intro Y hY hYn f hdom hproper hf e he ι D P hP k hk S hS hne Z hZ hgen c hc hcoeff
  obtain ⟨J,hJ⟩ := exists_ampleDivisor_of_projective X
  exact surface_fixed_square_from_ample X hX f hf J hJ e he D P hP k hk S hS hne Z hZ hgen c hc hcoeff
end NumericalDimensionOne

end OAI
