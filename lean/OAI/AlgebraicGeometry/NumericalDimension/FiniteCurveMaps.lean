import Mathlib
import OAI.AlgebraicGeometry.NumericalDimension.PrimeSpecialization

namespace OAI

/-! Finite Curve Maps. -/

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne
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

end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne
open AlgebraicGeometry CategoryTheory TopologicalSpace

theorem normalCurveAffine_isDedekind {C : Scheme} [IsIntegral C]
    [IsLocallyNoetherian C] [StalkwiseNormal C]
    (hdim : ∀ x : C, Order.coheight x ≤ 1)
    {U : C.Opens} [Nonempty U] (hU : IsAffineOpen U) :
    IsDedekindDomain Γ(C,U) := by
  have := integrallyClosed_affine hU
  have := IsLocallyNoetherian.component_noetherian ⟨U,hU⟩
  have : Ring.DimensionLEOne Γ(C,U) := by
    constructor
    intro p hp hpp
    let q : PrimeSpectrum Γ(C,U) := ⟨p,hpp⟩
    have hn : hU.fromSpec q ≠ genericPoint C := by
      intro he
      have h := hU.fromSpec.isOpenEmbedding.injective
        (he.trans (genericPoint_eq_of_isOpenImmersion hU.fromSpec).symm)
      rw [genericPoint_eq_bot_of_affine] at h
      exact hp (congrArg PrimeSpectrum.asIdeal h)
    have hclosed := isClosed_point_of_curve_coheight hdim hn
    apply (PrimeSpectrum.isClosed_singleton_iff_isMaximal q).mp
    have hpre := hclosed.preimage hU.fromSpec.continuous
    have heq : hU.fromSpec ⁻¹' ({hU.fromSpec q} : Set C) = {q} := by
      ext t
      exact hU.fromSpec.isOpenEmbedding.injective.eq_iff
    rwa [heq] at hpre
  exact { }
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne
open AlgebraicGeometry CategoryTheory
variable {X Y : Scheme} (sX : X ⟶ Spec (.of ℂ)) (sY : Y ⟶ Spec (.of ℂ))
  [SmoothOfRelativeDimension 1 sX] [SmoothOfRelativeDimension 1 sY]

noncomputable def smoothCurvePrimeMap (f : X ⟶ Y) [IsFinite f]
    (p : PrimeDivisor X) : PrimeDivisor Y :=
  ⟨f p.1, coheight_eq_of_smooth_closed sY 1 (f p.1)
    (finiteCurvePrimeImage sX f p).2⟩

noncomputable def smoothCurvePrimeFiberEquiv (f : X ⟶ Y) [IsFinite f]
    (q : PrimeDivisor Y) :
    {p : PrimeDivisor X // smoothCurvePrimeMap sX sY f p = q} ≃
    {x : X // f x = q.1} := by
  refine
    { toFun := fun p => ⟨p.1.1, congrArg Subtype.val p.2⟩
      invFun := fun x => ⟨⟨x.1, ?_⟩, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · exact coheight_eq_of_smooth_closed sX 1 x.1
      (isClosed_point_of_isClosed_image f x.1
        (x.2.symm ▸ curvePrime_isClosed sY q))
  · exact Subtype.ext x.2
  · intro p
    rfl
  · intro x
    rfl
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne
lemma divisorSection_dominant_pullback
    {X Y : Scheme} [IsIntegral X] [IsIntegral Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    [StalkwiseNormal X] [StalkwiseNormal Y]
    (f : X ⟶ Y) [IsDominant f] {D : WeilDivisor Y} {E : WeilDivisor X}
    (hE : IsCartierPullback f D E) {r : Y.functionField} (hr : IsDivisorSection D r) :
    IsDivisorSection E (dominantFunctionFieldMap f r) := by
  by_cases hr0 : r = 0
  · exact Or.inl (by simp [hr0])
  right
  intro p
  obtain ⟨U, hU, hpU, g, hg, hDg, hEg⟩ := hE p.1
  let : Nonempty U := ⟨⟨f p.1, hpU⟩⟩
  have hron : IsDivisorSectionOn D U r := by
    rcases hr with h | h
    · exact Or.inl h
    · exact Or.inr (fun q _ => h q)
  obtain ⟨a, ha⟩ := (cartier_local_section_iff hU hg hDg r).mp hron
  have hprod : 0 ≤ X.ord (dominantFunctionFieldMap f (r * g)) p.1 := by
    apply (ord_nonnegative_iff_regular p _ ((map_ne_zero _).mpr (mul_ne_zero hr0 hg))).mpr
    refine ⟨f.stalkMap p.1 (Y.presheaf.germ U (f p.1) hpU a), ?_⟩
    rw [← dominantFunctionFieldMap_algebraMap,
      Y.algebraMap_germ_eq_germToFunctionField, ha]
  rw [map_mul, X.ord_mul ((map_ne_zero _).mpr hr0) ((map_ne_zero _).mpr hg)] at hprod
  rwa [hEg p hpU]
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne

theorem dominant_sections_linear_injection
    (X Y : ComplexProjectiveVariety) [StalkwiseNormal X.scheme] [StalkwiseNormal Y.scheme]
    (f : X.scheme ⟶ Y.scheme) [IsDominant f]
    (hf : f ≫ Y.structureMap = X.structureMap)
    (D : WeilDivisor Y.scheme) (E : WeilDivisor X.scheme) (hE : IsCartierPullback f D E) :
    letI := schemeFieldAlgebra (.of ℂ) X.structureMap
    letI := schemeFieldAlgebra (.of ℂ) Y.structureMap
    ∃ F : divisorSectionsOver (.of ℂ) Y.structureMap D →ₗ[ℂ]
        divisorSectionsOver (.of ℂ) X.structureMap E,
      Function.Injective F ∧ ∀ r, (F r).1 = dominantFunctionFieldMap f r.1 := by
  dsimp only
  let := schemeFieldAlgebra (.of ℂ) X.structureMap
  let := schemeFieldAlgebra (.of ℂ) Y.structureMap
  let F : divisorSectionsOver (.of ℂ) Y.structureMap D →ₗ[ℂ]
      divisorSectionsOver (.of ℂ) X.structureMap E := {
    toFun := fun r => ⟨dominantFunctionFieldMap f r.1,
      divisorSection_dominant_pullback f hE r.2⟩
    map_add' := fun _ _ => Subtype.ext (map_add _ _ _)
    map_smul' := by
      intro a r
      apply Subtype.ext
      change dominantFunctionFieldMap f (schemeFieldScalar (.of ℂ) Y.structureMap a * r.1) =
        schemeFieldScalar (.of ℂ) X.structureMap a * dominantFunctionFieldMap f r.1
      rw [map_mul, dominantFunctionFieldMap_scalar _ _ _ _ hf] }
  refine ⟨F, ?_, fun _ => rfl⟩
  intro r s h
  apply Subtype.ext
  exact (dominantFunctionFieldMap f).injective (congrArg Subtype.val h)
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne
open WithZero

theorem dvr_ordFrac_map
    {R S K L : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [Field L] [Algebra S L] [IsFractionRing S L]
    (f : R →+* S) (F : K →+* L)
    (hcomm : ∀ r, F (algebraMap R K r) = algebraMap S L (f r))
    (a : K) (ha : a ≠ 0) (n : ℤ)
    (hn : Ring.ordFrac R a = WithZero.exp n) :
    Ring.ordFrac S (F a) = WithZero.exp
      ((Module.length S (S ⧸ (IsLocalRing.maximalIdeal R).map f)).toNat * n : ℤ) := by
  obtain ⟨π,hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have hi : Function.Injective f := by
    intro x y h
    apply IsFractionRing.injective R K
    apply F.injective
    rw [hcomm,hcomm,h]
  have hπS : f π ≠ 0 := by simpa only [map_zero] using hi.ne hπ.ne_zero
  obtain ⟨m,u,hm⟩ := IsDiscreteValuationRing.exists_units_eq_smul_zpow_of_irreducible hπ ha
  have hRm : Ring.ordFrac R a = WithZero.exp m := by
    rw [hm, Units.smul_def, Algebra.smul_def, map_mul, Ring.ordFrac_of_isUnit u.isUnit,
      one_mul, map_zpow₀, Ring.ordFrac_irreducible hπ]
    simp
  have hmn : m = n := by
    exact WithZero.exp_injective (hRm.symm.trans hn)
  subst m
  have hidx : Module.length S (S ⧸ (IsLocalRing.maximalIdeal R).map f) = Ring.ord S (f π) := by
    rw [hπ.maximalIdeal_eq,Ideal.map_span,Set.image_singleton]
    rfl
  rw [hidx,hm,Units.smul_def,Algebra.smul_def,map_mul,hcomm,map_zpow₀,hcomm,map_mul,
    Ring.ordFrac_of_isUnit (u.isUnit.map f),one_mul,map_zpow₀]
  have hval : Ring.ordFrac S (algebraMap S L (f π)) =
      WithZero.exp ((Ring.ord S (f π)).toNat : ℤ) := by
    rw [Ring.ordFrac_eq_ord _ hπS]
    exact Ring.ordMonoidWithZeroHom_eq_coe S (mem_nonZeroDivisors_of_ne_zero hπS)
      (ENat.natCast_toNat (Ring.ord_ne_top (mem_nonZeroDivisors_of_ne_zero hπS))).symm
  rw [hval]
  simp [mul_comm]
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne
open AlgebraicGeometry CategoryTheory
variable {X Y : Scheme} [IsIntegral X] [IsIntegral Y]
  [IsLocallyNoetherian X] [IsLocallyNoetherian Y]

noncomputable def curveRamificationLength (f : X ⟶ Y) (p : PrimeDivisor X) : ℕ :=
  (Module.length (X.presheaf.stalk p.1)
    (X.presheaf.stalk p.1 ⧸ (IsLocalRing.maximalIdeal (Y.presheaf.stalk (f p.1))).map
      (f.stalkMap p.1).hom)).toNat
variable [StalkwiseNormal X] [StalkwiseNormal Y]

theorem order_dominant_at_prime (f : X ⟶ Y) [IsDominant f]
    (p : PrimeDivisor X) (hp : Order.coheight (f p.1) = 1)
    (a : Y.functionField) (ha : a ≠ 0) :
    X.ord (dominantFunctionFieldMap f a) p.1 =
      (curveRamificationLength f p : ℤ) * Y.ord a (f p.1) := by
  let := dvr_at_prime_divisor p
  let := dvr_at_prime_divisor (⟨f p.1,hp⟩ : PrimeDivisor Y)
  apply (X.ord_eq_iff p.2 ((map_ne_zero (dominantFunctionFieldMap f)).mpr ha)).mpr
  exact dvr_ordFrac_map (f.stalkMap p.1).hom (dominantFunctionFieldMap f)
    (dominantFunctionFieldMap_algebraMap f p.1) a ha (Y.ord a (f p.1))
    ((Y.ord_eq_iff hp ha).mp rfl)

theorem cartierPullback_coefficient_ramification (f : X ⟶ Y) [IsDominant f]
    {D : WeilDivisor Y} {E : WeilDivisor X} (hE : IsCartierPullback f D E)
    (p : PrimeDivisor X) (hp : Order.coheight (f p.1) = 1) :
    E p = (curveRamificationLength f p : ℤ) * D ⟨f p.1,hp⟩ := by
  obtain ⟨U,hU,hpU,a,ha,hDa,hEa⟩ := hE p.1
  rw [hEa p hpU,order_dominant_at_prime f p hp a ha,← hDa ⟨f p.1,hp⟩ hpU]
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne
open AlgebraicGeometry CategoryTheory

theorem curveRamificationLength_eq_affine
    {X Y : Scheme} [IsIntegral X] [IsIntegral Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (f : X ⟶ Y) (V : Y.Opens) (hV : IsAffineOpen V)
    (hU : IsAffineOpen (f ⁻¹ᵁ V)) (p : PrimeDivisor X) (hp : f p.1 ∈ V) :
    let := (f.app V).hom.toAlgebra
    curveRamificationLength f p = (hU.primeIdealOf ⟨p.1,hp⟩).asIdeal.ramificationIdx Γ(Y,V) := by
  dsimp only
  let := (f.app V).hom.toAlgebra
  let q := hU.primeIdealOf ⟨p.1,hp⟩
  let r := hV.primeIdealOf ⟨f p.1,hp⟩
  let := X.presheaf.algebra_section_stalk (⟨p.1,hp⟩ : (f ⁻¹ᵁ V))
  let := hU.isLocalization_stalk (⟨p.1,hp⟩ : (f ⁻¹ᵁ V))
  let := Y.presheaf.algebra_section_stalk (⟨f p.1,hp⟩ : V)
  let := hV.isLocalization_stalk (⟨f p.1,hp⟩ : V)
  have he : q.asIdeal.under Γ(Y,V) = r.asIdeal := by
    have hh := IsAffineOpen.comap_primeIdealOf_appLE V hV (f ⁻¹ᵁ V) hU le_rfl hp
    rw [Scheme.Hom.appLE_eq_app] at hh
    exact congrArg PrimeSpectrum.asIdeal hh
  let : q.asIdeal.LiesOver r.asIdeal := ⟨he.symm⟩
  let e := IsLocalization.algEquiv q.asIdeal.primeCompl
    (Localization.AtPrime q.asIdeal) (X.presheaf.stalk p.1)
  have hma : (IsLocalRing.maximalIdeal (Y.presheaf.stalk (f p.1))).map
      (f.stalkMap p.1).hom = r.asIdeal.map
        ((X.presheaf.germ (f ⁻¹ᵁ V) p.1 hp).hom.comp (f.app V).hom) := by
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal r.asIdeal
      (Y.presheaf.stalk (f p.1)),Ideal.map_map]
    congr 1
    exact congrArg CommRingCat.Hom.hom (f.germ_stalkMap V p.1 hp)
  have hemap : (r.asIdeal.map (algebraMap Γ(Y,V) (Localization.AtPrime q.asIdeal))).map
      e.toRingEquiv.toRingHom = r.asIdeal.map
        ((X.presheaf.germ (f ⁻¹ᵁ V) p.1 hp).hom.comp (f.app V).hom) := by
    rw [Ideal.map_map]
    congr 1
    ext a
    exact e.commutes ((f.app V) a)
  change curveRamificationLength f p = q.asIdeal.ramificationIdx Γ(Y,V)
  rw [curveRamificationLength, hma,Ideal.ramificationIdx_eq r.asIdeal]
  apply congrArg ENat.toNat
  rw [← hemap,Module.length_quotient,Module.length_quotient]
  simpa only [Ideal.comap_symm, RingEquiv.toRingHom_eq_coe, Ideal.map_coe, q] using
    Ideal.coheight_comap_of_surjective e.toRingEquiv.symm e.toRingEquiv.symm.surjective
      (r.asIdeal.map (algebraMap Γ(Y,V) (Localization.AtPrime q.asIdeal)))
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne
open AlgebraicGeometry CategoryTheory
variable {X Y : Scheme} [IsIntegral X] [IsIntegral Y]

noncomputable def curveFieldDegree (f : X ⟶ Y) [IsDominant f] : ℕ :=
  letI := (dominantFunctionFieldMap f).toAlgebra
  Module.finrank Y.functionField X.functionField

theorem curveFieldDegree_eq_affine (f : X ⟶ Y) [IsDominant f]
    (V : Y.Opens) (hV : IsAffineOpen V) (hU : IsAffineOpen (f ⁻¹ᵁ V))
    [Nonempty (f ⁻¹ᵁ V)] [Nonempty V] :
    letI := (f.app V).hom.toAlgebra
    curveFieldDegree f = Module.finrank Γ(Y,V) Γ(X,f ⁻¹ᵁ V) := by
  let := (f.app V).hom.toAlgebra
  let := (dominantFunctionFieldMap f).toAlgebra
  let := functionField_isFractionRing_of_isAffineOpen X (f ⁻¹ᵁ V) hU
  let := functionField_isFractionRing_of_isAffineOpen Y V hV
  let : Algebra Γ(Y,V) X.functionField :=
    ((X.germToFunctionField (f ⁻¹ᵁ V)).hom.comp (f.app V).hom).toAlgebra
  have : IsScalarTower Γ(Y,V) Γ(X,f ⁻¹ᵁ V) X.functionField :=
    IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower Γ(Y,V) Y.functionField X.functionField := by
    apply IsScalarTower.of_algebraMap_eq
    intro a
    obtain ⟨x,hx⟩ := ‹Nonempty (f ⁻¹ᵁ V)›
    change X.germToFunctionField (f ⁻¹ᵁ V) (f.app V a) =
      dominantFunctionFieldMap f (Y.germToFunctionField V a)
    rw [← Y.algebraMap_germ_eq_germToFunctionField (x := f x) hx,
      dominantFunctionFieldMap_algebraMap]
    rw [f.germ_stalkMap_apply V x hx a]
    exact (X.algebraMap_germ_eq_germToFunctionField hx _).symm
  exact IsFractionRing.finrank_eq Γ(Y,V) Y.functionField
    Γ(X,f ⁻¹ᵁ V) X.functionField
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne
open AlgebraicGeometry CategoryTheory

theorem affineResidue_isAlgClosed {Y : Scheme}
    (sY : Y ⟶ Spec (.of ℂ)) [LocallyOfFiniteType sY]
    (V : Y.Opens) (hV : IsAffineOpen V) (y : V)
    (hy : IsClosed ({y.1} : Set Y)) :
    IsAlgClosed (hV.primeIdealOf y).asIdeal.ResidueField := by
  let q := hV.primeIdealOf y
  have hq : IsClosed ({q} : Set (Spec Γ(Y,V))) :=
    (PrimeSpectrum.isClosed_singleton_iff_isMaximal q).mpr
      (hV.primeIdealOf_isMaximal_of_isClosed y hy)
  let e := (Scheme.Spec.residueFieldIso Γ(Y,V) q).symm ≪≫
    residueFieldIsoBase (hV.fromSpec ≫ sY) q hq
  exact IsAlgClosed.of_ringEquiv ℂ _ e.symm.commRingCatIsoToRingEquiv
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne
open AlgebraicGeometry CategoryTheory
variable {X Y : Scheme} [IsIntegral X] [IsIntegral Y]
  [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [StalkwiseNormal Y]
  (sX : X ⟶ Spec (.of ℂ)) (sY : Y ⟶ Spec (.of ℂ))
  [SmoothOfRelativeDimension 1 sX] [SmoothOfRelativeDimension 1 sY]

theorem smoothCurve_fiber_ramification_sum (f : X ⟶ Y) [IsFinite f] [IsDominant f]
    (q : PrimeDivisor Y) :
    (∑ᶠ p : {p : PrimeDivisor X // smoothCurvePrimeMap sX sY f p = q},
      curveRamificationLength f p.1) = curveFieldDegree f := by
  classical
  let : Smooth sY := SmoothOfRelativeDimension.smooth (n := 1) (f := sY)
  obtain ⟨V,hV,hqV,_⟩ := exists_isAffineOpen_mem_and_subset
    (show q.1 ∈ (⊤ : Y.Opens) from trivial)
  have hU : IsAffineOpen (f ⁻¹ᵁ V) := hV.preimage f
  let : Nonempty V := ⟨⟨q.1,hqV⟩⟩
  obtain ⟨x,hx⟩ := f.surjective q.1
  let : Nonempty (f ⁻¹ᵁ V) := ⟨⟨x, by change f x ∈ V; rw [hx]; exact hqV⟩⟩
  let := (f.app V).hom.toAlgebra
  let : Module.Finite Γ(Y,V) Γ(X,f ⁻¹ᵁ V) := f.finite_app V hV
  let : IsSchemeTheoreticallyDominant f := .of_isDominant f
  let : Module.IsTorsionFree Γ(Y,V) Γ(X,f ⁻¹ᵁ V) :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr (f.app_injective V)
  let := normalCurveAffine_isDedekind (coheight_le_of_smooth_dimension sY 1) hV
  let r := hV.primeIdealOf ⟨q.1,hqV⟩
  let : IsAlgClosed r.asIdeal.ResidueField :=
    affineResidue_isAlgClosed sY V hV ⟨q.1,hqV⟩ (curvePrime_isClosed sY q)
  let e := (smoothCurvePrimeFiberEquiv sX sY f q).trans
    (affineFiberEquiv f V hV hU ⟨q.1,hqV⟩)
  let : Fintype {x : X // f x = q.1} := (f.finite_preimage_singleton q.1).fintype
  let : Fintype {p : PrimeDivisor X // smoothCurvePrimeMap sX sY f p = q} :=
    Fintype.ofEquiv _ (smoothCurvePrimeFiberEquiv sX sY f q).symm
  let : Fintype (r.asIdeal.primesOver Γ(X,f ⁻¹ᵁ V)) := Fintype.ofEquiv _ e
  rw [finsum_eq_sum_of_fintype]
  calc
    ∑ p : {p : PrimeDivisor X // smoothCurvePrimeMap sX sY f p = q},
        curveRamificationLength f p.1 =
        ∑ t : r.asIdeal.primesOver Γ(X,f ⁻¹ᵁ V), t.1.ramificationIdx Γ(Y,V) := by
      rw [← e.sum_comp]
      apply Finset.sum_congr rfl
      intro p _
      have hp : f p.1.1 ∈ V := by
        rw [show f p.1.1 = q.1 from congrArg Subtype.val p.2]
        exact hqV
      exact curveRamificationLength_eq_affine f V hV hU p.1 hp
    _ = Module.finrank Γ(Y,V) Γ(X,f ⁻¹ᵁ V) := by
      have hh := Ideal.sum_ramification_inertia_eq_finrank r.asIdeal Γ(X,f ⁻¹ᵁ V)
      simpa only [NumericalDimensionOneCurveAux.inertiaDegree_one_of_algClosed_residue r.asIdeal,mul_one] using hh
    _ = curveFieldDegree f := (curveFieldDegree_eq_affine f V hV hU).symm
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne
open AlgebraicGeometry CategoryTheory
lemma complexWeilDegree_eq_finsum {X : Scheme} (D : WeilDivisor X) :
    complexWeilDegree D = ∑ᶠ p, D p := by
  symm
  exact finsum_eq_sum_of_support_subset D (by
    intro p hp
    exact Finsupp.mem_support_iff.mpr hp)
variable {X Y : Scheme} [IsIntegral X] [IsIntegral Y]
  [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
  [StalkwiseNormal X] [StalkwiseNormal Y]
  (sX : X ⟶ Spec (.of ℂ)) (sY : Y ⟶ Spec (.of ℂ))
  [SmoothOfRelativeDimension 1 sX] [SmoothOfRelativeDimension 1 sY]
include sX sY in

theorem smoothCurve_degree_cartierPullback (f : X ⟶ Y) [IsFinite f] [IsDominant f]
    {D : WeilDivisor Y} {E : WeilDivisor X} (hE : IsCartierPullback f D E) :
    complexWeilDegree E = (curveFieldDegree f : ℤ) * complexWeilDegree D := by
  classical
  have hfiber (q : PrimeDivisor Y) :
      (∑ᶠ p : {p : PrimeDivisor X // smoothCurvePrimeMap sX sY f p = q},
        E p.1) = (curveFieldDegree f : ℤ) * D q := by
    let : Fintype {x : X // f x = q.1} := (f.finite_preimage_singleton q.1).fintype
    let : Fintype {p : PrimeDivisor X // smoothCurvePrimeMap sX sY f p = q} :=
      Fintype.ofEquiv _ (smoothCurvePrimeFiberEquiv sX sY f q).symm
    have hpE (p : {p : PrimeDivisor X // smoothCurvePrimeMap sX sY f p = q}) :
        E p.1 = (curveRamificationLength f p.1 : ℤ) * D q := by
      rw [cartierPullback_coefficient_ramification f hE p.1
        (smoothCurvePrimeMap sX sY f p.1).2]
      change (curveRamificationLength f p.1 : ℤ) * D (smoothCurvePrimeMap sX sY f p.1) = _
      rw [p.2]
    simp_rw [finsum_eq_sum_of_fintype,hpE]
    rw [← Finset.sum_mul,← Nat.cast_sum]
    congr 1
    exact_mod_cast (by simpa only [finsum_eq_sum_of_fintype] using
      smoothCurve_fiber_ramification_sum sX sY f q)
  rw [complexWeilDegree_eq_finsum E,complexWeilDegree_eq_finsum D]
  rw [← finsum_fiberwise (smoothCurvePrimeMap sX sY f) E E.hasFiniteSupport]
  simp_rw [hfiber]
  exact (mul_finsum D (curveFieldDegree f : ℤ)).symm
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne
open AlgebraicGeometry CategoryTheory
variable {X C Y : Scheme} [IsIntegral X] [IsIntegral C] [IsIntegral Y]
  [IsLocallyNoetherian X] [IsLocallyNoetherian C] [IsLocallyNoetherian Y]
  [StalkwiseNormal C]

theorem IsPulledCartierRepresentative.comp_dominant
    (f : X ⟶ C) [IsDominant f] (i : C ⟶ Y)
    {D : WeilDivisor Y} {E : WeilDivisor C} {F : WeilDivisor X}
    (hE : IsPulledCartierRepresentative i D E) (hF : IsCartierPullback f E F) :
    IsPulledCartierRepresentative (f ≫ i) D F := by
  obtain ⟨U,hU,hηU,g,hg,hDg,hE⟩ := hE
  have hsp : f (genericPoint X) ⤳ genericPoint C :=
    (Inseparable.of_eq (dominant_genericPoint f)).specializes
  refine ⟨U,hU,?_,g,hg,hDg,?_⟩
  · simpa only [Scheme.Hom.comp_apply,dominant_genericPoint f] using hηU
  intro x
  obtain ⟨V,hV,hxV,h,hh,hDh,a,ha,hea,hEa⟩ := hE (f x)
  let a' := Y.presheaf.stalkSpecializes (i.base.hom.map_specializes hsp) a
  have hefield : dominantFunctionFieldMap f (i.stalkMap (genericPoint C) a) =
      (f ≫ i).stalkMap (genericPoint X) a' := by
    change f.stalkMap (genericPoint X)
      (C.presheaf.stalkSpecializes hsp (i.stalkMap (genericPoint C) a)) = _
    rw [← i.stalkSpecializes_stalkMap_apply (f (genericPoint X)) (genericPoint C) hsp a]
    rw [Scheme.Hom.stalkMap_comp]
    rfl
  refine ⟨V,hV,hxV,h,hh,hDh,a',ha.map _,?_,?_⟩
  · exact (algebraMap_stalkSpecializes (i.base.hom.map_specializes hsp) a).trans hea
  intro p hpV
  obtain ⟨W,hW,hpW,hWV⟩ := exists_isAffineOpen_mem_and_subset
    (show f p.1 ∈ i ⁻¹ᵁ V from hpV)
  obtain ⟨A,_hA,hpA,k,hk,hEk,hFk⟩ := hF p.1
  have hb : (i.stalkMap (genericPoint C) a : C.functionField) ≠ 0 :=
    (ha.map (i.stalkMap (genericPoint C)).hom).ne_zero
  have hEb (q : PrimeDivisor C) (hq : q.1 ∈ W) :
      E q = C.ord (i.stalkMap (genericPoint C) a) q.1 := hEa q (hWV hq)
  exact (hFk p hpA).trans ((pulled_equation_order_eq f hk hb hEk hEb p hpA hpW).trans
    (congrArg (fun z : X.functionField => X.ord z p.1) hefield))
end NumericalDimensionOne

end OAI
