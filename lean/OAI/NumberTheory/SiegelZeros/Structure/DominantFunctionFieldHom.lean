import Mathlib
import PrimeNumberTheoremAnd.SiegelZeros.HadamardSupport

namespace OAI

namespace SiegelZeros


noncomputable section

local instance WeightedTorusJets.Geometry.polynomialGradedAlgebra
    (R σ : Type*) [CommSemiring R] :
    GradedAlgebra (MvPolynomial.homogeneousSubmodule σ R) := MvPolynomial.gradedAlgebra

open Module

open CategoryTheory AlgebraicGeometry

namespace WeightedTorusJets

universe u

local instance scheme_top_nonempty (Z : Scheme) [Nonempty Z] : Nonempty (⊤ : Z.Opens) :=
  ⟨⟨Classical.choice inferInstance, Set.mem_univ _⟩⟩

theorem existsUnique_globalSection_scalar (K : Type u) [Field K] [IsAlgClosed K]
    {X : Scheme.{u}} [IsIntegral X] (f : X ⟶ Spec (CommRingCat.of K))
    [UniversallyClosed f] (s : Γ(X, ⊤)) :
    ∃! c : K, ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ f.appTop).hom c = s := by
  have hIntegral : ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ f.appTop).hom.IsIntegral := by
    apply RingHom.isIntegral_respectsIso.2
      (e := (Scheme.ΓSpecIso (CommRingCat.of K)).symm.commRingCatIsoToRingEquiv)
    exact isIntegral_appTop_of_universallyClosed f
  exact (IsAlgClosed.ringHom_bijective_of_isIntegral _ hIntegral).existsUnique s

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]

theorem genericPoint_eq_of_isDominant (f : X ⟶ Y) [IsDominant f] :
    f (genericPoint X) = genericPoint Y := by
  have h : IsGenericPoint (f (genericPoint X)) Set.univ := by
    simpa only [Set.image_univ, f.denseRange.closure_range] using
      (genericPoint_spec X).image f.continuous
  exact h.eq (genericPoint_spec Y)

noncomputable def dominantFunctionFieldHom (f : X ⟶ Y) [IsDominant f] :
    Y.functionField ⟶ X.functionField :=
  (Y.presheaf.stalkCongr (.of_eq (genericPoint_eq_of_isDominant f).symm)).hom ≫
    f.stalkMap (genericPoint X)

theorem germToFunctionField_dominantFunctionFieldHom (f : X ⟶ Y) [IsDominant f] :
    Y.germToFunctionField ⊤ ≫ dominantFunctionFieldHom f =
      f.appTop ≫ X.germToFunctionField ⊤ := by
  calc
    _ = Y.presheaf.germ ⊤ (f (genericPoint X)) (Set.mem_univ _) ≫
        f.stalkMap (genericPoint X) := by
      rw [dominantFunctionFieldHom, ← Category.assoc]
      congr 1
      exact Y.presheaf.germ_stalkSpecializes _
        (specializes_of_eq (genericPoint_eq_of_isDominant f))
    _ = _ := f.germ_stalkMap ⊤ (genericPoint X) (Set.mem_univ _)

theorem isDominant_fromSpecStalk_genericPoint (Z : Scheme.{u}) [IsIntegral Z] :
    IsDominant (Z.fromSpecStalk (genericPoint Z)) := by
  constructor
  rw [denseRange_iff_closure_range]
  apply Set.eq_univ_of_univ_subset
  rw [← genericPoint_closure Z]
  apply closure_mono
  exact Set.singleton_subset_iff.mpr
    ⟨IsLocalRing.closedPoint Z.functionField, Z.fromSpecStalk_closedPoint⟩

end WeightedTorusJets

open CategoryTheory AlgebraicGeometry

namespace WeightedTorusJets

universe u

theorem finite_integralClosure_of_normal_subring
    (R K A L : Type*) [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [IsIntegrallyClosed R] [Field K] [CommRing A] [Field L]
    [Algebra R K] [IsFractionRing R K] [Algebra R A] [Algebra A L]
    [Algebra R L] [IsScalarTower R A L] [Algebra K L] [IsScalarTower R K L]
    [Algebra.IsIntegral R A] [FiniteDimensional K L] [Algebra.IsSeparable K L] :
    Module.Finite A (integralClosure A L) := by
  have : IsIntegralClosure (integralClosure A L) R L := {
    algebraMap_injective := Subtype.val_injective
    isIntegral_iff := by
      intro x
      constructor
      · intro hx
        exact ⟨⟨x, hx.tower_top⟩, rfl⟩
      · rintro ⟨x, rfl⟩
        exact isIntegral_trans (R := R) (A := A) _ x.property }
  have : Module.Finite R (integralClosure A L) :=
    IsIntegralClosure.finite R K L (integralClosure A L)
  exact Module.Finite.of_restrictScalars_finite R A (integralClosure A L)

theorem finite_integralClosure_of_finiteType_charZero (k A : Type*)
    [Field k] [CharZero k] [CommRing A] [IsDomain A] [Algebra k A]
    [Algebra.FiniteType k A] : Module.Finite A (integralClosure A (FractionRing A)) := by
  obtain ⟨n, g, hg, hfin⟩ := exists_finite_inj_algHom_of_fg k A
  let P := MvPolynomial (Fin n) k
  let : Algebra P A := g.toRingHom.toAlgebra
  have : Module.Finite P A := hfin
  have : FaithfulSMul P A := (faithfulSMul_iff_algebraMap_injective P A).mpr hg
  let := FractionRing.liftAlgebra P (FractionRing A)
  have : Module.Finite (FractionRing P) (FractionRing A) := by
    apply Module.rank_lt_aleph0_iff.mp
    rw [Algebra.IsAlgebraic.rank_fractionRing]
    exact Module.rank_lt_aleph0 P A
  exact finite_integralClosure_of_normal_subring P (FractionRing P) A (FractionRing A)

theorem isFractionRing_genericPoint_preimage_sections
    (Y : Scheme.{u}) [IsIntegral Y] (U : Y.Opens) (hU : IsAffineOpen U) [Nonempty U] :
    let n := Y.fromSpecStalk (genericPoint Y)
    let := (n.app U).hom.toAlgebra
    IsFractionRing Γ(Y, U) Γ(Spec Y.functionField, n ⁻¹ᵁ U) := by
  let n := Y.fromSpecStalk (genericPoint Y)
  let := (n.app U).hom.toAlgebra
  have hm : genericPoint Y ∈ U :=
    ((genericPoint_spec Y).mem_open_set_iff U.isOpen).mpr
      (by simpa using (inferInstance : Nonempty U))
  have hpre : n ⁻¹ᵁ U = ⊤ := by
    apply top_unique
    intro x _
    change n x ∈ U
    have hx : x = IsLocalRing.closedPoint Y.functionField :=
      Subsingleton.elim (α := PrimeSpectrum Y.functionField) _ _
    rw [hx, Scheme.fromSpecStalk_closedPoint]
    exact hm
  let e : Y.functionField ≅ Γ(Spec Y.functionField, n ⁻¹ᵁ U) :=
    (Scheme.ΓSpecIso Y.functionField).symm ≪≫
      (Spec Y.functionField).presheaf.mapIso (eqToIso hpre).op
  let eA : Y.functionField ≃ₐ[Γ(Y, U)] Γ(Spec Y.functionField, n ⁻¹ᵁ U) :=
    { e.commRingCatIsoToRingEquiv with
      commutes' := fun a ↦ by
        change e.hom (Y.germToFunctionField U a) = n.app U a
        rw [Scheme.fromSpecStalk_app hm]
        rfl }
  have := functionField_isFractionRing_of_isAffineOpen Y U hU
  exact IsFractionRing.of_algEquiv eA

theorem isFinite_genericNormalization (k : Type u) [Field k] [CharZero k]
    (Y : Scheme.{u}) [IsIntegral Y]
    (g : Y ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType g] :
    IsFinite (Y.fromSpecStalk (genericPoint Y)).fromNormalization := by
  let n := Y.fromSpecStalk (genericPoint Y)
  constructor
  intro U hU
  let A := Γ(Y, U)
  let L := Γ(Spec Y.functionField, n ⁻¹ᵁ U)
  let : Algebra A L := (n.app U).hom.toAlgebra
  let F := (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ g.appLE ⊤ U le_top
  let : Algebra k A := F.hom.toAlgebra
  have : Algebra.FiniteType k A := by
    change F.hom.FiniteType
    apply RingHom.finiteType_respectsIso.2
      (e := (Scheme.ΓSpecIso (CommRingCat.of k)).symm.commRingCatIsoToRingEquiv)
    exact g.finiteType_appLE (isAffineOpen_top _) hU le_top
  have hfin : Module.Finite A (integralClosure A L) := by
    by_cases hne : Nonempty U
    · have : IsFractionRing A L := isFractionRing_genericPoint_preimage_sections Y U hU
      have := finite_integralClosure_of_finiteType_charZero k A
      exact Module.Finite.equiv (FractionRing.algEquiv A L).mapIntegralClosure.toLinearEquiv
    · have hUbot : U = ⊥ := by
        apply bot_unique
        intro x hx
        exact False.elim (hne ⟨⟨x, hx⟩⟩)
      have hprebot : n ⁻¹ᵁ U = ⊥ := by rw [hUbot]; rfl
      have : Subsingleton L := by dsimp only [L]; rw [hprebot]; infer_instance
      infer_instance
  rw [n.fromNormalization_app hU, CommRingCat.hom_comp]
  exact (RingHom.Finite.of_surjective _
    (n.normalizationObjIso hU).symm.commRingCatIsoToRingEquiv.surjective).comp
      (RingHom.finite_algebraMap.mpr hfin)

end WeightedTorusJets

open IsLocalRing

theorem isDiscreteValuationRing_of_fraction_pole
    {R K : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsLocalRing R]
    [IsIntegrallyClosed R] [Field K] [Algebra R K] [IsFractionRing R K]
    (y : K) (hy : y ∉ Set.range (algebraMap R K))
    (hmul : ∀ r ∈ maximalIdeal R, y * algebraMap R K r ∈ Set.range (algebraMap R K)) :
    IsDiscreteValuationRing R := by
  classical
  have hnf : ¬ IsField R := fun h ↦ hy ((IsFractionRing.surjective_iff_isField.mpr h) y)
  have hmne : maximalIdeal R ≠ ⊥ := isField_iff_maximalIdeal_eq.not.mp hnf
  let M : Submodule R K := Submodule.map (Algebra.linearMap R K) (maximalIdeal R)
  have hM : M ≠ ⊥ := by
    obtain ⟨a, ha, hane⟩ := (Submodule.ne_bot_iff _).mp hmne
    rw [Submodule.ne_bot_iff]
    exact ⟨algebraMap R K a, ⟨a, ha, rfl⟩,
      (IsFractionRing.to_map_eq_zero_iff (K := K)).not.mpr hane⟩
  have hstable : ¬ ∀ z ∈ M, y * z ∈ M := by
    intro h
    have hint : IsIntegral R y := isIntegral_of_smul_mem_submodule M hM
      (Submodule.FG.map _ (IsNoetherian.noetherian _)) y h
    exact hy (IsIntegrallyClosed.algebraMap_eq_of_integral hint)
  push Not at hstable
  obtain ⟨z, hz, hyz⟩ := hstable
  obtain ⟨r, hr, rfl⟩ := hz
  obtain ⟨t, ht⟩ := hmul r hr
  have htunit : IsUnit t := by
    by_contra htunit
    apply hyz
    exact ⟨t, htunit, ht⟩
  obtain ⟨v, hv⟩ := htunit.exists_right_inv
  let u : R := r * v
  have hu : u ∈ maximalIdeal R := Ideal.mul_mem_right _ _ hr
  have hyu : y * algebraMap R K u = 1 := by
    rw [show u = r * v from rfl, map_mul, ← mul_assoc, ← ht, ← map_mul, hv, map_one]
  have hp : (maximalIdeal R).IsPrincipal := by
    refine ⟨⟨u, le_antisymm ?_ ?_⟩⟩
    · intro a ha
      obtain ⟨b, hb⟩ := hmul a ha
      apply Ideal.mem_span_singleton'.mpr
      refine ⟨b, ?_⟩
      apply IsFractionRing.injective R K
      rw [map_mul, hb, mul_right_comm, hyu, one_mul]
    · exact Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hu)
  exact ((IsDiscreteValuationRing.TFAE R hnf).out 5 1).mp hp

theorem height_eq_one_of_prime_denominator
    {R K : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (p : Ideal R) [p.IsPrime] (y : K)
    (hp : ∀ r : R, r ∈ p ↔ y * algebraMap R K r ∈ Set.range (algebraMap R K)) :
    p.height = 1 := by
  classical
  let S := Localization.subalgebra.ofField K p.primeCompl p.primeCompl_le_nonZeroDivisors
  have : IsLocalRing S := IsLocalization.AtPrime.isLocalRing S p
  have : IsNoetherianRing S :=
    IsLocalization.isNoetherianRing p.primeCompl S inferInstance
  have : IsIntegrallyClosed S :=
    isIntegrallyClosed_of_isLocalization S p.primeCompl p.primeCompl_le_nonZeroDivisors
  have hmap (a : R) (s : p.primeCompl) :
      algebraMap S K (IsLocalization.mk' S a s) =
        algebraMap R K a / algebraMap R K s := by
    have hs : algebraMap R K s ≠ 0 := (IsFractionRing.to_map_eq_zero_iff (K := K)).not.mpr
      (fun hzero ↦ s.2 (hzero ▸ p.zero_mem))
    apply (eq_div_iff hs).mpr
    have h := congrArg (algebraMap S K) (IsLocalization.mk'_spec S a s)
    simpa only [map_mul, ← IsScalarTower.algebraMap_apply R S K] using h
  have hnot : y ∉ Set.range (algebraMap S K) := by
    rintro ⟨z, hz⟩
    obtain ⟨a, s, rfl⟩ := IsLocalization.exists_mk'_eq p.primeCompl z
    apply s.2
    apply (hp s).mpr
    refine ⟨a, ?_⟩
    rw [← hz, hmap]
    have hs : algebraMap R K s ≠ 0 := (IsFractionRing.to_map_eq_zero_iff (K := K)).not.mpr
      (fun hzero ↦ s.2 (hzero ▸ p.zero_mem))
    exact (div_mul_cancel₀ _ hs).symm
  have hmul : ∀ r ∈ maximalIdeal S,
      y * algebraMap S K r ∈ Set.range (algebraMap S K) := by
    intro z hz
    obtain ⟨a, s, rfl⟩ := IsLocalization.exists_mk'_eq p.primeCompl z
    have ha : a ∈ p := (IsLocalization.AtPrime.mk'_mem_maximal_iff S p a s).mp hz
    obtain ⟨b, hb⟩ := (hp a).mp ha
    refine ⟨IsLocalization.mk' S b s, ?_⟩
    rw [hmap, hmap, hb, mul_div_assoc]
  have : IsDiscreteValuationRing S := isDiscreteValuationRing_of_fraction_pole y hnot hmul
  have hdim := IsDiscreteValuationRing.ringKrullDim_eq_one S
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height p S] at hdim
  exact_mod_cast hdim

theorem mem_algebraMap_of_mem_height_one_localizations
    {R K : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R]
    [Field K] [Algebra R K] [IsFractionRing R K] {x : K}
    (hlocal : ∀ p : PrimeSpectrum R, p.asIdeal.height = 1 →
      x ∈ Localization.subalgebra.ofField K p.asIdeal.primeCompl
        p.asIdeal.primeCompl_le_nonZeroDivisors) :
    x ∈ Set.range (algebraMap R K) := by
  classical
  by_contra hx
  let B : Submodule R K := (Algebra.linearMap R K).range
  let D : K → Ideal R := fun y ↦ B.colon {y}
  have hD (y : K) (r : R) :
      r ∈ D y ↔ y * algebraMap R K r ∈ Set.range (algebraMap R K) := by
    simp only [D, Submodule.mem_colon_singleton, B, LinearMap.mem_range,
      Algebra.linearMap_apply, Algebra.smul_def, mul_comm, Set.mem_range]
  have hDx : D x ≠ ⊤ := by
    intro heq
    have hmem : (1 : R) ∈ D x := heq ▸ (show (1 : R) ∈ (⊤ : Ideal R) by simp)
    exact hx (by simpa using (hD x 1).mp hmem)
  obtain ⟨p, ⟨hle, hpne, y, rfl⟩, hmax⟩ :=
    set_has_maximal_iff_noetherian.mpr (inferInstance : IsNoetherianRing R)
      {p : Ideal R | D x ≤ p ∧ p ≠ ⊤ ∧ ∃ y : K, p = D y}
      ⟨D x, le_rfl, hDx, x, rfl⟩
  have hprime : (D y).IsPrime := by
    refine ⟨hpne, ?_⟩
    intro a b hab
    by_cases ha : a ∈ D y
    · exact Or.inl ha
    apply Or.inr
    have H : D y ≤ D (algebraMap R K a * y) := by
      intro c hc
      obtain ⟨d, hd⟩ := (hD y c).mp hc
      apply (hD _ c).mpr
      refine ⟨a * d, ?_⟩
      rw [map_mul, hd, mul_assoc]
    have Hne : D (algebraMap R K a * y) ≠ ⊤ := by
      intro heq
      apply ha
      have hmem : (1 : R) ∈ D (algebraMap R K a * y) :=
        heq ▸ (show (1 : R) ∈ (⊤ : Ideal R) by simp)
      simpa [hD, mul_comm] using hmem
    have Heq : D y = D (algebraMap R K a * y) :=
      H.eq_of_not_lt (hmax _ ⟨hle.trans H, Hne, _, rfl⟩)
    rw [Heq, hD]
    simpa [map_mul, mul_left_comm, mul_assoc] using (hD y (a * b)).mp hab
  have : (D y).IsPrime := hprime
  have hheight : (D y).height = 1 := height_eq_one_of_prime_denominator (D y) y (hD y)
  obtain ⟨a, s, hs, hxs⟩ := hlocal ⟨D y, hprime⟩ hheight
  apply hs
  apply hle
  apply (hD x s).mpr
  refine ⟨a, ?_⟩
  rw [hxs, mul_assoc, inv_mul_cancel₀, mul_one]
  exact (IsFractionRing.to_map_eq_zero_iff (K := K)).not.mpr
    (fun hzero ↦ hs (hzero ▸ (D y).zero_mem))

open AlgebraicGeometry TopologicalSpace CategoryTheory

namespace AlgebraicGeometry.Scheme

variable {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X]

theorem isDiscreteValuationRing_stalk_of_isIntegrallyClosed {x : X}
    [IsIntegrallyClosed (X.presheaf.stalk x)] (hx : Order.coheight x = 1) :
    IsDiscreteValuationRing (X.presheaf.stalk x) := by
  have : Ring.KrullDimLE 1 (X.presheaf.stalk x) := krullDimLE_of_coheight_le hx.le
  have hnf : ¬ IsField (X.presheaf.stalk x) := by
    intro h
    have hzero := ringKrullDim_eq_zero_of_isField h
    rw [ringKrullDim_stalk_eq_coheight, hx] at hzero
    exact one_ne_zero hzero
  apply ((IsDiscreteValuationRing.TFAE (X.presheaf.stalk x) hnf).out 4 1).mp
  refine ⟨inferInstance, IsLocalRing.maximalIdeal (X.presheaf.stalk x), ?_, ?_⟩
  · exact ⟨IsLocalRing.isField_iff_maximalIdeal_eq.not.mp hnf, inferInstance⟩
  · intro p hp
    exact IsLocalRing.eq_maximalIdeal (hp.2.isMaximal_of_ne_bot hp.1)

theorem exists_stalk_unit_of_ord_eq_zero {x : X}
    [IsDiscreteValuationRing (X.presheaf.stalk x)]
    (hx : Order.coheight x = 1) {f : X.functionField} (hf : f ≠ 0)
    (hord : X.ord f x = 0) :
    ∃ u : X.presheaf.stalk x, IsUnit u ∧
      algebraMap (X.presheaf.stalk x) X.functionField u = f := by
  have h : Ring.ordFrac (X.presheaf.stalk x) f = 1 := by
    simpa [Scheme.ordHom] using (X.ord_eq_iff hx hf).mp hord
  change f ∈ (IsUnit.submonoid (X.presheaf.stalk x)).map
    (algebraMap (X.presheaf.stalk x) X.functionField)
  rw [← Ring.mker_ordFrac_eq_isUnitSubmonoid]
  exact h

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry

variable {X : Scheme} [IsIntegral X]

theorem IsAffineOpen.isIntegrallyClosed_of_stalks {U : X.Opens}
    (hU : IsAffineOpen U) [Nonempty U]
    [∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)] : IsIntegrallyClosed Γ(X, U) := by
  let (p : PrimeSpectrum Γ(X, U)) : Algebra Γ(X, U) (X.presheaf.stalk (hU.fromSpec p)) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨hU.fromSpec p, (hU.isoSpec.inv p).2⟩
  have (p : Ideal Γ(X, U)) [hp : p.IsPrime] :
      IsLocalization.AtPrime (X.presheaf.stalk (hU.fromSpec ⟨p, hp⟩)) p :=
    hU.isLocalization_stalk' ⟨p, hp⟩ (hU.isoSpec.inv _).2
  exact IsIntegrallyClosed.of_isLocalization_maximal
    (fun p hp ↦ X.presheaf.stalk (hU.fromSpec ⟨p, hp.isPrime⟩)) (fun _ _ ↦ inferInstance)

theorem IsAffineOpen.exists_section_of_codim_one_regular {U : X.Opens}
    (hU : IsAffineOpen U) [Nonempty U] [IsLocallyNoetherian X]
    [∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)] (f : X.functionField)
    (hregular : ∀ x : X, Order.coheight x = 1 →
      ∃ u : X.presheaf.stalk x, algebraMap (X.presheaf.stalk x) X.functionField u = f) :
    ∃ s : Γ(X, U), X.germToFunctionField U s = f := by
  have : IsFractionRing Γ(X, U) X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X U hU
  have : IsIntegrallyClosed Γ(X, U) := IsAffineOpen.isIntegrallyClosed_of_stalks hU
  have : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  have hmem : f ∈ Set.range (algebraMap Γ(X, U) X.functionField) := by
    apply mem_algebraMap_of_mem_height_one_localizations
    intro p hp
    let x : X := hU.fromSpec p
    have hxU : x ∈ U := (hU.isoSpec.inv p).2
    let : Algebra Γ(X, U) (X.presheaf.stalk x) :=
      TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨x, hxU⟩
    have : IsLocalization.AtPrime (X.presheaf.stalk x) p.asIdeal :=
      hU.isLocalization_stalk' p hxU
    have hx : Order.coheight x = 1 := by
      have hdim := IsLocalization.AtPrime.ringKrullDim_eq_height p.asIdeal (X.presheaf.stalk x)
      rw [ringKrullDim_stalk_eq_coheight, hp] at hdim
      exact_mod_cast hdim
    have : IsScalarTower Γ(X, U) (X.presheaf.stalk x) X.functionField :=
      functionField_isScalarTower X U ⟨x, hxU⟩
    obtain ⟨u, hu⟩ := hregular x hx
    obtain ⟨a, s, rfl⟩ := IsLocalization.exists_mk'_eq p.asIdeal.primeCompl u
    refine ⟨a, s, s.2, ?_⟩
    rw [← hu, ← div_eq_mul_inv]
    have hs : algebraMap Γ(X, U) X.functionField s ≠ 0 :=
      (IsFractionRing.to_map_eq_zero_iff (K := X.functionField)).not.mpr
        (fun hzero ↦ s.2 (hzero ▸ p.asIdeal.zero_mem))
    apply (eq_div_iff hs).mpr
    have h := congrArg (algebraMap (X.presheaf.stalk x) X.functionField)
      (IsLocalization.mk'_spec (X.presheaf.stalk x) a s)
    simpa only [map_mul, ← IsScalarTower.algebraMap_apply Γ(X, U)
      (X.presheaf.stalk x) X.functionField] using h
  exact hmem

end AlgebraicGeometry

namespace AlgebraicGeometry.Scheme

variable {X : Scheme} [IsIntegral X]

theorem exists_global_unit_of_stalk_units {f : X.functionField}
    (h : ∀ x : X, ∃ u : X.presheaf.stalk x, IsUnit u ∧
      algebraMap (X.presheaf.stalk x) X.functionField u = f) :
    ∃ s : Γ(X, ⊤), IsUnit s ∧
      X.presheaf.germ ⊤ (genericPoint X) (by simp) s = f := by
  classical
  have : Nonempty (⊤ : X.Opens) := ⟨⟨Classical.arbitrary X, by simp⟩⟩
  change ∃ s : Γ(X, ⊤), IsUnit s ∧ X.germToFunctionField ⊤ s = f
  have hlocal (x : X) : ∃ (U : X.Opens) (hx : x ∈ U) (s : Γ(X, U)), IsUnit s ∧
      algebraMap (X.presheaf.stalk x) X.functionField (X.presheaf.germ U x hx s) = f := by
    obtain ⟨u, hu, huf⟩ := h x
    obtain ⟨U, hxU, s, hs⟩ := X.presheaf.exists_germ_eq u
    obtain ⟨V, i, hxV, hv⟩ := X.toRingedSpace.isUnit_res_of_isUnit_germ U s x hxU
      (hs.symm ▸ hu)
    refine ⟨V, hxV, X.presheaf.map i.op s, hv, ?_⟩
    rw [X.presheaf.germ_res_apply i x hxV s, hs, huf]
  choose U hx s hs hf using hlocal
  have (x : X) : Nonempty (U x) := ⟨⟨x, hx x⟩⟩
  have hfield (x : X) : X.germToFunctionField (U x) (s x) = f := by
    rw [← X.algebraMap_germ_eq_germToFunctionField (hx x)]
    exact hf x
  have hcover : (⊤ : X.Opens) ≤ iSup U := by
    intro x _
    exact Opens.mem_iSup.mpr ⟨x, hx x⟩
  have hc : TopCat.Presheaf.IsCompatible X.presheaf U s := by
    intro x y
    apply TopCat.Presheaf.section_ext X.sheaf
    intro z hz
    change X.presheaf.germ (U x ⊓ U y) z hz
        (X.presheaf.map (Opens.infLELeft (U x) (U y)).op (s x)) =
      X.presheaf.germ (U x ⊓ U y) z hz
        (X.presheaf.map (Opens.infLERight (U x) (U y)).op (s y))
    apply IsFractionRing.injective (X.presheaf.stalk z) X.functionField
    rw [X.presheaf.germ_res_apply, X.presheaf.germ_res_apply,
      X.algebraMap_germ_eq_germToFunctionField hz.1,
      X.algebraMap_germ_eq_germToFunctionField hz.2]
    exact (hfield x).trans (hfield y).symm
  obtain ⟨g, hg, _⟩ : ∃ g : Γ(X, ⊤),
      (∀ i, X.presheaf.map (homOfLE (show U i ≤ ⊤ from le_top)).op g = s i) ∧ _ :=
    X.sheaf.existsUnique_gluing' U ⊤ (fun _ ↦ homOfLE le_top) hcover s hc
  refine ⟨g, ?_, ?_⟩
  · apply X.toRingedSpace.isUnit_of_isUnit_germ
    intro x hxTop
    have heq : X.presheaf.germ ⊤ x hxTop g =
        X.presheaf.germ (U x) x (hx x) (s x) := by
      rw [← hg x, X.presheaf.germ_res_apply]
    rw [heq]
    exact (hs x).map (X.presheaf.germ (U x) x (hx x)).hom
  · let x : X := Classical.arbitrary X
    rw [← hfield x, ← hg x, ← X.algebraMap_germ_eq_germToFunctionField (hx x),
      X.presheaf.germ_res_apply, X.algebraMap_germ_eq_germToFunctionField]

variable [IsLocallyNoetherian X]
  [∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)]

theorem exists_global_unit_of_ord_eq_zero (f : X.functionField) (hf : f ≠ 0)
    (hord : ∀ x : X, X.ord f x = 0) :
    ∃ s : Γ(X, ⊤), IsUnit s ∧
      X.presheaf.germ ⊤ (genericPoint X) (by simp) s = f := by
  have hunit (x : X) (hx : Order.coheight x = 1) :
      ∃ u : X.presheaf.stalk x, IsUnit u ∧
        algebraMap (X.presheaf.stalk x) X.functionField u = f := by
    have : IsDiscreteValuationRing (X.presheaf.stalk x) :=
      isDiscreteValuationRing_stalk_of_isIntegrallyClosed hx
    exact exists_stalk_unit_of_ord_eq_zero hx hf (hord x)
  apply exists_global_unit_of_stalk_units
  intro x
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, _⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (show x ∈ (⊤ : X.Opens) by simp)
      (⊤ : X.Opens).isOpen
  have : Nonempty U := ⟨⟨x, hxU⟩⟩
  obtain ⟨s, hs⟩ := IsAffineOpen.exists_section_of_codim_one_regular hU f fun y hy ↦ by
    obtain ⟨u, _, hu⟩ := hunit y hy
    exact ⟨u, hu⟩
  obtain ⟨t, ht⟩ := IsAffineOpen.exists_section_of_codim_one_regular hU f⁻¹ fun y hy ↦ by
    obtain ⟨u, hu, huf⟩ := hunit y hy
    refine ⟨↑hu.unit⁻¹, ?_⟩
    rw [map_units_inv, hu.unit_spec, huf]
  have hst : s * t = 1 := by
    apply X.germToFunctionField_injective U
    rw [map_mul, map_one, hs, ht, mul_inv_cancel₀ hf]
  have hsu : IsUnit s := IsUnit.of_mul_eq_one t hst
  refine ⟨X.presheaf.germ U x hxU s, hsu.map (X.presheaf.germ U x hxU).hom, ?_⟩
  rw [X.algebraMap_germ_eq_germToFunctionField hxU, hs]

end AlgebraicGeometry.Scheme

open AlgebraicGeometry TopologicalSpace CategoryTheory

end

end SiegelZeros

end OAI
