import Mathlib

namespace OAI

/-! Normal local rings, height-one orders, divisors and descent of rational functions. -/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Order Polynomial
open scoped TensorProduct WithZero
universe u

namespace RelativeDenominators

open IsLocalRing

 
theorem maximalIdeal_isPrincipal_of_fraction_witness
    {R K : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [IsLocalRing R] [IsIntegrallyClosed R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (x : K) (hx : ∀ r : R, algebraMap R K r ≠ x)
    (hxM : ∀ m ∈ maximalIdeal R,
      ∃ r : R, algebraMap R K r = x * algebraMap R K m) :
    (maximalIdeal R).IsPrincipal := by
  classical
  by_cases hbot : maximalIdeal R = ⊥
  · rw [hbot]
    infer_instance
  obtain ⟨a, ha, ha0⟩ : ∃ a ∈ maximalIdeal R, a ≠ (0 : R) := by
    by_contra! h
    apply hbot
    rwa [Submodule.eq_bot_iff]
  let M := Submodule.map (Algebra.linearMap R K) (maximalIdeal R)
  have hM : M ≠ ⊥ := by
    rw [Submodule.ne_bot_iff]
    exact ⟨_, ⟨a, ha, rfl⟩,
      (IsFractionRing.to_map_eq_zero_iff (K := K)).not.mpr ha0⟩
  have hfg : M.FG := Submodule.FG.map _ (IsNoetherian.noetherian _)
  by_cases hclosed : ∀ y ∈ M, x * y ∈ M
  · have hi := isIntegral_of_smul_mem_submodule M hM hfg x hclosed
    obtain ⟨r, hr⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hi
    exact (hx r hr).elim
  have htop :
      (M.map (DistribSMul.toLinearMap R K x)).comap (Algebra.linearMap R K) = ⊤ := by
    contrapose! hclosed with h
    rintro m' ⟨m, hm, rfl : algebraMap R K m = m'⟩
    obtain ⟨k, hk⟩ := hxM m hm
    exact ⟨k, le_maximalIdeal h ⟨_, ⟨_, hm, rfl⟩, hk.symm⟩, hk⟩
  obtain ⟨y, hy, hxy⟩ : ∃ y ∈ maximalIdeal R, x * algebraMap R K y = 1 := by
    rw [Ideal.eq_top_iff_one, Submodule.mem_comap] at htop
    obtain ⟨_, ⟨y, hy, rfl⟩, hy'⟩ := htop
    exact ⟨y, hy, by simpa using hy'⟩
  refine ⟨⟨y, ?_⟩⟩
  apply le_antisymm
  · intro m hm
    obtain ⟨k, hk⟩ := hxM m hm
    apply Ideal.mem_span_singleton'.mpr
    refine ⟨k, IsFractionRing.injective R K ?_⟩
    rw [map_mul, hk]
    calc x * algebraMap R K m * algebraMap R K y =
        algebraMap R K m * (x * algebraMap R K y) := by ring
      _ = algebraMap R K m := by rw [hxy, mul_one]
  · rwa [Submodule.span_le, Set.singleton_subset_iff]

 
theorem exists_prime_colon_over
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [H : IsNoetherianRing R] (N : Submodule R M) (x : M) (hx : x ∉ N) :
    ∃ (P : Ideal R) (y : M), P.IsPrime ∧ P = N.colon {y} ∧ N.colon {x} ≤ P := by
  classical
  obtain ⟨P, ⟨hle, hne, y, rfl⟩, hmax⟩ :=
    set_has_maximal_iff_noetherian.mpr H
      { P | N.colon {x} ≤ P ∧ P ≠ ⊤ ∧ ∃ y : M, P = N.colon {y} }
      ⟨_, le_rfl, by simpa [Submodule.colon_eq_top_iff_subset] using hx, x, rfl⟩
  refine ⟨_, y, ⟨hne, ?_⟩, rfl, hle⟩
  intro a b hab
  rw [or_iff_not_imp_left]
  intro ha
  rw [Submodule.mem_colon_singleton] at ha hab
  have hle' : N.colon {y} ≤ N.colon {a • y} := by
    intro c hc
    rw [Submodule.mem_colon_singleton] at hc ⊢
    rw [smul_comm]
    exact N.smul_mem a hc
  rw [hle'.eq_of_not_lt (hmax _ ⟨hle.trans hle',
    by simpa [Submodule.colon_eq_top_iff_subset] using ha, _, rfl⟩),
    Submodule.mem_colon_singleton, smul_comm, smul_smul]
  exact hab

section HeightOne

variable {R K : Type*} [CommRing R] [IsDomain R]
  [Field K] [Algebra R K] [IsFractionRing R K]

 

theorem mem_localization_iff_denominator (P : Ideal R) [P.IsPrime] (x : K) :
    x ∈ Localization.subalgebra.ofField K P.primeCompl P.primeCompl_le_nonZeroDivisors ↔
      ∃ s : R, s ∉ P ∧ s ∈ (Algebra.linearMap R K).range.colon {x} := by
  constructor
  · rintro ⟨a, s, hs, hx⟩
    refine ⟨s, hs, ?_⟩
    rw [Submodule.mem_colon_singleton, Algebra.smul_def]
    refine ⟨a, ?_⟩
    change algebraMap R K a = algebraMap R K s * x
    have hs0 : algebraMap R K s ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors
        (P.primeCompl_le_nonZeroDivisors hs)
    rw [hx, mul_left_comm, mul_inv_cancel₀ hs0, mul_one]
  · rintro ⟨s, hs, h⟩
    obtain ⟨a, ha⟩ := (Submodule.mem_colon_singleton.mp h)
    refine ⟨a, s, hs, ?_⟩
    have hs0 : algebraMap R K s ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors
        (P.primeCompl_le_nonZeroDivisors hs)
    simp only [Algebra.linearMap_apply, Algebra.smul_def] at ha
    rw [← div_eq_mul_inv, eq_div_iff hs0, mul_comm]
    exact ha.symm

 
theorem height_eq_one_of_prime_denominator_ideal
    [IsNoetherianRing R] [IsIntegrallyClosed R]
    (P : Ideal R) [P.IsPrime] (y : K)
    (hP : P = (Algebra.linearMap R K).range.colon {y}) : P.height = 1 := by
  classical
  let A := Localization.subalgebra.ofField K P.primeCompl P.primeCompl_le_nonZeroDivisors
  let : IsLocalRing A := IsLocalization.AtPrime.isLocalRing A P
  let : IsNoetherianRing A := IsLocalization.isNoetherianRing P.primeCompl A inferInstance
  let : IsIntegrallyClosed A := isIntegrallyClosed_of_isLocalization A
    P.primeCompl P.primeCompl_le_nonZeroDivisors
  have hy : y ∉ A := by
    rw [mem_localization_iff_denominator]
    rintro ⟨s, hs, hd⟩
    exact hs (hP ▸ hd)
  have hmul : ∀ m ∈ maximalIdeal A,
      ∃ r : A, algebraMap A K r = y * algebraMap A K m := by
    intro m hm
    obtain ⟨a, s, hs, he⟩ := m.property
    have hs0 : algebraMap R K s ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors
        (P.primeCompl_le_nonZeroDivisors hs)
    have hma : algebraMap R A a = algebraMap R A s * m := by
      apply Subtype.ext
      change algebraMap R K a = algebraMap R K s * (m : K)
      rw [he, mul_left_comm, mul_inv_cancel₀ hs0, mul_one]
    have ha : a ∈ P := (IsLocalization.AtPrime.to_map_mem_maximal_iff A P a).mp (by
      rw [hma]
      exact (maximalIdeal A).mul_mem_left _ hm)
    rw [hP, Submodule.mem_colon_singleton] at ha
    obtain ⟨k, hk⟩ := ha
    simp only [Algebra.linearMap_apply, Algebra.smul_def] at hk
    refine ⟨⟨algebraMap R K k * (algebraMap R K s)⁻¹, k, s, hs, rfl⟩, ?_⟩
    change algebraMap R K k * (algebraMap R K s)⁻¹ = y * (m : K)
    rw [he, hk]
    ring
  have : (maximalIdeal A).IsPrincipal :=
    maximalIdeal_isPrincipal_of_fraction_witness y
      (fun r h => hy (h ▸ r.property)) hmul
  have hle : P.height ≤ 1 := by
    rw [← IsLocalization.AtPrime.under_maximalIdeal A P,
      IsLocalization.height_under P.primeCompl]
    exact Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes
      (maximalIdeal A) (maximalIdeal A) (by simp [Ideal.minimalPrimes_eq_subsingleton_self])
  have hne : P ≠ ⊥ := by
    obtain ⟨a, b, hb, he⟩ := IsFractionRing.div_surjective R y
    have hbP : b ∈ P := by
      rw [hP, Submodule.mem_colon_singleton, Algebra.smul_def]
      refine ⟨a, ?_⟩
      change algebraMap R K a = algebraMap R K b * y
      rw [← he, mul_div_cancel₀ _
        (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb)]
    intro hbot
    rw [hbot, Submodule.mem_bot] at hbP
    exact nonZeroDivisors.ne_zero hb hbP
  exact le_antisymm hle (Order.one_le_iff_ne_zero.mpr
    (Ideal.height_eq_zero_iff_eq_bot.not.mpr hne))

 

theorem exists_algebraMap_eq_of_mem_height_one_localizations
    [IsNoetherianRing R] [IsIntegrallyClosed R] (x : K)
    (hx : ∀ (P : Ideal R) [P.IsPrime], P.height = 1 →
      x ∈ Localization.subalgebra.ofField K P.primeCompl P.primeCompl_le_nonZeroDivisors) :
    ∃ r : R, algebraMap R K r = x := by
  classical
  by_contra h
  have hx' : x ∉ (Algebra.linearMap R K).range := h
  obtain ⟨P, y, hprime, hP, hle⟩ :=
    exists_prime_colon_over (Algebra.linearMap R K).range x hx'
  have : P.IsPrime := hprime
  have hheight : P.height = 1 := height_eq_one_of_prime_denominator_ideal P y hP
  obtain ⟨s, hs, hd⟩ := (mem_localization_iff_denominator P x).mp (hx P hheight)
  exact hs (hle hd)

end HeightOne

 

open AlgebraicGeometry TopologicalSpace Order CategoryTheory

 

theorem integrallyClosed_affine_sections
    (X : Scheme) [IsIntegral X]
    (hNormal : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (U : X.Opens) (hU : IsAffineOpen U) [Nonempty U] :
    IsIntegrallyClosed Γ(X, U) := by
  apply IsIntegrallyClosed.of_localization_maximal
  intro p hp hpmax
  let y : PrimeSpectrum Γ(X, U) := ⟨p, inferInstance⟩
  let S := X.presheaf.stalk (hU.fromSpec y)
  let : Algebra Γ(X, U) S :=
    X.presheaf.algebra_section_stalk ⟨hU.fromSpec y, (hU.isoSpec.inv y).2⟩
  let : IsLocalization.AtPrime S p := hU.isLocalization_stalk' y (hU.isoSpec.inv y).2
  let : IsIntegrallyClosed S := hNormal _
  exact IsIntegrallyClosed.of_equiv
    (IsLocalization.algEquiv p.primeCompl S (Localization.AtPrime p)).toRingEquiv

 

theorem dvr_stalk_of_normal_codimOne
    (X : Scheme) [IsIntegral X] [IsLocallyNoetherian X]
    (x : X) (hx : coheight x = 1) [IsIntegrallyClosed (X.presheaf.stalk x)] :
    IsDiscreteValuationRing (X.presheaf.stalk x) := by
  let R := X.presheaf.stalk x
  have hdim : ringKrullDim R = 1 := by
    rw [ringKrullDim_stalk_eq_coheight, hx]
    rfl
  have hnf : ¬ IsField R := by
    intro h
    have hzero := ringKrullDim_eq_zero_of_isField h
    rw [hdim] at hzero
    exact one_ne_zero hzero
  let : Ring.KrullDimLE 1 R := krullDimLE_of_coheight_le hx.le
  apply ((IsDiscreteValuationRing.TFAE R hnf).out 1 4).mpr
  refine ⟨inferInstance, IsLocalRing.maximalIdeal R, ⟨?_, inferInstance⟩, ?_⟩
  · exact IsLocalRing.isField_iff_maximalIdeal_eq.not.mp hnf
  · intro P hP
    exact IsLocalRing.eq_maximalIdeal (hP.2.isMaximal_of_ne_bot hP.1)

 

 
abbrev PrimeDivisor (X : Scheme) := {x : X // coheight x = 1}

 
abbrev WeilDivisor (X : Scheme) := PrimeDivisor X →₀ ℤ

 

theorem finite_codimOne_outside_open (X : Scheme) [IsIntegral X] [IsNoetherian X]
    (U : X.Opens) [Nonempty U] :
    {x : X | coheight x = 1 ∧ x ∉ U}.Finite := by
  classical
  obtain ⟨S, hSf, hSc, hSi, hSU⟩ :=
    NoetherianSpace.exists_finite_set_isClosed_irreducible U.isOpen.isClosed_compl
  let g : S → X := fun s => (hSi s.1 s.2).genericPoint
  let : Finite S := hSf.to_subtype
  apply (Set.finite_range g).subset
  intro x hx
  obtain ⟨s, hsS, hxs⟩ : ∃ s ∈ S, x ∈ s := by
    have hxS : x ∈ ⋃₀ S := by rw [← hSU]; exact hx.2
    exact Set.mem_sUnion.mp hxS
  refine ⟨⟨s, hsS⟩, ?_⟩
  have hg : IsGenericPoint (g ⟨s, hsS⟩) s :=
    (hSi s hsS).isGenericPoint_genericPoint (hSc s hsS)
  have hle : x ≤ g ⟨s, hsS⟩ := hg.specializes hxs
  have hgnU : g ⟨s, hsS⟩ ∉ U := by
    have hgS : g ⟨s, hsS⟩ ∈ ⋃₀ S := Set.mem_sUnion.mpr ⟨s, hsS, hg.mem⟩
    rwa [← hSU] at hgS
  have huet : genericPoint X ∈ U := by
    apply (genericPoint_spec X).mem_open_set_iff U.isOpen |>.mpr
    simpa using Set.nonempty_coe_sort.mp (inferInstance : Nonempty U)
  have hback : g ⟨s, hsS⟩ ≤ x := by
    by_contra hn
    have hlt : x < g ⟨s, hsS⟩ := lt_iff_le_not_ge.mpr ⟨hle, hn⟩
    have hheight : coheight (g ⟨s, hsS⟩) = 0 := by
      apply Order.lt_one_iff.mp
      exact (coheight_le_coe_iff.mp (by simpa using hx.1.le)) _ hlt
    have hmax : IsMax (g ⟨s, hsS⟩) := coheight_eq_zero.mp hheight
    have hgeneric : genericPoint X ≤ g ⟨s, hsS⟩ :=
      hmax (genericPoint_specializes _)
    exact hgnU (hgeneric.mem_open U.isOpen huet)
  exact ((show g ⟨s, hsS⟩ ⤳ x from hle).antisymm
    (show x ⤳ g ⟨s, hsS⟩ from hback)).eq

 
theorem finite_support_ord (X : Scheme) [IsIntegral X] [IsNoetherian X]
    (f : X.functionField) (hf : f ≠ 0) :
    (Function.support fun x : PrimeDivisor X => X.ord f x.1).Finite := by
  obtain ⟨U, hUaff, f', hUne, hf', hf'unit⟩ := exists_isUnit_germ_eq X f hf
  let : Nonempty U := hUne
  have hfinite := finite_codimOne_outside_open X U
  apply (hfinite.preimage Subtype.val_injective.injOn).subset
  intro x hx
  refine ⟨x.2, ?_⟩
  intro hxU
  have hz : X.ord f x.1 = 0 := by
    rw [← hf']
    exact X.ord_of_isUnit hf'unit hxU
  exact hx hz

 
noncomputable def principalDivisor (X : Scheme) [IsIntegral X] [IsNoetherian X]
    (f : X.functionFieldˣ) : WeilDivisor X :=
  Finsupp.ofSupportFinite (fun x => X.ord (f : X.functionField) x.1)
    (finite_support_ord X (f : X.functionField) (Units.ne_zero f))

@[simp] theorem principalDivisor_apply (X : Scheme) [IsIntegral X] [IsNoetherian X]
    (f : X.functionFieldˣ) (x : PrimeDivisor X) :
    principalDivisor X f x = X.ord (f : X.functionField) x.1 := rfl

 

theorem exists_stalk_unit_of_ord_eq_zero
    (X : Scheme) [IsIntegral X] [IsLocallyNoetherian X]
    (x : X) (hx : coheight x = 1) [IsIntegrallyClosed (X.presheaf.stalk x)]
    (f : X.functionField) (hf : f ≠ 0) (hord : X.ord f x = 0) :
    ∃ s : X.presheaf.stalk x, IsUnit s ∧ algebraMap _ X.functionField s = f := by
  let : IsDiscreteValuationRing (X.presheaf.stalk x) :=
    dvr_stalk_of_normal_codimOne X x hx
  have h : Ring.ordFrac (X.presheaf.stalk x) f = 1 := by
    simpa [Scheme.ordHom] using (X.ord_eq_iff hx hf).mp hord
  change f ∈ MonoidHom.mker (Ring.ordFrac (X.presheaf.stalk x)) at h
  rw [Ring.mker_ordFrac_eq_isUnitSubmonoid] at h
  exact h

 

theorem exists_affine_section_of_ord_eq_zero
    (X : Scheme) [IsIntegral X] [IsNoetherian X]
    (hNormal : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (U : X.Opens) (hU : IsAffineOpen U) [Nonempty U]
    (f : X.functionField) (hf : f ≠ 0)
    (hord : ∀ x : X, x ∈ U → coheight x = 1 → X.ord f x = 0) :
    ∃ s : Γ(X, U), algebraMap Γ(X, U) X.functionField s = f := by
  let : IsIntegrallyClosed Γ(X, U) := integrallyClosed_affine_sections X hNormal U hU
  let : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  let : IsFractionRing Γ(X, U) X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X U hU
  apply exists_algebraMap_eq_of_mem_height_one_localizations
  intro P hP hheight
  let y : PrimeSpectrum Γ(X, U) := ⟨P, hP⟩
  let z : X := hU.fromSpec y
  have hzU : z ∈ U := (hU.isoSpec.inv y).2
  have hz : coheight z = 1 := by
    change coheight (hU.fromSpec y) = 1
    erw [coheight_eq_of_isOpenImmersion hU.fromSpec,
      ← idealHeight_eq_coheight Γ(X, U) y]
    exact hheight
  let : IsIntegrallyClosed (X.presheaf.stalk z) := hNormal z
  obtain ⟨s, hsunit, hs⟩ := exists_stalk_unit_of_ord_eq_zero X z hz f hf (hord z hzU hz)
  let : Algebra Γ(X, U) (X.presheaf.stalk z) :=
    X.presheaf.algebra_section_stalk ⟨z, hzU⟩
  let : IsLocalization.AtPrime (X.presheaf.stalk z) P := hU.isLocalization_stalk' y hzU
  have : IsScalarTower Γ(X, U) (X.presheaf.stalk z) X.functionField :=
    functionField_isScalarTower X U ⟨z, hzU⟩
  obtain ⟨a, b, he⟩ := IsLocalization.exists_mk'_eq P.primeCompl s
  rw [mem_localization_iff_denominator]
  refine ⟨b, b.property, ?_⟩
  rw [Submodule.mem_colon_singleton, Algebra.smul_def]
  refine ⟨a, ?_⟩
  change algebraMap Γ(X, U) X.functionField a = algebraMap Γ(X, U) X.functionField b * f
  rw [← hs, IsScalarTower.algebraMap_apply Γ(X, U) (X.presheaf.stalk z) X.functionField b,
    ← map_mul, ← he, IsLocalization.mk'_spec',
    ← IsScalarTower.algebraMap_apply Γ(X, U) (X.presheaf.stalk z) X.functionField]

 
theorem germToFunctionField_map
    (X : Scheme) [IsIntegral X] {U V : X.Opens} [Nonempty U] [Nonempty V]
    (i : U ⟶ V) (s : Γ(X, V)) :
    X.germToFunctionField U (X.presheaf.map i.op s) = X.germToFunctionField V s := by
  change X.presheaf.germ U _ _ (X.presheaf.map i.op s) = X.presheaf.germ V _ _ s
  rw [← ConcreteCategory.comp_apply, X.presheaf.germ_res]

 
instance nonempty_top_of_integral (X : Scheme) [IsIntegral X] : Nonempty (⊤ : X.Opens) :=
  ⟨⟨genericPoint X, trivial⟩⟩

 
theorem exists_section_of_ord_eq_zero
    (X : Scheme) [IsIntegral X] [IsNoetherian X]
    (hNormal : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (V : X.Opens) [hV : Nonempty V]
    (f : X.functionField) (hf : f ≠ 0)
    (hord : ∀ x : X, x ∈ V → coheight x = 1 → X.ord f x = 0) :
    ∃ s : Γ(X, V), algebraMap Γ(X, V) X.functionField s = f := by
  classical
  choose U hU hxU hUV using fun x : V => exists_isAffineOpen_mem_and_subset x.property
  let : ∀ x : V, Nonempty (U x) := fun x => ⟨⟨x, hxU x⟩⟩
  choose s hs using fun x : V => exists_affine_section_of_ord_eq_zero X hNormal (U x) (hU x)
    f hf (fun y hy => hord y (hUV x hy))
  have hgen : ∀ x : V, genericPoint X ∈ U x := fun x =>
    ((genericPoint_spec X).mem_open_set_iff (U x).isOpen).mpr ⟨x, trivial, hxU x⟩
  have hcover : V ≤ iSup U := by
    intro x hx
    exact Opens.mem_iSup.mpr ⟨⟨x, hx⟩, hxU ⟨x, hx⟩⟩
  have hcompat : TopCat.Presheaf.IsCompatible X.presheaf U s := by
    intro i j
    let : Nonempty ((U i ⊓ U j : X.Opens) : Set X) :=
      ⟨⟨genericPoint X, hgen i, hgen j⟩⟩
    apply @Scheme.germToFunctionField_injective X _ (U i ⊓ U j)
      ⟨⟨genericPoint X, hgen i, hgen j⟩⟩
    rw [germToFunctionField_map, germToFunctionField_map]
    exact (hs i).trans (hs j).symm
  obtain ⟨g, hg, _⟩ := X.sheaf.existsUnique_gluing' U V
    (fun x => homOfLE (hUV x)) hcover s hcompat
  refine ⟨g, ?_⟩
  let x : V := hV.some
  have he := hg x
  have he' := congrArg (X.germToFunctionField (U x)) he
  change X.germToFunctionField (U x)
    (X.presheaf.map (homOfLE (hUV x)).op g) =
      X.germToFunctionField (U x) (s x) at he'
  erw [germToFunctionField_map] at he'
  exact he'.trans (hs x)

 
theorem exists_global_section_of_ord_eq_zero
    (X : Scheme) [IsIntegral X] [IsNoetherian X]
    (hNormal : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (f : X.functionField) (hf : f ≠ 0)
    (hord : ∀ x : X, coheight x = 1 → X.ord f x = 0) :
    ∃ s : Γ(X, ⊤), algebraMap Γ(X, ⊤) X.functionField s = f :=
  exists_section_of_ord_eq_zero X hNormal ⊤ f hf (fun x _ => hord x)

 
theorem exists_section_unit_of_ord_eq_zero
    (X : Scheme) [IsIntegral X] [IsNoetherian X]
    (hNormal : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (V : X.Opens) [hV : Nonempty V]
    (f : X.functionFieldˣ)
    (hord : ∀ x : X, x ∈ V → coheight x = 1 → X.ord (f : X.functionField) x = 0) :
    ∃ u : Γ(X, V)ˣ, algebraMap Γ(X, V) X.functionField (u : Γ(X, V)) =
      (f : X.functionField) := by
  have hordinv : ∀ x : X, x ∈ V → coheight x = 1 →
      X.ord (f : X.functionField)⁻¹ x = 0 := by
    intro x hxV hx
    rw [X.ord_eq_iff hx (inv_ne_zero (Units.ne_zero f))]
    have h := (X.ord_eq_iff hx (Units.ne_zero f)).mp (hord x hxV hx)
    change X.ordHom x hx (f : X.functionField)⁻¹ = 1
    change X.ordHom x hx (f : X.functionField) = 1 at h
    rw [map_inv₀, h, inv_one]
  obtain ⟨s, hs⟩ := exists_section_of_ord_eq_zero X hNormal V _ (Units.ne_zero f) hord
  obtain ⟨t, ht⟩ := exists_section_of_ord_eq_zero X hNormal V _
    (inv_ne_zero (Units.ne_zero f)) hordinv
  have hst : s * t = 1 := by
    apply X.germToFunctionField_injective V
    change algebraMap Γ(X, V) X.functionField (s * t) = algebraMap Γ(X, V) X.functionField 1
    rw [map_mul, hs, ht, mul_inv_cancel₀ (Units.ne_zero f), map_one]
  exact ⟨⟨s, t, hst, by rw [mul_comm, hst]⟩, hs⟩

 

theorem rational_function_eq_global_unit_of_divisor_zero
    (X : Scheme) [IsIntegral X] [IsNoetherian X]
    (hNormal : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (f : X.functionFieldˣ) (hdiv : principalDivisor X f = 0) :
    ∃ u : Γ(X, ⊤)ˣ, algebraMap Γ(X, ⊤) X.functionField (u : Γ(X, ⊤)) =
      (f : X.functionField) := by
  apply exists_section_unit_of_ord_eq_zero X hNormal ⊤ f
  intro x _ hx
  simpa using congrArg (fun D : WeilDivisor X => D ⟨x, hx⟩) hdiv

 

theorem genericPoint_eq_of_dominant
    {X Z : Scheme} [IsIntegral X] [IsIntegral Z]
    (f : X ⟶ Z) [IsDominant f] : f (genericPoint X) = genericPoint Z := by
  apply IsGenericPoint.eq _ (genericPoint_spec Z)
  simpa [Set.image_univ, f.denseRange.closure_range] using
    (genericPoint_spec X).image f.continuous

 
noncomputable def functionFieldPullback
    {X Z : Scheme} [IsIntegral X] [IsIntegral Z]
    (f : X ⟶ Z) [IsDominant f] : Z.functionField →+* X.functionField :=
  (Z.presheaf.stalkSpecializes (specializes_of_eq (genericPoint_eq_of_dominant f)) ≫
    f.stalkMap (genericPoint X)).hom

instance nonempty_preimage_of_dominant
    {X Z : Scheme} [IsIntegral X] [IsIntegral Z]
    (f : X ⟶ Z) [IsDominant f] (U : Z.Opens) [Nonempty U] :
    Nonempty (f ⁻¹ᵁ U) := by
  refine ⟨⟨genericPoint X, ?_⟩⟩
  change f (genericPoint X) ∈ U
  rw [genericPoint_eq_of_dominant f]
  apply ((genericPoint_spec Z).mem_open_set_iff U.isOpen).mpr
  simpa using Set.nonempty_coe_sort.mp (inferInstance : Nonempty U)

 
theorem functionFieldPullback_germ
    {X Z : Scheme} [IsIntegral X] [IsIntegral Z]
    (f : X ⟶ Z) [IsDominant f] (U : Z.Opens) [Nonempty U] (s : Γ(Z, U)) :
    functionFieldPullback f (Z.germToFunctionField U s) =
      X.germToFunctionField (f ⁻¹ᵁ U) (f.app U s) := by
  have he : Z.germToFunctionField U ≫
      CommRingCat.ofHom (functionFieldPullback f) =
      f.app U ≫ X.germToFunctionField (f ⁻¹ᵁ U) := by
    change Z.presheaf.germ U _ _ ≫
      (Z.presheaf.stalkSpecializes _ ≫ f.stalkMap _) = _
    rw [← Category.assoc, Z.presheaf.germ_stalkSpecializes, f.germ_stalkMap]
  exact congrArg (fun h => h s) he

 

def IsVerticalDivisor {X Z : Scheme} [IsIntegral Z]
    (f : X ⟶ Z) (D : WeilDivisor X) : Prop :=
  ∀ p : PrimeDivisor X, D p ≠ 0 → f p.1 ≠ genericPoint Z

 

theorem exists_open_avoiding_vertical_divisor
    {X Z : Scheme} [IsIntegral Z] (f : X ⟶ Z) (D : WeilDivisor X)
    (hvert : IsVerticalDivisor f D) :
    ∃ U : Z.Opens, genericPoint Z ∈ U ∧
      ∀ p : PrimeDivisor X, f p.1 ∈ U → D p = 0 := by
  classical
  let B : Set Z := ⋃ p ∈ D.support, closure ({f p.1} : Set Z)
  have hclosed : IsClosed B := isClosed_biUnion_finset (fun _ _ => isClosed_closure)
  let U : Z.Opens := ⟨Bᶜ, hclosed.isOpen_compl⟩
  refine ⟨U, ?_, ?_⟩
  · intro h
    obtain ⟨p, hp, hmem⟩ := Set.mem_iUnion₂.mp h
    have hspec : f p.1 ⤳ genericPoint Z := specializes_iff_mem_closure.mpr hmem
    exact hvert p (Finsupp.mem_support_iff.mp hp)
      (hspec.antisymm (genericPoint_specializes _)).eq
  · intro p hp
    by_contra hn
    exact hp (Set.mem_iUnion₂.mpr ⟨p, Finsupp.mem_support_iff.mpr hn,
      subset_closure (Set.mem_singleton _)⟩)

 

theorem rational_function_descends_of_vertical_divisor
    {X Z : Scheme} [IsIntegral X] [IsIntegral Z] [IsNoetherian X]
    (hNormal : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (f : X ⟶ Z) [IsDominant f] [IsIso f.c]
    (u : X.functionFieldˣ) (hvert : IsVerticalDivisor f (principalDivisor X u)) :
    ∃ v : Z.functionFieldˣ,
      functionFieldPullback f (v : Z.functionField) = (u : X.functionField) := by
  obtain ⟨U, hgen, hU⟩ := exists_open_avoiding_vertical_divisor f _ hvert
  let : Nonempty U := ⟨⟨genericPoint Z, hgen⟩⟩
  obtain ⟨s, hs⟩ := exists_section_unit_of_ord_eq_zero X hNormal (f ⁻¹ᵁ U) u
    (fun x hx hcodim => hU ⟨x, hcodim⟩ hx)
  let t : Γ(Z, U)ˣ := Units.map (inv (f.app U)).hom.toMonoidHom s
  have ht : f.app U (t : Γ(Z, U)) = (s : Γ(X, f ⁻¹ᵁ U)) := by
    change f.app U (inv (f.app U) (s : Γ(X, f ⁻¹ᵁ U))) = _
    exact congrArg (fun g => g (s : Γ(X, f ⁻¹ᵁ U))) (IsIso.inv_hom_id (f.app U))
  refine ⟨Units.map (Z.germToFunctionField U).hom.toMonoidHom t, ?_⟩
  change functionFieldPullback f (Z.germToFunctionField U (t : Γ(Z, U))) = _
  rw [functionFieldPullback_germ, ht]
  exact hs

end RelativeDenominators
end

end OAI
