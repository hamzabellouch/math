import Mathlib

namespace OAI

/-! Normal Divisors. -/



namespace NumericalDimensionOne

variable {R K : Type*} [CommRing R] [IsDomain R]
  [Field K] [Algebra R K] [IsFractionRing R K]

def denominatorIdeal (R : Type*) [CommRing R] [Algebra R K] (x : K) : Ideal R :=
  (Algebra.linearMap R K).range.colon {x}

omit [IsDomain R] [IsFractionRing R K] in
lemma mem_denominatorIdeal (x : K) (r : R) :
    r ∈ denominatorIdeal R x ↔ ∃ a : R, algebraMap R K a = algebraMap R K r * x := by
  simp [denominatorIdeal, Submodule.mem_colon_singleton, Algebra.smul_def]

lemma denominatorIdeal_ne_bot (x : K) : denominatorIdeal R x ≠ ⊥ := by
  obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.surj (nonZeroDivisors R) x
  have hb : (b : R) ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp b.2
  intro h
  have hbmem : (b : R) ∈ denominatorIdeal R x := by
    rw [mem_denominatorIdeal]
    exact ⟨a, by simpa [mul_comm] using hab.symm⟩
  rw [h, Ideal.mem_bot] at hbmem
  exact hb hbmem

omit [IsDomain R] [IsFractionRing R K] in
lemma denominatorIdeal_eq_top_iff (x : K) :
    denominatorIdeal R x = ⊤ ↔ ∃ a : R, algebraMap R K a = x := by
  rw [Ideal.eq_top_iff_one, mem_denominatorIdeal]
  simp

variable [IsNoetherianRing R] [IsIntegrallyClosed R]

theorem prime_denominator_height {x : K} (hp : (denominatorIdeal R x).IsPrime) :
    (denominatorIdeal R x).height = 1 := by
  let P := denominatorIdeal R x
  let M : Submodule R K := Submodule.map (Algebra.linearMap R K) P
  have hx : ¬ ∃ a : R, algebraMap R K a = x := by
    intro h
    exact hp.ne_top ((denominatorIdeal_eq_top_iff x).mpr h)
  have hM : M ≠ ⊥ := by
    intro heq
    apply denominatorIdeal_ne_bot (R := R) x
    apply le_antisymm _ bot_le
    intro a ha
    have ham : algebraMap R K a ∈ M := ⟨a, ha, rfl⟩
    rw [heq, Submodule.mem_bot] at ham
    exact (IsFractionRing.injective R K) (by simpa using ham)
  have hnotstable : ¬ ∀ y ∈ M, x * y ∈ M := by
    intro hstable
    have hi : IsIntegral R x := isIntegral_of_smul_mem_submodule M hM
      ((IsNoetherian.noetherian P).map (Algebra.linearMap R K)) x hstable
    exact hx (IsIntegrallyClosed.algebraMap_eq_of_integral hi)
  push Not at hnotstable
  obtain ⟨y, hyM, hxyM⟩ := hnotstable
  obtain ⟨a, haP, rfl⟩ := hyM
  obtain ⟨b, hb⟩ := (mem_denominatorIdeal (R := R) x a).mp haP
  have hbP : b ∉ P := by
    intro hbP
    apply hxyM
    exact ⟨b, hbP, by simpa [mul_comm] using hb⟩
  have hmin : P ∈ (Ideal.span {a}).minimalPrimes := by
    refine ⟨⟨hp, (Ideal.span_singleton_le_iff_mem P).mpr haP⟩, ?_⟩
    intro Q hQ hQP c hcP
    obtain ⟨d, hd⟩ := (mem_denominatorIdeal (R := R) x c).mp hcP
    have hbc : b * c = a * d := by
      apply IsFractionRing.injective R K
      rw [map_mul, map_mul, hb, hd]
      ring
    have hac : b * c ∈ Q := by
      rw [hbc]
      exact Q.mul_mem_right d (hQ.2 (Ideal.subset_span (Set.mem_singleton a)))
    exact (hQ.1.mem_or_mem hac).resolve_left fun hbQ => hbP (hQP hbQ)
  have hle : P.height ≤ 1 :=
    Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes (Ideal.span {a}) P hmin
  have hne : P.height ≠ 0 := Ideal.height_eq_zero_iff_eq_bot.not.mpr
    (denominatorIdeal_ne_bot x)
  exact le_antisymm hle (Order.one_le_iff_ne_zero.mpr hne)

omit [IsDomain R] [IsFractionRing R K] [IsNoetherianRing R] [IsIntegrallyClosed R] in

lemma quotient_annihilator_eq (x : K) :
    (⊥ : Submodule R (K ⧸ (Algebra.linearMap R K).range)).colon
      {Submodule.Quotient.mk x} = denominatorIdeal R x := by
  ext r
  rw [Submodule.mem_colon_singleton, Submodule.mem_bot,
    ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
  exact (Submodule.mem_colon_singleton).symm

theorem normal_domain_height_one_criterion (x : K) :
    (∃ a : R, algebraMap R K a = x) ↔
      ∀ p : Ideal R, p.IsPrime → p.height = 1 →
        ∃ s : R, s ∉ p ∧ ∃ a : R,
          algebraMap R K s * x = algebraMap R K a := by
  constructor
  · rintro ⟨a, rfl⟩ p hp _
    refine ⟨1, ?_, a, by simp⟩
    exact fun h => hp.ne_top ((Ideal.eq_top_iff_one p).mpr h)
  · intro hregular
    by_contra hx
    let N : Submodule R K := (Algebra.linearMap R K).range
    have hxzero : Submodule.Quotient.mk x ≠ (0 : K ⧸ N) := by
      intro hzero
      exact hx ((LinearMap.mem_range).mp
        ((Submodule.Quotient.mk_eq_zero N).mp hzero))
    obtain ⟨P, hP, hxs⟩ :=
      exists_le_isAssociatedPrime_of_isNoetherianRing R
        (Submodule.Quotient.mk x : K ⧸ N) hxzero
    obtain ⟨hp, y, hy⟩ := isAssociatedPrime_iff.mp hP
    obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective N y
    have heq : P = denominatorIdeal R w := hy.trans (quotient_annihilator_eq w)
    have hheight : P.height = 1 := by
      rw [heq]
      exact prime_denominator_height (heq ▸ hp)
    obtain ⟨s, hs, a, ha⟩ := hregular P hp hheight
    apply hs
    apply hxs
    rw [quotient_annihilator_eq, mem_denominatorIdeal]
    exact ⟨a, ha.symm⟩

end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory

namespace NumericalDimensionOne

class StalkwiseNormal (X : Scheme) : Prop where
  integrallyClosed_stalk : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)

attribute [instance] StalkwiseNormal.integrallyClosed_stalk

abbrev PrimeDivisor (X : Scheme) := {x : X // Order.coheight x = 1}
abbrev WeilDivisor (X : Scheme) := PrimeDivisor X →₀ ℤ

instance nonempty_top_open (X : Scheme) [Nonempty X] : Nonempty (⊤ : X.Opens) :=
  ⟨⟨Classical.arbitrary X, trivial⟩⟩

variable {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X] [StalkwiseNormal X]

theorem dvr_at_prime_divisor (p : PrimeDivisor X) :
    IsDiscreteValuationRing (X.presheaf.stalk p.1) := by
  have hd : ringKrullDim (X.presheaf.stalk p.1) = 1 :=
    by rw [ringKrullDim_stalk_eq_coheight, p.2]; rfl
  have hnf : ¬ IsField (X.presheaf.stalk p.1) :=
    (ringKrullDim_eq_one_iff_of_isLocalRing_isDomain.mp hd).1
  have : Ring.KrullDimLE 1 (X.presheaf.stalk p.1) :=
    krullDimLE_of_coheight_le p.2.le
  have : Ring.DimensionLEOne (X.presheaf.stalk p.1) :=
    ⟨fun {I} hI hprime =>
      Ring.krullDimLE_one_iff_of_noZeroDivisors.mp inferInstance I hI hprime⟩
  have : IsDedekindDomain (X.presheaf.stalk p.1) := { }
  exact ((IsDiscreteValuationRing.TFAE (X.presheaf.stalk p.1) hnf).out 3 1).mp
    (show IsDedekindDomain (X.presheaf.stalk p.1) from inferInstance)

def IsDivisorSection (D : WeilDivisor X) (f : X.functionField) : Prop :=
  f = 0 ∨ ∀ p : PrimeDivisor X, 0 ≤ X.ord f p.1 + D p

theorem divisorSection_add {D : WeilDivisor X} {f g : X.functionField}
    (hf : IsDivisorSection D f) (hg : IsDivisorSection D g) :
    IsDivisorSection D (f + g) := by
  rcases hf with rfl | hf
  · simpa [IsDivisorSection] using hg
  rcases hg with rfl | hg
  · simpa [IsDivisorSection] using (Or.inr hf : IsDivisorSection D f)
  by_cases hfg : f + g = 0
  · exact Or.inl hfg
  right
  intro p
  have := dvr_at_prime_divisor p
  have h := X.ord_add (x := p.1) hfg
  have hm : -(D p) ≤ min (X.ord f p.1) (X.ord g p.1) :=
    le_min (by have := hf p; omega) (by have := hg p; omega)
  omega

omit [StalkwiseNormal X] in
theorem divisorSection_smul {D : WeilDivisor X} (a : Γ(X, ⊤))
    {f : X.functionField} (hf : IsDivisorSection D f) :
    IsDivisorSection D (a • f) := by
  by_cases ha : a = 0
  · left; simp [ha]
  rcases hf with rfl | hf
  · left; simp
  right
  intro p
  have h := X.ord_le_smul (x := p.1) (U := ⊤) (by trivial) ha f
  have := hf p
  omega

def divisorSections (D : WeilDivisor X) : Submodule Γ(X, ⊤) X.functionField where
  carrier := {f | IsDivisorSection D f}
  zero_mem' := Or.inl rfl
  add_mem' := divisorSection_add
  smul_mem' := divisorSection_smul

section PrincipalDivisor
variable [CompactSpace X]

omit [StalkwiseNormal X] in

theorem finite_primeDivisors_in_closed {Z : Set X} (hZ : IsClosed Z)
    (hproper : Z ≠ Set.univ) :
    {p : PrimeDivisor X | p.1 ∈ Z}.Finite := by
  classical
  let : PartialOrder X := specializationOrder X
  let : AlgebraicGeometry.IsNoetherian X := ⟨⟩
  obtain ⟨S, hSfinite, hSclosed, hSirr, hZS⟩ :=
    TopologicalSpace.NoetherianSpace.exists_finite_set_isClosed_irreducible hZ
  let : Fintype S := hSfinite.fintype
  let g : S → X := fun T => (hSirr T.1 T.2).genericPoint
  have hgen : genericPoint X ∉ Z := by
    intro h
    apply hproper
    exact Set.eq_univ_of_univ_subset
      (((genericPoint_spec X).mem_closed_set_iff hZ).mp h)
  have hfin : (Set.range g).Finite := Set.finite_range g
  apply ((hfin.preimage (f := fun p : PrimeDivisor X => p.1)
    Subtype.val_injective.injOn)).subset
  intro p hp
  obtain ⟨T, hT, hpT⟩ := Set.mem_sUnion.mp (hZS ▸ hp)
  let q := g ⟨T, hT⟩
  have hq : IsGenericPoint q T := (hSirr T hT).isGenericPoint_genericPoint (hSclosed T hT)
  have hqp : p.1 ≤ q := hq.specializes hpT
  have hqg : q < genericPoint X := by
    refine lt_of_le_of_ne (genericPoint_specializes q) ?_
    intro heq
    apply hgen
    rw [← heq, hZS]
    exact Set.mem_sUnion.mpr ⟨T, hT, hq.mem⟩
  have hqone : (1 : ℕ∞) ≤ Order.coheight q := by
    exact le_trans (by simp) (Order.coheight_add_one_le hqg)
  have hpq : p.1 = q := by
    by_contra hne
    have h := Order.coheight_add_one_le (lt_of_le_of_ne hqp hne)
    rw [p.2] at h
    have htwo : (2 : ℕ∞) ≤ 1 := (add_le_add hqone (le_refl (1 : ℕ∞))).trans h
    norm_num at htwo
  exact ⟨⟨T, hT⟩, hpq.symm⟩

omit [StalkwiseNormal X] in

theorem ord_finite_support (f : X.functionField) :
    (Function.support (fun p : PrimeDivisor X => X.ord f p.1)).Finite := by
  by_cases hf : f = 0
  · simp [hf]
  obtain ⟨U, _, f', hU, heq, hunit⟩ := exists_isUnit_germ_eq X f hf
  have hproper : (U : Set X)ᶜ ≠ Set.univ := by
    intro h
    obtain ⟨x⟩ := hU
    have hx : x.1 ∈ (U : Set X)ᶜ := by rw [h]; trivial
    exact hx x.2
  apply (finite_primeDivisors_in_closed U.isOpen.isClosed_compl hproper).subset
  intro p hp hpU
  apply hp
  rw [← heq]
  exact X.ord_of_isUnit hunit hpU

noncomputable def principalWeilDivisor (f : X.functionField) : WeilDivisor X :=
  Finsupp.ofSupportFinite (fun p => X.ord f p.1) (ord_finite_support f)

omit [StalkwiseNormal X] in
@[simp] theorem principalWeilDivisor_apply (f : X.functionField) (p : PrimeDivisor X) :
    principalWeilDivisor f p = X.ord f p.1 := rfl

end PrincipalDivisor

theorem ord_nonnegative_iff_regular (p : PrimeDivisor X) (f : X.functionField)
    (hf : f ≠ 0) :
    0 ≤ X.ord f p.1 ↔ ∃ a : X.presheaf.stalk p.1,
      algebraMap (X.presheaf.stalk p.1) X.functionField a = f := by
  have := dvr_at_prime_divisor p
  rw [X.le_ord_iff p.2 hf]
  change 1 ≤ Ring.ordFrac (X.presheaf.stalk p.1) f ↔ _
  rw [Ring.ordFrac_eq_valuation_inv, one_le_inv₀
    (WithZero.pos_iff_ne_zero.mpr ((map_ne_zero _).mpr hf))]
  constructor
  · intro h
    obtain ⟨n, d, hnd⟩ :=
      IsDedekindDomain.HeightOneSpectrum.exists_primeCompl_mul_eq_of_integer
        (IsDiscreteValuationRing.maximalIdeal (X.presheaf.stalk p.1)) f h
    have hd : IsUnit (d : X.presheaf.stalk p.1) := by
      simpa [IsDiscreteValuationRing.maximalIdeal, IsLocalRing.mem_maximalIdeal,
        mem_nonunits_iff] using d.2
    obtain ⟨u, hu⟩ := hd
    refine ⟨n * ↑(u⁻¹), ?_⟩
    rw [map_mul, ← hnd, ← hu, mul_assoc, ← map_mul]
    simp
  · rintro ⟨a, rfl⟩
    exact (IsDiscreteValuationRing.maximalIdeal (X.presheaf.stalk p.1)).valuation_le_one a

omit [IsLocallyNoetherian X] in

theorem integrallyClosed_affine {U : X.Opens} (hU : IsAffineOpen U) [Nonempty U] :
    IsIntegrallyClosed Γ(X, U) := by
  let (x : PrimeSpectrum Γ(X, U)) : Algebra Γ(X, U) (X.presheaf.stalk (hU.fromSpec x)) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨hU.fromSpec x, (hU.isoSpec.inv x).2⟩
  have (P : Ideal Γ(X, U)) [hP : P.IsPrime] :
      IsLocalization.AtPrime (X.presheaf.stalk (hU.fromSpec ⟨P, hP⟩)) P :=
    hU.isLocalization_stalk' ⟨P, hP⟩ (hU.isoSpec.inv _).2
  exact IsIntegrallyClosed.of_isLocalization_maximal
    (fun P hP => X.presheaf.stalk (hU.fromSpec ⟨P, hP.isPrime⟩))
    (fun _ _ => inferInstance)

theorem affine_regular_iff_nonnegative_orders {U : X.Opens} (hU : IsAffineOpen U)
    [Nonempty U] (f : X.functionField) :
    (∃ a : Γ(X, U), X.germToFunctionField U a = f) ↔
      (f = 0 ∨ ∀ p : PrimeDivisor X, p.1 ∈ U → 0 ≤ X.ord f p.1) := by
  constructor
  · rintro ⟨a, rfl⟩
    by_cases hf : X.germToFunctionField U a = 0
    · exact Or.inl hf
    right
    intro p hpU
    apply (ord_nonnegative_iff_regular p _ hf).mpr
    exact ⟨X.presheaf.germ U p.1 hpU a,
      X.algebraMap_germ_eq_germToFunctionField hpU a⟩
  · rintro (rfl | h)
    · exact ⟨0, map_zero _⟩
    by_cases hf : f = 0
    · exact ⟨0, by simp [hf]⟩
    have := integrallyClosed_affine hU
    have := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
    have := functionField_isFractionRing_of_isAffineOpen X U hU
    change ∃ a : Γ(X, U), algebraMap Γ(X, U) X.functionField a = f
    apply (normal_domain_height_one_criterion (R := Γ(X, U)) f).mpr
    intro P hP hPh
    let y : PrimeSpectrum Γ(X, U) := ⟨P, hP⟩
    let x : U := ⟨hU.fromSpec y, (hU.isoSpec.inv y).2⟩
    let : Algebra Γ(X, U) (X.presheaf.stalk x.1) :=
      TopCat.Presheaf.algebra_section_stalk X.presheaf x
    have : IsLocalization.AtPrime (X.presheaf.stalk x.1) P :=
      hU.isLocalization_stalk' y x.2
    have := functionField_isScalarTower X U x
    have hx : Order.coheight x.1 = 1 := by
      have heq := IsLocalization.AtPrime.ringKrullDim_eq_height P
        (X.presheaf.stalk x.1)
      rw [ringKrullDim_stalk_eq_coheight, hPh] at heq
      exact_mod_cast heq
    obtain ⟨a, ha⟩ := (ord_nonnegative_iff_regular ⟨x.1, hx⟩ f hf).mp
      (h ⟨x.1, hx⟩ x.2)
    obtain ⟨⟨n, d⟩, hnd⟩ := IsLocalization.surj P.primeCompl a
    refine ⟨d, d.2, n, ?_⟩
    have hd : algebraMap (X.presheaf.stalk x.1) X.functionField
        (algebraMap Γ(X, U) (X.presheaf.stalk x.1) d) =
        algebraMap Γ(X, U) X.functionField d :=
      (IsScalarTower.algebraMap_apply Γ(X, U) (X.presheaf.stalk x.1) X.functionField d).symm
    have hn : algebraMap (X.presheaf.stalk x.1) X.functionField
        (algebraMap Γ(X, U) (X.presheaf.stalk x.1) n) =
        algebraMap Γ(X, U) X.functionField n :=
      (IsScalarTower.algebraMap_apply Γ(X, U) (X.presheaf.stalk x.1) X.functionField n).symm
    have hmap := congrArg (algebraMap (X.presheaf.stalk x.1) X.functionField) hnd
    rw [map_mul, ha, hd, hn] at hmap
    exact (mul_comm _ _).trans hmap

omit [IsLocallyNoetherian X] [StalkwiseNormal X] in
lemma germToFunctionField_restrict {U V : X.Opens} [Nonempty U] [Nonempty V]
    (i : U ⟶ V) (a : Γ(X, V)) :
    X.germToFunctionField U (X.presheaf.map i.op a) = X.germToFunctionField V a := by
  exact ConcreteCategory.congr_hom (X.presheaf.germ_res i (genericPoint X)
    (((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr (by simpa using ‹Nonempty U›))) a

theorem global_regular_iff_nonnegative_orders (f : X.functionField) :
    (∃ a : Γ(X, ⊤), X.germToFunctionField ⊤ a = f) ↔
      (f = 0 ∨ ∀ p : PrimeDivisor X, 0 ≤ X.ord f p.1) := by
  classical
  constructor
  · rintro ⟨a, rfl⟩
    by_cases hf : X.germToFunctionField ⊤ a = 0
    · exact Or.inl hf
    right
    intro p
    apply (ord_nonnegative_iff_regular p _ hf).mpr
    exact ⟨X.presheaf.germ ⊤ p.1 (by trivial) a,
      X.algebraMap_germ_eq_germToFunctionField (U := ⊤) (by trivial) a⟩
  · rintro (rfl | h)
    · exact ⟨0, map_zero _⟩
    let U : X → X.Opens := fun x => (X.affineCover.f (X.affineCover.idx x)).opensRange
    have hxU (x : X) : x ∈ U x := X.affineCover.covers x
    have hU (x : X) : IsAffineOpen (U x) := isAffineOpen_opensRange _
    let (x : X) : Nonempty (U x) := ⟨⟨x, hxU x⟩⟩
    have hgU (x : X) : genericPoint X ∈ U x :=
      ((genericPoint_spec X).mem_open_set_iff (U x).isOpen).mpr
        (by simpa using (inferInstance : Nonempty (U x)))
    have hlocal (x : X) : ∃ a : Γ(X, U x), X.germToFunctionField (U x) a = f :=
      (affine_regular_iff_nonnegative_orders (hU x) f).mpr (Or.inr fun p _ => h p)
    choose sf hsf using hlocal
    have hcompatible : TopCat.Presheaf.IsCompatible X.presheaf U sf := by
      intro x y
      let : Nonempty (U x ⊓ U y : X.Opens) := ⟨⟨genericPoint X, hgU x, hgU y⟩⟩
      apply X.germToFunctionField_injective (U x ⊓ U y)
      rw [germToFunctionField_restrict, germToFunctionField_restrict, hsf, hsf]
    have hcover : (⊤ : X.Opens) ≤ ⨆ x, U x := by
      intro x _
      exact TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hxU x⟩
    obtain ⟨a, ha, _⟩ := X.sheaf.existsUnique_gluing' U ⊤
      (fun _ => homOfLE le_top) hcover sf hcompatible
    refine ⟨a, ?_⟩
    let x : X := genericPoint X
    have hax : X.presheaf.map (homOfLE (le_top : U x ≤ ⊤)).op a = sf x := ha x
    rw [← germToFunctionField_restrict (U := U x) (homOfLE le_top) a, hax, hsf x]

omit [StalkwiseNormal X] in
lemma order_one (x : X) : X.ord (1 : X.functionField) x = 0 := by
  have h := X.ord_mul (x := x) (f := (1 : X.functionField)) (g := 1) one_ne_zero one_ne_zero
  simp only [mul_one] at h
  omega

omit [StalkwiseNormal X] in
lemma order_inv (f : X.functionField) (hf : f ≠ 0) (x : X) :
    X.ord f⁻¹ x = - X.ord f x := by
  have h := X.ord_mul (x := x) hf (inv_ne_zero hf)
  rw [mul_inv_cancel₀ hf, order_one] at h
  omega

def IsCartierDivisor (D : WeilDivisor X) : Prop :=
  ∀ x : X, ∃ U : X.Opens, IsAffineOpen U ∧ x ∈ U ∧
    ∃ f : X.functionField, f ≠ 0 ∧ ∀ p : PrimeDivisor X,
      p.1 ∈ U → D p = X.ord f p.1

omit [StalkwiseNormal X] in
lemma isCartierDivisor_zero : IsCartierDivisor (0 : WeilDivisor X) := by
  intro x
  let U : X.Opens := (X.affineCover.f (X.affineCover.idx x)).opensRange
  refine ⟨U, isAffineOpen_opensRange _, X.affineCover.covers x, 1, one_ne_zero, ?_⟩
  intro p _
  simp [order_one]

omit [StalkwiseNormal X] in
lemma isCartierDivisor_neg {D : WeilDivisor X} (hD : IsCartierDivisor D) :
    IsCartierDivisor (-D) := by
  intro x
  obtain ⟨U, hU, hx, f, hf, heq⟩ := hD x
  refine ⟨U, hU, hx, f⁻¹, inv_ne_zero hf, ?_⟩
  intro p hp
  simp only [Finsupp.neg_apply, heq p hp, order_inv f hf]

omit [StalkwiseNormal X] in
lemma isCartierDivisor_add {D E : WeilDivisor X}
    (hD : IsCartierDivisor D) (hE : IsCartierDivisor E) :
    IsCartierDivisor (D + E) := by
  intro x
  obtain ⟨U, hU, hxU, f, hf, hDf⟩ := hD x
  obtain ⟨V, hV, hxV, g, hg, hEg⟩ := hE x
  obtain ⟨W, hW, hxW, hWU⟩ := exists_isAffineOpen_mem_and_subset
    (show x ∈ U ⊓ V from ⟨hxU, hxV⟩)
  refine ⟨W, hW, hxW, f * g, mul_ne_zero hf hg, ?_⟩
  intro p hp
  simp only [Finsupp.add_apply, hDf p (hWU hp).1, hEg p (hWU hp).2, X.ord_mul hf hg]

def cartierDivisors : AddSubgroup (WeilDivisor X) where
  carrier := {D | IsCartierDivisor D}
  zero_mem' := isCartierDivisor_zero
  add_mem' := isCartierDivisor_add
  neg_mem' := isCartierDivisor_neg

def IsDivisorSectionOn (D : WeilDivisor X) (U : X.Opens) (f : X.functionField) : Prop :=
  f = 0 ∨ ∀ p : PrimeDivisor X, p.1 ∈ U → 0 ≤ X.ord f p.1 + D p

theorem cartier_local_section_iff {D : WeilDivisor X} {U : X.Opens}
    (hU : IsAffineOpen U) [Nonempty U] {g : X.functionField} (hg : g ≠ 0)
    (heq : ∀ p : PrimeDivisor X, p.1 ∈ U → D p = X.ord g p.1)
    (f : X.functionField) :
    IsDivisorSectionOn D U f ↔ ∃ a : Γ(X, U), X.germToFunctionField U a = f * g := by
  rw [affine_regular_iff_nonnegative_orders hU]
  by_cases hf : f = 0
  · simp [IsDivisorSectionOn, hf]
  simp only [IsDivisorSectionOn, hf, false_or, mul_ne_zero hf hg,
    X.ord_mul hf hg]
  constructor <;> intro h p hp
  · simpa only [heq p hp] using h p hp
  · simpa only [heq p hp] using h p hp

omit [StalkwiseNormal X] in

theorem divisorSection_mul {D E : WeilDivisor X} {f g : X.functionField}
    (hf : IsDivisorSection D f) (hg : IsDivisorSection E g) :
    IsDivisorSection (D + E) (f * g) := by
  rcases hf with rfl | hf
  · exact Or.inl (zero_mul _)
  rcases hg with rfl | hg
  · exact Or.inl (mul_zero _)
  by_cases hf0 : f = 0
  · exact Or.inl (by simp [hf0])
  by_cases hg0 : g = 0
  · exact Or.inl (by simp [hg0])
  right
  intro p
  rw [X.ord_mul hf0 hg0, Finsupp.add_apply]
  have := hf p
  have := hg p
  omega

theorem divisorSections_mono {D E : WeilDivisor X} (hDE : D ≤ E) :
    divisorSections D ≤ divisorSections E := by
  intro f hf
  rcases hf with rfl | hf
  · exact Or.inl rfl
  right
  intro p
  have := hf p
  have := hDE p
  omega

end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory

namespace NumericalDimensionOne
section DominantScalars
variable {X Y : Scheme} [IsIntegral X] [IsIntegral Y]

lemma dominant_genericPoint (f : X ⟶ Y) [IsDominant f] :
    f (genericPoint X) = genericPoint Y := by
  apply ((genericPoint_spec Y).eq _).symm
  simpa only [Set.image_univ, f.denseRange.closure_range] using
    (genericPoint_spec X).image f.continuous

noncomputable def dominantFunctionFieldMap (f : X ⟶ Y) [IsDominant f] :
    Y.functionField →+* X.functionField :=
  ((Y.presheaf.stalkCongr
    (Inseparable.of_eq (dominant_genericPoint f).symm)).hom ≫
      f.stalkMap (genericPoint X)).hom

lemma dominantFunctionFieldMap_algebraMap (f : X ⟶ Y) [IsDominant f]
    (x : X) (r : Y.presheaf.stalk (f x)) :
    dominantFunctionFieldMap f (algebraMap (Y.presheaf.stalk (f x)) Y.functionField r) =
      algebraMap (X.presheaf.stalk x) X.functionField (f.stalkMap x r) := by
  change f.stalkMap (genericPoint X)
    (Y.presheaf.stalkSpecializes
      (Inseparable.of_eq (dominant_genericPoint f).symm).specializes'
      (Y.presheaf.stalkSpecializes ((genericPoint_spec Y).specializes trivial) r)) =
      X.presheaf.stalkSpecializes _ (f.stalkMap x r)
  rw [Y.presheaf.stalkSpecializes_comp_apply]
  exact f.stalkSpecializes_stalkMap_apply (genericPoint X) x
    ((genericPoint_spec X).specializes (Set.mem_univ x)) r

end DominantScalars

section CartierPullbackDefinition
variable {X Y : Scheme} [IsIntegral X] [IsIntegral Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]

def IsCartierPullback (f : X ⟶ Y) [IsDominant f]
    (D : WeilDivisor Y) (E : WeilDivisor X) : Prop :=
  ∀ x : X, ∃ U : Y.Opens, IsAffineOpen U ∧ f x ∈ U ∧
    ∃ g : Y.functionField, g ≠ 0 ∧
      (∀ p : PrimeDivisor Y, p.1 ∈ U → D p = Y.ord g p.1) ∧
      (∀ p : PrimeDivisor X, f p.1 ∈ U → E p = X.ord (dominantFunctionFieldMap f g) p.1)

end CartierPullbackDefinition
end NumericalDimensionOne

end OAI
