import OAI.AlgebraicGeometry.SurfaceCones.CompletionParameters

namespace OAI

noncomputable section

attribute [local instance] ExplicitCone.actualCompletion_noetherian

namespace SmallCM

noncomputable def localDepth (R : Type*) [CommRing R] [IsLocalRing R]
    (M : Type*) [AddCommGroup M] [Module R M] : ℕ∞ :=
  sSup {n : ℕ∞ | ∃ rs : List R,
    (∀ x ∈ rs, x ∈ IsLocalRing.maximalIdeal R) ∧
    RingTheory.Sequence.IsRegular M rs ∧ n = (rs.length : ℕ∞)}

/-- Existence of a complete normal local domain over ℂ with no small Cohen–Macaulay module. -/
def MainClaim : Prop :=
  ∃ (R : Type) (_ : CommRing R) (_ : IsDomain R) (_ : IsNoetherianRing R)
    (_ : IsIntegrallyClosed R) (_ : IsLocalRing R) (_ : Algebra ℂ R),
    IsAdicComplete (IsLocalRing.maximalIdeal R) R ∧
    ringKrullDim R = 3 ∧
    Function.Bijective (algebraMap ℂ (IsLocalRing.ResidueField R)) ∧
    ∀ (M : Type) [AddCommGroup M] [Module R M],
      Nontrivial M → Module.Finite R M → localDepth R M ≠ 3

end SmallCM

namespace SmallCM
/-! Finite depth is attained by a regular sequence and cannot exceed dimension. -/
section Depth

variable {R M : Type*} [CommRing R] [IsLocalRing R]
  [AddCommGroup M] [Module R M]

lemma regular_length_le_localDepth (rs : List R)
    (hm : ∀ x ∈ rs, x ∈ IsLocalRing.maximalIdeal R)
    (hr : RingTheory.Sequence.IsRegular M rs) :
    (rs.length : ℕ∞) ≤ localDepth R M :=
  le_sSup ⟨rs, hm, hr, rfl⟩

/-- Finite positive depth is attained, not merely approached by sequence lengths. -/
lemma exists_regularSequence_of_localDepth_eq {n : ℕ}
    (hdepth : localDepth R M = (n + 1 : ℕ)) :
    ∃ rs : List R, (∀ x ∈ rs, x ∈ IsLocalRing.maximalIdeal R) ∧
      RingTheory.Sequence.IsRegular M rs ∧ rs.length = n + 1 := by
  have hlt : (n : ℕ∞) < localDepth R M := by rw [hdepth]; exact_mod_cast Nat.lt_succ_self n
  obtain ⟨a, ⟨rs, hm, hr, rfl⟩, hlen⟩ := lt_sSup_iff.mp hlt
  have hle := regular_length_le_localDepth rs hm hr
  rw [hdepth] at hle
  have hlower : n < rs.length := by exact_mod_cast hlen
  have hupper : rs.length ≤ n + 1 := by exact_mod_cast hle
  exact ⟨rs, hm, hr, by omega⟩

/-- A regular sequence in a finite module over a Noetherian local ring has
length at most the ring dimension. -/
lemma regular_length_le_dimension [IsNoetherianRing R] [Module.Finite R M]
    (rs : List R) (hr : RingTheory.Sequence.IsRegular M rs) :
    (rs.length : WithBot ℕ∞) ≤ ringKrullDim R := by
  let := hr.quot_ofList_smul_nontrivial (⊤ : Submodule R M)
  have hn := Module.supportDim_ne_bot_of_nontrivial R
    (M ⧸ Ideal.ofList rs • (⊤ : Submodule R M))
  obtain ⟨d, hd⟩ := WithBot.ne_bot_iff_exists.mp hn
  have hnonneg : 0 ≤ Module.supportDim R
      (M ⧸ Ideal.ofList rs • (⊤ : Submodule R M)) := by
    rw [← hd]
    exact WithBot.coe_le_coe.mpr (bot_le : (0 : ℕ∞) ≤ d)
  calc
    (rs.length : WithBot ℕ∞) ≤ Module.supportDim R
        (M ⧸ Ideal.ofList rs • (⊤ : Submodule R M)) + rs.length :=
      le_add_of_nonneg_left hnonneg
    _ = Module.supportDim R M := Module.supportDim_add_length_eq_supportDim_of_isRegular rs hr
    _ ≤ ringKrullDim R := Module.supportDim_le_ringKrullDim R M

lemma localDepth_le_of_dimension_eq [IsNoetherianRing R] [Module.Finite R M]
    {d : ℕ} (hdim : ringKrullDim R = d) : localDepth R M ≤ d := by
  apply sSup_le
  rintro a ⟨rs, _, hr, rfl⟩
  have h := regular_length_le_dimension rs hr
  rw [hdim] at h
  exact_mod_cast h

/-- In dimension three, excluding depth three is equivalent to excluding
regular sequences of length three. -/
lemma localDepth_eq_three_iff [IsNoetherianRing R] [Module.Finite R M]
    (hdim : ringKrullDim R = 3) :
    localDepth R M = 3 ↔ ∃ rs : List R,
      (∀ x ∈ rs, x ∈ IsLocalRing.maximalIdeal R) ∧
      RingTheory.Sequence.IsRegular M rs ∧ rs.length = 3 := by
  constructor
  · intro h
    exact exists_regularSequence_of_localDepth_eq (n := 2) h
  · rintro ⟨rs, hm, hr, hlen⟩
    apply le_antisymm (localDepth_le_of_dimension_eq (d := 3) hdim)
    simpa [hlen] using regular_length_le_localDepth rs hm hr

end Depth


open IsLocalRing

lemma exists_regular_outside_maximalSquare
    {R M : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M] [Nontrivial M]
    (hr : ∃ r ∈ maximalIdeal R, IsSMulRegular M r) :
    ∃ x ∈ maximalIdeal R, x ∉ (maximalIdeal R)^2 ∧ IsSMulRegular M x := by
  classical
  let m := maximalIdeal R
  have hmnot : ¬ m ≤ m^2 := by
    intro hle
    have hmzero : m = ⊥ := Submodule.eq_bot_of_le_smul_of_le_jacobson_bot
      m m (IsNoetherian.noetherian _) (by simpa [pow_two, Ideal.smul_eq_mul] using hle)
      (maximalIdeal_le_jacobson _)
    obtain ⟨r, hrm, hreg⟩ := hr
    have hr0 : r = 0 := by simpa [← show m = maximalIdeal R from rfl, hmzero] using hrm
    have hall (x : M) : x = 0 := hreg (by simp [hr0])
    exact not_subsingleton M ⟨fun x y => (hall x).trans (hall y).symm⟩
  by_contra! hn
  have hsub : (m : Set R) ⊆ ⋃ I ∈ insert (m^2) (associatedPrimes R M), (I : Set R) := by
    intro x hxm
    by_cases hx : x ∈ m^2
    · exact Set.mem_iUnion.mpr ⟨m^2, Set.mem_iUnion.mpr ⟨Set.mem_insert _ _, hx⟩⟩
    · have hnot : ¬ IsSMulRegular M x := hn x hxm hx
      have hxAss : x ∈ ⋃ I ∈ associatedPrimes R M, (I : Set R) := by
        rw [biUnion_associatedPrimes_eq_compl_regular]
        exact hnot
      obtain ⟨I, hI, hxI⟩ := Set.mem_iUnion₂.mp hxAss
      exact Set.mem_iUnion₂.mpr ⟨I, Set.mem_insert_of_mem _ hI, hxI⟩
  have hprime : ∀ I ∈ insert (m^2) (associatedPrimes R M),
      I ≠ m^2 → I ≠ m^2 → I.IsPrime := by
    intro I hI hne _
    exact IsAssociatedPrime.isPrime ((Set.mem_insert_iff.mp hI).resolve_left hne)
  obtain ⟨I, hI, hle⟩ :=
    (Ideal.subset_union_prime_finite ((associatedPrimes.finite R M).insert (m^2))
      (m^2) (m^2) hprime).mp hsub
  rcases Set.mem_insert_iff.mp hI with rfl | hI
  · exact hmnot hle
  · obtain ⟨r, hrm, hreg⟩ := hr
    have hbad : r ∈ ⋃ J ∈ associatedPrimes R M, (J : Set R) :=
      Set.mem_iUnion₂.mpr ⟨I, hI, hle hrm⟩
    rw [biUnion_associatedPrimes_eq_compl_regular] at hbad
    exact hbad hreg


open IsLocalRing RingTheory.Sequence CategoryTheory Abelian Limits

universe u

lemma ext_vanishing_after_regular_quotient {R : Type u} [CommRing R]
    (M N : ModuleCat.{u} R) (x : R) (hx : IsSMulRegular M x) (n : ℕ)
    (hExt : ∀ i < n + 1, Subsingleton (Ext N M i)) :
    ∀ i < n, Subsingleton (Ext N (ModuleCat.of R (QuotSMulTop x M)) i) := by
  intro i hi
  have zero1 := AddCommGrpCat.isZero_of_iff_subsingleton.mpr (hExt i (by omega))
  have zero2 := AddCommGrpCat.isZero_of_iff_subsingleton.mpr (hExt (i+1) (by omega))
  exact AddCommGrpCat.subsingleton_of_isZero <| ShortComplex.Exact.isZero_of_both_zeros
    ((Ext.covariant_sequence_exact₃' N hx.smulShortComplex_shortExact) i (i+1) rfl)
    (zero1.eq_zero_of_src _) (zero2.eq_zero_of_tgt _)

/-- Quotienting by any regular element in the maximal ideal loses at most one
in regular-sequence depth. This is the bridge needed when replacing a parameter
by one outside the square of the maximal ideal. -/
lemma regular_sequence_after_quotient
    {R M : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M] [Nontrivial M]
    (rs : List R) (hmem : ∀ r ∈ rs, r ∈ maximalIdeal R)
    (hreg : IsRegular M rs) (n : ℕ) (hlen : n + 1 ≤ rs.length)
    (x : R) (hxm : x ∈ maximalIdeal R) (hx : IsSMulRegular M x) :
    ∃ ts : List R, ts.length = n ∧ (∀ t ∈ ts, t ∈ maximalIdeal R) ∧
      IsRegular (QuotSMulTop x M) ts := by
  let M' := ModuleCat.of R M
  let N := ModuleCat.of R (ResidueField R)
  have hNsupp : Module.support R N = PrimeSpectrum.zeroLocus (maximalIdeal R) := by
    rw [Module.support_eq_zeroLocus]
    change PrimeSpectrum.zeroLocus (↑(Module.annihilator R (R ⧸ maximalIdeal R)) : Set R) = _
    rw [Ideal.annihilator_quotient]
  have hm_lt : maximalIdeal R • (⊤ : Submodule R M) < ⊤ :=
    (Submodule.top_ne_ideal_smul_of_le_jacobson_annihilator
      (maximalIdeal_le_jacobson (Module.annihilator R M))).symm.lt_top
  have hExt := ModuleCat.subsingleton_ext_of_exists_isRegular (maximalIdeal R)
    N hNsupp.le M' hm_lt rs hmem hreg
  have hExt' := ext_vanishing_after_regular_quotient M' N x hx n
    (fun i hi => hExt i (hi.trans_le hlen))
  have : Nontrivial (QuotSMulTop x M) := Submodule.Quotient.nontrivial_iff.mpr <|
    (Submodule.top_ne_pointwise_smul_of_mem_jacobson_annihilator
      (maximalIdeal_le_jacobson (Module.annihilator R M) hxm)).symm
  have hmQ_lt : maximalIdeal R • (⊤ : Submodule R (QuotSMulTop x M)) < ⊤ :=
    (Submodule.top_ne_ideal_smul_of_le_jacobson_annihilator
      (maximalIdeal_le_jacobson (Module.annihilator R (QuotSMulTop x M)))).symm.lt_top
  exact ModuleCat.exists_isRegular_of_exists_subsingleton_ext (maximalIdeal R) n
    (ModuleCat.of R (QuotSMulTop x M)) hmQ_lt N hNsupp hExt'


open IsLocalRing
open scoped BigOperators

lemma quotient_generators_drop
    {R : Type*} [CommRing R] [IsLocalRing R] {n : ℕ}
    (v : Fin (n+1) → R) (hv : Ideal.span (Set.range v) = maximalIdeal R)
    (x : R) (_hxm : x ∈ maximalIdeal R) (hx : x ∉ (maximalIdeal R)^2) :
    ∃ w : Fin n → R ⧸ Ideal.span {x},
      Ideal.span (Set.range w) = Ideal.map (Ideal.Quotient.mk _) (maximalIdeal R) := by
  classical
  have hxspan : x ∈ Submodule.span R (Set.range v) := by
    change x ∈ Ideal.span (Set.range v)
    rwa [hv]
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun R).mp hxspan
  have hai : ∃ i, IsUnit (a i) := by
    by_contra! hnot
    have hm : ∀ i, a i ∈ maximalIdeal R := fun i => (mem_maximalIdeal _).mpr (hnot i)
    apply hx
    rw [← ha]
    exact Ideal.sum_mem _ (fun i _ => by
      change a i * v i ∈ (maximalIdeal R)^2
      rw [pow_two]
      exact Ideal.mul_mem_mul (hm i) (hv ▸ Ideal.subset_span (Set.mem_range_self i)))
  obtain ⟨i, hi⟩ := hai
  let f := Ideal.Quotient.mk (Ideal.span {x})
  let w : Fin n → R ⧸ Ideal.span {x} := fun j => f (v (i.succAbove j))
  use w
  let I : Ideal (R ⧸ Ideal.span {x}) := Ideal.span (Set.range w)
  have hvI : ∀ j, j ≠ i → f (v j) ∈ I := by
    intro j hj
    obtain ⟨k, rfl⟩ := (Fin.eq_self_or_eq_succAbove i j).resolve_left hj
    exact Ideal.subset_span (Set.mem_range_self k)
  have hiI : f (v i) ∈ I := by
    have hsum : (∑ j, f (a j) * f (v j)) = 0 := by
      simp_rw [← map_mul]
      rw [← map_sum]
      change f (∑ j, a j * v j) = 0
      rw [show (∑ j, a j * v j) = x from ha]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
    have hother : (∑ j ∈ Finset.univ.erase i, f (a j) * f (v j)) ∈ I :=
      Ideal.sum_mem I (fun j hj => I.mul_mem_left _ (hvI j (Finset.mem_erase.mp hj).1))
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)] at hsum
    have hprod : f (a i) * f (v i) ∈ I := by
      rw [eq_neg_of_add_eq_zero_right hsum]
      exact I.neg_mem hother
    rcases hi.map f with ⟨u, hu⟩
    rw [← hu] at hprod
    simpa [← mul_assoc] using I.mul_mem_left (↑u⁻¹) hprod
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro _ ⟨j, rfl⟩
    exact Ideal.mem_map_of_mem _ (hv ▸ Ideal.subset_span (Set.mem_range_self _))
  · rw [← hv, Ideal.map_span, ← Set.range_comp]
    apply Ideal.span_le.mpr
    rintro _ ⟨j, rfl⟩
    by_cases hj : j = i
    · subst j; exact hiI
    · exact hvI j hj

open RingTheory.Sequence


/-- A finite module whose regular-sequence depth is at least the number of
specified generators of the maximal ideal is free. -/
lemma free_of_regular_length_le_generators
    (n : ℕ) {R M : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M] [Nontrivial M]
    (v : Fin n → R) (hv : Ideal.span (Set.range v) = maximalIdeal R)
    (rs : List R) (hmem : ∀ r ∈ rs, r ∈ maximalIdeal R)
    (hreg : IsRegular M rs) (hlen : n ≤ rs.length) : Module.Free R M := by
  induction n generalizing R M with
  | zero =>
    have hm : maximalIdeal R = ⊥ := by rw [← hv]; simp
    let := (isField_iff_maximalIdeal_eq.mpr hm).toField
    infer_instance
  | succ n ih =>
    have hr : ∃ r ∈ maximalIdeal R, IsSMulRegular M r := by
      cases rs with
      | nil => simp at hlen
      | cons r ss =>
        exact ⟨r, hmem r (by simp), (isRegular_cons_iff M r ss).mp hreg |>.1⟩
    obtain ⟨x, hxm, hxsq, hx⟩ := exists_regular_outside_maximalSquare hr
    let R' := R ⧸ Ideal.span {x}
    let Q := QuotSMulTop x M
    have hproper : Ideal.span {x} ≠ ⊤ := by
      intro htop
      have hle : Ideal.span {x} ≤ maximalIdeal R := by simpa using hxm
      rw [htop] at hle
      exact (maximalIdeal.isMaximal R).ne_top (top_le_iff.mp hle)
    let : Nontrivial R' := Ideal.Quotient.nontrivial_iff.mpr hproper
    let : IsLocalRing R' := IsLocalRing.of_surjective' _ Ideal.Quotient.mk_surjective
    let : Module.Finite R' Q := Module.Finite.of_restrictScalars_finite R _ _
    let : Nontrivial Q := nontrivial_quotSMulTop_of_mem_maximalIdeal M hxm
    obtain ⟨w, hw⟩ := quotient_generators_drop v hv x hxm hxsq
    have hw' : Ideal.span (Set.range w) = maximalIdeal R' := hw.trans
      (map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective)
    obtain ⟨ts, hlen', hmem', hreg'⟩ := regular_sequence_after_quotient rs hmem hreg n hlen x hxm hx
    have hqmem : ∀ r ∈ ts.map (Ideal.Quotient.mk (Ideal.span {x})),
        r ∈ maximalIdeal R' := by
      intro r hr
      obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hr
      rw [← map_maximalIdeal_of_surjective (Ideal.Quotient.mk (Ideal.span {x}))
        Ideal.Quotient.mk_surjective]
      exact Ideal.mem_map_of_mem _ (hmem' t ht)
    have hqreg : IsRegular Q (ts.map (Ideal.Quotient.mk (Ideal.span {x}))) :=
      IsRegular.of_isWeaklyRegular_of_mem_maximalIdeal Q hqmem
        ((isWeaklyRegular_map_algebraMap_iff R' Q ts).mpr hreg'.toIsWeaklyRegular)
    have hfree := ih w hw' _ hqmem hqreg (by simp [hlen'])
    have := Module.finitePresentation_of_finite R M
    exact (Module.free_quotSMulTop_iff_free R M
      ((maximalIdeal_le_jacobson (⊥ : Ideal R)) hxm) hx).mp hfree


lemma exists_regular_from_mapped_radical
    {A R M : Type*} [CommRing A] [CommRing R] [Algebra A R]
    [IsNoetherianRing R] [AddCommGroup M] [Module R M] [Module.Finite R M]
    (I : Ideal A) (r : R) (hr : r ∈ (I.map (algebraMap A R)).radical)
    (hreg : IsSMulRegular M r) :
    ∃ a ∈ I, IsSMulRegular M (algebraMap A R a) := by
  classical
  let s := Ideal.comap (algebraMap A R) '' associatedPrimes R M
  have hs : s.Finite := (associatedPrimes.finite R M).image _
  have hprime : ∀ J ∈ s, J.IsPrime := by
    rintro J ⟨P, hP, rfl⟩
    let : P.IsPrime := IsAssociatedPrime.isPrime hP
    infer_instance
  by_contra! hnone
  have hsub : (I : Set A) ⊆ ⋃ J ∈ s, (J : Set A) := by
    intro a ha
    have hbad : algebraMap A R a ∈ ⋃ P ∈ associatedPrimes R M, (P : Set R) := by
      rw [biUnion_associatedPrimes_eq_compl_regular]
      exact hnone a ha
    obtain ⟨P, hP, haP⟩ := Set.mem_iUnion₂.mp hbad
    exact Set.mem_iUnion₂.mpr ⟨P.comap (algebraMap A R), ⟨P, hP, rfl⟩, haP⟩
  obtain ⟨J, hJ, hIJ⟩ := (Ideal.subset_union_prime_finite hs (⊤ : Ideal A) ⊤
    (fun J hJ _ _ => hprime J hJ)).mp hsub
  obtain ⟨P, hP, rfl⟩ := hJ
  have hmap : I.map (algebraMap A R) ≤ P := Ideal.map_le_iff_le_comap.mpr hIJ
  have hrP : r ∈ P := by
    have hp : P.IsPrime := IsAssociatedPrime.isPrime hP
    simpa [hp.radical] using (Ideal.radical_mono hmap hr)
  have hbad : r ∈ ⋃ Q ∈ associatedPrimes R M, (Q : Set R) :=
    Set.mem_iUnion₂.mpr ⟨P, hP, hrP⟩
  rw [biUnion_associatedPrimes_eq_compl_regular] at hbad
  exact hbad hreg

open RingTheory.Sequence IsLocalRing

lemma regular_sequence_change_scalars
    {A R : Type u} [CommRing A] [CommRing R] [IsLocalRing A] [IsLocalRing R]
    [Algebra A R] [IsNoetherianRing R]
    (hrad : (Ideal.map (algebraMap A R) (maximalIdeal A)).radical = maximalIdeal R)
    (n : ℕ) {M : Type u} [AddCommGroup M] [Module A M] [Module R M]
    [IsScalarTower A R M] [Module.Finite R M] [Nontrivial M]
    (rs : List R) (hmem : ∀ r ∈ rs, r ∈ maximalIdeal R)
    (hreg : IsRegular M rs) (hlen : n ≤ rs.length) :
    ∃ ts : List A, ts.length = n ∧ (∀ t ∈ ts, t ∈ maximalIdeal A) ∧
      IsRegular M (ts.map (algebraMap A R)) := by
  induction n generalizing M rs with
  | zero => exact ⟨[], rfl, by simp, IsRegular.nil R M⟩
  | succ n ih =>
    have hr : ∃ r ∈ maximalIdeal R, IsSMulRegular M r := by
      cases rs with
      | nil => simp at hlen
      | cons r ss =>
        exact ⟨r, hmem r (by simp), (isRegular_cons_iff M r ss).mp hreg |>.1⟩
    obtain ⟨r, hrm, hrreg⟩ := hr
    obtain ⟨a, ham, hareg⟩ := exists_regular_from_mapped_radical (maximalIdeal A) r
      (hrad ▸ hrm) hrreg
    have harm : algebraMap A R a ∈ maximalIdeal R := by
      rw [← hrad]
      exact Ideal.le_radical (Ideal.mem_map_of_mem _ ham)
    let : Nontrivial (QuotSMulTop (algebraMap A R a) M) :=
      nontrivial_quotSMulTop_of_mem_maximalIdeal M harm
    obtain ⟨us, hulen, humem, hureg⟩ :=
      regular_sequence_after_quotient rs hmem hreg n hlen (algebraMap A R a) harm hareg
    obtain ⟨ts, htlen, htmem, htreg⟩ := ih us humem hureg (by omega)
    exact ⟨a :: ts, by simp [htlen], by simpa using And.intro ham htmem,
      by simpa only [List.map_cons] using IsRegular.cons hareg htreg⟩

lemma regular_sequence_change_scalars_source
    {A R : Type u} [CommRing A] [CommRing R] [IsLocalRing A] [IsLocalRing R]
    [Algebra A R] [IsNoetherianRing R]
    (hrad : (Ideal.map (algebraMap A R) (maximalIdeal A)).radical = maximalIdeal R)
    (n : ℕ) {M : Type u} [AddCommGroup M] [Module A M] [Module R M]
    [IsScalarTower A R M] [Module.Finite R M] [Module.Finite A M] [Nontrivial M]
    (rs : List R) (hmem : ∀ r ∈ rs, r ∈ maximalIdeal R)
    (hreg : IsRegular M rs) (hlen : n ≤ rs.length) :
    ∃ ts : List A, ts.length = n ∧ (∀ t ∈ ts, t ∈ maximalIdeal A) ∧
      IsRegular M ts := by
  obtain ⟨ts, hlen, hmem, hreg⟩ := regular_sequence_change_scalars hrad n rs hmem hreg hlen
  exact ⟨ts, hlen, hmem, IsRegular.of_isWeaklyRegular_of_mem_maximalIdeal M hmem
    ((isWeaklyRegular_map_algebraMap_iff R M ts).mp hreg.toIsWeaklyRegular)⟩
/-- A sufficiently deep finite module is free over a local base whose maximal ideal is generated by the given number of parameters. -/
theorem free_over_finite_local_base
    {A R M : Type u} [CommRing A] [CommRing R] [IsLocalRing A] [IsLocalRing R]
    [Algebra A R] [IsNoetherianRing A] [IsNoetherianRing R] [Module.Finite A R]
    [AddCommGroup M] [Module A M] [Module R M] [IsScalarTower A R M]
    [Module.Finite R M] [Nontrivial M]
    (hrad : (Ideal.map (algebraMap A R) (maximalIdeal A)).radical = maximalIdeal R)
    (n : ℕ) (v : Fin n → A) (hv : Ideal.span (Set.range v) = maximalIdeal A)
    (rs : List R) (hmem : ∀ r ∈ rs, r ∈ maximalIdeal R)
    (hreg : IsRegular M rs) (hlen : n ≤ rs.length) : Module.Free A M := by
  let : Module.Finite A M := Module.Finite.trans R M
  obtain ⟨ts, htslen, htsmem, htsreg⟩ :=
    regular_sequence_change_scalars_source hrad n rs hmem hreg hlen
  exact free_of_regular_length_le_generators n v hv ts htsmem htsreg htslen.ge


open IsLocalRing

lemma radical_map_maximalIdeal_of_integral
    {A R : Type*} [CommRing A] [CommRing R] [IsLocalRing A] [IsLocalRing R]
    [Algebra A R] [Algebra.IsIntegral A R] :
    (Ideal.map (algebraMap A R) (maximalIdeal A)).radical = maximalIdeal R := by
  have hcomap : (maximalIdeal R).comap (algebraMap A R) = maximalIdeal A :=
    eq_maximalIdeal (Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := A) (maximalIdeal R))
  have hle : Ideal.map (algebraMap A R) (maximalIdeal A) ≤ maximalIdeal R :=
    Ideal.map_le_iff_le_comap.mpr hcomap.symm.le
  apply le_antisymm
  · exact (maximalIdeal.isMaximal R).isPrime.radical_le_iff.mpr hle
  · rw [Ideal.radical_eq_sInf]
    apply le_sInf
    intro P hP
    let : P.IsPrime := hP.2
    have hAP : (maximalIdeal A) ≤ P.comap (algebraMap A R) :=
      Ideal.map_le_iff_le_comap.mp hP.1
    have hAPeq : P.comap (algebraMap A R) = maximalIdeal A :=
      (maximalIdeal.isMaximal A).eq_of_le (Ideal.IsPrime.ne_top inferInstance) hAP |>.symm
    have hPmax : P.IsMaximal := Ideal.isMaximal_of_isIntegral_of_isMaximal_under (R := A) (S := R) P
      (by
        change (P.comap (algebraMap A R)).IsMaximal
        rw [hAPeq]
        exact maximalIdeal.isMaximal A)
    exact (eq_maximalIdeal hPmax).symm.le

/-- The completed-cone module is free over the *actual* three-dimensional
power-series base, once the finite algebra structure has been constructed.
No grading of the module, and no prescribed regular parameter sequence, is
assumed. This closes the local-algebra step in the manuscript, lines 303–309. -/
theorem free_over_powerSeries_of_depth_three
    {R M : Type} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [Algebra (MvPowerSeries (Fin 3) ℂ) R] [Module.Finite (MvPowerSeries (Fin 3) ℂ) R]
    [AddCommGroup M] [Module R M] [Module (MvPowerSeries (Fin 3) ℂ) M]
    [IsScalarTower (MvPowerSeries (Fin 3) ℂ) R M]
    [Module.Finite R M] [Nontrivial M] (hdepth : localDepth R M = 3) :
    Module.Free (MvPowerSeries (Fin 3) ℂ) M := by
  obtain ⟨rs, hmem, hreg, hlen⟩ := exists_regularSequence_of_localDepth_eq (n := 2) hdepth
  exact free_over_finite_local_base radical_map_maximalIdeal_of_integral 3
    MvPowerSeries.X mvPowerSeries_vars_eq_maximal rs hmem hreg hlen.ge

end SmallCM

namespace ExplicitCone
noncomputable def parameterHom : MvPowerSeries (Fin 3) ℂ →ₐ[ℂ] completedRing :=
  exists_finite_injective_completed_parameters.choose

lemma parameterHom_injective : Function.Injective parameterHom :=
  exists_finite_injective_completed_parameters.choose_spec.1

lemma parameterHom_finite : parameterHom.Finite :=
  exists_finite_injective_completed_parameters.choose_spec.2

noncomputable instance completedRing_parameterAlgebra :
    Algebra (MvPowerSeries (Fin 3) ℂ) completedRing := parameterHom.toRingHom.toAlgebra

instance completedRing_parameterFinite :
    Module.Finite (MvPowerSeries (Fin 3) ℂ) completedRing := parameterHom_finite

instance completedRing_parameterTower :
    IsScalarTower ℂ (MvPowerSeries (Fin 3) ℂ) completedRing :=
  IsScalarTower.of_algebraMap_eq (fun a => (parameterHom.commutes a).symm)

instance completedRing_parameterFaithful :
    FaithfulSMul (MvPowerSeries (Fin 3) ℂ) completedRing :=
  (faithfulSMul_iff_algebraMap_injective _ _).mpr parameterHom_injective

/-- No extra structure or condition on M is assumed: scalar restriction is
canonical, through the actual finite injective normalization map. -/
theorem module_free_from_depth_three (M : Type) [AddCommGroup M]
    [Module completedRing M] [Module.Finite completedRing M] [Nontrivial M]
    (hdepth : SmallCM.localDepth completedRing M = 3) :
    letI := Module.restrictScalars (MvPowerSeries (Fin 3) ℂ) completedRing M
    Module.Free (MvPowerSeries (Fin 3) ℂ) M := by
  let := Module.restrictScalars (MvPowerSeries (Fin 3) ℂ) completedRing M
  let : IsScalarTower (MvPowerSeries (Fin 3) ℂ) completedRing M :=
    IsScalarTower.restrictScalars (MvPowerSeries (Fin 3) ℂ) completedRing M
  exact SmallCM.free_over_powerSeries_of_depth_three (R := completedRing) hdepth
end ExplicitCone


namespace SmallCM
variable {A R M : Type*} [CommRing A] [IsDomain A]
    [CommRing R] [IsDomain R] [Algebra A R] [Algebra.IsAlgebraic A R]
    [AddCommGroup M] [Module A M] [Module R M] [IsScalarTower A R M]

lemma torsionFree_of_algebraic [Module.IsTorsionFree A M] : Module.IsTorsionFree R M where
  isSMulRegular r hr := by
    have hr0 : r ≠ 0 := isRegular_iff_ne_zero.mp hr
    obtain ⟨a, ha, s, hs⟩ := (Algebra.IsAlgebraic.isAlgebraic (R := A) r).exists_nonzero_dvd
      (mem_nonZeroDivisors_of_ne_zero hr0)
    intro m n hmn
    change r • m = r • n at hmn
    apply (IsSMulRegular.of_ne_zero (M := M) ha)
    change a • m = a • n
    rw [← IsScalarTower.algebraMap_smul R a m, ← IsScalarTower.algebraMap_smul R a n,
      hs, mul_comm r s, mul_smul, mul_smul, hmn]
end SmallCM

namespace SmallCM
lemma support_eq_univ_of_torsionFree {R M : Type*} [CommRing R] [IsDomain R]
    [AddCommGroup M] [Module R M] [Module.IsTorsionFree R M] [Nontrivial M]
    [Module.Finite R M] : Module.support R M = Set.univ := by
  obtain ⟨m, hm⟩ := exists_ne (0 : M)
  have ha : Module.annihilator R M = ⊥ := by
    apply le_antisymm _ bot_le
    intro a ha
    change a = 0
    exact (smul_eq_zero.mp (Module.mem_annihilator.mp ha m)).resolve_right hm
  rw [Module.support_eq_zeroLocus, ha, PrimeSpectrum.zeroLocus_bot]
end SmallCM

namespace ExplicitCone
/-- Every hypothetical small CM module for the actual ring has full support
and positive generic rank. This uses no grading or algebra structure on M. -/
theorem module_properties_from_depth_three (M : Type) [AddCommGroup M]
    [Module completedRing M] [Module.Finite completedRing M] [Nontrivial M]
    (hdepth : SmallCM.localDepth completedRing M = 3) :
    Module.IsTorsionFree completedRing M ∧
      0 < Module.finrank completedRing M ∧ Module.support completedRing M = Set.univ := by
  let : IsDomain (MvPowerSeries (Fin 3) ℂ) := NoZeroDivisors.to_isDomain _
  let := Module.restrictScalars (MvPowerSeries (Fin 3) ℂ) completedRing M
  let : IsScalarTower (MvPowerSeries (Fin 3) ℂ) completedRing M :=
    IsScalarTower.restrictScalars (MvPowerSeries (Fin 3) ℂ) completedRing M
  let : Module.Free (MvPowerSeries (Fin 3) ℂ) M := module_free_from_depth_three M hdepth
  let : Module.IsTorsionFree completedRing M :=
    SmallCM.torsionFree_of_algebraic (A := MvPowerSeries (Fin 3) ℂ)
  exact ⟨inferInstance, Module.finrank_pos, SmallCM.support_eq_univ_of_torsionFree⟩
end ExplicitCone

end

end OAI
