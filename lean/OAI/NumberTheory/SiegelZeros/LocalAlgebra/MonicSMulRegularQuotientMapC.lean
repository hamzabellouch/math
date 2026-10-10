import Mathlib
import PrimeNumberTheoremAnd.SiegelZeros.HadamardSupport

namespace OAI

namespace SiegelZeros


open Polynomial

namespace WeightedTorusJets

theorem monic_isSMulRegular_quotient_map_C {A : Type*} [CommRing A]
    (I : Ideal A) {y : A[X]} (hy : y.Monic) :
    IsSMulRegular (A[X] ⧸ I.map (Polynomial.C : A →+* A[X])) y := by
  let e := I.polynomialQuotientEquivQuotientPolynomial.symm
  apply (e.toEquiv.isSMulRegular_congr (r := y)
    (s := y.map (Ideal.Quotient.mk I)) ?_).mpr
  · exact (hy.map (Ideal.Quotient.mk I)).isRegular.left
  · intro z
    change e (Ideal.Quotient.mk _ y * z) = y.map (Ideal.Quotient.mk I) * e z
    rw [map_mul]
    congr 1



open Ideal IsLocalRing Polynomial RingTheory.Sequence

theorem exists_regular_generators_polynomial_localization
    {A : Type*} [CommRing A] [IsLocalRing A]
    (rs : List A) (hreg : IsRegular A rs) (hgen : Ideal.ofList rs = maximalIdeal A)
    (p : Ideal A[X]) [p.IsPrime] (hclosed : p.comap Polynomial.C = maximalIdeal A) :
    ∃ ss : List (Localization.AtPrime p),
      IsRegular (Localization.AtPrime p) ss ∧
        Ideal.ofList ss = maximalIdeal (Localization.AtPrime p) := by
  let S := Localization.AtPrime p
  let rsC := rs.map (Polynomial.C : A →+* A[X])
  let q := (maximalIdeal A).map (Polynomial.C : A →+* A[X])
  have hweak : IsWeaklyRegular A[X] rsC := by
    simpa only [Polynomial.algebraMap_eq] using
      hreg.toIsWeaklyRegular.of_flat (S := A[X])
  have hgenC : Ideal.ofList rsC = q := by
    rw [show rsC = rs.map (Polynomial.C : A →+* A[X]) from rfl,
      ← Ideal.map_ofList, hgen]
  have hqle : q ≤ p := by
    simpa only [q, ← hclosed] using (Ideal.map_comap_le : (p.comap C).map C ≤ p)
  by_cases hpq : p = q
  · refine ⟨rsC.map (algebraMap A[X] S),
      hweak.isRegular_of_isLocalization_of_mem S p (fun r hr => ?_), ?_⟩
    · apply hqle
      rw [← hgenC]
      exact Ideal.subset_span hr
    · rw [← Ideal.map_ofList, hgenC, ← hpq, Localization.AtPrime.map_eq_maximalIdeal]
  · have hm : (p.comap C).IsMaximal := by
      rw [hclosed]
      infer_instance
    obtain ⟨y, hy, hpy⟩ := Polynomial.exists_monic_span_sup_map_eq A p hm
      (by simpa only [hclosed] using hpq)
    have hgens : Ideal.ofList (rsC ++ [y]) = p := by
      rw [Ideal.ofList_append, Ideal.ofList_singleton, hgenC]
      simpa only [q, hclosed] using hpy.symm
    have hweak' : IsWeaklyRegular A[X] (rsC ++ [y]) := by
      rw [isWeaklyRegular_append_iff, isWeaklyRegular_singleton_iff]
      refine ⟨hweak, ?_⟩
      rw [Ideal.smul_eq_mul, Ideal.mul_top, hgenC]
      exact monic_isSMulRegular_quotient_map_C (maximalIdeal A) hy
    refine ⟨(rsC ++ [y]).map (algebraMap A[X] S),
      hweak'.isRegular_of_isLocalization_of_mem S p (fun r hr => ?_), ?_⟩
    · rw [← hgens]
      exact Ideal.subset_span hr
    · rw [← Ideal.map_ofList, hgens, Localization.AtPrime.map_eq_maximalIdeal]

end WeightedTorusJets

open Ideal RingTheory.Sequence IsLocalRing

namespace WeightedTorusJets

theorem regular_maximal_generators_of_ringEquiv {R S : Type*} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S] (e : R ≃+* S) {rs : List R}
    (hreg : IsRegular R rs) (hgen : Ideal.ofList rs = maximalIdeal R) :
    IsRegular S (rs.map e) ∧ Ideal.ofList (rs.map e) = maximalIdeal S := by
  constructor
  · apply (e.toAddEquiv.isRegular_congr ?_).mp hreg
    exact List.forall₂_map_right_iff.mpr <|
      List.forall₂_same.mpr fun r _ z ↦ e.map_mul r z
  · change Ideal.ofList (rs.map e.toRingHom) = maximalIdeal S
    rw [← Ideal.map_ofList, hgen]
    exact map_ringEquiv_maximalIdeal e

theorem exists_regular_maximal_generators_field_localization (K : Type*) [Field K]
    (p : Ideal K) [p.IsPrime] :
    ∃ rs : List (Localization.AtPrime p), IsRegular (Localization.AtPrime p) rs ∧
      Ideal.ofList rs = maximalIdeal (Localization.AtPrime p) := by
  refine ⟨[], IsRegular.nil _ _, ?_⟩
  have hmap : p.map (algebraMap K (Localization.AtPrime p)) = ⊥ := by
    exact (congrArg (Ideal.map (algebraMap K (Localization.AtPrime p)))
      (Ideal.eq_bot_of_prime p)).trans Ideal.map_bot
  rw [← Localization.AtPrime.map_eq_maximalIdeal, hmap]
  simp

theorem exists_regular_maximal_generators_localizations_of_ringEquiv
    {R S : Type*} [CommRing R] [CommRing S] (e : R ≃+* S)
    (hR : ∀ (p : Ideal R) [p.IsPrime],
      ∃ rs : List (Localization.AtPrime p), IsRegular (Localization.AtPrime p) rs ∧
        Ideal.ofList rs = maximalIdeal (Localization.AtPrime p))
    (p : Ideal S) [p.IsPrime] :
    ∃ rs : List (Localization.AtPrime p), IsRegular (Localization.AtPrime p) rs ∧
      Ideal.ofList rs = maximalIdeal (Localization.AtPrime p) := by
  obtain ⟨rs, hreg, hgen⟩ := hR (p.comap e)
  let E := IsLocalization.ringEquivOfRingEquiv
    (Localization.AtPrime (p.comap e)) (Localization.AtPrime p)
    e (e.map_primeCompl_comap_eq p)
  exact ⟨rs.map E, regular_maximal_generators_of_ringEquiv E hreg hgen⟩



open Ideal RingTheory.Sequence IsLocalRing Polynomial

theorem exists_regular_maximal_generators_polynomial_localizations
    {R : Type*} [CommRing R]
    (hR : ∀ (p : Ideal R) [p.IsPrime],
      ∃ rs : List (Localization.AtPrime p), IsRegular (Localization.AtPrime p) rs ∧
        Ideal.ofList rs = maximalIdeal (Localization.AtPrime p))
    (p : Ideal R[X]) [p.IsPrime] :
    ∃ rs : List (Localization.AtPrime p), IsRegular (Localization.AtPrime p) rs ∧
      Ideal.ofList rs = maximalIdeal (Localization.AtPrime p) := by
  let q := p.comap C
  let S := (Localization.AtPrime q)[X]
  let pc := Submonoid.map Polynomial.C.toMonoidHom q.primeCompl
  let : Algebra R[X] S := Polynomial.algebra R (Localization.AtPrime q)
  have : IsLocalization pc S := Polynomial.isLocalization _ _
  let pS := p.map (algebraMap R[X] S)
  have disj : Disjoint (pc : Set R[X]) (p : Set R[X]) := by
    simpa [pc, q] using! Set.disjoint_image_left.mpr
      (Set.disjoint_compl_left_iff_subset.mpr (fun _ a ↦ a))
  have : pS.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint pc _ _ ‹_› disj
  have : IsLocalization.AtPrime (Localization.AtPrime pS) p := by
    convert IsLocalization.isLocalization_isLocalization_atPrime_isLocalization pc
      (Localization.AtPrime pS) pS
    exact (IsLocalization.under_map_of_isPrime_disjoint pc _ ‹_› disj).symm
  have hclosed : comap C pS = maximalIdeal (Localization.AtPrime q) := by
    rw [← IsLocalization.map_under q.primeCompl _ (comap C pS),
      ← IsLocalization.map_under q.primeCompl _ (maximalIdeal (Localization.AtPrime q))]
    simp only [comap_comap, S, pS]
    rw [← Polynomial.algebraMap_eq (R := Localization.AtPrime q),
      ← IsScalarTower.algebraMap_eq R (Localization.AtPrime q) (Localization.AtPrime q)[X],
      IsScalarTower.algebraMap_eq R R[X] (Localization.AtPrime q)[X], ← comap_comap,
      ← Ideal.under_def R[X], IsLocalization.under_map_of_isPrime_disjoint pc _ ‹_› disj]
    simp [q, IsLocalization.AtPrime.under_maximalIdeal (Localization.AtPrime q) q]
  obtain ⟨rs, hreg, hgen⟩ := hR q
  obtain ⟨ss, hsreg, hsgen⟩ :=
    exists_regular_generators_polynomial_localization rs hreg hgen pS hclosed
  let e := (IsLocalization.algEquiv p.primeCompl
    (Localization.AtPrime pS) (Localization.AtPrime p)).toRingEquiv
  exact ⟨ss.map e, regular_maximal_generators_of_ringEquiv e hsreg hsgen⟩

theorem exists_regular_maximal_generators_mvPolynomial_localization
    (K : Type*) [Field K] (σ : Type*) [Finite σ]
    (p : Ideal (MvPolynomial σ K)) [p.IsPrime] :
    ∃ rs : List (Localization.AtPrime p), IsRegular (Localization.AtPrime p) rs ∧
      Ideal.ofList rs = maximalIdeal (Localization.AtPrime p) := by
  revert p
  induction σ using Finite.induction_empty_option with
  | of_equiv e IH =>
    exact exists_regular_maximal_generators_localizations_of_ringEquiv
      (MvPolynomial.renameEquiv K e).toRingEquiv IH
  | h_empty =>
    exact exists_regular_maximal_generators_localizations_of_ringEquiv
      (MvPolynomial.isEmptyRingEquiv K PEmpty).symm
      (exists_regular_maximal_generators_field_localization K)
  | h_option IH =>
    exact exists_regular_maximal_generators_localizations_of_ringEquiv
      (MvPolynomial.optionEquivLeft K _).toRingEquiv.symm
      (exists_regular_maximal_generators_polynomial_localizations IH)

end WeightedTorusJets

open Ideal RingTheory.Sequence
open scoped Pointwise

namespace WeightedTorusJets

theorem span_singleton_sup_eq_of_sub_mem {R : Type*} [CommRing R]
    (J : Ideal R) {a b : R} (hdiff : a - b ∈ J) :
    Ideal.span {a} ⊔ J = Ideal.span {b} ⊔ J := by
  apply le_antisymm
  · refine sup_le ((Ideal.span_singleton_le_iff_mem _).mpr ?_) le_sup_right
    exact (Submodule.sub_mem_iff_left _ (Submodule.mem_sup_left (Ideal.mem_span_singleton_self b))).mp
      (Submodule.mem_sup_right hdiff)
  · refine sup_le ((Ideal.span_singleton_le_iff_mem _).mpr ?_) le_sup_right
    exact (Submodule.sub_mem_iff_right _ (Submodule.mem_sup_left (Ideal.mem_span_singleton_self a))).mp
      (Submodule.mem_sup_right hdiff)

theorem isRegular_append_singleton_iff_sub_mem {R M : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] (rs : List R) {a b : R}
    (hdiff : a - b ∈ Ideal.ofList rs) :
    IsRegular M (rs ++ [a]) ↔ IsRegular M (rs ++ [b]) := by
  have heq : Ideal.ofList (rs ++ [a]) = Ideal.ofList (rs ++ [b]) := by
    simpa only [Ideal.ofList_append, Ideal.ofList_singleton, sup_comm] using
      span_singleton_sup_eq_of_sub_mem (Ideal.ofList rs) hdiff
  have hab : Ideal.Quotient.mk (Ideal.ofList rs) a =
      Ideal.Quotient.mk (Ideal.ofList rs) b :=
    (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr hdiff
  simp only [RingTheory.Sequence.isRegular_iff, isWeaklyRegular_append_iff' M, List.map_singleton, hab, heq]

theorem isRegular_cons_iff_sub_mem {R M : Type*} [CommRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M] [IsNoetherian R M] (rs : List R) {a b : R}
    (hdiff : a - b ∈ Ideal.ofList rs) :
    IsRegular M (a :: rs) ↔ IsRegular M (b :: rs) := by
  have hp (x : R) : IsRegular M (x :: rs) ↔ IsRegular M (rs ++ [x]) :=
    ⟨fun h => IsLocalRing.isRegular_of_perm h (List.perm_append_singleton x rs).symm,
      fun h => IsLocalRing.isRegular_of_perm h (List.perm_append_singleton x rs)⟩
  exact (hp a).trans ((isRegular_append_singleton_iff_sub_mem rs hdiff).trans (hp b).symm)

theorem exists_regular_sequence_of_mem_sup_annihilator {R M : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] (J : Ideal R) (rs : List R)
    (hmem : ∀ r ∈ rs, r ∈ J ⊔ Module.annihilator R M) (hreg : IsRegular M rs) :
    ∃ ss : List R, ss.length = rs.length ∧ (∀ s ∈ ss, s ∈ J) ∧ IsRegular M ss := by
  have hrepresent : ∃ ss : List R,
      List.Forall₂ (fun r s : R => ∀ m : M, r • m = s • m) rs ss ∧
        (∀ s ∈ ss, s ∈ J) := by
    clear hreg
    induction rs with
    | nil => exact ⟨[], .nil, by simp⟩
    | cons r rs ih =>
      obtain ⟨s, hs, a, ha, hr⟩ := Submodule.mem_sup.mp (hmem r (by simp))
      obtain ⟨ss, hss, hssmem⟩ := ih (fun z hz => hmem z (by simp [hz]))
      refine ⟨s :: ss, .cons ?_ hss, ?_⟩
      · intro m
        rw [← hr, add_smul, Module.mem_annihilator.mp ha m, add_zero]
      · intro z hz
        rcases List.mem_cons.mp hz with rfl | hz
        · exact hs
        · exact hssmem z hz
  obtain ⟨ss, hss, hssmem⟩ := hrepresent
  exact ⟨ss, hss.length_eq.symm, hssmem,
    ((AddEquiv.refl M).isRegular_congr hss).mp hreg⟩

theorem exists_regular_sequence_quotSMulTop_of_mem_sup {R M : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] (x : R) (J : Ideal R) (rs : List R)
    (hmem : ∀ r ∈ rs, r ∈ Ideal.span {x} ⊔ J)
    (hreg : IsRegular (QuotSMulTop x M) rs) :
    ∃ ss : List R, ss.length = rs.length ∧ (∀ s ∈ ss, s ∈ J) ∧
      IsRegular (QuotSMulTop x M) ss := by
  apply exists_regular_sequence_of_mem_sup_annihilator J rs _ hreg
  intro r hr
  exact (show Ideal.span {x} ⊔ J ≤ J ⊔ Module.annihilator R (QuotSMulTop x M) from
    sup_le (le_sup_of_le_right ((Ideal.span_singleton_le_iff_mem _).mpr
      (QuotSMulTop.mem_annihilator M x))) le_sup_left) (hmem r hr)

end WeightedTorusJets

open Ideal RingTheory.Sequence
open CategoryTheory Abelian

universe u

namespace WeightedTorusJets

theorem exists_regular_sequence_quotient_of_regular_element {R : Type u} [CommRing R]
    [IsNoetherianRing R] (M : ModuleCat.{u} R) [Module.Finite R M] {I : Ideal R}
    (hI : I • (⊤ : Submodule R M) < ⊤) {x : R} (hxmem : x ∈ I)
    (hx : IsSMulRegular M x) (n : ℕ) (rs : List R) (hlen : rs.length = n + 1)
    (hmem : ∀ r ∈ rs, r ∈ I) (hreg : IsRegular M rs) :
    ∃ ss : List R, ss.length = n ∧ (∀ r ∈ ss, r ∈ I) ∧
      IsRegular (QuotSMulTop x M) ss := by
  let Q := ModuleCat.of R (R ⧸ I)
  have hsupp : Module.support R Q = PrimeSpectrum.zeroLocus I := by
    rw [Module.support_eq_zeroLocus, Ideal.annihilator_quotient]
  have hext : ∀ i < n + 1, Subsingleton (Ext Q M i) := by
    intro i hi
    exact ModuleCat.subsingleton_ext_of_exists_isRegular I Q hsupp.subset M hI rs
      hmem hreg i (hi.trans_eq hlen.symm)
  have hext' : ∀ i < n, Subsingleton (Ext Q (ModuleCat.of R (QuotSMulTop x M)) i) := by
    intro i hi
    have hzero₁ := AddCommGrpCat.isZero_of_iff_subsingleton.mpr (hext i (by omega))
    have hzero₂ := AddCommGrpCat.isZero_of_iff_subsingleton.mpr (hext (i + 1) (by omega))
    exact AddCommGrpCat.subsingleton_of_isZero <|
      ShortComplex.Exact.isZero_of_both_zeros
        ((Ext.covariant_sequence_exact₃' Q hx.smulShortComplex_shortExact) i (i + 1) rfl)
        (hzero₁.eq_zero_of_src _) (hzero₂.eq_zero_of_tgt _)
  have hquot : I • (⊤ : Submodule R (QuotSMulTop x M)) ≠ ⊤ := by
    intro htop
    absurd congrArg (Submodule.comap (Submodule.mkQ _)) htop
    simpa [Submodule.comap_smul_top_of_surjective I _ (Submodule.mkQ_surjective _),
      Submodule.smul_mono_left ((span_singleton_le_iff_mem I).mpr hxmem),
      ← Submodule.ideal_span_singleton_smul] using hI.ne
  exact ModuleCat.exists_isRegular_of_exists_subsingleton_ext I n
    (ModuleCat.of R (QuotSMulTop x M)) hquot.lt_top Q hsupp hext'

end WeightedTorusJets

open scoped BigOperators

namespace WeightedTorusJets

theorem exists_add_not_mem_of_prime_antichain {R : Type*} [CommRing R]
    (s : Finset (Ideal R)) (hp : ∀ P ∈ s, P.IsPrime)
    (hanti : ∀ P ∈ s, ∀ Q ∈ s, P ≠ Q → ¬ P ≤ Q)
    (a : R) (J : Ideal R)
    (havoid : ∀ P ∈ s, ¬ (Ideal.span {a} ⊔ J ≤ P)) :
    ∃ b ∈ J, ∀ P ∈ s, a + b ∉ P := by
  classical
  have hex (P : Ideal R) (hP : P ∈ s) :
      ∃ b : R, b ∈ J ∧ (∀ Q ∈ s, Q ≠ P → b ∈ Q) ∧
        (a ∈ P → b ∉ P) ∧ (a ∉ P → b = 0) := by
    by_cases ha : a ∈ P
    · have hJ : ¬ J ≤ P := by
        intro h
        exact havoid P hP (sup_le (P.span_singleton_le_iff_mem.mpr ha) h)
      have hi : ¬ (s.erase P).inf id ≤ P := by
        rw [(hp P hP).inf_le']
        rintro ⟨Q, hQ, hQP⟩
        have hm := Finset.mem_erase.mp hQ
        exact hanti Q hm.2 P hP hm.1 hQP
      have hn : ¬ J ⊓ (s.erase P).inf id ≤ P := by
        rw [(hp P hP).inf_le]
        exact not_or.mpr ⟨hJ, hi⟩
      obtain ⟨b, hb, hbp⟩ := SetLike.not_le_iff_exists.mp hn
      refine ⟨b, hb.1, ?_, (fun _ => hbp), (fun h => (h ha).elim)⟩
      intro Q hQ hQP
      exact (Finset.inf_le (f := id) (Finset.mem_erase.mpr ⟨hQP, hQ⟩)) hb.2
    · exact ⟨0, J.zero_mem, fun Q _ _ => Q.zero_mem, (fun h => (ha h).elim), (fun _ => rfl)⟩
  choose b hbJ hbQ hbP hbzero using hex
  let v : s → R := fun P => b P P.property
  refine ⟨∑ P : s, v P, J.sum_mem (fun P _ => hbJ P P.property), ?_⟩
  intro P hP ha
  let p : s := ⟨P, hP⟩
  have hrest : (∑ Q ∈ (Finset.univ : Finset s).erase p, v Q) ∈ P := by
    apply P.sum_mem
    intro Q hQ
    have hQp : (Q : Ideal R) ≠ P := by
      intro heq
      exact (Finset.mem_erase.mp hQ).1 (Subtype.ext heq)
    exact hbQ Q Q.property P hP hQp.symm
  have hsum : (∑ Q : s, v Q) = v p + ∑ Q ∈ (Finset.univ : Finset s).erase p, v Q := by
    symm
    exact Finset.add_sum_erase _ _ (Finset.mem_univ p)
  rw [hsum] at ha
  by_cases haP : a ∈ P
  · have hv : v p ∈ P := by
      have h := P.sub_mem ha (P.add_mem haP hrest)
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using h
    exact hbP P hP haP hv
  · have hv : v p = 0 := hbzero P hP haP
    exact haP (by simpa [hv] using P.sub_mem ha hrest)

end WeightedTorusJets

namespace WeightedTorusJets.Geometry

theorem exists_add_not_mem_of_finite_prime {R : Type*} [CommRing R]
    (s : Finset (Ideal R)) (hp : ∀ P ∈ s, P.IsPrime) (a : R) (J : Ideal R)
    (havoid : ∀ P ∈ s, ¬ (Ideal.span {a} ⊔ J ≤ P)) :
    ∃ b ∈ J, ∀ P ∈ s, a + b ∉ P := by
  classical
  let t := s.filter (Maximal (· ∈ s))
  have htanti : ∀ P ∈ t, ∀ Q ∈ t, P ≠ Q → ¬ P ≤ Q := by
    intro P hP Q hQ hne hle
    exact hne (le_antisymm hle
      ((Finset.mem_filter.mp hP).2.2 (Finset.mem_filter.mp hQ).1 hle))
  obtain ⟨b, hb, hbavoid⟩ := exists_add_not_mem_of_prime_antichain t
    (fun P hP ↦ hp P (Finset.mem_filter.mp hP).1) htanti a J
    (fun P hP ↦ havoid P (Finset.mem_filter.mp hP).1)
  refine ⟨b, hb, fun P hP hab ↦ ?_⟩
  obtain ⟨Q, hPQ, hQ⟩ := s.exists_le_maximal hP
  exact hbavoid Q (Finset.mem_filter.mpr ⟨hQ.1, hQ⟩) (hPQ hab)

theorem exists_add_isSMulRegular {R M : Type*} [CommRing R] [IsNoetherianRing R]
    [AddCommGroup M] [Module R M] [IsNoetherian R M] (a : R) (J : Ideal R)
    (havoid : ∀ P ∈ associatedPrimes R M, ¬ (Ideal.span {a} ⊔ J ≤ P)) :
    ∃ b ∈ J, IsSMulRegular M (a + b) := by
  classical
  have hfinite := associatedPrimes.finite R M
  obtain ⟨b, hb, hbavoid⟩ := exists_add_not_mem_of_finite_prime hfinite.toFinset
    (fun P hP ↦ (hfinite.mem_toFinset.mp hP).isPrime) a J
    (fun P hP ↦ havoid P (hfinite.mem_toFinset.mp hP))
  refine ⟨b, hb, ?_⟩
  have hnot : a + b ∉ ⋃ P ∈ associatedPrimes R M, (P : Set R) := by
    intro h
    obtain ⟨P, hP⟩ := Set.mem_iUnion.mp h
    obtain ⟨hPass, hmem⟩ := Set.mem_iUnion.mp hP
    exact hbavoid P (hfinite.mem_toFinset.mpr hPass) hmem
  simpa only [biUnion_associatedPrimes_eq_compl_regular R M, Set.mem_compl_iff,
    Set.mem_ofPred_eq, not_not] using hnot

theorem exists_add_isSMulRegular_of_exists {R M : Type*} [CommRing R] [IsNoetherianRing R]
    [AddCommGroup M] [Module R M] [IsNoetherian R M] (a : R) (J : Ideal R)
    (h : ∃ x ∈ Ideal.span {a} ⊔ J, IsSMulRegular M x) :
    ∃ b ∈ J, IsSMulRegular M (a + b) := by
  obtain ⟨x, hx, hxreg⟩ := h
  apply exists_add_isSMulRegular a J
  intro P hP hle
  have hxnot : x ∉ ⋃ Q ∈ associatedPrimes R M, (Q : Set R) := by
    simpa only [biUnion_associatedPrimes_eq_compl_regular R M, Set.mem_compl_iff,
      Set.mem_ofPred_eq, not_not] using hxreg
  exact hxnot (Set.mem_iUnion.mpr ⟨P, Set.mem_iUnion.mpr ⟨hP, hle hx⟩⟩)

end WeightedTorusJets.Geometry

namespace WeightedTorusJets

universe uReg

theorem isRegular_of_exists_regular_sequence_in_ofList {R : Type uReg} [CommRing R]
    [IsNoetherianRing R] [IsLocalRing R] (gs : List R) (M : Type uReg)
    [AddCommGroup M] [Module R M] [Module.Finite R M]
    (hproper : Ideal.ofList gs • (⊤ : Submodule R M) < ⊤)
    (rs : List R) (hlen : rs.length = gs.length)
    (hmem : ∀ r ∈ rs, r ∈ Ideal.ofList gs) (hreg : IsRegular M rs) :
    IsRegular M gs := by
  induction gs generalizing M rs with
  | nil =>
    have hrs : rs = [] := List.length_eq_zero_iff.mp hlen
    subst rs
    exact hreg
  | cons a gs ih =>
    cases rs with
    | nil => simp at hlen
    | cons z zs =>
      obtain ⟨b, hb, hxreg⟩ := Geometry.exists_add_isSMulRegular_of_exists a
        (Ideal.ofList gs) ⟨z, by simpa only [Ideal.ofList_cons] using hmem z (by simp),
          ((isRegular_cons_iff M z zs).mp hreg).1⟩
      let x := a + b
      have hdiff : x - a ∈ Ideal.ofList gs := by
        simpa only [x, add_sub_cancel_left] using hb
      have heq : Ideal.ofList (x :: gs) = Ideal.ofList (a :: gs) := by
        simpa only [Ideal.ofList_cons] using
          span_singleton_sup_eq_of_sub_mem (Ideal.ofList gs) hdiff
      have hxmem : x ∈ Ideal.ofList (a :: gs) :=
        heq ▸ Ideal.subset_span (by simp)
      obtain ⟨ss, hsslen, hssmem, hssreg⟩ :=
        exists_regular_sequence_quotient_of_regular_element (ModuleCat.of R M) hproper
          hxmem hxreg gs.length (z :: zs) hlen hmem hreg
      obtain ⟨ts, htslen, htsmem, htsreg⟩ :=
        exists_regular_sequence_quotSMulTop_of_mem_sup x (Ideal.ofList gs) ss
          (fun r hr => by simpa only [← heq, Ideal.ofList_cons] using hssmem r hr) hssreg
      have hquot : Ideal.ofList gs • (⊤ : Submodule R (QuotSMulTop x M)) < ⊤ := by
        apply lt_top_iff_ne_top.mpr
        intro htop
        have htop' := (Submodule.top_eq_ofList_cons_smul_iff (M := M)
          (r := x) (rs := gs)).mpr htop.symm
        rw [heq] at htop'
        exact hproper.ne htop'.symm
      have htail := ih (QuotSMulTop x M) hquot ts (htslen.trans hsslen) htsmem htsreg
      exact (isRegular_cons_iff_sub_mem gs hdiff).mp
        ((isRegular_cons_iff M x gs).mpr ⟨hxreg, htail⟩)

end WeightedTorusJets

namespace WeightedTorusJets
open IsLocalRing
theorem exists_regular_sequence_of_le_radical {R : Type u} [CommRing R]
    [IsNoetherianRing R] (M : ModuleCat.{u} R) [Module.Finite R M] {I J : Ideal R}
    (hI : I • (⊤ : Submodule R M) < ⊤) (hJ : J • (⊤ : Submodule R M) < ⊤)
    (hIJ : I ≤ J.radical) (rs : List R) (hmem : ∀ r ∈ rs, r ∈ I)
    (hreg : IsRegular M rs) :
    ∃ ss : List R, ss.length = rs.length ∧ (∀ r ∈ ss, r ∈ J) ∧ IsRegular M ss := by
  let Q := ModuleCat.of R (R ⧸ J)
  have hsupp : Module.support R Q = PrimeSpectrum.zeroLocus J := by
    rw [Module.support_eq_zeroLocus, Ideal.annihilator_quotient]
  have hsub : Module.support R Q ⊆ PrimeSpectrum.zeroLocus I := by
    rw [hsupp, PrimeSpectrum.zeroLocus_subset_zeroLocus_iff]
    exact hIJ
  have hext := ModuleCat.subsingleton_ext_of_exists_isRegular I Q hsub M hI rs hmem hreg
  exact ModuleCat.exists_isRegular_of_exists_subsingleton_ext J rs.length M hJ Q hsupp hext

theorem regular_maximal_generators_length {R : Type*} [CommRing R]
    [IsNoetherianRing R] [IsLocalRing R] {rs : List R}
    (hreg : IsRegular R rs) (hgen : Ideal.ofList rs = maximalIdeal R) :
    (rs.length : ℕ∞) = (maximalIdeal R).height := by
  let := Ideal.Quotient.field (maximalIdeal R)
  have h := ringKrullDim_add_length_eq_ringKrullDim_of_isRegular rs hreg
  rw [hgen, ringKrullDim_eq_zero_of_field, zero_add,
    ← maximalIdeal_height_eq_ringKrullDim] at h
  exact_mod_cast h

end WeightedTorusJets
namespace WeightedTorusJets

universe uReg

theorem isRegular_parameters_of_exists_regular_maximal_generators
    {R : Type uReg} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (hex : ∃ rs : List R, IsRegular R rs ∧
      Ideal.ofList rs = IsLocalRing.maximalIdeal R)
    (fs : List R) (hrad : (Ideal.ofList fs).radical = IsLocalRing.maximalIdeal R)
    (hlen : (fs.length : ℕ∞) = (IsLocalRing.maximalIdeal R).height) :
    IsRegular R fs := by
  obtain ⟨rs, hrsreg, hrsgen⟩ := hex
  have hproper : Ideal.ofList fs ≠ ⊤ := by
    intro htop
    rw [htop, Ideal.radical_top] at hrad
    exact (IsLocalRing.maximalIdeal.isMaximal R).ne_top hrad.symm
  have hM : IsLocalRing.maximalIdeal R • (⊤ : Submodule R R) < ⊤ := by
    simpa only [Ideal.smul_eq_mul, Ideal.mul_top] using
      (IsLocalRing.maximalIdeal.isMaximal R).ne_top.lt_top
  obtain ⟨ss, hsslen, hssmem, hssreg⟩ := exists_regular_sequence_of_le_radical
    (ModuleCat.of R R) hM
    (by simpa only [Ideal.smul_eq_mul, Ideal.mul_top] using hproper.lt_top)
    (le_of_eq hrad.symm) rs
    (fun r hr => hrsgen ▸ Ideal.subset_span hr) hrsreg
  have hrslen : rs.length = fs.length := by
    exact_mod_cast (regular_maximal_generators_length hrsreg hrsgen).trans hlen.symm
  exact isRegular_of_exists_regular_sequence_in_ofList fs R
    (by simpa only [Ideal.smul_eq_mul, Ideal.mul_top] using hproper.lt_top)
    ss (hsslen.trans hrslen) hssmem hssreg

end WeightedTorusJets


end SiegelZeros

end OAI
