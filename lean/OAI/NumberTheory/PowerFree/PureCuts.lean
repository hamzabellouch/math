import OAI.NumberTheory.PowerFree.GenericCuts

namespace OAI

universe u

open scoped BigOperators
open Matrix
open scoped BigOperators

namespace QuarticPowerFree

section
open Algebra

theorem prime_height_le_of_goingDown {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] [Algebra.HasGoingDown R S]
    (p : Ideal R) [p.IsPrime] [p.FiniteHeight]
    (P : Ideal S) [P.IsPrime] [P.LiesOver p] : p.height ≤ P.height := by
  obtain ⟨l, hl, hn⟩ := p.exists_ltSeries_length_eq_height
  have hlp : l.last.asIdeal = p := congrArg PrimeSpectrum.asIdeal hl
  have : P.LiesOver l.last.asIdeal := hlp.symm ▸ (inferInstance : P.LiesOver p)
  obtain ⟨L, hL, hlast, _⟩ := Ideal.exists_ltSeries_of_hasGoingDown l P
  have hlength : (L.length : ℕ∞) ≤ Order.height L.last := Order.length_le_height (show L.last ≤ L.last from le_rfl)
  have hh : Order.height L.last = P.height :=
    (congrArg Order.height hlast).trans (PrimeSpectrum.height_eq_orderHeight _).symm
  calc
    p.height = (l.length : ℕ∞) := hn.symm
    _ = (L.length : ℕ∞) := congrArg Nat.cast hL.symm
    _ ≤ P.height := hlength.trans_eq hh

theorem mvPolynomial_maximal_height {K : Type*} [Field K]
    (n : ℕ) (P : Ideal (MvPolynomial (Fin n) K)) [P.IsMaximal] : P.height = n := by
  induction n with
  | zero =>
    have hdim := MvPolynomial.ringKrullDim_of_isNoetherianRing (ι := Fin 0) (R := K)
    have h := Ideal.height_le_ringKrullDim_of_ne_top (I := P) Ideal.IsPrime.ne_top'
    simp only [ENat.card_eq_coe_fintype_card, Fintype.card_fin, Nat.cast_zero,
      ringKrullDim_eq_zero_of_field] at hdim
    rw [hdim] at h
    exact le_antisymm (by exact_mod_cast h) (zero_le)
  | succ n ih =>
    let e := (MvPolynomial.finSuccEquiv K n).toRingEquiv
    let Q := P.map e
    have : Q.IsMaximal := Ideal.map_isMaximal_of_equiv e
    let q : Ideal (MvPolynomial (Fin n) K) := Q.comap Polynomial.C
    have : q.IsMaximal := Polynomial.isMaximal_comap_C_of_isJacobsonRing Q
    have he : Q.height = P.height := e.height_map P
    have hq : Q.LiesOver q := ⟨rfl⟩
    rw [← he, Polynomial.height_eq_height_add_one q Q, ih q, Nat.cast_add, Nat.cast_one]

theorem normalization_size_le_maximal_height {K A : Type*} [Field K] [CommRing A]
    [IsDomain A] [Algebra K A] (s : ℕ) (g : MvPolynomial (Fin s) K →ₐ[K] A)
    (hg : Function.Injective g) (hi : g.IsIntegral)
    (P : Ideal A) [P.IsMaximal] : (s : ℕ∞) ≤ P.height := by
  let R := MvPolynomial (Fin s) K
  let : Algebra R A := g.toRingHom.toAlgebra
  have : FaithfulSMul R A := (faithfulSMul_iff_algebraMap_injective R A).mpr hg
  have : Algebra.IsIntegral R A := ⟨hi⟩
  let p : Ideal R := P.under R
  have : p.IsMaximal := Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := R) P
  rw [← mvPolynomial_maximal_height s p]
  exact prime_height_le_of_goingDown p P

theorem normalization_trdeg {K A : Type u} [Field K] [CommRing A]
    [IsDomain A] [Algebra K A] (s : ℕ) (g : MvPolynomial (Fin s) K →ₐ[K] A)
    (hg : Function.Injective g) (hi : g.IsIntegral) : trdeg K A = s := by
  let R := MvPolynomial (Fin s) K
  let : Algebra R A := g.toRingHom.toAlgebra
  have : FaithfulSMul R A := (faithfulSMul_iff_algebraMap_injective R A).mpr hg
  have : Algebra.IsIntegral R A := ⟨hi⟩
  have : IsScalarTower K R A := IsScalarTower.of_algebraMap_eq' (by
    ext x
    exact (g.commutes x).symm)
  have h := trdeg_add_eq K R (A := A)
  have hz : trdeg R A = 0 := trdeg_eq_zero_iff.mpr inferInstance
  rw [hz, add_zero] at h
  rw [← h, MvPolynomial.trdeg_of_isDomain]
  simp

theorem finite_type_trdeg_le_maximal_height {K A : Type u} [Field K] [CommRing A]
    [IsDomain A] [Algebra K A] [Algebra.FiniteType K A]
    (P : Ideal A) [P.IsMaximal] :
    ∃ s : ℕ, trdeg K A = s ∧ (s : ℕ∞) ≤ P.height := by
  obtain ⟨s, g, hg, hi⟩ := exists_integral_inj_algHom_of_fg K A
  exact ⟨s, normalization_trdeg s g hg hi,
    normalization_size_le_maximal_height s g hg hi P⟩

theorem trdeg_le_one_of_principal_maximal {K A : Type u} [Field K] [CommRing A]
    [IsDomain A] [Algebra K A] [Algebra.FiniteType K A]
    (p : A) (P : Ideal A) [P.IsMaximal]
    (hP : P ∈ (Ideal.span {p}).minimalPrimes) : trdeg K A ≤ 1 := by
  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing K A
  obtain ⟨s, hs, hheight⟩ := finite_type_trdeg_le_maximal_height (K := K) P
  have hle := Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes (Ideal.span {p}) P hP
  rw [hs]
  have hn : s ≤ 1 := by exact_mod_cast hheight.trans hle
  exact_mod_cast hn

open scoped nonZeroDivisors

theorem localized_algebraic_prime_isMaximal
    {R A F B : Type u} [CommRing R] [IsDomain R] [CommRing A] [IsDomain A]
    [Field F] [CommRing B] [Algebra R A] [Algebra R F] [IsFractionRing R F]
    [Algebra A B] [Algebra R B] [Algebra F B]
    [IsScalarTower R A B] [IsScalarTower R F B]
    [IsLocalization (Algebra.algebraMapSubmonoid A R⁰) B]
    (P : Ideal A) [P.IsPrime]
    [FaithfulSMul R (A ⧸ P)] [Algebra.IsAlgebraic R (A ⧸ P)] :
    (P.map (algebraMap A B)).IsMaximal := by
  let M := Algebra.algebraMapSubmonoid A R⁰
  have hdis : Disjoint (M : Set A) (P : Set A) := by
    rw [Set.disjoint_left]
    rintro a ⟨r, hr, rfl⟩ ha
    have hzero : algebraMap R (A ⧸ P) r = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr ha
    have hr0 : r ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hr
    exact hr0 ((FaithfulSMul.algebraMap_injective R (A ⧸ P))
      (hzero.trans (map_zero _).symm))
  let Q := P.map (algebraMap A B)
  have : Q.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint M B P inferInstance hdis
  let C := B ⧸ Q
  let f : A →ₐ[R] C := (Ideal.Quotient.mkₐ R Q).comp (IsScalarTower.toAlgHom R A B)
  let g : (A ⧸ P) →ₐ[R] C := Ideal.Quotient.liftₐ P f (by
    intro a ha
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem _ ha))
  have hnum (a : A) : IsAlgebraic F (f a) := by
    have hr := IsAlgebraic.algHom g (Algebra.IsAlgebraic.isAlgebraic (R := R) (Ideal.Quotient.mk P a))
    exact hr.extendScalars (FaithfulSMul.algebraMap_injective R F)
  have h_alg : Algebra.IsAlgebraic F C := by
    constructor
    intro c
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective c
    obtain ⟨⟨a,s⟩, hs⟩ := IsLocalization.surj M b
    obtain ⟨r, hr, hsr⟩ := s.property
    have hrn : r ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hr
    have hrF : algebraMap R F r ≠ 0 := by simpa using (IsFractionRing.injective R F).ne hrn
    have hrel : Ideal.Quotient.mk Q b * algebraMap F C (algebraMap R F r) = f a := by
      change Ideal.Quotient.mk Q b * Ideal.Quotient.mk Q (algebraMap F B (algebraMap R F r)) = _
      rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply R A B, hsr,
        ← map_mul, hs]
      rfl
    have hc : Ideal.Quotient.mk Q b = f a * algebraMap F C (algebraMap R F r)⁻¹ := by
      rw [← hrel, mul_assoc, ← map_mul, mul_inv_cancel₀ hrF, map_one, mul_one]
    rw [hc]
    exact (hnum a).mul (isAlgebraic_algebraMap _)
  have : Algebra.IsIntegral F C := Algebra.IsAlgebraic.isIntegral
  exact Ideal.Quotient.maximal_of_isField Q (isField_of_isIntegral_of_isField' (Field.toIsField F))

open scoped TensorProduct nonZeroDivisors

theorem principal_minimal_trdeg_bound_of_normalization
    {K A : Type u} [Field K] [CommRing A] [IsDomain A] [Algebra K A]
    [Algebra.FiniteType K A] (p : A) (P : Ideal A) [P.IsPrime]
    (hP : P ∈ (Ideal.span {p}).minimalPrimes) (s : ℕ)
    (g : MvPolynomial (Fin s) K →ₐ[K] A)
    (hg : Function.Injective ((Ideal.Quotient.mkₐ K P).comp g))
    (hi : ((Ideal.Quotient.mkₐ K P).comp g).IsIntegral) :
    Algebra.trdeg K A ≤ (s : Cardinal) + 1 := by
  let R := MvPolynomial (Fin s) K
  let : Algebra R A := g.toRingHom.toAlgebra
  have hga : Function.Injective g := Function.Injective.of_comp hg
  have : FaithfulSMul R A := (faithfulSMul_iff_algebraMap_injective R A).mpr hga
  have : FaithfulSMul R (A ⧸ P) :=
    (faithfulSMul_iff_algebraMap_injective R (A ⧸ P)).mpr hg
  have : Algebra.IsIntegral R (A ⧸ P) := ⟨hi⟩
  have : IsScalarTower K R A := IsScalarTower.of_algebraMap_eq' (by
    ext x
    exact (g.commutes x).symm)
  have : Algebra.FiniteType R A := Algebra.FiniteType.of_restrictScalars_finiteType K R A
  let F := FractionRing R
  let B := F ⊗[R] A
  let : Algebra A B := Algebra.TensorProduct.rightAlgebra
  let M := Algebra.algebraMapSubmonoid A R⁰
  have hM : M ≤ A⁰ := by
    rintro a ⟨r, hr, rfl⟩
    apply mem_nonZeroDivisors_iff_ne_zero.mpr
    simpa using (FaithfulSMul.algebraMap_injective R A).ne (mem_nonZeroDivisors_iff_ne_zero.mp hr)
  have : IsDomain B := IsLocalization.isDomain_of_le_nonZeroDivisors B hM
  have : FaithfulSMul A B := (faithfulSMul_iff_algebraMap_injective A B).mpr
    (IsLocalization.injective B hM)
  let Q := P.map (algebraMap A B)
  have : Q.IsMaximal := localized_algebraic_prime_isMaximal (R := R) (F := F) P
  have hdis : Disjoint (M : Set A) (P : Set A) := by
    rw [Set.disjoint_left]
    rintro a ⟨r, hr, rfl⟩ ha
    have hz : algebraMap R (A ⧸ P) r = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr ha
    exact (mem_nonZeroDivisors_iff_ne_zero.mp hr)
      ((FaithfulSMul.algebraMap_injective R (A ⧸ P)) (hz.trans (map_zero _).symm))
  have hQP : Q.under A = P :=
    IsLocalization.under_map_of_isPrime_disjoint M B inferInstance hdis
  have hm : Q ∈ (Ideal.span {algebraMap A B p}).minimalPrimes := by
    rw [← Set.image_singleton, ← Ideal.map_span, IsLocalization.minimalPrimes_map M B]
    simpa only [Set.mem_preimage, hQP] using hP
  have hFB : Algebra.trdeg F B ≤ 1 := trdeg_le_one_of_principal_maximal
    (algebraMap A B p) Q hm
  have : IsScalarTower K A B := IsScalarTower.of_algebraMap_eq (fun k => by
    rw [IsScalarTower.algebraMap_apply K R B, IsScalarTower.algebraMap_apply K R A,
      IsScalarTower.algebraMap_apply R A B])
  have : Algebra.IsAlgebraic A B := IsLocalization.isAlgebraic B M
  have hAB := trdeg_add_eq K A (A := B)
  rw [trdeg_eq_zero (R := A) (A := B), add_zero] at hAB
  have : Algebra.IsAlgebraic R F := IsLocalization.isAlgebraic F R⁰
  have hRF := trdeg_add_eq K R (A := F)
  rw [trdeg_eq_zero (R := R) (A := F), add_zero, MvPolynomial.trdeg_of_isDomain] at hRF
  have hRF' : Algebra.trdeg K F = (s : Cardinal) := by simpa using hRF.symm
  have : FaithfulSMul F B := (faithfulSMul_iff_algebraMap_injective F B).mpr
    (algebraMap F B).injective
  have hBF := trdeg_add_eq K F (A := B)
  rw [hRF'] at hBF
  rw [hAB, ← hBF]
  exact add_le_add_right hFB _

theorem principal_minimal_trdeg_bound
    {K A : Type u} [Field K] [CommRing A] [IsDomain A] [Algebra K A]
    [Algebra.FiniteType K A] (p : A) (P : Ideal A) [P.IsPrime]
    (hP : P ∈ (Ideal.span {p}).minimalPrimes) :
    Algebra.trdeg K A ≤ Algebra.trdeg K (A ⧸ P) + 1 := by
  classical
  obtain ⟨s, g, hg, hi⟩ := exists_integral_inj_algHom_of_fg K (A ⧸ P)
  choose x hx using fun i : Fin s => Ideal.Quotient.mk_surjective (g (MvPolynomial.X i))
  let G : MvPolynomial (Fin s) K →ₐ[K] A := MvPolynomial.aeval x
  have he : (Ideal.Quotient.mkₐ K P).comp G = g := by
    apply MvPolynomial.algHom_ext
    intro i
    simpa only [G, AlgHom.comp_apply, MvPolynomial.aeval_X, Ideal.Quotient.mkₐ_eq_mk] using hx i
  have hG : Function.Injective ((Ideal.Quotient.mkₐ K P).comp G) := he.symm ▸ hg
  have hI : ((Ideal.Quotient.mkₐ K P).comp G).IsIntegral := he.symm ▸ hi
  rw [normalization_trdeg s g hg hi]
  exact principal_minimal_trdeg_bound_of_normalization p P hP s G hG hI

end
open MvPolynomial

theorem quotient_hilbert_le {n : ℕ} {K : Type*} [Field K]
    (I J : Ideal (MvPolynomial (Fin n) K)) (hIJ : I ≤ J) (T : ℕ) :
    Module.finrank K ((totalSpace T).map (Ideal.Quotient.mkₐ K J).toLinearMap) ≤
      Module.finrank K ((totalSpace T).map (Ideal.Quotient.mkₐ K I).toLinearMap) := by
  let F := (totalSpace T).map (Ideal.Quotient.mkₐ K I).toLinearMap
  let := totalSpace_finite (n := n) (K := K) T
  let f := (Ideal.Quotient.factorₐ K hIJ).toLinearMap.domRestrict F
  have hr : LinearMap.range f = (totalSpace T).map (Ideal.Quotient.mkₐ K J).toLinearMap := by
    ext z
    constructor
    · rintro ⟨⟨y,q,hq,rfl⟩,rfl⟩
      exact ⟨q,hq,rfl⟩
    · rintro ⟨q,hq,rfl⟩
      exact ⟨⟨Ideal.Quotient.mk I q,⟨q,hq,rfl⟩⟩,rfl⟩
  rw [← hr]
  exact LinearMap.finrank_range_le f

theorem cut_minimal_hilbert_codim_le_one {n : ℕ} {K : Type u} [Field K]
    (I Q : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime] [Q.IsPrime]
    (p : MvPolynomial (Fin n) K)
    (hQ : Q ∈ (I ⊔ Ideal.span {p}).minimalPrimes)
    (P S : Polynomial ℚ)
    (hP : ∀ᶠ T : ℕ in Filter.atTop,
      (Module.finrank K ((totalSpace T).map (Ideal.Quotient.mkₐ K I).toLinearMap) : ℚ) =
        P.eval (T : ℚ))
    (hS : ∀ᶠ T : ℕ in Filter.atTop,
      (Module.finrank K ((totalSpace T).map (Ideal.Quotient.mkₐ K Q).toLinearMap) : ℚ) =
        S.eval (T : ℚ)) : P.natDegree ≤ S.natDegree + 1 := by
  let A := MvPolynomial (Fin n) K ⧸ I
  let q := Q.map (Ideal.Quotient.mk I)
  have hIQ : I ≤ Q := le_sup_left.trans hQ.le
  have hq : q ∈ (Ideal.span {Ideal.Quotient.mk I p}).minimalPrimes := by
    rw [← Set.image_singleton, ← Ideal.map_span,
      Ideal.minimalPrimes_map_of_surjective Ideal.Quotient.mk_surjective, Ideal.mk_ker,
      sup_comm]
    exact ⟨Q,hQ,rfl⟩
  have : q.IsPrime := hq.isPrime
  have hi := principal_minimal_trdeg_bound (K := K) (Ideal.Quotient.mk I p) q hq
  let e : (A ⧸ q) ≃ₐ[K] (MvPolynomial (Fin n) K ⧸ Q) :=
    DoubleQuot.quotQuotEquivQuotOfLEₐ K hIQ
  have he : Algebra.trdeg K (A ⧸ q) = Algebra.trdeg K (MvPolynomial (Fin n) K ⧸ Q) :=
    AlgEquiv.trdeg_eq e
  rw [he, ← hilbert_natDegree_eq_trdeg I P hP, ← hilbert_natDegree_eq_trdeg Q S hS] at hi
  exact_mod_cast hi

theorem proper_cut_hilbert_purity {n h : ℕ} {K : Type u} [Field K]
    (I Q : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime] [Q.IsPrime]
    (p : MvPolynomial (Fin n) K) (hp : p ∉ I)
    (hQ : Q ∈ (I ⊔ Ideal.span {p}).minimalPrimes)
    (P D S : Polynomial ℚ)
    (hP : ∀ᶠ T : ℕ in Filter.atTop,
      (Module.finrank K ((totalSpace T).map (Ideal.Quotient.mkₐ K I).toLinearMap) : ℚ) = P.eval (T : ℚ))
    (hD : ∀ᶠ T : ℕ in Filter.atTop,
      (Module.finrank K ((totalSpace T).map
        (Ideal.Quotient.mkₐ K (I ⊔ Ideal.span {p})).toLinearMap) : ℚ) = D.eval (T : ℚ))
    (hS : ∀ᶠ T : ℕ in Filter.atTop,
      (Module.finrank K ((totalSpace T).map (Ideal.Quotient.mkₐ K Q).toLinearMap) : ℚ) = S.eval (T : ℚ))
    (hdeg : P.natDegree = h+1) : S.natDegree = h := by
  have hd := (proper_cut_hilbert_polynomial I p hp P D (hP.mono fun _ ht => ht.symm)
    (hD.mono fun _ ht => ht.symm) h hdeg.le).1
  have hs : S.natDegree ≤ D.natDegree := by
    apply natDegree_le_of_eventually_nat_eval_bounds S D
    · exact hS.mono fun T ht => ht ▸ (show (0 : ℚ) ≤ Module.finrank K
        ((totalSpace T).map (Ideal.Quotient.mkₐ K Q).toLinearMap) from Nat.cast_nonneg _)
    · filter_upwards [hS,hD] with T ht hd
      rw [← ht,← hd]
      exact_mod_cast quotient_hilbert_le (I ⊔ Ideal.span {p}) Q hQ.le T
  have hl := cut_minimal_hilbert_codim_le_one I Q p hQ P S hP hS
  omega

end QuarticPowerFree

end OAI
