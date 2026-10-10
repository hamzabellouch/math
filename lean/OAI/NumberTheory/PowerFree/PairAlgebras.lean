import OAI.NumberTheory.PowerFree.HighDegree

namespace OAI

namespace QuarticPowerFree
open MvPolynomial MonomialOrder
open scoped MonomialOrder

noncomputable def pairRelation {n : ℕ} {R : Type*} [CommRing R] (k : ℕ) (q : Fin n → R)
    (i : Fin n) : MvPolynomial (Fin n ⊕ Fin n) R :=
  X (Sum.inl i) ^ k * X (Sum.inr i) - C (q i)

def PairNormal {n : ℕ} (k : ℕ) (m : (Fin n ⊕ Fin n) →₀ ℕ) : Prop :=
  ∀ i, m (Sum.inl i) < k ∨ m (Sum.inr i) = 0

theorem pair_normal_form {n : ℕ} {R : Type*} [CommRing R] [Nontrivial R]
    (k : ℕ) (q : Fin n → R) (p : MvPolynomial (Fin n ⊕ Fin n) R) :
    ∃ (g : Fin n →₀ MvPolynomial (Fin n ⊕ Fin n) R)
      (r : MvPolynomial (Fin n ⊕ Fin n) R),
      p = Finsupp.linearCombination _ (pairRelation k q) g + r ∧
      ∀ m ∈ r.support, PairNormal k m := by
  classical
  let o : LinearOrder (Fin n ⊕ Fin n) :=
    LinearOrder.lift' (Fintype.equivFin _) (Fintype.equivFin _).injective
  have : @WellFoundedGT (Fin n ⊕ Fin n) o.toLT := Finite.wellFounded_of_trans_of_irrefl _
  let e : Fin n → ((Fin n ⊕ Fin n) →₀ ℕ) := fun i =>
    Finsupp.single (Sum.inl i) k + Finsupp.single (Sum.inr i) 1
  have he (i) : X (Sum.inl i) ^ k * X (Sum.inr i) = monomial (e i) (1 : R) := by
    rw [X_pow_eq_monomial, X, monomial_mul_monomial, one_mul]
  have hlt (i) : degLex.degree (C (q i)) ≺[degLex]
      degLex.degree (monomial (e i) (1 : R)) := by
    apply lt_of_not_ge
    intro h
    have ht := MvPolynomial.degLex_totalDegree_monotone h
    rw [totalDegree_C, totalDegree_monomial _ one_ne_zero] at ht
    have hp : 1 ≤ (e i).sum (fun _ a => a) := by
      exact (show 1 ≤ (e i) (Sum.inr i) by simp [e]).trans
        (by simpa using Finsupp.single_le_sum (g := fun _ a => a) (e i) (fun _ _ => Nat.zero_le _) (Sum.inr i))
    omega
  have hd (i) : degLex.degree (pairRelation k q i) = e i := by
    rw [pairRelation, he, degLex.degree_sub_of_lt (hlt i),
      degLex.degree_monomial, ite_eq_right one_ne_zero]
  have hu (i) : IsUnit (degLex.leadingCoeff (pairRelation k q i)) := by
    rw [pairRelation, he, degLex.leadingCoeff_sub_of_lt (hlt i),
      degLex.leadingCoeff_monomial]
    exact isUnit_one
  obtain ⟨g, r, h, _, hr⟩ := MonomialOrder.div hu p
  refine ⟨g, r, h, ?_⟩
  intro m hm i
  have hnd := hr m hm i
  rw [hd] at hnd
  by_contra! hn
  apply hnd
  intro a
  cases a with
  | inl j => by_cases h : j = i <;> simp [e, h, hn.1]
  | inr j =>
    by_cases h : j = i
    · simp [e, h]; omega
    · simp [e, h]

def pairExponent {n : ℕ} (k : ℕ) (m : (Fin n ⊕ Fin n) →₀ ℕ) : Fin n → ℤ :=
  fun i => (m (Sum.inl i) : ℤ) - (k : ℤ) * m (Sum.inr i)

theorem pairExponent_injective_normal {n k : ℕ} {m m' : (Fin n ⊕ Fin n) →₀ ℕ}
    (hm : PairNormal k m) (hm' : PairNormal k m')
    (h : pairExponent k m = pairExponent k m') : m = m' := by
  have hc (i) : m (Sum.inl i) = m' (Sum.inl i) ∧
      m (Sum.inr i) = m' (Sum.inr i) := by
    have he := congrFun h i
    dsimp [pairExponent] at he
    have hN : (0 : ℤ) ≤ m (Sum.inl i) := Int.natCast_nonneg _
    have hN' : (0 : ℤ) ≤ m' (Sum.inl i) := Int.natCast_nonneg _
    have hK : (0 : ℤ) ≤ k := Int.natCast_nonneg _
    have hM : (m (Sum.inl i) : ℤ) < k ∨ (m (Sum.inr i) : ℤ) = 0 := by
      exact_mod_cast hm i
    have hM' : (m' (Sum.inl i) : ℤ) < k ∨ (m' (Sum.inr i) : ℤ) = 0 := by
      exact_mod_cast hm' i
    have hs : (m (Sum.inr i) : ℤ) = m' (Sum.inr i) := by
      rcases hM with ha | hb <;> rcases hM' with ha' | hb'
      · by_contra hs
        rcases lt_or_gt_of_ne hs with hs | hs
        · have ht := mul_le_mul_of_nonneg_left (show
            (m (Sum.inr i) : ℤ) + 1 ≤ m' (Sum.inr i) by omega) hK
          nlinarith
        · have ht := mul_le_mul_of_nonneg_left (show
            (m' (Sum.inr i) : ℤ) + 1 ≤ m (Sum.inr i) by omega) hK
          nlinarith
      · by_contra hs
        have ht := mul_le_mul_of_nonneg_left
          (show (1 : ℤ) ≤ m (Sum.inr i) by omega) hK
        rw [hb', mul_zero] at he
        nlinarith
      · by_contra hs
        have ht := mul_le_mul_of_nonneg_left
          (show (1 : ℤ) ≤ m' (Sum.inr i) by omega) hK
        rw [hb, mul_zero] at he
        nlinarith
      · omega
    rw [hs] at he
    constructor <;> omega
  ext a
  cases a with
  | inl i => exact (hc i).1
  | inr i => exact (hc i).2

noncomputable def pairLaurentMap {n : ℕ} {R : Type*} [CommRing R]
    (k : ℕ) (q : Fin n → R) :
    MvPolynomial (Fin n ⊕ Fin n) R →+* AddMonoidAlgebra R (Fin n → ℤ) :=
  eval₂Hom AddMonoidAlgebra.singleZeroRingHom
    (Sum.elim (fun i => AddMonoidAlgebra.single (Pi.single i 1) 1)
      (fun i => AddMonoidAlgebra.single (Pi.single i (-(k : ℤ))) (q i)))

theorem pairLaurentMap_monomial {n : ℕ} {R : Type*} [CommRing R]
    (k : ℕ) (q : Fin n → R) (m : (Fin n ⊕ Fin n) →₀ ℕ) (c : R) :
    pairLaurentMap k q (monomial m c) =
      AddMonoidAlgebra.single (pairExponent k m)
        (c * ∏ i, q i ^ m (Sum.inr i)) := by
  classical
  rw [pairLaurentMap, eval₂Hom_monomial]
  rw [Finsupp.prod_fintype _ _ (by simp)]
  simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr,
    AddMonoidAlgebra.single_pow, one_pow, AddMonoidAlgebra.prod_single,
    Finset.prod_const_one, AddMonoidAlgebra.single_mul_single, one_mul]
  change AddMonoidAlgebra.single 0 c *
      AddMonoidAlgebra.single _ (∏ i, q i ^ m (Sum.inr i)) = _
  rw [AddMonoidAlgebra.single_mul_single, zero_add]
  congr 1
  ext i
  simp [pairExponent, Finset.sum_apply, Pi.single_apply, mul_comm, sub_eq_add_neg]

theorem pairLaurentMap_relation {n : ℕ} {R : Type*} [CommRing R]
    (k : ℕ) (q : Fin n → R) (i : Fin n) :
    pairLaurentMap k q (pairRelation k q i) = 0 := by
  classical
  simp only [pairRelation, map_sub, map_mul, map_pow]
  simp only [pairLaurentMap, eval₂Hom_X', eval₂Hom_C, Sum.elim_inl, Sum.elim_inr,
    AddMonoidAlgebra.single_pow, one_pow, AddMonoidAlgebra.single_mul_single, one_mul]
  have he : k • Pi.single i (1 : ℤ) + Pi.single i (-(k : ℤ)) = (0 : Fin n → ℤ) := by
    ext j
    by_cases h : j = i <;> simp [h]
  rw [he]
  exact sub_self _

theorem pairLaurentMap_normal_injective {n : ℕ} {R : Type*} [CommRing R] [IsDomain R]
    (k : ℕ) (q : Fin n → R) (hq : ∀ i, q i ≠ 0)
    (r : MvPolynomial (Fin n ⊕ Fin n) R)
    (hr : ∀ m ∈ r.support, PairNormal k m) (he : pairLaurentMap k q r = 0) :
    r = 0 := by
  classical
  ext m
  by_cases hm : m ∈ r.support
  · have hc : (pairLaurentMap k q r).coeff (pairExponent k m) =
        r.coeff m * ∏ i, q i ^ m (Sum.inr i) := by
      conv_lhs => rw [r.as_sum, map_sum]
      rw [AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply,
        Finset.sum_eq_single_of_mem m hm]
      · simp [pairLaurentMap_monomial, AddMonoidAlgebra.coeff_single]
      · intro m' hm' hne
        have hE : pairExponent k m' ≠ pairExponent k m :=
          fun hh => hne (pairExponent_injective_normal (hr m' hm') (hr m hm) hh)
        simp [pairLaurentMap_monomial, AddMonoidAlgebra.coeff_single, hE]
    rw [he] at hc
    have hp : (∏ i, q i ^ m (Sum.inr i)) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr (fun i _ => pow_ne_zero _ (hq i))
    have hc0 : r.coeff m = 0 := (mul_eq_zero.mp hc.symm).resolve_right hp
    simpa using hc0
  · simpa using notMem_support_iff.mp hm

theorem pair_ideal_eq_ker {n : ℕ} {R : Type*} [CommRing R] [IsDomain R]
    (k : ℕ) (q : Fin n → R) (hq : ∀ i, q i ≠ 0) :
    Ideal.span (Set.range (pairRelation k q)) = RingHom.ker (pairLaurentMap k q) := by
  classical
  have hle : Ideal.span (Set.range (pairRelation k q)) ≤
      RingHom.ker (pairLaurentMap k q) := by
    apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact pairLaurentMap_relation k q i
  apply le_antisymm hle
  intro p hp
  obtain ⟨g, r, hpr, hr⟩ := pair_normal_form k q p
  have hg : Finsupp.linearCombination _ (pairRelation k q) g ∈
      Ideal.span (Set.range (pairRelation k q)) := by
    rw [Finsupp.linearCombination_apply, Finsupp.sum]
    apply Ideal.sum_mem
    intro i _
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)
  have her : pairLaurentMap k q r = 0 := by
    have he := congrArg (pairLaurentMap k q) hpr
    rw [map_add, show pairLaurentMap k q p = 0 from hp,
      show pairLaurentMap k q (Finsupp.linearCombination _ (pairRelation k q) g) = 0
        from hle hg, zero_add] at he
    exact he.symm
  rw [pairLaurentMap_normal_injective k q hq r hr her, add_zero] at hpr
  exact hpr ▸ hg

theorem pair_ideal_isPrime {n : ℕ} {R : Type*} [CommRing R] [IsDomain R]
    (k : ℕ) (q : Fin n → R) (hq : ∀ i, q i ≠ 0) :
    (Ideal.span (Set.range (pairRelation k q))).IsPrime := by
  rw [pair_ideal_eq_ker k q hq]
  exact RingHom.ker_isPrime _

theorem pair_normal_quotient_bijective {n : ℕ} {R : Type*} [CommRing R] [IsDomain R]
    (k : ℕ) (q : Fin n → R) (hq : ∀ i, q i ≠ 0) :
    Function.Bijective
      (((Ideal.Quotient.mkₐ R (Ideal.span (Set.range (pairRelation k q)))).toLinearMap).comp
        (restrictSupport R {m : (Fin n ⊕ Fin n) →₀ ℕ | PairNormal k m}).subtype) := by
  classical
  let I := Ideal.span (Set.range (pairRelation k q))
  let M := restrictSupport R {m : (Fin n ⊕ Fin n) →₀ ℕ | PairNormal k m}
  let f := ((Ideal.Quotient.mkₐ R I).toLinearMap).comp M.subtype
  change Function.Bijective f
  constructor
  · apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro p hp
    apply Subtype.ext
    apply pairLaurentMap_normal_injective k q hq p.val (fun m hm => p.property hm)
    have hmem : p.val ∈ I := Ideal.Quotient.eq_zero_iff_mem.mp hp
    change p.val ∈ RingHom.ker (pairLaurentMap k q)
    rwa [← pair_ideal_eq_ker k q hq]
  · intro y
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨g, r, hpr, hr⟩ := pair_normal_form k q p
    refine ⟨⟨r, fun m hm => hr m hm⟩, ?_⟩
    have hg : Finsupp.linearCombination _ (pairRelation k q) g ∈ I := by
      rw [Finsupp.linearCombination_apply, Finsupp.sum]
      apply Ideal.sum_mem
      intro i _
      exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)
    change (Ideal.Quotient.mk I) r = (Ideal.Quotient.mk I) p
    rw [hpr, map_add, Ideal.Quotient.eq_zero_iff_mem.mpr hg, zero_add]

noncomputable def pairNormalEquiv {n : ℕ} {R : Type*} [CommRing R] [IsDomain R]
    (k : ℕ) (q : Fin n → R) (hq : ∀ i, q i ≠ 0) :
    restrictSupport R {m : (Fin n ⊕ Fin n) →₀ ℕ | PairNormal k m} ≃ₗ[R]
      MvPolynomial (Fin n ⊕ Fin n) R ⧸ Ideal.span (Set.range (pairRelation k q)) :=
  LinearEquiv.ofBijective
    (((Ideal.Quotient.mkₐ R (Ideal.span (Set.range (pairRelation k q)))).toLinearMap).comp
      (restrictSupport R {m : (Fin n ⊕ Fin n) →₀ ℕ | PairNormal k m}).subtype)
    (pair_normal_quotient_bijective k q hq)

noncomputable def pairNormalBasis {n : ℕ} {R : Type*} [CommRing R] [IsDomain R]
    (k : ℕ) (q : Fin n → R) (hq : ∀ i, q i ≠ 0) :
    Module.Basis {m : (Fin n ⊕ Fin n) →₀ ℕ // PairNormal k m} R
      (MvPolynomial (Fin n ⊕ Fin n) R ⧸ Ideal.span (Set.range (pairRelation k q))) :=
  (basisRestrictSupport R {m : (Fin n ⊕ Fin n) →₀ ℕ | PairNormal k m}).map (pairNormalEquiv k q hq)

abbrev PairRing {n : ℕ} {R : Type*} [CommRing R] (k : ℕ) (q : Fin n → R) :=
  MvPolynomial (Fin n ⊕ Fin n) R ⧸ Ideal.span (Set.range (pairRelation k q))

noncomputable def pairCoeffs {n : ℕ} {K R : Type*} [Field K] [CommRing R] [Algebra K R]
    (k : ℕ) (q : Fin n → R) : R →ₐ[K] PairRing k q :=
  (Ideal.Quotient.mkₐ K _).comp (IsScalarTower.toAlgHom K R _)

noncomputable def pairScalePre {n : ℕ} {K R : Type*} [Field K] [CommRing R] [Algebra K R]
    (k A B : ℕ) (q : Fin n → R) (L : R →ₐ[K] Polynomial R) :
    MvPolynomial (Fin n ⊕ Fin n) R →ₐ[K] Polynomial (PairRing k q) :=
  MvPolynomial.aevalTower ((Polynomial.mapAlgHom (pairCoeffs (K := K) k q)).comp L)
    (fun i : Fin n ⊕ Fin n => Polynomial.monomial (Sum.elim (fun _ => A) (fun _ => B) i)
      (Ideal.Quotient.mk (Ideal.span (Set.range (pairRelation k q))) (X i)))

theorem pairScalePre_relation {n : ℕ} {K R : Type*} [Field K] [CommRing R] [Algebra K R]
    (k A B : ℕ) (q : Fin n → R) (L : R →ₐ[K] Polynomial R)
    (hq : ∀ i, L (q i) = Polynomial.monomial (k*A+B) (q i)) (i : Fin n) :
    pairScalePre k A B q L (pairRelation k q i) = 0 := by
  have hr : (Ideal.Quotient.mk (Ideal.span (Set.range (pairRelation k q))))
      (X (Sum.inl i)^k * X (Sum.inr i)) = pairCoeffs (K := K) k q (q i) := by
    have hh : Ideal.Quotient.mk (Ideal.span (Set.range (pairRelation k q)))
        (pairRelation k q i) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨i,rfl⟩)
    simpa [pairRelation, pairCoeffs, sub_eq_zero] using hh
  simp only [pairRelation, map_sub, map_mul, map_pow, pairScalePre,
    MvPolynomial.aevalTower_X, Sum.elim_inl, Sum.elim_inr,
    MvPolynomial.aevalTower_C, AlgHom.comp_apply, hq,
    Polynomial.mapAlgHom_monomial,
    Polynomial.monomial_pow, Polynomial.monomial_mul_monomial, Nat.mul_comm A k]
  rw [← map_pow, ← map_mul, hr, sub_self]

noncomputable def pairScale {n : ℕ} {K R : Type*} [Field K] [CommRing R] [Algebra K R]
    (k A B : ℕ) (q : Fin n → R) (L : R →ₐ[K] Polynomial R)
    (hq : ∀ i, L (q i) = Polynomial.monomial (k*A+B) (q i)) :
    PairRing k q →ₐ[K] Polynomial (PairRing k q) :=
  Ideal.Quotient.liftₐ _ (pairScalePre k A B q L) (by
    have hh : Ideal.span (Set.range (pairRelation k q)) ≤
        RingHom.ker (pairScalePre k A B q L).toRingHom := by
      apply Ideal.span_le.mpr
      rintro _ ⟨i,rfl⟩
      exact pairScalePre_relation k A B q L hq i
    exact fun x hx => hh hx)

theorem pairNormalBasis_apply {n : ℕ} {R : Type*} [CommRing R] [IsDomain R]
    (k : ℕ) (q : Fin n → R) (hq : ∀ i, q i ≠ 0)
    (m : {m : (Fin n ⊕ Fin n) →₀ ℕ // PairNormal k m}) :
    pairNormalBasis k q hq m = Ideal.Quotient.mk _ (monomial m.val 1) := by
  simp only [pairNormalBasis, Module.Basis.map_apply, pairNormalEquiv,
    LinearEquiv.ofBijective_apply, LinearMap.comp_apply, Submodule.subtype_apply,
    AlgHom.toLinearMap_apply, Ideal.Quotient.mkₐ_eq_mk]
  congr 1
  ext d
  change (((AddMonoidAlgebra.supportedEquivFinsupp _).symm
    (Finsupp.single m (1:R))) : MvPolynomial (Fin n ⊕ Fin n) R).coeff d = _
  simp only [AddMonoidAlgebra.supportedEquivFinsupp, LinearEquiv.symm_trans_apply]
  change (((Finsupp.supportedEquivFinsupp (R := R) {m | PairNormal k m}).symm
    (Finsupp.single m (1:R))) : (((Fin n ⊕ Fin n) →₀ ℕ) →₀ R)) d = _
  rw [Finsupp.supportedEquivFinsupp_symm_single]
  rfl

theorem aevalTower_monomial_homogeneous {σ K R S : Type*} [Field K] [CommRing R]
    [CommRing S] [Algebra K R] [Algebra K S]
    (f : R →ₐ[K] S) (L : R →ₐ[K] Polynomial S) (g : σ → S) (w : σ → ℕ)
    (m : σ →₀ ℕ) (r : R) (e : ℕ) (hr : L r = Polynomial.monomial e (f r)) :
    MvPolynomial.aevalTower L (fun i => Polynomial.monomial (w i) (g i)) (monomial m r) =
      Polynomial.monomial (e + Finsupp.weight w m)
        (MvPolynomial.aevalTower f g (monomial m r)) := by
  classical
  change eval₂ L.toRingHom _ (monomial m r) = Polynomial.monomial _
    (eval₂ f.toRingHom g (monomial m r))
  rw [eval₂_monomial, eval₂_monomial]
  simp only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom]
  rw [hr]
  simp only [← Polynomial.C_mul_X_pow_eq_monomial, Finsupp.prod, mul_pow,
    ← map_pow, Finset.prod_mul_distrib, ← map_prod]
  simp only [← pow_mul, Finset.prod_pow_eq_pow_sum]
  have hw : (∑ i ∈ m.support, w i * m i) = Finsupp.weight w m := by
    simp [Finsupp.weight, Finsupp.linearCombination_apply, Finsupp.sum, mul_comm]
  rw [hw, pow_add, map_mul]
  ring

theorem pairScale_monomial {n : ℕ} {K R : Type*} [Field K] [CommRing R] [Algebra K R]
    (k A B : ℕ) (q : Fin n → R) (L : R →ₐ[K] Polynomial R)
    (hq : ∀ i, L (q i) = Polynomial.monomial (k*A+B) (q i))
    (m : (Fin n ⊕ Fin n) →₀ ℕ) (r : R) (e : ℕ)
    (hr : L r = Polynomial.monomial e r) :
    pairScale k A B q L hq (Ideal.Quotient.mk _ (monomial m r)) =
      Polynomial.monomial (e+Finsupp.weight (Sum.elim (fun _ => A) (fun _ => B)) m)
        (Ideal.Quotient.mk _ (monomial m r)) := by
  change pairScalePre k A B q L (monomial m r) = _
  have hs := aevalTower_monomial_homogeneous (pairCoeffs (K := K) k q)
    ((Polynomial.mapAlgHom (pairCoeffs (K := K) k q)).comp L)
    (fun i : Fin n ⊕ Fin n => Ideal.Quotient.mk _ (X i))
    (Sum.elim (fun _ => A) (fun _ => B)) m r e
    (by simp [hr])
  have he : MvPolynomial.aevalTower (pairCoeffs (K := K) k q)
      (fun i : Fin n ⊕ Fin n => Ideal.Quotient.mk _ (X i)) = Ideal.Quotient.mkₐ K _ := by
    apply MvPolynomial.algHom_ext'
    · ext r
      simp [pairCoeffs]
    · intro i
      simp
  simpa only [pairScalePre, he, Ideal.Quotient.mkₐ_eq_mk] using hs

theorem pairNormalBasis_smul {n : ℕ} {R : Type*} [CommRing R] [IsDomain R]
    (k : ℕ) (q : Fin n → R) (hq : ∀ i, q i ≠ 0)
    (m : {m : (Fin n ⊕ Fin n) →₀ ℕ // PairNormal k m}) (r : R) :
    r • pairNormalBasis k q hq m = Ideal.Quotient.mk _ (monomial m.val r) := by
  rw [pairNormalBasis_apply]
  have hh := map_smul (Ideal.Quotient.mkₐ R (Ideal.span (Set.range (pairRelation k q)))) r
    (monomial m.val 1)
  simpa [MvPolynomial.smul_monomial, smul_eq_mul] using hh.symm

theorem pairBasis_homogeneous {n : ℕ} {ι K R : Type*} [Field K] [CommRing R]
    [IsDomain R] [Algebra K R]
    (k A B : ℕ) (q : Fin n → R) (hnq : ∀ i, q i ≠ 0)
    (L : R →ₐ[K] Polynomial R)
    (hq : ∀ i, L (q i) = Polynomial.monomial (k*A+B) (q i))
    (b : Module.Basis ι K R) (w : ι → ℕ)
    (hb : ∀ i, L (b i) = Polynomial.monomial (w i) (b i))
    (i : ι × {m : (Fin n ⊕ Fin n) →₀ ℕ // PairNormal k m}) :
    pairScale k A B q L hq ((b.smulTower (pairNormalBasis k q hnq)) i) =
      Polynomial.monomial (w i.1 +
        Finsupp.weight (Sum.elim (fun _ => A) (fun _ => B)) i.2.val)
        ((b.smulTower (pairNormalBasis k q hnq)) i) := by
  simp only [Module.Basis.smulTower_apply, pairNormalBasis_smul]
  exact pairScale_monomial k A B q L hq i.2.val (b i.1) (w i.1) (hb i.1)

noncomputable def normPair_weightedLift {σ R : Type*} [CommSemiring R] (w : σ → ℕ) :
    MvPolynomial σ R →+* Polynomial (MvPolynomial σ R) :=
  eval₂Hom (Polynomial.C.comp C)
    (fun i => Polynomial.C (X i) * Polynomial.X ^ w i)

theorem normPair_weightedLift_monomial {σ R : Type*} [CommSemiring R] (w : σ → ℕ)
    (m : σ →₀ ℕ) (r : R) :
    normPair_weightedLift w (monomial m r) =
      Polynomial.C (monomial m r) * Polynomial.X ^ (Finsupp.weight w m) := by
  classical
  simp only [normPair_weightedLift, eval₂Hom_monomial, RingHom.comp_apply]
  simp only [Finsupp.prod, mul_pow, ← map_pow, Finset.prod_mul_distrib,
    ← map_prod]
  rw [← mul_assoc, ← Polynomial.C_mul]
  congr 1
  · rw [monomial_eq, Finsupp.prod]
  · simp only [← pow_mul, Finset.prod_pow_eq_pow_sum]
    congr 1
    simp [Finsupp.weight, Finsupp.linearCombination_apply, Finsupp.sum, mul_comm]

noncomputable def weightedScale {σ K : Type*} [Field K] (w : σ → ℕ) :
    MvPolynomial σ K →ₐ[K] Polynomial (MvPolynomial σ K) where
  toRingHom := normPair_weightedLift w
  commutes' := by
    intro r
    simp [normPair_weightedLift, MvPolynomial.algebraMap_eq, Polynomial.algebraMap_apply]

theorem weightedScale_monomial {σ K : Type*} [Field K] (w : σ → ℕ)
    (m : σ →₀ ℕ) (r : K) :
    weightedScale w (MvPolynomial.monomial m r) =
      Polynomial.monomial (Finsupp.weight w m) (MvPolynomial.monomial m r) := by
  exact (normPair_weightedLift_monomial w m r).trans Polynomial.C_mul_X_pow_eq_monomial

theorem weightedScale_X {σ K : Type*} [Field K] (w : σ → ℕ) (i : σ) :
    weightedScale (K := K) w (X i) = Polynomial.monomial (w i) (X i) := by
  simp [weightedScale, normPair_weightedLift, Polynomial.C_mul_X_pow_eq_monomial]

theorem weightedScale_C {σ K : Type*} [Field K] (w : σ → ℕ) (r : K) :
    weightedScale w (MvPolynomial.C r) = Polynomial.monomial 0 (MvPolynomial.C r) := by
  simp [weightedScale, normPair_weightedLift]

def triplePairWeights (A B : ℕ) : Fin 3 → ℕ := ![A,B,1]

noncomputable def pairConeQ {n : ℕ} {K : Type*} [Field K]
    (k A B : ℕ) (θ : Fin n → K) (i : Fin n) : MvPolynomial (Fin 3) K :=
  X 0 ^ k * X 1 + C (θ i) * X 2 ^ (k*A+B)

theorem pairConeQ_ne_zero {n : ℕ} {K : Type*} [Field K] (k A B : ℕ)
    (hB : 0 < B) (θ : Fin n → K) (i : Fin n) : pairConeQ k A B θ i ≠ 0 := by
  have hQ : k*A+B ≠ 0 := by omega
  intro hz
  have hh := congrArg (MvPolynomial.eval (fun i : Fin 3 => if i = 2 then (0:K) else 1)) hz
  simp only [pairConeQ, map_add, map_mul, map_pow, MvPolynomial.eval_X,
    MvPolynomial.eval_C, show (0 : Fin 3) ≠ 2 by decide,
    show (1 : Fin 3) ≠ 2 by decide, ite_false, ite_true, one_pow, one_mul,
    zero_pow hQ, mul_zero, add_zero, map_zero] at hh
  exact one_ne_zero hh

theorem pairConeQ_homogeneous {n : ℕ} {K : Type*} [Field K]
    (k A B : ℕ) (θ : Fin n → K) (i : Fin n) :
    weightedScale (triplePairWeights A B) (pairConeQ k A B θ i) =
      Polynomial.monomial (k*A+B) (pairConeQ k A B θ i) := by
  simp only [pairConeQ, map_add, map_mul, map_pow, weightedScale_X, weightedScale_C,
    triplePairWeights, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Polynomial.monomial_pow, Polynomial.monomial_mul_monomial,
    Nat.one_mul, Nat.zero_add, Nat.mul_comm A k]

end QuarticPowerFree

end OAI
