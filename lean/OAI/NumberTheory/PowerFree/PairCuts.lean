import OAI.NumberTheory.PowerFree.PairHilbert

namespace OAI

namespace QuarticPowerFree
open scoped BigOperators
abbrev PairBasisIndex (n k : ℕ) :=
  (Fin 3 →₀ ℕ) × {m : (Fin n ⊕ Fin n) →₀ ℕ // PairNormal k m}

def pairIndexToTuple {n k : ℕ} (i : PairBasisIndex n k) : Fin (n+1) → ℕ × ℕ :=
  Fin.cons (i.1 0, i.1 1) (fun j => (i.2.val (Sum.inl j), i.2.val (Sum.inr j)))

noncomputable def tupleBasisIndex {n k : ℕ} (p : Fin (n+1) → ℕ × ℕ) (t : ℕ)
    (hp : ∀ i : Fin n, (p i.succ).1 < k ∨ (p i.succ).2 = 0) : PairBasisIndex n k :=
  (Finsupp.equivFunOnFinite.symm ![(p 0).1, (p 0).2, t],
   ⟨Finsupp.equivFunOnFinite.symm (Sum.elim (fun i => (p i.succ).1) (fun i => (p i.succ).2)),
    by simpa [PairNormal] using hp⟩)

noncomputable def pairBasisWeight {n k : ℕ} (A B : ℕ) (i : PairBasisIndex n k) : ℕ :=
  Finsupp.weight (triplePairWeights A B) i.1 +
  Finsupp.weight (Sum.elim (fun _ => A) (fun _ => B)) i.2.val

theorem pairIndexToTuple_normal {n k : ℕ} (i : PairBasisIndex n k) :
    ∀ j : Fin n, (pairIndexToTuple i j.succ).1 < k ∨
      (pairIndexToTuple i j.succ).2 = 0 := by
  simpa [pairIndexToTuple, PairNormal] using i.2.property

theorem pairBasisWeight_eq {n k : ℕ} (A B : ℕ) (i : PairBasisIndex n k) :
    pairBasisWeight A B i = i.1 2 + ∑ j, (A*(pairIndexToTuple i j).1+B*(pairIndexToTuple i j).2) := by
  simp only [pairBasisWeight, Finsupp.weight_eq_sum, smul_eq_mul,
    Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr]
  have h3 : (∑ j : Fin 3, i.1 j * triplePairWeights A B j) =
      i.1 0 * A + i.1 1 * B + i.1 2 := by
    simp [Fin.sum_univ_succ, triplePairWeights, add_assoc]
  rw [h3, Fin.sum_univ_succ]
  simp only [pairIndexToTuple, Fin.cons_zero, Fin.cons_succ,
    Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum]
  ring

theorem pairIndexToTuple_tupleBasisIndex {n k : ℕ} (p : Fin (n+1) → ℕ × ℕ)
    (t : ℕ) (hp : ∀ i : Fin n, (p i.succ).1 < k ∨ (p i.succ).2 = 0) :
    pairIndexToTuple (tupleBasisIndex p t hp) = p := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [pairIndexToTuple, tupleBasisIndex]
  · simp [pairIndexToTuple, tupleBasisIndex]

theorem tupleBasisIndex_pairIndexToTuple {n k : ℕ} (i : PairBasisIndex n k) :
    tupleBasisIndex (pairIndexToTuple i) (i.1 2) (pairIndexToTuple_normal i) = i := by
  apply Prod.ext
  · ext j
    fin_cases j <;> simp [tupleBasisIndex, pairIndexToTuple]
  · apply Subtype.ext
    ext j
    cases j <;> simp [tupleBasisIndex, pairIndexToTuple]

noncomputable def pairBasisWeightEquiv {n k A B : ℕ} (hA : 0 < A) (hB : 0 < B) (T : ℕ) :
    {i : PairBasisIndex n k // pairBasisWeight A B i = T} ≃
      {p // p ∈ ambientPairTuples n A B k T} where
  toFun i := ⟨pairIndexToTuple i.val, (mem_ambientPairTuples hA hB _).mpr
    ⟨pairIndexToTuple_normal i.val, by
      have hi := i.property
      rw [pairBasisWeight_eq] at hi
      omega⟩⟩
  invFun p := ⟨tupleBasisIndex p.val (T-∑ j, (A*(p.val j).1+B*(p.val j).2))
    ((mem_ambientPairTuples hA hB p.val).mp p.property).1, by
      rw [pairBasisWeight_eq, pairIndexToTuple_tupleBasisIndex]
      change (T - ∑ j, (A*(p.val j).1+B*(p.val j).2)) +
        (∑ j, (A*(p.val j).1+B*(p.val j).2)) = T
      exact Nat.sub_add_cancel ((mem_ambientPairTuples hA hB p.val).mp p.property).2⟩
  left_inv i := by
    apply Subtype.ext
    have hi := i.property
    rw [pairBasisWeight_eq] at hi
    have ht : T - ∑ j, (A*(pairIndexToTuple i.val j).1+B*(pairIndexToTuple i.val j).2) = i.val.1 2 := by omega
    dsimp only
    rw [ht]
    exact tupleBasisIndex_pairIndexToTuple i.val
  right_inv p := by
    apply Subtype.ext
    dsimp only
    exact pairIndexToTuple_tupleBasisIndex p.val _ _

abbrev PairCone {n : ℕ} {K : Type*} [Field K] (k A B : ℕ) (θ : Fin n → K) :=
  PairRing k (pairConeQ k A B θ)

noncomputable def pairConeScale {n : ℕ} {K : Type*} [Field K]
    (k A B : ℕ) (θ : Fin n → K) :
    PairCone k A B θ →ₐ[K] Polynomial (PairCone k A B θ) :=
  pairScale k A B (pairConeQ k A B θ) (weightedScale (triplePairWeights A B))
    (pairConeQ_homogeneous k A B θ)

noncomputable def pairConeBasis {n : ℕ} {K : Type*} [Field K]
    (k A B : ℕ) (hB : 0 < B) (θ : Fin n → K) :
    Module.Basis (PairBasisIndex n k) K (PairCone k A B θ) :=
  (MvPolynomial.basisMonomials (Fin 3) K).smulTower
    (pairNormalBasis k (pairConeQ k A B θ) (pairConeQ_ne_zero k A B hB θ))

theorem pairConeBasis_homogeneous {n : ℕ} {K : Type*} [Field K]
    (k A B : ℕ) (hB : 0 < B) (θ : Fin n → K) (i : PairBasisIndex n k) :
    pairConeScale k A B θ (pairConeBasis k A B hB θ i) =
      Polynomial.monomial (pairBasisWeight A B i) (pairConeBasis k A B hB θ i) := by
  apply pairBasis_homogeneous
  intro m
  exact weightedScale_monomial (triplePairWeights A B) m 1

theorem pairCone_finite {n : ℕ} {K : Type*} [Field K]
    (k A B : ℕ) (hA : 0 < A) (hB : 0 < B) (θ : Fin n → K) (T : ℕ) :
    Module.Finite K (homogeneousSpace (pairConeScale k A B θ) T) := by
  classical
  let := Fintype.ofEquiv _ (pairBasisWeightEquiv (n := n) (k := k) hA hB T).symm
  exact homogeneousSpace_finite _ (pairConeBasis k A B hB θ) (pairBasisWeight A B)
    (pairConeBasis_homogeneous k A B hB θ) T

theorem pairCone_finrank {n : ℕ} {K : Type*} [Field K]
    (k A B : ℕ) (hA : 0 < A) (hB : 0 < B) (θ : Fin n → K) (T : ℕ) :
    Module.finrank K (homogeneousSpace (pairConeScale k A B θ) T) =
      (ambientPairTuples n A B k T).card := by
  classical
  let := Fintype.ofEquiv _ (pairBasisWeightEquiv (n := n) (k := k) hA hB T).symm
  rw [homogeneousSpace_finrank _ (pairConeBasis k A B hB θ) (pairBasisWeight A B)
    (pairConeBasis_homogeneous k A B hB θ) T]
  exact (Fintype.card_congr (pairBasisWeightEquiv hA hB T)).trans (Fintype.card_coe _)

theorem pairCone_cut_hilbert {n : ℕ} {K : Type*} [Field K]
    (k A B : ℕ) (hA : 0 < A) (hB : 0 < B) (θ : Fin n → K)
    (u v : ℕ) (c : PairCone k A B θ) (hc : c ≠ 0)
    (hC : pairConeScale k A B θ c = Polynomial.monomial (A*u+B*v) c) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℕ, A*u+B*v ≤ T →
      |(Module.finrank K ((homogeneousSpace (pairConeScale k A B θ) T).map
        (Ideal.Quotient.mkₐ K (Ideal.span {c})).toLinearMap) : ℝ) -
        ((A*u+B*v : ℕ):ℝ)*((k*A+B : ℕ):ℝ)^n /
          (((n+1).factorial:ℝ)*(A:ℝ)^(n+1)*(B:ℝ)^(n+1))*(T:ℝ)^(n+1)| ≤
        C*((T:ℝ)+1)^n := by
  let : (Ideal.span (Set.range (pairRelation k (pairConeQ k A B θ)))).IsPrime :=
    pair_ideal_isPrime k _ (pairConeQ_ne_zero k A B hB θ)
  obtain ⟨C,hC0,herror⟩ := pairFilteredDifference_hilbert_error (h := n) (k := k) hA hB u v
  refine ⟨C,hC0,fun T hT => ?_⟩
  let := pairCone_finite k A B hA hB θ (A*u+B*v+(T-(A*u+B*v)))
  have he := homogeneous_principal_finrank (pairConeScale k A B θ)
    (A*u+B*v) (T-(A*u+B*v)) c hc hC
  rw [Nat.add_sub_of_le hT, pairCone_finrank k A B hA hB θ,
    pairCone_finrank k A B hA hB θ] at he
  have he' := congrArg (Nat.cast : ℕ → ℝ) he
  push_cast at he'
  have h := herror T
  simp only [ite_eq_left hT] at h
  rw [← he', add_sub_cancel_right] at h
  exact h

open MvPolynomial

noncomputable def pairMap {n : ℕ} {R S : Type*} [CommRing R] [CommRing S]
    (k : ℕ) (q : Fin n → R) (f : R →+* S) :
    PairRing k q →+* PairRing k (fun i => f (q i)) :=
  Ideal.Quotient.lift _ ((Ideal.Quotient.mk _).comp (MvPolynomial.map f)) (by
    have h : Ideal.span (Set.range (pairRelation k q)) ≤
        RingHom.ker ((Ideal.Quotient.mk (Ideal.span
          (Set.range (pairRelation k (fun i => f (q i)))))).comp (MvPolynomial.map f)) := by
      apply Ideal.span_le.mpr
      rintro _ ⟨i,rfl⟩
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      have hm : MvPolynomial.map f (pairRelation k q i) =
          pairRelation k (fun i => f (q i)) i := by simp [pairRelation]
      change MvPolynomial.map f (pairRelation k q i) ∈ _
      rw [hm]
      exact Ideal.subset_span ⟨i,rfl⟩
    exact fun p hp => h hp)

@[simp] theorem pairMap_mk {n : ℕ} {R S : Type*} [CommRing R] [CommRing S]
    (k : ℕ) (q : Fin n → R) (f : R →+* S) (p : MvPolynomial (Fin n ⊕ Fin n) R) :
    pairMap k q f (Ideal.Quotient.mk _ p) =
      Ideal.Quotient.mk _ (MvPolynomial.map f p) := rfl

noncomputable def pairCoeffMap {n : ℕ} {R : Type*} [CommRing R]
    (k : ℕ) (q : Fin n → R) : R →+* PairRing k q :=
  (Ideal.Quotient.mk _).comp MvPolynomial.C

theorem pairMap_eq_zero_iff_dvd {n : ℕ} {R S : Type*} [CommRing R] [IsDomain R]
    [CommRing S] [IsDomain S] (k : ℕ) (q : Fin n → R) (f : R →+* S)
    (hq : ∀ i, q i ≠ 0) (hFq : ∀ i, f (q i) ≠ 0)
    (t : R) (ht : ∀ r, f r = 0 ↔ t ∣ r) (x : PairRing k q) :
    pairMap k q f x = 0 ↔ pairCoeffMap k q t ∣ x := by
  classical
  obtain ⟨p,hp⟩ := (pair_normal_quotient_bijective k q hq).2 x
  change Ideal.Quotient.mk _ p.val = x at hp
  subst x
  constructor
  · intro hx
    have hn : ∀ m ∈ (MvPolynomial.map f p.val).support, PairNormal k m :=
      fun m hm => p.property (MvPolynomial.support_map_subset _ _ hm)
    have hz : MvPolynomial.map f p.val = 0 := by
      apply pairLaurentMap_normal_injective k (fun i => f (q i)) hFq _ hn
      have hh : MvPolynomial.map f p.val ∈
          Ideal.span (Set.range (pairRelation k (fun i => f (q i)))) :=
        Ideal.Quotient.eq_zero_iff_mem.mp hx
      rwa [pair_ideal_eq_ker k _ hFq] at hh
    obtain ⟨r,hr⟩ := (MvPolynomial.C_dvd_iff_map_hom_eq_zero f t ht p.val).mpr hz
    refine ⟨Ideal.Quotient.mk _ r, ?_⟩
    change Ideal.Quotient.mk _ p.val =
      Ideal.Quotient.mk _ (C t) * Ideal.Quotient.mk _ r
    rw [← map_mul, hr]
  · rintro ⟨r,hr⟩
    rw [hr, map_mul]
    have hft : f t = 0 := (ht t).mpr dvd_rfl
    suffices pairMap k q f (pairCoeffMap k q t) = 0 by rw [this, zero_mul]
    change Ideal.Quotient.mk _ (MvPolynomial.map f (C t)) = 0
    simp [hft]

theorem pairCoeff_span_isPrime {n : ℕ} {R S : Type*} [CommRing R] [IsDomain R]
    [CommRing S] [IsDomain S] (k : ℕ) (q : Fin n → R) (f : R →+* S)
    (hq : ∀ i, q i ≠ 0) (hFq : ∀ i, f (q i) ≠ 0)
    (t : R) (ht : ∀ r, f r = 0 ↔ t ∣ r) :
    (Ideal.span {pairCoeffMap k q t}).IsPrime := by
  let : (Ideal.span (Set.range (pairRelation k (fun i => f (q i))))).IsPrime :=
    pair_ideal_isPrime k _ hFq
  have he : Ideal.span {pairCoeffMap k q t} = RingHom.ker (pairMap k q f) := by
    ext x
    simp only [Ideal.mem_span_singleton, RingHom.mem_ker]
    exact (pairMap_eq_zero_iff_dvd k q f hq hFq t ht x).symm
  rw [he]
  exact RingHom.ker_isPrime _

theorem pairCoeffMap_injective {n : ℕ} {R : Type*} [CommRing R] [IsDomain R]
    (k : ℕ) (q : Fin n → R) (hq : ∀ i, q i ≠ 0) :
    Function.Injective (pairCoeffMap k q) := by
  intro r s h
  have hm : C (r-s) ∈ Ideal.span (Set.range (pairRelation k q)) := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change pairCoeffMap k q (r-s) = 0
    rw [map_sub,h,sub_self]
  rw [pair_ideal_eq_ker k q hq] at hm
  have hh : pairLaurentMap k q (C (r-s)) = 0 := hm
  simpa [pairLaurentMap, AddMonoidAlgebra.single_eq_zero, sub_eq_zero] using hh

open Classical

noncomputable def eraseVariable {σ R : Type*} [CommRing R] (i : σ) :
    MvPolynomial σ R →+* MvPolynomial σ R := by
  classical
  exact eval₂Hom C (fun j => if j = i then 0 else X j)

@[simp] theorem eraseVariable_X {σ R : Type*} [CommRing R] (i j : σ) :
    eraseVariable (R := R) i (X j) = if j = i then 0 else X j := by
  classical
  simp [eraseVariable]

@[simp] theorem eraseVariable_C {σ R : Type*} [CommRing R] (i : σ) (r : R) :
    eraseVariable i (C r) = C r := by simp [eraseVariable]

theorem X_dvd_sub_eraseVariable {σ R : Type*} [CommRing R]
    (i : σ) (p : MvPolynomial σ R) : X i ∣ p - eraseVariable i p := by
  classical
  induction p using MvPolynomial.induction_on with
  | C r => simp
  | add p q hp hq =>
    simpa only [map_add, add_sub_add_comm] using dvd_add hp hq
  | mul_X p j hp =>
    rw [map_mul, eraseVariable_X]
    by_cases hj : j = i
    · simp only [hj, ite_true, mul_zero, sub_zero]
      exact dvd_mul_left _ _
    · simpa only [ite_eq_right hj, ← sub_mul] using dvd_mul_of_dvd_left hp (X j)

theorem eraseVariable_eq_zero_iff {σ R : Type*} [CommRing R]
    (i : σ) (p : MvPolynomial σ R) : eraseVariable i p = 0 ↔ X i ∣ p := by
  classical
  constructor
  · intro h
    simpa [h] using X_dvd_sub_eraseVariable i p
  · rintro ⟨r,rfl⟩
    simp

theorem dvd_of_dvd_prime_mul {R : Type*} [CommRing R] [IsDomain R]
    {a c x : R} (ha : Prime a) (hc : ¬ a ∣ c) (h : c ∣ a * x) : c ∣ x := by
  obtain ⟨y, hy⟩ := h
  have hay : a ∣ y := (ha.dvd_or_dvd (show a ∣ c * y by rw [← hy]; exact dvd_mul_right _ _)).resolve_left hc
  obtain ⟨z, rfl⟩ := hay
  refine ⟨z, ?_⟩
  apply mul_left_cancel₀ ha.ne_zero
  calc
    a * x = c * (a * z) := hy
    _ = a * (c * z) := by ring

theorem dvd_of_dvd_coordinate_mul {R : Type*} [CommRing R] [IsDomain R]
    (s : Set R) {c x a : R} (hp : ∀ a ∈ s, Prime a)
    (hc : ∀ a ∈ s, ¬ a ∣ c) (ha : a ∈ Submonoid.closure s) (h : c ∣ a * x) :
    c ∣ x := by
  suffices hh : ∀ x, c ∣ a * x → c ∣ x from hh x h
  clear h x
  induction ha using Submonoid.closure_induction with
  | mem a ha => exact fun _ h => dvd_of_dvd_prime_mul (hp _ ha) (hc _ ha) h
  | one => simp
  | mul a b ha hb ihA ihB =>
    intro x h
    exact ihB x (ihA (b * x) (by simpa [mul_assoc] using h))

theorem principal_under_map_coordinates {R S : Type*}
    [CommRing R] [IsDomain R] [CommRing S] [Algebra R S]
    (s : Set R) [IsLocalization (Submonoid.closure s) S]
    (c : R) (hp : ∀ a ∈ s, Prime a) (hc : ∀ a ∈ s, ¬ a ∣ c) :
    Ideal.comap (algebraMap R S) ((Ideal.span {c}).map (algebraMap R S)) =
      Ideal.span {c} := by
  ext x
  rw [Ideal.mem_comap, IsLocalization.algebraMap_mem_map_algebraMap_iff
    (Submonoid.closure s), Ideal.mem_span_singleton]
  constructor
  · rintro ⟨a, ha, hax⟩
    exact dvd_of_dvd_coordinate_mul s hp hc ha (Ideal.mem_span_singleton.mp hax)
  · intro h
    exact ⟨1, (Submonoid.closure s).one_mem, by simpa [Ideal.mem_span_singleton] using h⟩

theorem principal_isPrime_of_localization_coordinates {R S : Type*}
    [CommRing R] [IsDomain R] [CommRing S] [Algebra R S]
    (s : Set R) [IsLocalization (Submonoid.closure s) S]
    (c : R) (hp : ∀ a ∈ s, Prime a) (hc : ∀ a ∈ s, ¬ a ∣ c)
    (hlocal : ((Ideal.span {c}).map (algebraMap R S)).IsPrime) :
    (Ideal.span {c}).IsPrime := by
  rw [← principal_under_map_coordinates (S := S) s c hp hc]
  have : ((Ideal.span {c}).map (algebraMap R S)).IsPrime := hlocal
  exact Ideal.comap_isPrime _ _

theorem principal_saturated_power {R : Type*} [CommRing R] [IsDomain R]
    {c t x : R} (ht : Prime t) (hc : ¬ t ∣ c) (n : ℕ) (h : c ∣ t ^ n * x) : c ∣ x := by
  induction n generalizing x with
  | zero => simpa using h
  | succ n ih =>
    apply ih
    apply dvd_of_dvd_prime_mul ht hc
    simpa [pow_succ, mul_comm t, mul_assoc] using h

theorem saturated_quotient_localization_injective {R : Type*} [CommRing R] [IsDomain R]
    {c t : R} (ht : Prime t) (hc : ¬ t ∣ c) :
    Function.Injective (algebraMap (R ⧸ Ideal.span {c})
      (Localization.Away (Ideal.Quotient.mk (Ideal.span {c}) t))) := by
  apply IsLocalization.injective (M := Submonoid.powers (Ideal.Quotient.mk (Ideal.span {c}) t))
  rintro s ⟨n, rfl⟩
  apply mem_nonZeroDivisors_iff_left.mpr
  intro x hx
  obtain ⟨x,rfl⟩ := Ideal.Quotient.mk_surjective x
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  apply Ideal.mem_span_singleton.mpr
  apply principal_saturated_power ht hc n
  apply Ideal.mem_span_singleton.mp
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  simpa only [map_mul, map_pow] using hx

theorem homogeneous_dehomogenization_kernel {K R : Type*} [Field K] [CommRing R]
    [IsDomain R] [Algebra K R] (L : R →ₐ[K] Polynomial R)
    {c t x : R} {E T : ℕ} (ht : Prime t) (hc : ¬ t ∣ c)
    (hT : L t = Polynomial.monomial 1 t)
    (hC : L c = Polynomial.monomial E c)
    (hX : L x = Polynomial.monomial T x) :
    x ∈ Ideal.span {c} ⊔ Ideal.span {t-1} ↔ x ∈ Ideal.span {c} := by
  constructor
  · intro hx
    let Q := R ⧸ Ideal.span {c}
    let S := Localization.Away (Ideal.Quotient.mk (Ideal.span {c}) t)
    let q : R →+* Q := Ideal.Quotient.mk (Ideal.span {c})
    let a : R →+* S := (algebraMap Q S).comp q
    let z : S := IsLocalization.Away.invSelf (q t)
    let ev : R →+* S := (Polynomial.eval₂RingHom a z).comp L.toRingHom
    have hq : q c = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span rfl)
    have hevC : ev c = 0 := by
      change Polynomial.eval₂ a z (L c) = 0
      rw [hC, Polynomial.eval₂_monomial]
      have ha : a c = 0 := by change (algebraMap Q S) (q c) = 0; simp [hq]
      simp [ha]
    have hevT : ev (t-1) = 0 := by
      rw [map_sub, map_one, sub_eq_zero]
      change Polynomial.eval₂ a z (L t) = 1
      rw [hT, Polynomial.eval₂_monomial, pow_one]
      exact IsLocalization.Away.mul_invSelf (q t)
    have hker : Ideal.span {c} ⊔ Ideal.span {t-1} ≤ RingHom.ker ev := by
      apply sup_le
      · exact Ideal.span_le.mpr (by rintro _ rfl; exact hevC)
      · exact Ideal.span_le.mpr (by rintro _ rfl; exact hevT)
    have hh : a x * z^T = 0 := by
      have h := hker hx
      change Polynomial.eval₂ a z (L x) = 0 at h
      rwa [hX, Polynomial.eval₂_monomial] at h
    have hz : a t * z = 1 := IsLocalization.Away.mul_invSelf (q t)
    have ha : a x = 0 := by
      have he := congrArg (fun y : S => y * (a t)^T) hh
      have hz' : z*a t = 1 := by rwa [mul_comm] at hz
      simpa only [mul_assoc, ← mul_pow, hz', one_pow, mul_one, zero_mul] using he
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    apply saturated_quotient_localization_injective ht hc
    change a x = (algebraMap Q S) 0
    simpa using ha
  · intro hx
    exact (show Ideal.span {c} ≤ Ideal.span {c} ⊔ Ideal.span {t-1} from le_sup_left) hx

theorem homogeneous_dehomogenization_finrank {K R : Type*} [Field K] [CommRing R]
    [IsDomain R] [Algebra K R] (L : R →ₐ[K] Polynomial R)
    {c t : R} {E T : ℕ} [Module.Finite K (homogeneousSpace L T)]
    (ht : Prime t) (hc : ¬ t ∣ c)
    (hT : L t = Polynomial.monomial 1 t)
    (hC : L c = Polynomial.monomial E c) :
    Module.finrank K ((homogeneousSpace L T).map
      (Ideal.Quotient.mkₐ K (Ideal.span {c} ⊔ Ideal.span {t-1})).toLinearMap) =
    Module.finrank K ((homogeneousSpace L T).map
      (Ideal.Quotient.mkₐ K (Ideal.span {c})).toLinearMap) := by
  let F := homogeneousSpace L T
  let f := (Ideal.Quotient.mkₐ K (Ideal.span {c} ⊔ Ideal.span {t-1})).toLinearMap.domRestrict F
  let g := (Ideal.Quotient.mkₐ K (Ideal.span {c})).toLinearMap.domRestrict F
  have he : LinearMap.ker f = LinearMap.ker g := by
    ext x
    change Ideal.Quotient.mk _ x.val = 0 ↔ Ideal.Quotient.mk _ x.val = 0
    simp only [Ideal.Quotient.eq_zero_iff_mem]
    exact homogeneous_dehomogenization_kernel L ht hc hT hC x.property
  have h := f.finrank_range_add_finrank_ker.trans g.finrank_range_add_finrank_ker.symm
  rw [he] at h
  have hh := Nat.add_right_cancel h
  change Module.finrank K (LinearMap.range ((Ideal.Quotient.mkₐ K
    (Ideal.span {c} ⊔ Ideal.span {t-1})).toLinearMap.domRestrict F)) =
    Module.finrank K (LinearMap.range ((Ideal.Quotient.mkₐ K
      (Ideal.span {c})).toLinearMap.domRestrict F)) at hh
  rw [LinearMap.range_domRestrict, LinearMap.range_domRestrict] at hh
  exact hh

theorem pairCone_t_prime {n : ℕ} {K : Type*} [Field K]
    (k A B : ℕ) (hB : 0 < B) (θ : Fin n → K) :
    Prime (pairCoeffMap k (pairConeQ k A B θ) (X 2)) := by
  have hq := pairConeQ_ne_zero k A B hB θ
  have hQ : k*A+B ≠ 0 := by omega
  have hf : ∀ i, eraseVariable (R := K) (2 : Fin 3) (pairConeQ k A B θ i) ≠ 0 := by
    intro i
    simp only [pairConeQ, map_add, map_mul, map_pow, eraseVariable_X,
      eraseVariable_C, show (0:Fin 3) ≠ 2 by decide, show (1:Fin 3) ≠ 2 by decide,
      ite_false, ite_true, zero_pow hQ, mul_zero, add_zero]
    exact mul_ne_zero (pow_ne_zero _ (X_ne_zero _)) (X_ne_zero _)
  have ht : pairCoeffMap k (pairConeQ k A B θ) (X 2) ≠ 0 := by
    intro hz
    exact X_ne_zero (R := K) (2 : Fin 3)
      ((pairCoeffMap_injective k _ hq) (hz.trans (map_zero _).symm))
  apply (Ideal.span_singleton_prime ht).mp
  exact pairCoeff_span_isPrime k _ (eraseVariable (R := K) (2:Fin 3)) hq hf (X 2)
    (eraseVariable_eq_zero_iff _)

theorem pairScale_coeff {n : ℕ} {K R : Type*} [Field K] [CommRing R] [Algebra K R]
    (k A B : ℕ) (q : Fin n → R) (L : R →ₐ[K] Polynomial R)
    (hq : ∀ i, L (q i) = Polynomial.monomial (k*A+B) (q i)) (r : R) :
    pairScale k A B q L hq (pairCoeffMap k q r) =
      Polynomial.map (pairCoeffMap k q) (L r) := by
  change pairScalePre k A B q L (C r) = _
  simp only [pairScalePre, MvPolynomial.aevalTower_C, AlgHom.comp_apply]
  rfl

theorem pairCone_t_homogeneous {n : ℕ} {K : Type*} [Field K]
    (k A B : ℕ) (θ : Fin n → K) :
    pairConeScale k A B θ (pairCoeffMap k (pairConeQ k A B θ) (X 2)) =
      Polynomial.monomial 1 (pairCoeffMap k (pairConeQ k A B θ) (X 2)) := by
  simp only [pairConeScale, pairScale_coeff, weightedScale_X, triplePairWeights,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Polynomial.map_monomial]

theorem pairAffine_cut_hilbert {n : ℕ} {K : Type*} [Field K]
    (k A B : ℕ) (hA : 0 < A) (hB : 0 < B) (θ : Fin n → K)
    (u v : ℕ) (c : PairCone k A B θ) (hc : c ≠ 0)
    (hC : pairConeScale k A B θ c = Polynomial.monomial (A*u+B*v) c)
    (hinfty : ¬ pairCoeffMap k (pairConeQ k A B θ) (X 2) ∣ c) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℕ, A*u+B*v ≤ T →
      |(Module.finrank K ((homogeneousSpace (pairConeScale k A B θ) T).map
        (Ideal.Quotient.mkₐ K (Ideal.span {c} ⊔
         Ideal.span {pairCoeffMap k (pairConeQ k A B θ) (X 2)-1})).toLinearMap) : ℝ) -
        ((A*u+B*v : ℕ):ℝ)*((k*A+B : ℕ):ℝ)^n /
          (((n+1).factorial:ℝ)*(A:ℝ)^(n+1)*(B:ℝ)^(n+1))*(T:ℝ)^(n+1)| ≤
        C*((T:ℝ)+1)^n := by
  let : (Ideal.span (Set.range (pairRelation k (pairConeQ k A B θ)))).IsPrime :=
    pair_ideal_isPrime k _ (pairConeQ_ne_zero k A B hB θ)
  obtain ⟨C,hC0,herror⟩ := pairCone_cut_hilbert k A B hA hB θ u v c hc hC
  refine ⟨C,hC0,fun T hT => ?_⟩
  let := pairCone_finite k A B hA hB θ T
  rw [homogeneous_dehomogenization_finrank (pairConeScale k A B θ)
    (pairCone_t_prime k A B hB θ) hinfty (pairCone_t_homogeneous k A B θ) hC]
  exact herror T hT

end QuarticPowerFree

end OAI
