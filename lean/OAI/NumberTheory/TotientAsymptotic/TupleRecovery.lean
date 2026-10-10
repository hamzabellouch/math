import OAI.NumberTheory.TotientAsymptotic.Basic

namespace OAI

/-!
The prime-occurrence allocation bound in equations (residual-factorization)
and (tuple-recovery-cost). Repeated prime factors are counted with multiplicity.
-/

open scoped BigOperators

namespace TotientAsymptotic

private lemma prod_update_div {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : ι → ℕ) (i : ι) {p : ℕ} (hp : p ∣ f i) :
    (∏ j, Function.update f i (f i / p) j) = (∏ j, f j) / p := by
  rw [Finset.prod_update_of_mem (Finset.mem_univ i)]
  rw [← Finset.mul_prod_erase Finset.univ f (Finset.mem_univ i)]
  rw [Finset.sdiff_singleton_eq_erase]
  simpa [Nat.mul_comm] using (Nat.mul_div_assoc (∏ j ∈ Finset.univ.erase i, f j) hp).symm

private lemma update_div_injOn {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Finset (ι → ℕ)) (i : ι) (p : ℕ)
    (hS : ∀ f ∈ S, p ∣ f i) :
    Set.InjOn (fun (f : ι → ℕ) => Function.update f i (f i / p)) (↑S : Set (ι → ℕ)) := by
  intro f hf f' hf' he
  funext j
  by_cases hji : j = i
  · subst j
    have hh := congrFun he i
    simp only [Function.update_self] at hh
    calc
      f i = (f i / p) * p := (Nat.div_mul_cancel (hS f hf)).symm
      _ = (f' i / p) * p := congrArg (fun t => t*p) hh
      _ = f' i := Nat.div_mul_cancel (hS f' hf')
  · simpa [Function.update_of_ne hji] using congrFun he j

/-- Ordered factorizations into `k` labeled slots are bounded by assigning each
prime occurrence to a slot. The finite set may contain any chosen restrictions. -/
theorem ordered_factorizations_card_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (n : ℕ) (hn : 0 < n) (T : Finset (ι → ℕ))
    (hT : ∀ f ∈ T, ∏ i, f i = n) :
    T.card ≤ (Fintype.card ι)^n.primeFactorsList.length := by
  classical
  induction n using Nat.strong_induction_on generalizing T with
  | h n ih =>
    by_cases hn1 : n = 1
    · subst n
      have hf (f : ι → ℕ) (hf : f ∈ T) (i : ι) : f i = 1 := by
        apply Nat.dvd_one.mp
        rw [← hT f hf]
        exact Finset.dvd_prod_of_mem f (Finset.mem_univ i)
      have hc : T.card ≤ 1 := Finset.card_le_one.mpr (fun f hff f' hff' =>
        funext (fun i => (hf f hff i).trans (hf f' hff' i).symm))
      simpa using hc
    · obtain ⟨p, hp, hpn⟩ := Nat.exists_prime_and_dvd hn1
      have hquot : 0 < n/p := Nat.div_pos (Nat.le_of_dvd hn hpn) hp.pos
      have hlt : n/p < n := Nat.div_lt_self hn hp.one_lt
      let S : ι → Finset (ι → ℕ) := fun i => T.filter (fun f => p ∣ f i)
      let U : ι → Finset (ι → ℕ) := fun i =>
        (S i).image (fun f => Function.update f i (f i/p))
      have hU (i : ι) : (U i).card ≤ (Fintype.card ι)^(n/p).primeFactorsList.length := by
        apply ih (n/p) hlt hquot (U i)
        intro f hf
        obtain ⟨f', hf', rfl⟩ := Finset.mem_image.mp hf
        have hf'' := Finset.mem_filter.mp hf'
        rw [prod_update_div f' i hf''.2, hT f' hf''.1]
      have hS (i : ι) : (S i).card = (U i).card := by
        symm
        apply Finset.card_image_of_injOn
        exact update_div_injOn (S i) i p (fun f hf => (Finset.mem_filter.mp hf).2)
      have hcover : T ⊆ Finset.univ.biUnion S := by
        intro f hf
        have hdiv : p ∣ ∏ i, f i := by rw [hT f hf]; exact hpn
        obtain ⟨i, _, hi⟩ := (hp.prime.dvd_finsetProd_iff f).mp hdiv
        exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, Finset.mem_filter.mpr ⟨hf, hi⟩⟩
      have hlength : n.primeFactorsList.length = 1+(n/p).primeFactorsList.length := by
        have hprod : p*(n/p) = n := Nat.mul_div_cancel' hpn
        have hperm := Nat.perm_primeFactorsList_mul hp.ne_zero hquot.ne'
        rw [hprod, Nat.primeFactorsList_prime hp] at hperm
        simpa [Nat.add_comm] using hperm.length_eq
      calc
        T.card ≤ (Finset.univ.biUnion S).card := Finset.card_le_card hcover
        _ ≤ ∑ i, (S i).card := Finset.card_biUnion_le
        _ = ∑ i, (U i).card := Finset.sum_congr rfl (fun i _ => hS i)
        _ ≤ ∑ _i : ι, (Fintype.card ι)^(n/p).primeFactorsList.length :=
          Finset.sum_le_sum (fun i _ => hU i)
        _ = (Fintype.card ι)^n.primeFactorsList.length := by
          rw [hlength, pow_add]
          simp

/-- The two residual factorizations in an ordered collision pair have the
product of the two prime-occurrence bounds, including repeated factors. -/
theorem ordered_factorization_pairs_card_le {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (n m : ℕ) (hn : 0 < n) (hm : 0 < m)
    (T : Finset (ι → ℕ)) (U : Finset (κ → ℕ))
    (hT : ∀ f ∈ T, ∏ i, f i = n) (hU : ∀ f ∈ U, ∏ i, f i = m) :
    (T ×ˢ U).card ≤ (Fintype.card ι)^n.primeFactorsList.length *
      (Fintype.card κ)^m.primeFactorsList.length := by
  rw [Finset.card_product]
  exact Nat.mul_le_mul (ordered_factorizations_card_le n hn T hT)
    (ordered_factorizations_card_le m hm U hU)

def prefixDatumEncoding {n : ℕ} (t : PrefixDatum n) : Fin (n+1) → ℕ :=
  Fin.cons t.d (fun i => t.primes i-1)

lemma prefixDatumEncoding_injOn {n : ℕ} (T : Finset (PrefixDatum n))
    (hT : ∀ t ∈ T, ∀ i, 1 ≤ t.primes i) :
    Set.InjOn prefixDatumEncoding (↑T : Set (PrefixDatum n)) := by
  intro t ht u hu he
  have hd : t.d = u.d := by
    have h := congrFun he 0
    simpa [prefixDatumEncoding] using h
  have hp : t.primes = u.primes := by
    funext i
    have h := congrFun he i.succ
    simp only [prefixDatumEncoding, Fin.cons_succ] at h
    have ht1 := hT t ht i
    have hu1 := hT u hu i
    omega
  cases t
  cases u
  simp_all

/-- Concrete tuple data inside a residual totient are bounded by the ordered
factorization estimate. The tail totient is a separate, final factor. -/
theorem prefixData_card_le {n D : ℕ} (hD : 0 < D) (T : Finset (PrefixDatum n))
    (hp : ∀ t ∈ T, ∀ i, 1 ≤ t.primes i)
    (hprod : ∀ t ∈ T, t.d * (∏ i, (t.primes i-1)) = D) :
    T.card ≤ (n+1)^D.primeFactorsList.length := by
  classical
  let E := T.image prefixDatumEncoding
  have hE : ∀ f ∈ E, ∏ i, f i = D := by
    intro f hf
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hf
    simpa only [prefixDatumEncoding, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
      using hprod t ht
  have hcard : E.card = T.card := Finset.card_image_of_injOn (prefixDatumEncoding_injOn T hp)
  have h := ordered_factorizations_card_le D hD E hE
  simpa only [hcard, Fintype.card_fin] using h

end TotientAsymptotic

end OAI
