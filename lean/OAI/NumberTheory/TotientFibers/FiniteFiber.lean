import Mathlib

namespace OAI

open scoped BigOperators

namespace TotientFibers

def fiber (n : ℕ) : Set ℕ := {m : ℕ | 0 < m ∧ Nat.totient m = n}

noncomputable def g (n : ℕ) : ℕ := (fiber n).ncard

theorem preimage_le {m n : ℕ} (hm : 0 < m) (h : Nat.totient m = n) :
    m ≤ n * ∏ p ∈ Finset.Icc 1 (n + 1), p := by
  have hn : 0 < n := h ▸ Nat.totient_pos.mpr hm
  have hs : m.primeFactors ⊆ Finset.Icc 1 (n + 1) := by
    intro p hp
    have hp' := Nat.prime_of_mem_primeFactors hp
    have hd : p - 1 ∣ n := by
      rw [← h, ← Nat.totient_prime hp']
      exact Nat.totient_dvd_of_dvd (Nat.dvd_of_mem_primeFactors hp)
    have hle := Nat.le_of_dvd hn hd
    exact Finset.mem_Icc.mpr ⟨hp'.one_le, by omega⟩
  calc
    m ≤ m * ∏ p ∈ m.primeFactors, (p - 1) := by
      apply Nat.le_mul_of_pos_right
      exact Finset.prod_pos fun p hp => Nat.sub_pos_of_lt
        (Nat.prime_of_mem_primeFactors hp).one_lt
    _ = n * ∏ p ∈ m.primeFactors, p := by
      rw [← h, Nat.totient_mul_prod_primeFactors]
    _ ≤ n * ∏ p ∈ Finset.Icc 1 (n + 1), p := by
      apply Nat.mul_le_mul_left
      exact Finset.prod_le_prod_of_subset_of_one_le hs fun p hp _ =>
        (Finset.mem_Icc.mp hp).1

theorem fiber_finite (n : ℕ) : (fiber n).Finite := by
  refine (Set.finite_Icc 1 (n * ∏ p ∈ Finset.Icc 1 (n + 1), p)).subset ?_
  intro m hm
  exact ⟨hm.1, preimage_le hm.1 hm.2⟩

theorem card_le_g {n : ℕ} {s : Finset ℕ}
    (hs : ∀ m ∈ s, 0 < m ∧ Nat.totient m = n) : s.card ≤ g n := by
  rw [g, ← Set.ncard_coe_finset]
  exact Set.ncard_le_ncard hs (fiber_finite n)

theorem two_le_g_prime_pred {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    2 ≤ g (p - 1) := by
  have hne : p ≠ 2 * p := by nlinarith [hp.pos]
  have hcard : ({p, 2 * p} : Finset ℕ).card = 2 := by simp [hne]
  rw [← hcard]
  apply card_le_g
  intro m hm
  rcases Finset.mem_insert.mp hm with rfl | hm
  · exact ⟨hp.pos, Nat.totient_prime hp⟩
  · have hm' := Finset.mem_singleton.mp hm
    subst m
    exact ⟨Nat.mul_pos (by decide) hp.pos, by rw [Nat.totient_two_mul_of_odd (hp.odd_of_ne_two hp2),
      Nat.totient_prime hp]⟩

theorem totient_large_fibers_of_one_le {ε : ℝ} (hε : 1 ≤ ε) :
    Set.Infinite {n : ℕ | 0 < n ∧ (n : ℝ) ^ (1 - ε) < (g n : ℝ)} := by
  apply Set.infinite_of_forall_exists_gt
  intro N
  obtain ⟨p, hNp, hp⟩ := Nat.exists_infinite_primes (N + 3)
  have hn : 0 < p - 1 := by omega
  refine ⟨p - 1, ⟨hn, ?_⟩, by omega⟩
  have hg : 2 ≤ g (p - 1) := two_le_g_prime_pred hp (by omega)
  have hn' : (1 : ℝ) ≤ (p - 1 : ℕ) := by exact_mod_cast hn
  have hpow := Real.rpow_le_one_of_one_le_of_nonpos hn' (sub_nonpos.mpr hε)
  have hg' : (2 : ℝ) ≤ g (p - 1) := by exact_mod_cast hg
  linarith

theorem infinite_of_unbounded_g {P : ℕ → Prop}
    (h : ∀ B : ℕ, ∃ n : ℕ, 0 < n ∧ P n ∧ B < g n) :
    Set.Infinite {n : ℕ | 0 < n ∧ P n} := by
  apply Set.Infinite.of_image g
  apply Set.infinite_of_forall_exists_gt
  intro B
  obtain ⟨n, hn, hPn, hBn⟩ := h B
  exact ⟨g n, ⟨n, ⟨hn, hPn⟩, rfl⟩, hBn⟩

theorem factorization_le_log {n U : ℕ} (hn : 0 < n) (hU : n ≤ U) (p : ℕ) :
    n.factorization p ≤ Nat.log 2 U := by
  by_cases hp : p.Prime
  · apply Nat.le_log_of_pow_le (by decide)
    exact (Nat.pow_le_pow_left hp.two_le _).trans ((Nat.ordProj_le p hn.ne').trans hU)
  · rw [Nat.factorization_eq_zero_of_not_prime n hp]
    exact Nat.zero_le _

theorem card_le_of_smooth {S : Finset ℕ} {B U : ℕ}
    (hpos : ∀ n ∈ S, 0 < n) (hbound : ∀ n ∈ S, n ≤ U)
    (hsmooth : ∀ n ∈ S, ∀ p : ℕ, p.Prime → p ∣ n → p ≤ B) :
    S.card ≤ (Nat.log 2 U + 1) ^ B := by
  let E : ↥S → (↥(Finset.Icc 1 B) → Fin (Nat.log 2 U + 1)) :=
    fun n p => ⟨n.val.factorization p.val,
      Nat.lt_succ_of_le (factorization_le_log (hpos n.val n.property)
        (hbound n.val n.property) p.val)⟩
  have hinj : Function.Injective E := by
    intro a b hab
    apply Subtype.ext
    apply Nat.eq_of_factorization_eq (hpos a.val a.property).ne'
      (hpos b.val b.property).ne'
    intro p
    by_cases hp : p ∈ Finset.Icc 1 B
    · exact congrArg Fin.val (congrFun hab ⟨p, hp⟩)
    · have hz : ∀ n ∈ S, n.factorization p = 0 := by
        intro n hn
        by_cases hprime : p.Prime
        · apply Nat.factorization_eq_zero_of_not_dvd
          intro hd
          exact hp (Finset.mem_Icc.mpr ⟨hprime.one_le, hsmooth n hn p hprime hd⟩)
        · exact Nat.factorization_eq_zero_of_not_prime n hprime
      rw [hz a.val a.property, hz b.val b.property]
  have hcard := Nat.card_le_card_of_injective E hinj
  rw [Nat.card_fun, Nat.card_fin] at hcard
  simpa only [Nat.card_fun, Nat.card_fin, Nat.card_eq_fintype_card, Fintype.card_coe,
    Nat.card_Icc, Nat.add_sub_cancel] using hcard

theorem prime_prod_eq_iff {Q R : Finset ℕ}
    (hQ : ∀ p ∈ Q, p.Prime) (hR : ∀ p ∈ R, p.Prime) :
    (∏ p ∈ Q, p) = (∏ p ∈ R, p) ↔ Q = R := by
  constructor
  · intro h
    have := congrArg Nat.primeFactors h
    simpa only [Nat.primeFactors_prod hQ, Nat.primeFactors_prod hR] using this
  · rintro rfl
    rfl

theorem totient_prime_prod {Q : Finset ℕ} (hQ : ∀ p ∈ Q, p.Prime) :
    Nat.totient (∏ p ∈ Q, p) = ∏ p ∈ Q, (p - 1) := by
  have hpos : 0 < ∏ p ∈ Q, p := Finset.prod_pos fun p hp => (hQ p hp).pos
  apply Nat.mul_right_cancel hpos
  simpa only [Nat.primeFactors_prod hQ, mul_comm] using
    Nat.totient_mul_prod_primeFactors (∏ p ∈ Q, p)

theorem finite_pigeonhole {P : Finset ℕ} {X B k : ℕ} {a : ℝ}
    (hprime : ∀ p ∈ P, p.Prime) (hsize : ∀ p ∈ P, p ≤ X)
    (hsmooth : ∀ p ∈ P, ∀ q : ℕ, q.Prime → q ∣ p - 1 → q ≤ B)
    (ha : 0 ≤ a)
    (hcount : ((Nat.log 2 (X ^ k) + 1 : ℕ) : ℝ) ^ B * a < (P.card.choose k : ℝ)) :
    ∃ n : ℕ, 0 < n ∧ n ≤ X ^ k ∧
      (∀ q : ℕ, q.Prime → q ∣ n → q ≤ B) ∧ a < (g n : ℝ) := by
  let S := (P.powersetCard k).image (fun Q => ∏ p ∈ Q, p)
  let T := S.image Nat.totient
  have hS : S.card = P.card.choose k := by
    unfold S
    rw [Finset.card_image_of_injOn, Finset.card_powersetCard]
    intro Q hQ R hR hQR
    exact (prime_prod_eq_iff
      (fun p hp => hprime p ((Finset.mem_powersetCard.mp hQ).1 hp))
      (fun p hp => hprime p ((Finset.mem_powersetCard.mp hR).1 hp))).mp hQR
  have hpos : ∀ m ∈ S, 0 < m := by
    intro m hm
    obtain ⟨Q, hQ, rfl⟩ := Finset.mem_image.mp hm
    exact Finset.prod_pos fun p hp => (hprime p ((Finset.mem_powersetCard.mp hQ).1 hp)).pos
  have hvalues : ∀ n ∈ T, 0 < n ∧ n ≤ X ^ k ∧
      (∀ q : ℕ, q.Prime → q ∣ n → q ≤ B) := by
    intro n hn
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hn
    have hmpos := hpos m hm
    obtain ⟨Q, hQ, rfl⟩ := Finset.mem_image.mp hm
    obtain ⟨hQP, hQk⟩ := Finset.mem_powersetCard.mp hQ
    refine ⟨Nat.totient_pos.mpr hmpos, ?_, ?_⟩
    · calc
        Nat.totient (∏ p ∈ Q, p) ≤ ∏ p ∈ Q, p := Nat.totient_le _
        _ ≤ X ^ Q.card := Finset.prod_le_pow_card _ _ _ fun p hp => hsize p (hQP hp)
        _ = X ^ k := by rw [hQk]
    · intro q hq hd
      rw [totient_prime_prod (fun p hp => hprime p (hQP hp))] at hd
      obtain ⟨p, hp, hdiv⟩ := (hq.prime.dvd_finsetProd_iff _).mp hd
      exact hsmooth p (hQP hp) q hq hdiv
  have hT : T.card ≤ (Nat.log 2 (X ^ k) + 1) ^ B :=
    card_le_of_smooth (fun n hn => (hvalues n hn).1)
      (fun n hn => (hvalues n hn).2.1) (fun n hn => (hvalues n hn).2.2)
  have hT' : (T.card : ℝ) ≤ ((Nat.log 2 (X ^ k) + 1 : ℕ) : ℝ) ^ B := by
    exact_mod_cast hT
  have havg : T.card • a < (S.card : ℝ) := by
    rw [nsmul_eq_mul, hS]
    exact (mul_le_mul_of_nonneg_right hT' ha).trans_lt hcount
  obtain ⟨n, hn, han⟩ := Finset.exists_lt_card_fiber_of_nsmul_lt_card_of_maps_to
    (fun m hm => Finset.mem_image_of_mem Nat.totient hm) havg
  refine ⟨n, (hvalues n hn).1, (hvalues n hn).2.1, (hvalues n hn).2.2, ?_⟩
  have hgn : (S.filter (fun m => Nat.totient m = n)).card ≤ g n := by
    apply card_le_g
    intro m hm
    obtain ⟨hmS, hmn⟩ := Finset.mem_filter.mp hm
    exact ⟨hpos m hmS, hmn⟩
  exact han.trans_le (by exact_mod_cast hgn)

theorem binomial_ge_ratio {M k : ℕ} (hkM : k ≤ M) :
    ((M : ℝ) / k) ^ k ≤ (M.choose k : ℝ) := by
  have hid : (∏ j ∈ Finset.range k, ((M - j : ℕ) : ℝ) / (k - j : ℕ)) =
      (M.choose k : ℝ) := by
    rw [Finset.prod_div_distrib, ← Nat.cast_prod, ← Nat.cast_prod,
      ← Nat.descFactorial_eq_prod_range, ← Nat.descFactorial_eq_prod_range,
      Nat.descFactorial_self, Nat.descFactorial_eq_factorial_mul_choose, Nat.cast_mul]
    have hfact : (k.factorial : ℝ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
    exact mul_div_cancel_left₀ _ hfact
  calc
    ((M : ℝ) / k) ^ k = ∏ j ∈ Finset.range k, ((M : ℝ) / k) := by simp [div_pow]
    _ ≤ ∏ j ∈ Finset.range k, ((M - j : ℕ) : ℝ) / (k - j : ℕ) := by
      apply Finset.prod_le_prod₀ (fun _ _ => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
      intro j hj
      have hjk : j < k := Finset.mem_range.mp hj
      have hjM : j ≤ M := hjk.le.trans hkM
      have hjk' : (j : ℝ) < k := by exact_mod_cast hjk
      have hkM' : (k : ℝ) ≤ M := by exact_mod_cast hkM
      have hkpos : (0 : ℝ) < k := by exact_mod_cast (Nat.zero_le j).trans_lt hjk
      rw [Nat.cast_sub hjM, Nat.cast_sub hjk.le, div_le_div_iff₀ hkpos (sub_pos.mpr hjk')]
      nlinarith [mul_nonneg (sub_nonneg.mpr hkM') (Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
    _ = (M.choose k : ℝ) := hid

theorem logarithmic_count_bound {t a : ℕ} (ht : 5 ≤ t) (ha : a ≤ t) :
    (Nat.log 2 ((t ^ a) ^ (t ^ 2)) + 1) ^ t ≤ t ^ (t ^ 2) := by
  have htone : 1 ≤ t := by omega
  have hpow : (t ^ a) ^ (t ^ 2) ≤ 2 ^ (t * (a * t ^ 2)) := by
    calc
      (t ^ a) ^ (t ^ 2) ≤ ((2 ^ t) ^ a) ^ (t ^ 2) :=
        Nat.pow_le_pow_left (Nat.pow_le_pow_left Nat.lt_two_pow_self.le a) _
      _ = 2 ^ (t * (a * t ^ 2)) := by rw [← pow_mul, ← pow_mul]
  have hlog : Nat.log 2 ((t ^ a) ^ (t ^ 2)) ≤ t * (a * t ^ 2) := by
    have := Nat.log_mono_right (b := 2) hpow
    rwa [Nat.log_pow (by decide)] at this
  have hexp : Nat.log 2 ((t ^ a) ^ (t ^ 2)) ≤ t ^ 4 := by
    calc
      Nat.log 2 ((t ^ a) ^ (t ^ 2)) ≤ t * (a * t ^ 2) := hlog
      _ ≤ t * (t * t ^ 2) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ ha)
      _ = t ^ 4 := by ring
  have hbase : Nat.log 2 ((t ^ a) ^ (t ^ 2)) + 1 ≤ t ^ 5 := by
    have hpos : 1 ≤ t ^ 4 := one_le_pow₀ htone
    have htwo : 2 * t ^ 4 ≤ t * t ^ 4 := Nat.mul_le_mul_right _ (by omega : 2 ≤ t)
    nlinarith [pow_succ t 4]
  calc
    (Nat.log 2 ((t ^ a) ^ (t ^ 2)) + 1) ^ t ≤ (t ^ 5) ^ t := Nat.pow_le_pow_left hbase _
    _ = t ^ (5 * t) := (pow_mul _ _ _).symm
    _ ≤ t ^ (t ^ 2) := pow_le_pow_right₀ htone (by nlinarith)

theorem finite_large_fiber {P : Finset ℕ} {t a : ℕ}
    (ha : 5 ≤ a) (hat : a ≤ t)
    (hprime : ∀ p ∈ P, p.Prime) (hsize : ∀ p ∈ P, p ≤ t ^ a)
    (hsmooth : ∀ p ∈ P, ∀ q : ℕ, q.Prime → q ∣ p - 1 → q ≤ t)
    (hcard : t ^ (a - 1) < P.card) :
    ∃ n : ℕ, 0 < n ∧ n ≤ (t ^ a) ^ (t ^ 2) ∧
      t ^ ((a - 4) * t ^ 2) < g n := by
  have ht : 5 ≤ t := ha.trans hat
  have htone : 1 ≤ t := by omega
  have htpos : 0 < t := by omega
  have hkM : t ^ 2 ≤ P.card :=
    (pow_le_pow_right₀ htone (by omega : 2 ≤ a - 1)).trans hcard.le
  have hratio : (t : ℝ) ^ (a - 3) < (P.card : ℝ) / (t ^ 2 : ℕ) := by
    rw [lt_div_iff₀ (by positivity), Nat.cast_pow, ← pow_add,
      show a - 3 + 2 = a - 1 by omega]
    exact_mod_cast hcard
  have hchoose : (t : ℝ) ^ ((a - 3) * t ^ 2) < (P.card.choose (t ^ 2) : ℝ) := by
    rw [pow_mul]
    exact (pow_lt_pow_left₀ hratio (by positivity) (by positivity)).trans_le
      (binomial_ge_ratio hkM)
  have hC : ((Nat.log 2 ((t ^ a) ^ (t ^ 2)) + 1 : ℕ) : ℝ) ^ t ≤
      (t : ℝ) ^ (t ^ 2) := by
    exact_mod_cast logarithmic_count_bound ht hat
  have hexp : t ^ 2 + (a - 4) * t ^ 2 = (a - 3) * t ^ 2 := by
    rw [show a - 3 = a - 4 + 1 by omega]
    ring
  have hcount : ((Nat.log 2 ((t ^ a) ^ (t ^ 2)) + 1 : ℕ) : ℝ) ^ t *
      (t : ℝ) ^ ((a - 4) * t ^ 2) < (P.card.choose (t ^ 2) : ℝ) := by
    calc
      _ ≤ (t : ℝ) ^ (t ^ 2) * (t : ℝ) ^ ((a - 4) * t ^ 2) :=
        mul_le_mul_of_nonneg_right hC (by positivity)
      _ = (t : ℝ) ^ ((a - 3) * t ^ 2) := by rw [← pow_add, hexp]
      _ < (P.card.choose (t ^ 2) : ℝ) := hchoose
  obtain ⟨n, hn, hnb, _, hgn⟩ := finite_pigeonhole hprime hsize hsmooth (by positivity) hcount
  exact ⟨n, hn, hnb, by exact_mod_cast hgn⟩

theorem finite_large_fiber_rpow {P : Finset ℕ} {t a : ℕ} {ε : ℝ}
    (ha : 5 ≤ a) (hat : a ≤ t) (hε : ε ≤ 1) (haε : 4 ≤ (a : ℝ) * ε)
    (hprime : ∀ p ∈ P, p.Prime) (hsize : ∀ p ∈ P, p ≤ t ^ a)
    (hsmooth : ∀ p ∈ P, ∀ q : ℕ, q.Prime → q ∣ p - 1 → q ≤ t)
    (hcard : t ^ (a - 1) < P.card) :
    ∃ n : ℕ, 0 < n ∧ t < g n ∧ (n : ℝ) ^ (1 - ε) < (g n : ℝ) := by
  obtain ⟨n, hn, hnb, hgn⟩ := finite_large_fiber ha hat hprime hsize hsmooth hcard
  have htone : 1 ≤ t := by omega
  have htpos : 0 < t := by omega
  have hexp_pos : 1 ≤ (a - 4) * t ^ 2 := Nat.mul_pos
    (by omega) (pow_pos htpos _)
  have htg : t < g n := by
    calc
      t = t ^ 1 := (pow_one t).symm
      _ ≤ t ^ ((a - 4) * t ^ 2) := pow_le_pow_right₀ htone hexp_pos
      _ < g n := hgn
  have ha4 : 4 ≤ a := by omega
  have hexp : (a : ℝ) * (1 - ε) ≤ (a - 4 : ℕ) := by
    rw [Nat.cast_sub ha4]
    norm_num
    nlinarith
  have hexp' : ((a * t ^ 2 : ℕ) : ℝ) * (1 - ε) ≤ (((a - 4) * t ^ 2 : ℕ) : ℝ) := by
    push_cast
    have h := mul_le_mul_of_nonneg_right hexp (sq_nonneg (t : ℝ))
    nlinarith
  have hnrpow : (n : ℝ) ^ (1 - ε) ≤ (t : ℝ) ^ ((a - 4) * t ^ 2) := by
    calc
      (n : ℝ) ^ (1 - ε) ≤ (((t ^ a) ^ (t ^ 2) : ℕ) : ℝ) ^ (1 - ε) :=
        Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hnb) (sub_nonneg.mpr hε)
      _ = (t : ℝ) ^ (((a * t ^ 2 : ℕ) : ℝ) * (1 - ε)) := by
        rw [Nat.cast_pow, Nat.cast_pow, ← pow_mul, ← Real.rpow_natCast_mul (Nat.cast_nonneg _)]
      _ ≤ (t : ℝ) ^ (((a - 4) * t ^ 2 : ℕ) : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast htone) hexp'
      _ = (t : ℝ) ^ ((a - 4) * t ^ 2) := Real.rpow_natCast _ _
  exact ⟨n, hn, htg, hnrpow.trans_lt (by exact_mod_cast hgn)⟩

end TotientFibers

end OAI
