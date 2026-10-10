import OAI.NumberTheory.PowerFree.Model

namespace OAI

open Filter Asymptotics
open scoped Topology
namespace QuarticPowerFree

open Polynomial

theorem resultant_derivative_ne_zero (f : Polynomial ℤ)
    (hf : Irreducible (f.map (Int.castRingHom ℚ))) :
    f.resultant f.derivative ≠ 0 := by
  have h := Polynomial.resultant_ne_zero _ _ hf.separable
  rw [Polynomial.derivative_map,
    Polynomial.natDegree_map_eq_of_injective Int.cast_injective,
    Polynomial.natDegree_map_eq_of_injective Int.cast_injective,
    Polynomial.resultant_map_map] at h
  intro hz
  apply h
  rw [hz]
  rfl

theorem derivative_not_dvd_of_good (f : Polynomial ℤ) (hdeg : f.natDegree ≠ 0)
    {p : ℕ} (hp : ¬ (p : ℤ) ∣ f.resultant f.derivative) {a : ℤ}
    (ha : (p : ℤ) ∣ f.eval a) : ¬ (p : ℤ) ∣ f.derivative.eval a := by
  obtain ⟨u, v, _, _, h⟩ := Polynomial.exists_mul_add_mul_eq_C_resultant f
    f.derivative le_rfl le_rfl (Or.inl hdeg)
  have he := congrArg (Polynomial.eval a) h
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C] at he
  intro hd
  apply hp
  rw [← he]
  exact dvd_add (dvd_mul_of_dvd_left ha (u.eval a)) (dvd_mul_of_dvd_left hd (v.eval a))

theorem divided_difference_eval (f : Polynomial ℤ) (a : ℤ) :
    (f /ₘ (X - C a)).eval a = f.derivative.eval a := by
  have h := congrArg (Polynomial.eval a)
    (Polynomial.divByMonic_add_X_sub_C_mul_derivative_divByMonic_eq_derivative f a)
  simpa only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_sub,
    Polynomial.eval_X, Polynomial.eval_C, sub_self, zero_mul, add_zero] using h

theorem eval_sub_eq_mul_divided_difference (f : Polynomial ℤ) (a b : ℤ) :
    f.eval b - f.eval a = (b - a) * (f /ₘ (X - C a)).eval b := by
  have h := congrArg (Polynomial.eval b)
    (Polynomial.X_sub_C_mul_divByMonic_eq_sub_modByMonic f a)
  simpa only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X,
    Polynomial.eval_C, Polynomial.modByMonic_X_sub_C_eq_C_eval] using h.symm

theorem prime_power_root_unique (f : Polynomial ℤ) {p k : ℕ} (hp : p.Prime)
    {a b : ℤ} (ha : (p : ℤ) ^ k ∣ f.eval a) (hb : (p : ℤ) ^ k ∣ f.eval b)
    (hab : (p : ℤ) ∣ b - a) (hd : ¬ (p : ℤ) ∣ f.derivative.eval a) :
    (p : ℤ) ^ k ∣ b - a := by
  let q := f /ₘ (X - C a)
  have hq : ¬ (p : ℤ) ∣ q.eval b := by
    intro hqb
    have hdiff : (p : ℤ) ∣ q.eval b - q.eval a :=
      hab.trans (Polynomial.sub_dvd_eval_sub b a q)
    have hqa : (p : ℤ) ∣ q.eval a := by
      simpa only [sub_sub_cancel] using dvd_sub hqb hdiff
    exact hd (by simpa only [q, divided_difference_eval] using hqa)
  have hp' : Prime (p : ℤ) := Int.prime_iff_natAbs_prime.mpr (by simpa using hp)
  have hcop : IsCoprime ((p : ℤ) ^ k) (q.eval b) :=
    (hp'.coprime_iff_not_dvd.mpr hq).pow_left
  apply hcop.dvd_of_dvd_mul_left
  rw [mul_comm, ← eval_sub_eq_mul_divided_difference]
  exact dvd_sub hb ha

theorem map_zmod_ne_zero_of_good (f : Polynomial ℤ) (hdeg : f.natDegree ≠ 0)
    {p : ℕ} (hp : ¬ (p : ℤ) ∣ f.resultant f.derivative) :
    f.map (Int.castRingHom (ZMod p)) ≠ 0 := by
  intro hz
  have hd : f.derivative.map (Int.castRingHom (ZMod p)) = 0 := by
    rw [← Polynomial.derivative_map, hz, Polynomial.derivative_zero]
  have he : (p : ℤ) ∣ f.eval 0 := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    have h := congrArg (Polynomial.eval (0 : ZMod p)) hz
    simpa [Polynomial.eval_zero] using h
  apply derivative_not_dvd_of_good f hdeg hp he
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  have h := congrArg (Polynomial.eval (0 : ZMod p)) hd
  simpa [Polynomial.eval_zero] using h

theorem rho_prime_pow_le_degree (f : Polynomial ℤ) (hdeg : f.natDegree ≠ 0)
    {p k : ℕ} (hp : p.Prime) (hk : k ≠ 0)
    (hgood : ¬ (p : ℤ) ∣ f.resultant f.derivative) :
    rho f (p ^ k) ≤ f.natDegree := by
  classical
  let : Fact p.Prime := ⟨hp⟩
  let F := f.map (Int.castRingHom (ZMod p))
  have hF : F ≠ 0 := map_zmod_ne_zero_of_good f hdeg hgood
  let s := (Finset.range (p ^ k)).filter fun a : ℕ =>
    ((p ^ k : ℕ) : ℤ) ∣ f.eval (a : ℤ)
  have hmap : Set.MapsTo (fun a : ℕ => (a : ZMod p)) (↑s) (↑F.roots.toFinset) := by
    intro a ha
    obtain ⟨_, ha⟩ := Finset.mem_filter.mp ha
    have ha' : (p : ℤ) ∣ f.eval (a : ℤ) :=
      (dvd_pow_self (p : ℤ) hk).trans (by simpa only [Nat.cast_pow] using ha)
    rw [Finset.mem_coe, Multiset.mem_toFinset, Polynomial.mem_roots hF]
    change F.eval (a : ZMod p) = 0
    rw [show F = f.map (Int.castRingHom (ZMod p)) from rfl,
      Polynomial.eval_map, ← Int.cast_natCast a (R := ZMod p)]
    change f.eval₂ (Int.castRingHom (ZMod p))
      ((Int.castRingHom (ZMod p)) (a : ℤ)) = 0
    rw [Polynomial.eval₂_at_apply]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd (f.eval (a : ℤ)) p).mpr ha'
  have hinj : Set.InjOn (fun a : ℕ => (a : ZMod p)) (↑s) := by
    intro a ha b hb hab
    obtain ⟨ha_lt, ha_root⟩ := Finset.mem_filter.mp ha
    obtain ⟨hb_lt, hb_root⟩ := Finset.mem_filter.mp hb
    rw [Finset.mem_range] at ha_lt hb_lt
    have hab' : (p : ℤ) ∣ (b : ℤ) - (a : ℤ) := by
      apply (ZMod.intCast_eq_intCast_iff_dvd_sub (a : ℤ) (b : ℤ) p).mp
      simpa only [Int.cast_natCast] using hab
    have ha' : (p : ℤ) ∣ f.eval (a : ℤ) :=
      (dvd_pow_self (p : ℤ) hk).trans (by simpa only [Nat.cast_pow] using ha_root)
    have hlarge := prime_power_root_unique f hp
      (by simpa only [Nat.cast_pow] using ha_root)
      (by simpa only [Nat.cast_pow] using hb_root) hab'
      (derivative_not_dvd_of_good f hdeg hgood ha')
    have hmod : a ≡ b [MOD p ^ k] := by
      apply Int.natCast_modEq_iff.mp
      rw [Int.modEq_iff_dvd]
      simpa only [Nat.cast_pow] using hlarge
    exact hmod.eq_of_lt_of_lt ha_lt hb_lt
  calc
    rho f (p ^ k) = s.card := rfl
    _ ≤ F.roots.toFinset.card := Finset.card_le_card_of_injOn _ hmap hinj
    _ ≤ F.roots.card := Multiset.toFinset_card_le _
    _ ≤ F.natDegree := Polynomial.card_roots' _
    _ ≤ f.natDegree := Polynomial.natDegree_map_le

theorem finite_resultant_primes (f : Polynomial ℤ)
    (hf : Irreducible (f.map (Int.castRingHom ℚ))) :
    {p : Nat.Primes | (p.val : ℤ) ∣ f.resultant f.derivative}.Finite := by
  have hn := resultant_derivative_ne_zero f hf
  have hbound : (Subtype.val ⁻¹' Set.Iic (f.resultant f.derivative).natAbs :
      Set Nat.Primes).Finite :=
    Set.Finite.preimage Subtype.val_injective.injOn (Set.finite_Iic _)
  apply hbound.subset
  intro p hp
  change p.val ≤ (f.resultant f.derivative).natAbs
  apply Nat.le_of_dvd (Int.natAbs_pos.mpr hn)
  simpa only [Int.natAbs_natCast] using Int.natAbs_dvd_natAbs.mpr hp

theorem summable_local_proportion (f : Polynomial ℤ)
    (hf : Irreducible (f.map (Int.castRingHom ℚ))) (hdeg : f.natDegree ≠ 0)
    {k : ℕ} (hk : 1 < k) :
    Summable (fun p : Nat.Primes => (rho f (p.val ^ k) : ℝ) / (p.val : ℝ) ^ k) := by
  have hs : Summable (fun p : Nat.Primes => (f.natDegree : ℝ) / (p.val : ℝ) ^ k) := by
    have hprime : Summable (fun p : Nat.Primes => (1 : ℝ) / (p.val : ℝ) ^ k) :=
      (Real.summable_one_div_nat_pow.mpr hk).comp_injective
        (i := fun p : Nat.Primes => p.val) Subtype.val_injective
    simpa only [mul_one_div] using hprime.mul_left (f.natDegree : ℝ)
  apply hs.of_norm_bounded_eventually
  filter_upwards [(finite_resultant_primes f hf).eventually_cofinite_notMem] with p hp
  have hr := rho_prime_pow_le_degree f hdeg (k := k) p.property (by omega) hp
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  apply div_le_div_of_nonneg_right (by exact_mod_cast hr) (by positivity)

theorem localFactor_pos (f : Polynomial ℤ) (k : ℕ)
    (h : LocallyAdmissible f k) (p : Nat.Primes) : 0 < localFactor f k p := by
  have hp : 0 < (p.val : ℝ) ^ k := pow_pos (by exact_mod_cast p.property.pos) _
  dsimp [localFactor]
  rw [sub_pos, div_lt_one hp]
  exact_mod_cast h p.val p.property

theorem densityConstant_converges_pos (f : Polynomial ℤ)
    (hf : Irreducible (f.map (Int.castRingHom ℚ))) (hdeg : f.natDegree ≠ 0)
    {k : ℕ} (hk : 1 < k) (hlocal : LocallyAdmissible f k) :
    Multipliable (localFactor f k) ∧ 0 < densityConstant f k := by
  have hs := (summable_local_proportion f hf hdeg hk).neg
  have hlog : Summable (fun p : Nat.Primes => Real.log (localFactor f k p)) := by
    simpa only [localFactor, sub_eq_add_neg] using
      Real.summable_log_one_add_of_summable hs
  refine ⟨Real.multipliable_of_summable_log (localFactor_pos f k hlocal) hlog, ?_⟩
  unfold densityConstant
  rw [← Real.rexp_tsum_eq_tprod (localFactor_pos f k hlocal) hlog]
  exact Real.exp_pos _

open scoped BigOperators Count

theorem count_mul_periodic (P : ℕ → Prop) [DecidablePred P] (q : ℕ)
    (hP : Function.Periodic P q) (a : ℕ) :
    Nat.count P (q * a) = a * Nat.count P q := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [Nat.mul_succ, Nat.count_add, ih]
    have hshift : (fun n => P (q * a + n)) = P := by
      funext n
      simpa [nsmul_eq_mul, mul_comm, add_comm] using hP.nsmul a n
    simp only [hshift]
    ring

theorem count_periodic_div_mod (P : ℕ → Prop) [DecidablePred P] (q N : ℕ)
    (hP : Function.Periodic P q) :
    Nat.count P N = (N / q) * Nat.count P q + Nat.count P (N % q) := by
  have hshift : (fun n => P (q * (N / q) + n)) = P := by
    funext n
    simpa [nsmul_eq_mul, mul_comm, add_comm] using hP.nsmul (N / q) n
  conv_lhs => rw [← Nat.div_add_mod N q]
  rw [Nat.count_add, count_mul_periodic P q hP]
  simp only [hshift]

theorem count_periodic_error (P : ℕ → Prop) [DecidablePred P] (q N : ℕ)
    (hq : 0 < q) (hP : Function.Periodic P q) :
    |(Nat.count P N : ℝ) - (Nat.count P q : ℝ) / q * N| ≤ q := by
  have hrem := Nat.count_le P (n := N % q)
  have hrlt := Nat.mod_lt N hq
  have hcnt := Nat.count_le P (n := q)
  have hq' : 0 < (q : ℝ) := Nat.cast_pos.mpr hq
  have hrem' : (Nat.count P (N % q) : ℝ) ≤ (N % q : ℕ) := by exact_mod_cast hrem
  have hrlt' : (N % q : ℕ) < (q : ℝ) := by exact_mod_cast hrlt
  have hcnt' : (Nat.count P q : ℝ) ≤ q := by exact_mod_cast hcnt
  have hvalue : (Nat.count P N : ℝ) - (Nat.count P q : ℝ) / q * N =
      Nat.count P (N % q) - (Nat.count P q : ℝ) / q * (N % q : ℕ) := by
    rw [count_periodic_div_mod P q N hP]
    push_cast
    have hN : (N : ℝ) = (q : ℝ) * (N / q : ℕ) + (N % q : ℕ) := by
      exact_mod_cast (Nat.div_add_mod N q).symm
    field_simp
    nlinarith [congrArg (fun x : ℝ => (Nat.count P q : ℝ) * x) hN]
  rw [hvalue, abs_le]
  have hrnon : (0 : ℝ) ≤ (N % q : ℕ) := Nat.cast_nonneg _
  have hremnon : (0 : ℝ) ≤ Nat.count P (N % q) := Nat.cast_nonneg _
  have hprop : 0 ≤ (Nat.count P q : ℝ) / q := by positivity
  have hprop' : (Nat.count P q : ℝ) / q ≤ 1 := (div_le_one hq').mpr hcnt'
  have hmul : (Nat.count P q : ℝ) / q * (N % q : ℕ) ≤ (N % q : ℕ) := by
    nlinarith
  constructor <;> nlinarith [mul_nonneg hprop hrnon]

theorem count_residues (q : ℕ) [NeZero q] (P : ZMod q → Prop)
    [DecidablePred P] :
    Nat.count (fun n : ℕ => P (n : ZMod q)) q = Fintype.card {a : ZMod q // P a} := by
  classical
  rw [Nat.count_eq_card_fintype]
  apply Fintype.card_congr
  refine {
    toFun := fun n => ⟨(n.val : ZMod q), n.property.2⟩
    invFun := fun a => ⟨a.val.val, ZMod.val_lt a.val, by simpa using a.property⟩
    left_inv := ?_
    right_inv := ?_ }
  · intro n
    apply Subtype.ext
    exact ZMod.val_natCast_of_lt n.property.1
  · intro a
    apply Subtype.ext
    exact ZMod.natCast_zmod_val a.val

theorem count_crt {ι : Type*} [Fintype ι] (m : ι → ℕ)
    (hm : ∀ i, 0 < m i) (hcoprime : Pairwise (fun i j => (m i).Coprime (m j)))
    (P : ∀ i, ZMod (m i) → Prop) [∀ i, DecidablePred (P i)] :
    Nat.count (fun n : ℕ => ∀ i, P i (n : ZMod (m i))) (∏ i, m i) =
      ∏ i, Nat.card {a : ZMod (m i) // P i a} := by
  classical
  let : ∀ i, NeZero (m i) := fun i => ⟨ne_of_gt (hm i)⟩
  let M := ∏ i, m i
  have hM : 0 < M := Finset.prod_pos (fun i _ => hm i)
  let : NeZero M := ⟨ne_of_gt hM⟩
  let e := ZMod.prodEquivPi m hcoprime
  let Q : ZMod M → Prop := fun a => ∀ i, P i (e a i)
  have hQ : (fun n : ℕ => ∀ i, P i (n : ZMod (m i))) =
      (fun n : ℕ => Q (n : ZMod M)) := by
    funext n
    dsimp [Q]
    simp only [map_natCast, Pi.natCast_apply]
  simp only [hQ]
  rw [count_residues M Q]
  calc
    _ = Fintype.card {a : (∀ i, ZMod (m i)) // ∀ i, P i (a i)} := by
      apply Fintype.card_congr
      exact e.toEquiv.subtypeEquiv (fun _ => Iff.rfl)
    _ = Fintype.card (∀ i, {a : ZMod (m i) // P i a}) :=
      Fintype.card_congr Equiv.subtypePiEquivPi
    _ = _ := by simp only [Fintype.card_pi, Nat.card_eq_fintype_card]

def AvoidPrimes (f : Polynomial ℤ) (k : ℕ) (s : Finset Nat.Primes) (n : ℕ) : Prop :=
  ∀ p ∈ s, ¬(p.val : ℤ) ^ k ∣ f.eval (n : ℤ)

instance (f : Polynomial ℤ) (k : ℕ) (s : Finset Nat.Primes) :
    DecidablePred (AvoidPrimes f k s) :=
  fun n => inferInstanceAs (Decidable (∀ p ∈ s, ¬(p.val : ℤ) ^ k ∣ f.eval (n : ℤ)))

theorem eval_zmod_eq_zero_iff (f : Polynomial ℤ) (q n : ℕ) :
    f.eval₂ (Int.castRingHom (ZMod q)) (n : ZMod q) = 0 ↔
      (q : ℤ) ∣ f.eval (n : ℤ) := by
  rw [← Int.cast_natCast n (R := ZMod q)]
  change f.eval₂ (Int.castRingHom (ZMod q))
    ((Int.castRingHom (ZMod q)) (n : ℤ)) = 0 ↔ _
  rw [Polynomial.eval₂_at_apply]
  exact ZMod.intCast_zmod_eq_zero_iff_dvd _ _

theorem rho_le (f : Polynomial ℤ) (q : ℕ) : rho f q ≤ q :=
  (Finset.card_filter_le _ _).trans_eq (Finset.card_range q)

theorem card_good_residues (f : Polynomial ℤ) (q : ℕ) [NeZero q] :
    Fintype.card {a : ZMod q // f.eval₂ (Int.castRingHom (ZMod q)) a ≠ 0} =
      q - rho f q := by
  classical
  rw [Fintype.card_subtype_compl, ZMod.card, ← count_residues]
  simp only [eval_zmod_eq_zero_iff, Nat.count_eq_card_filter_range, rho]

theorem finite_sieve_full_period (f : Polynomial ℤ) (k : ℕ) (s : Finset Nat.Primes) :
    Nat.count (AvoidPrimes f k s) (∏ p ∈ s, p.val ^ k) =
      ∏ p ∈ s, (p.val ^ k - rho f (p.val ^ k)) := by
  classical
  have hp : ∀ p : s, 0 < p.val.val ^ k := fun p => pow_pos p.val.property.pos _
  have hcp : Pairwise (fun p q : s => (p.val.val ^ k).Coprime (q.val.val ^ k)) := by
    intro p q hpq
    apply Nat.coprime_pow_primes k k p.val.property q.val.property
    intro heq
    exact hpq (Subtype.ext (Subtype.ext heq))
  let P : ∀ p : s, ZMod (p.val.val ^ k) → Prop :=
    fun p a => f.eval₂ (Int.castRingHom (ZMod (p.val.val ^ k))) a ≠ 0
  have h := count_crt (fun p : s => p.val.val ^ k) hp hcp P
  let : ∀ p : s, NeZero (p.val.val ^ k) := fun p => ⟨ne_of_gt (hp p)⟩
  have hpred : (fun n : ℕ => ∀ p : s, P p (n : ZMod (p.val.val ^ k))) =
      AvoidPrimes f k s := by
    funext n
    dsimp [P, AvoidPrimes]
    simp only [eval_zmod_eq_zero_iff, Nat.cast_pow, Subtype.forall]
  have hqprod : (∏ p : s, p.val.val ^ k) = ∏ p ∈ s, p.val ^ k :=
    Finset.prod_coe_sort s (fun p : Nat.Primes => p.val ^ k)
  have hrprod : (∏ p : s, (p.val.val ^ k - rho f (p.val.val ^ k))) =
      ∏ p ∈ s, (p.val ^ k - rho f (p.val ^ k)) :=
    Finset.prod_coe_sort s (fun p : Nat.Primes => p.val ^ k - rho f (p.val ^ k))
  simpa only [hpred, Nat.card_eq_fintype_card, P, card_good_residues,
    hqprod, hrprod] using h

theorem finite_sieve_periodic (f : Polynomial ℤ) (k : ℕ) (s : Finset Nat.Primes) :
    Function.Periodic (AvoidPrimes f k s) (∏ p ∈ s, p.val ^ k) := by
  intro n
  apply propext
  unfold AvoidPrimes
  apply forall_congr'
  intro p
  apply forall_congr'
  intro hp
  have hd : p.val ^ k ∣ ∏ q ∈ s, q.val ^ k := Finset.dvd_prod_of_mem _ hp
  have hz : ((∏ q ∈ s, q.val ^ k : ℕ) : ZMod (p.val ^ k)) = 0 :=
    (ZMod.natCast_eq_zero_iff _ _).mpr hd
  have heq : f.eval₂ (Int.castRingHom (ZMod (p.val ^ k)))
      ((n + ∏ q ∈ s, q.val ^ k : ℕ) : ZMod (p.val ^ k)) =
      f.eval₂ (Int.castRingHom (ZMod (p.val ^ k))) (n : ZMod (p.val ^ k)) := by
    simp only [Nat.cast_add, hz, add_zero]
  rw [← Nat.cast_pow, ← eval_zmod_eq_zero_iff,
    ← eval_zmod_eq_zero_iff, heq]

theorem finite_sieve_error (f : Polynomial ℤ) (k : ℕ) (s : Finset Nat.Primes) (N : ℕ) :
    |(Nat.count (AvoidPrimes f k s) N : ℝ) -
      (∏ p ∈ s, (1 - (rho f (p.val ^ k) : ℝ) / (p.val : ℝ) ^ k)) * N| ≤
        (∏ p ∈ s, p.val ^ k : ℕ) := by
  classical
  have hq : 0 < ∏ p ∈ s, p.val ^ k := Finset.prod_pos (fun p _ => pow_pos p.property.pos _)
  have h := count_periodic_error (AvoidPrimes f k s) (∏ p ∈ s, p.val ^ k) N hq
    (finite_sieve_periodic f k s)
  rw [finite_sieve_full_period] at h
  have hprod : ((∏ p ∈ s, (p.val ^ k - rho f (p.val ^ k)) : ℕ) : ℝ) /
      (∏ p ∈ s, p.val ^ k : ℕ) =
        ∏ p ∈ s, (1 - (rho f (p.val ^ k) : ℝ) / (p.val : ℝ) ^ k) := by
    push_cast
    rw [← Finset.prod_div_distrib]
    apply Finset.prod_congr rfl
    intro p hp
    rw [Nat.cast_sub (rho_le _ _), Nat.cast_pow, sub_div, div_self]
    exact pow_ne_zero _ (Nat.cast_ne_zero.mpr p.property.ne_zero)
  rw [hprod] at h
  exact h

theorem count_or_le (P Q : ℕ → Prop) [DecidablePred P] [DecidablePred Q] (N : ℕ) :
    Nat.count (fun n => P n ∨ Q n) N ≤ Nat.count P N + Nat.count Q N := by
  simp only [Nat.count_eq_card_filter_range, Finset.filter_or]
  exact Finset.card_union_le _ _

theorem count_exists_le {α : Type*} (s : Finset α) (P : α → ℕ → Prop)
    [∀ a, DecidablePred (P a)] (N : ℕ) :
    Nat.count (fun n => ∃ a ∈ s, P a n) N ≤ ∑ a ∈ s, Nat.count (P a) N := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    simp only [Finset.mem_insert, exists_eq_or_imp, Finset.sum_insert ha]
    exact (count_or_le _ _ _).trans (Nat.add_le_add_left ih _)

theorem root_predicate_periodic (f : Polynomial ℤ) (q : ℕ) :
    Function.Periodic (fun n : ℕ => (q : ℤ) ∣ f.eval (n : ℤ)) q := by
  intro n
  apply propext
  change (q : ℤ) ∣ f.eval ((n + q : ℕ) : ℤ) ↔ (q : ℤ) ∣ f.eval (n : ℤ)
  rw [← eval_zmod_eq_zero_iff, ← eval_zmod_eq_zero_iff]
  simp only [Nat.cast_add, ZMod.natCast_self, add_zero]

theorem count_roots_le (f : Polynomial ℤ) {q : ℕ} (hq : 0 < q) (N : ℕ) :
    (Nat.count (fun n : ℕ => (q : ℤ) ∣ f.eval (n : ℤ)) N : ℝ) ≤
      (rho f q : ℝ) * ((N : ℝ) / q + 1) := by
  rw [count_periodic_div_mod _ _ _ (root_predicate_periodic f q)]
  have hrem := Nat.count_monotone (fun n : ℕ => (q : ℤ) ∣ f.eval (n : ℤ))
    (Nat.mod_lt N hq).le
  have hcnt : Nat.count (fun n : ℕ => (q : ℤ) ∣ f.eval (n : ℤ)) q = rho f q := by
    rw [Nat.count_eq_card_filter_range]; rfl
  rw [hcnt] at hrem ⊢
  have hrem' : (Nat.count (fun n : ℕ => (q : ℤ) ∣ f.eval (n : ℤ)) (N % q) : ℝ) ≤
      (rho f q : ℝ) := by exact_mod_cast hrem
  have hdiv : ((N / q : ℕ) : ℝ) ≤ (N : ℝ) / q := by
    rw [le_div_iff₀ (by exact_mod_cast hq)]
    exact_mod_cast Nat.div_mul_le_self N q
  push_cast
  nlinarith [mul_le_mul_of_nonneg_right hdiv (Nat.cast_nonneg (rho f q) : (0 : ℝ) ≤ _)]

def primesUpTo (N : ℕ) : Finset Nat.Primes := (Nat.primesLE N).subtype Nat.Prime

@[simp] theorem mem_primesUpTo {N : ℕ} {p : Nat.Primes} :
    p ∈ primesUpTo N ↔ p.val ≤ N := by
  exact (Finset.mem_subtype (p := Nat.Prime) (s := Nat.primesLE N)
    (a := ⟨p.val, p.property⟩)).trans ((Nat.mem_primesLE).trans (and_iff_left p.property))

theorem card_primesUpTo (N : ℕ) : (primesUpTo N).card = Nat.primeCounting N := by
  calc
    _ = ((Nat.primesLE N).filter Nat.Prime).card := Finset.card_subtype _ _
    _ = (Nat.primesLE N).card := congrArg Finset.card (Finset.filter_true_of_mem
      (fun _ hp => (Nat.mem_primesLE.mp hp).2))
    _ = _ := Nat.primesLE_card_eq_primeCounting _

theorem primeCounting_ratio_tendsto :
    Tendsto (fun N : ℕ => (Nat.primeCounting N : ℝ) / N) atTop (nhds 0) := by
  have hcast : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hupper := hcast.eventually (Chebyshev.eventually_primeCounting_le (ε := 1) zero_lt_one)
  apply squeeze_zero' (Filter.Eventually.of_forall (fun _ => by positivity))
    (g := fun N : ℕ => (Real.log 4 + 1) / Real.log (N : ℝ))
  · filter_upwards [hupper, eventually_gt_atTop 0] with N hN hpos
    have hN' : (Nat.primeCounting N : ℝ) ≤
        (Real.log 4 + 1) * N / Real.log (N : ℝ) := by simpa using hN
    rw [div_le_iff₀ (Nat.cast_pos.mpr hpos)]
    calc
      _ ≤ _ := hN'
      _ = _ := by ring
  · simpa only [div_eq_mul_inv, mul_zero, Function.comp_apply, Pi.inv_apply] using
      ((Real.tendsto_log_atTop.comp hcast).inv_tendsto_atTop).const_mul (Real.log 4 + 1)

theorem tendsto_primesUpTo : Tendsto primesUpTo atTop atTop := by
  apply tendsto_atTop.2
  intro s
  refine Filter.eventually_atTop.2 ⟨s.sup (fun p => p.val), ?_⟩
  intro N hN p hp
  exact mem_primesUpTo.mpr ((Finset.le_sup (f := fun p => p.val) hp).trans hN)

theorem finite_product_tendsto (f : Polynomial ℤ) (k : ℕ)
    (h : Multipliable (localFactor f k)) :
    Tendsto (fun N : ℕ => ∏ p ∈ primesUpTo N, localFactor f k p)
      atTop (nhds (densityConstant f k)) :=
  h.hasProd.comp tendsto_primesUpTo

theorem finite_local_tail_small (f : Polynomial ℤ) {k : ℕ}
    (h : Summable (fun p : Nat.Primes => (rho f (p.val ^ k) : ℝ) / (p.val : ℝ) ^ k))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ Y : ℕ, ∀ s : Finset Nat.Primes, (∀ p ∈ s, Y < p.val) →
      ∑ p ∈ s, (rho f (p.val ^ k) : ℝ) / (p.val : ℝ) ^ k < ε := by
  classical
  obtain ⟨t, ht⟩ := summable_iff_vanishing_norm.mp h ε hε
  refine ⟨t.sup (fun p => p.val), ?_⟩
  intro s hs
  have hd : Disjoint s t := by
    apply Finset.disjoint_left.mpr
    intro p hp hpt
    exact (not_lt_of_ge (Finset.le_sup (f := fun p => p.val) hpt)) (hs p hp)
  have hb := ht s hd
  rwa [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg (fun _ _ => by positivity))] at hb

noncomputable def natCount (f : Polynomial ℤ) (k N : ℕ) : ℕ := by
  classical
  exact Nat.count (fun n : ℕ => PowerFree k (f.eval (n : ℤ))) N

noncomputable def tailCount (f : Polynomial ℤ) (k N : ℕ) : ℕ := by
  classical
  exact Nat.count (fun n : ℕ => ∃ p : ℕ, p.Prime ∧ N < p ∧
    (p : ℤ) ^ k ∣ f.eval (n : ℤ)) N

theorem natCount_le_finite (f : Polynomial ℤ) (k N : ℕ) (s : Finset Nat.Primes) :
    natCount f k N ≤ Nat.count (AvoidPrimes f k s) N := by
  classical
  apply Nat.count_mono_left
  intro n _ hn p _
  exact hn p.val p.property

theorem finite_sieve_difference_le (f : Polynomial ℤ) (k Y N : ℕ) :
    Nat.count (AvoidPrimes f k (primesUpTo Y)) N ≤ natCount f k N +
      (∑ p ∈ (primesUpTo N).filter (fun p => Y < p.val),
        Nat.count (fun n : ℕ => (p.val : ℤ) ^ k ∣ f.eval (n : ℤ)) N) +
      tailCount f k N := by
  classical
  let P := fun n : ℕ => PowerFree k (f.eval (n : ℤ))
  let I := fun n : ℕ => ∃ p ∈ (primesUpTo N).filter (fun p => Y < p.val),
    (p.val : ℤ) ^ k ∣ f.eval (n : ℤ)
  let T := fun n : ℕ => ∃ p : ℕ, p.Prime ∧ N < p ∧ (p : ℤ) ^ k ∣ f.eval (n : ℤ)
  have hsub : ∀ n < N, AvoidPrimes f k (primesUpTo Y) n → (P n ∨ I n) ∨ T n := by
    intro n _ hn
    by_cases hP : P n
    · exact Or.inl (Or.inl hP)
    · obtain ⟨p, hp, hdiv⟩ : ∃ p : ℕ, p.Prime ∧ (p : ℤ) ^ k ∣ f.eval (n : ℤ) := by
        simpa only [P, PowerFree, not_forall, Classical.not_imp, not_not, exists_prop] using hP
      by_cases hlarge : N < p
      · exact Or.inr ⟨p, hp, hlarge, hdiv⟩
      · have hY : Y < p := by
          by_contra h
          exact hn ⟨p, hp⟩ (mem_primesUpTo.mpr (Nat.le_of_not_gt h)) hdiv
        exact Or.inl (Or.inr ⟨⟨p, hp⟩, Finset.mem_filter.mpr
          ⟨mem_primesUpTo.mpr (Nat.le_of_not_gt hlarge), hY⟩, hdiv⟩)
  calc
    _ ≤ Nat.count (fun n => (P n ∨ I n) ∨ T n) N := Nat.count_mono_left hsub
    _ ≤ (Nat.count P N + Nat.count I N) + Nat.count T N :=
      (count_or_le _ _ _).trans (Nat.add_le_add_right (count_or_le _ _ _) _)
    _ ≤ _ := Nat.add_le_add_right (Nat.add_le_add_left (count_exists_le _ _ N) _) _

theorem intermediate_sieve_bound (f : Polynomial ℤ) (hdeg : f.natDegree ≠ 0)
    {k Y N : ℕ} (hk : 0 < k)
    (hY : ∀ p : Nat.Primes, (p.val : ℤ) ∣ f.resultant f.derivative → p.val ≤ Y) :
    (∑ p ∈ (primesUpTo N).filter (fun p => Y < p.val),
      (Nat.count (fun n : ℕ => (p.val : ℤ) ^ k ∣ f.eval (n : ℤ)) N : ℝ)) ≤
      (N : ℝ) * (∑ p ∈ (primesUpTo N).filter (fun p => Y < p.val),
        (rho f (p.val ^ k) : ℝ) / (p.val : ℝ) ^ k) +
      (f.natDegree : ℝ) * Nat.primeCounting N := by
  classical
  let s := (primesUpTo N).filter (fun p => Y < p.val)
  have hr (p : Nat.Primes) (hp : p ∈ s) : rho f (p.val ^ k) ≤ f.natDegree := by
    apply rho_prime_pow_le_degree f hdeg p.property (Nat.ne_of_gt hk)
    intro hbad
    exact (not_lt_of_ge (hY p hbad)) (Finset.mem_filter.mp hp).2
  calc
    _ ≤ ∑ p ∈ s, ((rho f (p.val ^ k) : ℝ) * ((N : ℝ) / p.val ^ k + 1)) := by
      apply Finset.sum_le_sum
      intro p _
      simpa only [Nat.cast_pow] using count_roots_le f (pow_pos p.property.pos k) N
    _ = (N : ℝ) * (∑ p ∈ s, (rho f (p.val ^ k) : ℝ) / (p.val : ℝ) ^ k) +
        ∑ p ∈ s, (rho f (p.val ^ k) : ℝ) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro p _
      ring
    _ ≤ (N : ℝ) * (∑ p ∈ s, (rho f (p.val ^ k) : ℝ) / (p.val : ℝ) ^ k) +
        (f.natDegree : ℝ) * Nat.primeCounting N := by
      apply add_le_add_right
      calc
        _ ≤ ∑ _p ∈ s, (f.natDegree : ℝ) :=
          Finset.sum_le_sum (fun p hp => by exact_mod_cast hr p hp)
        _ = (f.natDegree : ℝ) * s.card := by simp [mul_comm]
        _ ≤ _ := mul_le_mul_of_nonneg_left (by
          exact_mod_cast (Finset.card_filter_le _ _).trans_eq (card_primesUpTo N))
          (Nat.cast_nonneg _)

theorem finite_sieve_ratio_tendsto (f : Polynomial ℤ) (k : ℕ) (s : Finset Nat.Primes) :
    Tendsto (fun N : ℕ => (Nat.count (AvoidPrimes f k s) N : ℝ) / N)
      atTop (nhds (∏ p ∈ s, localFactor f k p)) := by
  classical
  rw [tendsto_iff_norm_sub_tendsto_zero]
  apply squeeze_zero' (Filter.Eventually.of_forall (fun _ => norm_nonneg _))
    (g := fun N : ℕ => (∏ p ∈ s, p.val ^ k : ℕ) / (N : ℝ))
  · filter_upwards [eventually_gt_atTop 0] with N hN
    have hN' : (0 : ℝ) < N := Nat.cast_pos.mpr hN
    have heq : (Nat.count (AvoidPrimes f k s) N : ℝ) / N -
        (∏ p ∈ s, localFactor f k p) =
        ((Nat.count (AvoidPrimes f k s) N : ℝ) -
          (∏ p ∈ s, localFactor f k p) * N) / N := by
      field_simp
    rw [Real.norm_eq_abs, heq, abs_div, abs_of_pos hN']
    exact div_le_div_of_nonneg_right (finite_sieve_error f k s N) (le_of_lt hN')
  · exact tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop

theorem exists_bad_prime_cutoff (f : Polynomial ℤ)
    (hf : Irreducible (f.map (Int.castRingHom ℚ))) :
    ∃ Y : ℕ, ∀ p : Nat.Primes, (p.val : ℤ) ∣ f.resultant f.derivative → p.val ≤ Y := by
  classical
  let s : Finset Nat.Primes := (finite_resultant_primes f hf).toFinset
  refine ⟨s.sup (fun p => p.val), ?_⟩
  intro p hp
  exact Finset.le_sup (f := fun p : Nat.Primes => p.val) (by simpa [s] using hp)

theorem finite_ratio_difference_le (f : Polynomial ℤ) (hdeg : f.natDegree ≠ 0)
    {k Y N : ℕ} (hk : 0 < k) (hN : 0 < N)
    (hY : ∀ p : Nat.Primes, (p.val : ℤ) ∣ f.resultant f.derivative → p.val ≤ Y) :
    (Nat.count (AvoidPrimes f k (primesUpTo Y)) N : ℝ) / N -
        (natCount f k N : ℝ) / N ≤
      (∑ p ∈ (primesUpTo N).filter (fun p => Y < p.val),
        (rho f (p.val ^ k) : ℝ) / (p.val : ℝ) ^ k) +
      (f.natDegree : ℝ) * ((Nat.primeCounting N : ℝ) / N) +
      (tailCount f k N : ℝ) / N := by
  classical
  have hN' : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hd := finite_sieve_difference_le f k Y N
  have hd' : (Nat.count (AvoidPrimes f k (primesUpTo Y)) N : ℝ) ≤
      (natCount f k N : ℝ) +
      (∑ p ∈ (primesUpTo N).filter (fun p => Y < p.val),
        (Nat.count (fun n : ℕ => (p.val : ℤ) ^ k ∣ f.eval (n : ℤ)) N : ℝ)) +
      (tailCount f k N : ℝ) := by exact_mod_cast hd
  have hi := intermediate_sieve_bound f hdeg hk hY (N := N)
  have hdv := div_le_div_of_nonneg_right hd' (le_of_lt hN')
  have hiv := div_le_div_of_nonneg_right hi (le_of_lt hN')
  simp only [add_div, mul_div_assoc] at hdv hiv
  rw [mul_div_cancel₀ _ (ne_of_gt hN')] at hiv
  linarith

theorem nat_density_from_large_prime_tail (f : Polynomial ℤ)
    (hf : Irreducible (f.map (Int.castRingHom ℚ))) (hdeg : f.natDegree ≠ 0)
    {k : ℕ} (hk : 1 < k) (hloc : LocallyAdmissible f k)
    (htail : Tendsto (fun N : ℕ => (tailCount f k N : ℝ) / N) atTop (nhds 0)) :
    Tendsto (fun N : ℕ => (natCount f k N : ℝ) / N)
      atTop (nhds (densityConstant f k)) := by
  classical
  have hconv := (densityConstant_converges_pos f hf hdeg hk hloc).1
  have hsum := summable_local_proportion f hf hdeg hk
  obtain ⟨Ybad, hbad⟩ := exists_bad_prime_cutoff f hf
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hε6 : 0 < ε / 6 := by positivity
  obtain ⟨Ylocal, hlocal⟩ := finite_local_tail_small f hsum hε6
  obtain ⟨Yprod, hprod⟩ := Metric.tendsto_atTop.mp (finite_product_tendsto f k hconv)
    (ε / 6) hε6
  let Y := max Ybad (max Ylocal Yprod)
  have hYbad : Ybad ≤ Y := le_max_left _ _
  have hYlocal : Ylocal ≤ Y := (le_max_left _ _).trans (le_max_right _ _)
  have hYprod : Yprod ≤ Y := (le_max_right _ _).trans (le_max_right _ _)
  have hprod' := hprod Y hYprod
  have hfinite := Metric.tendsto_nhds.mp (finite_sieve_ratio_tendsto f k (primesUpTo Y))
    (ε / 6) hε6
  have hprime : Tendsto (fun N : ℕ => (f.natDegree : ℝ) *
      ((Nat.primeCounting N : ℝ) / N)) atTop (nhds 0) := by
    simpa only [mul_zero, Function.comp_def] using primeCounting_ratio_tendsto.const_mul (f.natDegree : ℝ)
  have hprime' := Metric.tendsto_nhds.mp hprime (ε / 6) hε6
  have htail' := Metric.tendsto_nhds.mp htail (ε / 6) hε6
  filter_upwards [hfinite, hprime', htail', eventually_gt_atTop 0] with N hF hP hT hN
  have hmid := hlocal ((primesUpTo N).filter (fun p => Y < p.val)) (fun p hp =>
    lt_of_le_of_lt hYlocal (Finset.mem_filter.mp hp).2)
  have hd := finite_ratio_difference_le f hdeg (lt_trans Nat.zero_lt_one hk) hN
    (fun p hp => (hbad p hp).trans hYbad)
  have hle : (natCount f k N : ℝ) / N ≤
      (Nat.count (AvoidPrimes f k (primesUpTo Y)) N : ℝ) / N :=
    div_le_div_of_nonneg_right (by exact_mod_cast natCount_le_finite f k N (primesUpTo Y))
      (Nat.cast_nonneg _)
  simp only [Real.dist_eq, sub_zero] at hF hP hT hprod' ⊢
  have hP' := (le_abs_self _).trans_lt hP
  have hT' := (le_abs_self _).trans_lt hT
  have hF' := abs_sub_lt_iff.mp hF
  have hprod'' := abs_sub_lt_iff.mp hprod'
  apply abs_sub_lt_iff.mpr
  constructor <;> linarith

theorem count_interval_compare (P : ℕ → Prop) [DecidablePred P] (N : ℕ) :
    ((Finset.Icc 1 N).filter P).card ≤ Nat.count P N + 1 ∧
      Nat.count P N ≤ ((Finset.Icc 1 N).filter P).card + 1 := by
  constructor
  · have hs : (Finset.Icc 1 N).filter P ⊆ insert N ((Finset.range N).filter P) := by
      intro n hn
      obtain ⟨hin, hP⟩ := Finset.mem_filter.mp hn
      obtain ⟨_, hnN⟩ := Finset.mem_Icc.mp hin
      by_cases heq : n = N
      · exact Finset.mem_insert.mpr (Or.inl heq)
      · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_filter.mpr
          ⟨Finset.mem_range.mpr (lt_of_le_of_ne hnN heq), hP⟩))
    calc
      _ ≤ (insert N ((Finset.range N).filter P)).card := Finset.card_le_card hs
      _ ≤ _ := by simp [Nat.count_eq_card_filter_range]
  · have hs : (Finset.range N).filter P ⊆ insert 0 ((Finset.Icc 1 N).filter P) := by
      intro n hn
      obtain ⟨hin, hP⟩ := Finset.mem_filter.mp hn
      have hnN := Finset.mem_range.mp hin
      by_cases heq : n = 0
      · exact Finset.mem_insert.mpr (Or.inl heq)
      · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_filter.mpr
          ⟨Finset.mem_Icc.mpr ⟨Nat.one_le_iff_ne_zero.mpr heq, hnN.le⟩, hP⟩))
    calc
      _ ≤ (insert 0 ((Finset.Icc 1 N).filter P)).card := by
        simpa only [Nat.count_eq_card_filter_range] using Finset.card_le_card hs
      _ ≤ _ := by simp

theorem count_natCount_error (f : Polynomial ℤ) (k N : ℕ) :
    |(count f k (N : ℝ) : ℝ) - (natCount f k N : ℝ)| ≤ 1 := by
  classical
  have h := count_interval_compare (fun n : ℕ => PowerFree k (f.eval (n : ℤ))) N
  change |(((Finset.Icc 1 ⌊(N : ℝ)⌋₊).filter _).card : ℝ) - (Nat.count _ N : ℝ)| ≤ 1
  rw [Nat.floor_natCast]
  have h₁ : (((Finset.Icc 1 N).filter (fun n : ℕ => PowerFree k (f.eval (n : ℤ)))).card : ℝ) ≤
      (Nat.count (fun n : ℕ => PowerFree k (f.eval (n : ℤ))) N : ℝ) + 1 := by
    exact_mod_cast h.1
  have h₂ : (Nat.count (fun n : ℕ => PowerFree k (f.eval (n : ℤ))) N : ℝ) ≤
      (((Finset.Icc 1 N).filter (fun n : ℕ => PowerFree k (f.eval (n : ℤ)))).card : ℝ) + 1 := by
    exact_mod_cast h.2
  rw [abs_le]
  constructor <;> linarith

theorem real_asymptotic_from_nat_ratio (f : Polynomial ℤ) (k : ℕ) (c : ℝ)
    (h : Tendsto (fun N : ℕ => (natCount f k N : ℝ) / N) atTop (nhds c)) :
    (fun X : ℝ => (count f k X : ℝ) - c * X) =o[atTop] (fun X : ℝ => X) := by
  classical
  have herr : Tendsto (fun N : ℕ =>
      ((count f k (N : ℝ) : ℝ) - (natCount f k N : ℝ)) / N) atTop (nhds 0) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    simp only [sub_zero, Real.norm_eq_abs]
    apply squeeze_zero' (Filter.Eventually.of_forall (fun _ => abs_nonneg _))
      (g := fun N : ℕ => 1 / (N : ℝ))
    · filter_upwards [eventually_gt_atTop 0] with N hN
      rw [abs_div, abs_of_nonneg (Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
      exact div_le_div_of_nonneg_right (count_natCount_error f k N) (Nat.cast_nonneg _)
    · exact tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hnat : Tendsto (fun N : ℕ => (count f k (N : ℝ) : ℝ) / N)
      atTop (nhds c) := by
    have hh := herr.add h
    simpa only [sub_div, sub_add_cancel, zero_add] using hh
  have hfloor := hnat.comp (tendsto_nat_floor_atTop (α := ℝ))
  have hreal : Tendsto (fun X : ℝ => (count f k X : ℝ) / X) atTop (nhds c) := by
    have hh := hfloor.mul (tendsto_nat_floor_div_atTop (R := ℝ))
    rw [mul_one] at hh
    apply hh.congr'
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with X hX
    have hfloorpos : (⌊X⌋₊ : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.ne_zero_of_lt (Nat.floor_pos.mpr hX))
    have hc : count f k (⌊X⌋₊ : ℝ) = count f k X := by
      simp only [count, Nat.floor_natCast]
    simp only [Function.comp_apply, hc]
    field_simp
  apply (isLittleO_iff_tendsto' (by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with X hX
    exact fun hzero => False.elim (ne_of_gt hX hzero))).mpr
  have hh := hreal.sub_const c
  rw [sub_self] at hh
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with X hX
  field_simp

theorem densityStatement_from_large_prime_tail (f : Polynomial ℤ)
    (hf : Irreducible (f.map (Int.castRingHom ℚ))) (hdeg : f.natDegree ≠ 0)
    {k : ℕ} (hk : 1 < k) (hloc : LocallyAdmissible f k)
    (htail : Tendsto (fun N : ℕ => (tailCount f k N : ℝ) / N) atTop (nhds 0)) :
    DensityStatement f k := by
  obtain ⟨hprod, hpos⟩ := densityConstant_converges_pos f hf hdeg hk hloc
  exact ⟨hprod, hpos, real_asymptotic_from_nat_ratio f k _
    (nat_density_from_large_prime_tail f hf hdeg hk hloc htail)⟩

theorem linear_envelope_of_halving (a b : ℕ → ℝ) (ε : ℝ) (hε : 0 ≤ ε)
    (M : ℕ) (hM : 0 < M)
    (ha : ∀ n, a n ≤ n)
    (hstep : ∀ n, 2 ≤ n → a n ≤ a (n / 2) + b (n / 2))
    (hb : ∀ n, M ≤ n → b n ≤ ε * n) :
    ∀ n, a n ≤ ε * n + 2 * M := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n < 2 * M
    · have hcast : (n : ℝ) < 2 * M := by exact_mod_cast hn
      have hnonneg : 0 ≤ ε * n := mul_nonneg hε (Nat.cast_nonneg n)
      linarith [ha n]
    · have hhalf : M ≤ n / 2 := by omega
      have htwo : 2 ≤ n := by omega
      have hsmall : n / 2 < n := Nat.div_lt_self (by omega) (by omega)
      have hle : 2 * (n / 2 : ℕ) ≤ n := by omega
      have hcast : 2 * (n / 2 : ℕ) ≤ (n : ℝ) := by exact_mod_cast hle
      have hmul := mul_le_mul_of_nonneg_left hcast hε
      have hs := hstep n htwo
      have hi := ih (n / 2) hsmall
      have hh := hb (n / 2) hhalf
      nlinarith

theorem tendsto_zero_of_halving (a b : ℕ → ℝ)
    (ha0 : ∀ n, 0 ≤ a n) (ha : ∀ n, a n ≤ n)
    (hstep : ∀ n, 2 ≤ n → a n ≤ a (n / 2) + b (n / 2))
    (hb : Tendsto (fun n : ℕ => b n / n) atTop (nhds 0)) :
    Tendsto (fun n : ℕ => a n / n) atTop (nhds 0) := by
  rw [Metric.tendsto_atTop] at hb ⊢
  intro ε hε
  obtain ⟨M₀, hM₀⟩ := hb (ε / 2) (by positivity)
  let M := max M₀ 1
  have hM : 0 < M := by dsimp [M]; omega
  have hbound : ∀ n, M ≤ n → b n ≤ (ε / 2) * n := by
    intro n hn
    have hn0 : 0 < n := hM.trans_le hn
    have hh := hM₀ n ((le_max_left M₀ 1).trans hn)
    rw [Real.dist_eq, sub_zero] at hh
    have hlt := (abs_lt.mp hh).2
    have hnr : (0 : ℝ) < n := by exact_mod_cast hn0
    exact (div_lt_iff₀ hnr).mp hlt |>.le
  have henv := linear_envelope_of_halving a b (ε / 2) (by positivity) M hM
    ha hstep hbound
  have hconst : Tendsto (fun n : ℕ => (2 * M : ℝ) / n) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  rw [Metric.tendsto_atTop] at hconst
  obtain ⟨N, hN⟩ := hconst (ε / 2) (by positivity)
  refine ⟨max N 1, ?_⟩
  intro n hn
  have hn0 : 0 < n := by omega
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn0
  have hh := hN n ((le_max_left N 1).trans hn)
  rw [Real.dist_eq, sub_zero] at hh ⊢
  rw [abs_of_nonneg (div_nonneg (ha0 n) hnr.le)]
  have hc := (abs_lt.mp hh).2
  have he := (div_le_div_iff_of_pos_right hnr).mpr (henv n)
  rw [add_div, mul_div_cancel_right₀ _ (ne_of_gt hnr)] at he
  linarith

noncomputable def dyadicTailCount (f : Polynomial ℤ) (k M : ℕ) : ℕ := by
  classical
  exact ((Finset.Ioc M (2 * M)).filter fun n : ℕ =>
    ∃ p : ℕ, p.Prime ∧ M < p ∧ (p : ℤ)^k ∣ f.eval (n : ℤ)).card

theorem tailCount_halving (f : Polynomial ℤ) (k N : ℕ) :
    tailCount f k N ≤ tailCount f k (N / 2) + dyadicTailCount f k (N / 2) + 1 := by
  classical
  let E := fun M n : ℕ => ∃ p : ℕ, p.Prime ∧ M < p ∧ (p : ℤ)^k ∣ f.eval (n : ℤ)
  have hsub : (Finset.range N).filter (E N) ⊆
      ((Finset.range (N / 2)).filter (E (N / 2))) ∪
      insert (N / 2) ((Finset.Ioc (N / 2) (2 * (N / 2))).filter (E (N / 2))) := by
    intro n hn
    obtain ⟨hnN, p, hp, hNp, hdiv⟩ := Finset.mem_filter.mp hn
    have hnN' := Finset.mem_range.mp hnN
    have he : E (N / 2) n := ⟨p, hp, lt_of_le_of_lt (Nat.div_le_self N 2) hNp, hdiv⟩
    by_cases hsmall : n < N / 2
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hsmall, he⟩)
    · apply Finset.mem_union_right
      by_cases heq : n = N / 2
      · exact Finset.mem_insert.mpr (Or.inl heq)
      · apply Finset.mem_insert.mpr
        exact Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr (by omega), he⟩)
  have hcard := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  have hi := Finset.card_insert_le (N / 2)
    ((Finset.Ioc (N / 2) (2 * (N / 2))).filter (E (N / 2)))
  simp only [tailCount, dyadicTailCount, Nat.count_eq_card_filter_range]
  change ((Finset.range N).filter (E N)).card ≤ _
  change ((Finset.range N).filter (E N)).card ≤
    ((Finset.range (N / 2)).filter (E (N / 2))).card +
      ((Finset.Ioc (N / 2) (2 * (N / 2))).filter (E (N / 2))).card + 1
  omega

theorem global_tail_of_dyadic_tail (f : Polynomial ℤ) (k : ℕ)
    (h : Tendsto (fun M : ℕ => (dyadicTailCount f k M : ℝ) / M) atTop (nhds 0)) :
    Tendsto (fun N : ℕ => (tailCount f k N : ℝ) / N) atTop (nhds 0) := by
  classical
  apply tendsto_zero_of_halving (fun n => (tailCount f k n : ℝ))
    (fun n => (dyadicTailCount f k n : ℝ) + 1)
  · intro n; positivity
  · intro n
    have hn : tailCount f k n ≤ n := Nat.count_le _
    exact_mod_cast hn
  · intro n _
    have hh := tailCount_halving f k n
    exact_mod_cast hh
  · have hh := h.add (tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop :
        Tendsto (fun n : ℕ => (1 : ℝ) / n) atTop (nhds 0))
    simpa only [← add_div, add_zero] using hh

theorem exists_primitive_positive_normalization (f : Polynomial ℤ)
    (hf : Irreducible (f.map (Int.castRingHom ℚ))) :
    ∃ (a : ℤ) (g : Polynomial ℤ), a ≠ 0 ∧ f = C a * g ∧
      g.IsPrimitive ∧ 0 < g.leadingCoeff ∧ g.natDegree = f.natDegree ∧
      Irreducible (g.map (Int.castRingHom ℚ)) := by
  have hf0 : f ≠ 0 := fun he => hf.ne_zero (by simp [he])
  have hc : f.content ≠ 0 := content_eq_zero_iff.not.mpr hf0
  have hu : IsUnit (C (f.content : ℚ)) := isUnit_C.mpr
    (isUnit_iff_ne_zero.mpr (by exact_mod_cast hc))
  have hq : Irreducible (f.primPart.map (Int.castRingHom ℚ)) := by
    have he := congrArg (Polynomial.map (Int.castRingHom ℚ)) f.eq_C_content_mul_primPart
    simp only [Polynomial.map_mul, Polynomial.map_C] at he
    rw [he] at hf
    exact (irreducible_isUnit_mul hu).mp hf
  by_cases hpos : 0 < f.primPart.leadingCoeff
  · exact ⟨f.content, f.primPart, hc, f.eq_C_content_mul_primPart,
      f.isPrimitive_primPart, hpos, f.natDegree_primPart, hq⟩
  · refine ⟨-f.content, -f.primPart, neg_ne_zero.mpr hc, ?_, ?_, ?_, ?_, ?_⟩
    · simpa only [map_neg, neg_mul_neg] using f.eq_C_content_mul_primPart
    · exact isPrimitive_of_dvd f.isPrimitive_primPart (by simp)
    · rw [leadingCoeff_neg]
      have hne := leadingCoeff_ne_zero.mpr f.primPart_ne_zero
      omega
    · simp [f.natDegree_primPart]
    · rw [Polynomial.map_neg]
      have hi := (irreducible_isUnit_mul (show IsUnit (-1 : Polynomial ℚ) from
        isUnit_neg_one)).mpr hq
      simpa only [neg_one_mul] using hi

theorem prime_power_dvd_scalar_iff (a b : ℤ) (ha : a ≠ 0) (k : ℕ)
    {p : ℕ} (hp : p.Prime) (hpa : a.natAbs < p) :
    (p : ℤ)^k ∣ a * b ↔ (p : ℤ)^k ∣ b := by
  have hcp : p.Coprime a.natAbs := hp.coprime_iff_not_dvd.mpr
    (Nat.not_dvd_of_pos_of_lt (Int.natAbs_pos.mpr ha) hpa)
  have hci : IsCoprime (p : ℤ) a := Int.isCoprime_iff_nat_coprime.mpr (by simpa using hcp)
  exact ⟨hci.pow_left.dvd_of_dvd_mul_left, fun h => dvd_mul_of_dvd_right h a⟩

theorem tailCount_scalar_eq (a : ℤ) (ha : a ≠ 0) (g : Polynomial ℤ)
    (k N : ℕ) (hN : a.natAbs ≤ N) :
    tailCount (C a * g) k N = tailCount g k N := by
  classical
  unfold tailCount
  congr 1
  funext n
  apply propext
  constructor <;> rintro ⟨p, hp, hNp, hd⟩
  · refine ⟨p, hp, hNp, ?_⟩
    rw [eval_mul, eval_C] at hd
    exact (prime_power_dvd_scalar_iff a _ ha k hp (hN.trans_lt hNp)).mp hd
  · refine ⟨p, hp, hNp, ?_⟩
    rw [eval_mul, eval_C]
    exact dvd_mul_of_dvd_right hd a

theorem global_tail_scalar_iff (a : ℤ) (ha : a ≠ 0) (g : Polynomial ℤ) (k : ℕ) :
    Tendsto (fun N : ℕ => (tailCount (C a * g) k N : ℝ) / N) atTop (nhds 0) ↔
    Tendsto (fun N : ℕ => (tailCount g k N : ℝ) / N) atTop (nhds 0) := by
  apply tendsto_congr'
  filter_upwards [eventually_ge_atTop a.natAbs] with N hN
  rw [tailCount_scalar_eq a ha g k N hN]

theorem dyadic_tail_limit_of_power_saving (f : Polynomial ℤ) (k : ℕ)
    (δ C : ℝ) (hδ : 0 < δ)
    (hbound : ∀ᶠ M : ℕ in atTop,
      (dyadicTailCount f k M : ℝ) ≤ C * (M : ℝ) ^ (1 - δ)) :
    Tendsto (fun M : ℕ => (dyadicTailCount f k M : ℝ) / M) atTop (nhds 0) := by
  apply squeeze_zero' (Eventually.of_forall (fun M => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg M)))
    (g := fun M : ℕ => C * (M : ℝ) ^ (-δ))
  · filter_upwards [hbound, eventually_gt_atTop 0] with M hM hM0
    have hm : (0 : ℝ) < M := by exact_mod_cast hM0
    calc
      _ ≤ (C * (M : ℝ) ^ (1 - δ)) / M := div_le_div_of_nonneg_right hM hm.le
      _ = C * (M : ℝ) ^ (-δ) := by
        rw [show 1 - δ = -δ + 1 by ring, Real.rpow_add hm, Real.rpow_one]
        field_simp
  · simpa only [mul_zero, Function.comp_def] using
      ((tendsto_rpow_neg_atTop hδ).comp tendsto_natCast_atTop_atTop).const_mul C

theorem densityStatement_from_normalized_dyadic_tail (f g : Polynomial ℤ)
    (hf : Irreducible (f.map (Int.castRingHom ℚ))) (hdeg : f.natDegree ≠ 0)
    {k : ℕ} (hk : 1 < k) (hloc : LocallyAdmissible f k)
    (a : ℤ) (ha : a ≠ 0) (hfg : f = C a * g)
    (htail : Tendsto (fun M : ℕ => (dyadicTailCount g k M : ℝ) / M) atTop (nhds 0)) :
    DensityStatement f k := by
  apply densityStatement_from_large_prime_tail f hf hdeg hk hloc
  have hg := global_tail_of_dyadic_tail g k htail
  rw [hfg]
  exact (global_tail_scalar_iff a ha g k).mpr hg

end QuarticPowerFree

end OAI
