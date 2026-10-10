import OAI.Combinatorics.SquareDifference.PrimaryKernel

namespace OAI

section
open Finset
open scoped ComplexConjugate BigOperators
namespace SquareDifference

lemma coordinateChar_inflation_trivial {I : Type*} [DecidableEq I]
    (m : I → ℕ) {q L : ℕ} (hqL : q∣L)
    (e : ZMod L ≃+* ∀i, ZMod (m i))
    (ψ : AddChar (ZMod q) ℂ) (i : I) (hiq : (m i).Coprime q) :
    coordinateChar ((ψ.compAddMonoidHom (ZMod.castHom hqL (ZMod q)).toAddMonoidHom).compAddMonoidHom
      e.symm.toAddMonoidHom) i=1 := by
  let f : ZMod (m i) →+ ZMod q :=
    ((ZMod.castHom hqL (ZMod q)).toAddMonoidHom.comp e.symm.toAddMonoidHom).comp
      (AddMonoidHom.single (fun j => ZMod (m j)) i)
  have hf (a : ZMod (m i)) : f a=0 := by
    have hzero : m i • a=0 := by simp only [nsmul_eq_mul,ZMod.natCast_self,zero_mul]
    have h := congrArg f hzero
    rw [map_nsmul,map_zero,nsmul_eq_mul] at h
    exact (ZMod.isUnit_iff_coprime (m i) q).mpr hiq |>.mul_left_cancel (h.trans (mul_zero _).symm)
  ext a
  change ψ (f a)=1
  rw [hf,AddChar.map_zero_eq_one]

noncomputable def primaryModulus (q p : ℕ) : ℕ := p^(max 1 (q.factorization p))

lemma primaryModulus_of_dvd {q p : ℕ} (hq : q≠0) (hp : p.Prime) (h : p∣q) :
    primaryModulus q p=p^(q.factorization p) := by
  have he : 1≤q.factorization p := (hp.pow_dvd_iff_le_factorization hq).mp (by simpa using h)
  simp only [primaryModulus,max_eq_right he]

lemma primaryModulus_of_not_dvd {q p : ℕ} (h : ¬p∣q) : primaryModulus q p=p := by
  simp only [primaryModulus,Nat.factorization_eq_zero_of_not_dvd h,Nat.max_eq_left (by omega : 0≤1),pow_one]

lemma primaryModulus_pos {q p : ℕ} (hp : p.Prime) : 0<primaryModulus q p := pow_pos hp.pos _

lemma primaryModulus_le {q p : ℕ} (hp : p.Prime) : p≤primaryModulus q p := by
  change p≤p^max 1 (q.factorization p)
  simpa only [pow_one] using (pow_le_pow_right₀ hp.one_lt.le (le_max_left 1 (q.factorization p)))

lemma primaryModulus_dvd {q p : ℕ} (hq : q≠0) (hp : p.Prime) (h : p∣q) :
    primaryModulus q p∣q := by rw [primaryModulus_of_dvd hq hp h]; exact Nat.ordProj_dvd q p

lemma primaryModulus_coprime {q p : ℕ} (hp : p.Prime) (h : ¬p∣q) :
    (primaryModulus q p).Coprime q := by
  rw [primaryModulus_of_not_dvd h]
  exact hp.coprime_iff_not_dvd.mpr h

lemma primaryModulus_pairwise (q : ℕ) (S : Finset ℕ) (hp : ∀p∈S, p.Prime) :
    Pairwise (fun p r : S => (primaryModulus q p).Coprime (primaryModulus q r)) := by
  intro p r hpr
  apply Nat.Coprime.pow
  exact (Nat.coprime_primes (hp p p.prop) (hp r r.prop)).mpr
    (fun h => hpr (Subtype.ext h))

lemma dvd_primaryModulus_product (q : ℕ) (hq : q≠0) (S : Finset ℕ)
    (hS : q.primeFactors⊆S) :
    q∣∏p∈S, primaryModulus q p := by
  have he : q=∏p∈q.primeFactors, primaryModulus q p := by
    conv_lhs => rw [Nat.prod_primeFactors_pow_factorization hq]
    apply prod_congr rfl
    intro p hp
    exact (primaryModulus_of_dvd hq (Nat.mem_primeFactors.mp hp).1 (Nat.mem_primeFactors.mp hp).2.1).symm
  calc
    q = ∏p∈q.primeFactors, primaryModulus q p := he
    _ ∣ ∏p∈S, primaryModulus q p := prod_dvd_prod_of_subset _ _ _ hS

lemma prime_dvd_primaryModulus (q p : ℕ) : p∣primaryModulus q p := by
  exact dvd_pow_self p (by have := le_max_left 1 (q.factorization p); omega)

lemma primaryModulus_eq_or_square (q p : ℕ) :
    primaryModulus q p=p ∨ p*p∣primaryModulus q p := by
  by_cases he : max 1 (q.factorization p)=1
  · left; simp only [primaryModulus,he,pow_one]
  · right
    have h2 : 2 ≤ max 1 (q.factorization p) := by have := le_max_left 1 (q.factorization p); omega
    simpa only [primaryModulus,pow_two] using pow_dvd_pow p h2

lemma primaryModulus_eq_of_dvd_prime {q p : ℕ} (hp : p.Prime)
    (h : primaryModulus q p∣p) : primaryModulus q p=p :=
  le_antisymm (Nat.le_of_dvd hp.pos h) (primaryModulus_le hp)

lemma primaryModulus_two_small_or_large (q : ℕ) :
    primaryModulus q 2∣8 ∨ 16∣primaryModulus q 2 := by
  by_cases he : max 1 (q.factorization 2)≤3
  · left
    change 2^max 1 (q.factorization 2)∣2^3
    exact pow_dvd_pow 2 he
  · right
    change 2^4∣2^max 1 (q.factorization 2)
    exact pow_dvd_pow 2 (by omega)

lemma primaryModulus_odd_unit_two {q p : ℕ} (hp : p.Prime) (h2 : p≠2) :
    IsUnit (2 : ZMod (primaryModulus q p)) := by
  apply (ZMod.isUnit_iff_coprime 2 _).mpr
  apply Nat.Coprime.pow_right
  exact (Nat.coprime_primes Nat.prime_two hp).mpr h2.symm

instance primaryModulus_neZero (q p : ℕ) [Fact p.Prime] : NeZero (primaryModulus q p) :=
  ⟨(primaryModulus_pos (Fact.out : p.Prime)).ne'⟩

lemma primary_root_odd_zero {q p : ℕ} [Fact p.Prime]
    (hp : p≠2) (c : ZMod p) (hc : c≠0) (hm : primaryModulus q p≠p)
    (ψ : AddChar (ZMod (primaryModulus q p)) ℂ) (hψ : ψ.IsPrimitive) :
    (𝔼 x : ZMod (primaryModulus q p),
      (residueDensity (prime_dvd_primaryModulus q p) c x : ℂ)*ψ (x^2))=0 := by
  let : NeZero (primaryModulus q p) := ⟨(primaryModulus_pos (Fact.out : p.Prime)).ne'⟩
  have hs := (primaryModulus_eq_or_square q p).resolve_left hm
  apply residueDensity_quadratic_zero_dvd hs c _ ψ hψ
  have h2 : (2 : ZMod p)≠0 := Ring.two_ne_zero (by simpa only [ZMod.ringChar_zmod_n] using hp)
  exact mul_ne_zero h2 hc

lemma primary_root_two_zero (q : ℕ) (hm : ¬primaryModulus q 2∣8)
    (ψ : AddChar (ZMod (primaryModulus q 2)) ℂ) (hψ : ψ.IsPrimitive) :
    (𝔼 x : ZMod (primaryModulus q 2),
      (residueDensity (prime_dvd_primaryModulus q 2) 1 x : ℂ)*ψ (x^2))=0 := by
  let : NeZero (primaryModulus q 2) := ⟨(primaryModulus_pos Nat.prime_two).ne'⟩
  exact odd_root_quadratic_large_dvd ((primaryModulus_two_small_or_large q).resolve_left hm) ψ hψ

lemma primary_sieve_square_zero {q p : ℕ} [Fact p.Prime]
    (hp : p≠2) (hm : primaryModulus q p≠p)
    (ψ : AddChar (ZMod (primaryModulus q p)) ℂ) (hψ : ψ.IsPrimitive) :
    (𝔼 x : ZMod (primaryModulus q p), ψ (x^2))-
      (𝔼 x : ZMod (primaryModulus q p),
        (primeSieveWeight p (ZMod.castHom (prime_dvd_primaryModulus q p) (ZMod p) x) : ℂ)*ψ (x^2))=0 := by
  let : NeZero (primaryModulus q p) := ⟨(primaryModulus_pos (Fact.out : p.Prime)).ne'⟩
  exact prime_power_sieved_zero_dvd hp ((primaryModulus_eq_or_square q p).resolve_left hm) ψ hψ

noncomputable def expPhase (t : ℝ) : ℂ := Real.fourierChar t

noncomputable def periodicMean (a : ℕ → ℂ) (T : ℕ) : ℂ := (T : ℂ)⁻¹*∑m∈range T, a m

lemma rational_num_isUnit (b : ℚ) : IsUnit (b.num : ZMod b.den) := by
  have h := b.isCoprime_num_den.map (Int.castRingHom (ZMod b.den))
  change IsCoprime (b.num : ZMod b.den) ((b.den : ℤ) : ZMod b.den) at h
  rw [Int.cast_natCast,ZMod.natCast_self] at h
  exact isCoprime_zero_right.mp h

noncomputable def rationalChar (b : ℚ) : AddChar (ZMod b.den) ℂ :=
  (@ZMod.stdAddChar b.den ⟨b.pos.ne'⟩).mulShift b.num

lemma rationalChar_primitive (b : ℚ) : (rationalChar b).IsPrimitive := by
  let : NeZero b.den := ⟨b.pos.ne'⟩
  exact primitive_mulShift _ (ZMod.isPrimitive_stdAddChar b.den) _ (rational_num_isUnit b)

lemma rationalChar_int (b : ℚ) (z : ℤ) : rationalChar b (z : ZMod b.den)=expPhase ((b : ℝ)*(z : ℝ)) := by
  let : NeZero b.den := ⟨b.pos.ne'⟩
  rw [rationalChar,AddChar.mulShift_apply,← Int.cast_mul,ZMod.stdAddChar_coe]
  change Complex.exp _=Complex.exp (↑(2*Real.pi*((b : ℝ)*z))*Complex.I)
  congr 1
  have hb : (b : ℝ)=(b.num : ℝ)/(b.den : ℝ) := by exact_mod_cast b.num_div_den.symm
  rw [hb]
  push_cast
  ring

lemma rationalChar_nat_square (b : ℚ) (m : ℕ) :
    rationalChar b ((m : ZMod b.den)^2)=expPhase ((b : ℝ)*(m : ℝ)^2) := by
  have h₁ : (((m : ℤ)^2 : ℤ) : ZMod b.den)=(m : ZMod b.den)^2 := by
    rw [Int.cast_pow,Int.cast_natCast]
  have h₂ : (((m : ℤ)^2 : ℤ) : ℝ)=(m : ℝ)^2 := by
    rw [Int.cast_pow,Int.cast_natCast]
  rw [← h₁,← h₂]
  exact rationalChar_int b ((m : ℤ)^2)

open Fin.NatCast in
lemma finEquiv_natCast {q : ℕ} [NeZero q] (x : Fin q) :
    ZMod.finEquiv q x=(x.val : ZMod q) := by
  cases q with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ q =>
    change x=(Nat.cast x.val : Fin (q+1))
    exact (Fin.natCast_eq_mk x.isLt).symm

lemma expect_zmod_range {q : ℕ} [NeZero q] (f : ZMod q → ℂ) :
    (𝔼 x : ZMod q, f x)=periodicMean (fun m => f (m : ZMod q)) q := by
  rw [← Fintype.expect_equiv (ZMod.finEquiv q).toEquiv (fun x => f (ZMod.finEquiv q x)) f (fun _ => rfl)]
  simp_rw [finEquiv_natCast]
  rw [expect_eq_sum_div_card,card_univ,Fintype.card_fin,Fin.sum_univ_eq_sum_range (fun m => f (m : ZMod q)) q]
  simp only [periodicMean,div_eq_mul_inv,mul_comm]

lemma periodicMean_shift_one (a : ℕ → ℂ) (q : ℕ) (h : Function.Periodic a q) :
    periodicMean (fun m => a (m+1)) q=periodicMean a q := by
  have hs := (sum_range_succ' a q).symm.trans (sum_range_succ a q)
  have h0 : a q=a 0 := by simpa using h 0
  rw [h0] at hs
  exact congrArg (fun z : ℂ => (q : ℂ)⁻¹*z) (add_right_cancel hs)

lemma zmod_natCast_periodic (q : ℕ) (f : ZMod q → ℂ) :
    Function.Periodic (fun m : ℕ => f (m : ZMod q)) q := by
  intro m
  simp only [Nat.cast_add,ZMod.natCast_self,add_zero]

lemma periodicMean_factor_expect {q t : ℕ} [NeZero q] [NeZero t]
    (hqt : q∣t) (f : ZMod q → ℂ) :
    periodicMean (fun m : ℕ => f (m : ZMod q)) t=𝔼 x : ZMod q, f x := by
  have he := (expect_zmod_range (fun x : ZMod t => f (ZMod.castHom hqt (ZMod q) x))).symm
  simp only [map_natCast] at he
  apply he.trans
  exact expect_surjective_addHom (ZMod.castHom hqt (ZMod q)).toAddMonoidHom
    (ZMod.ringHom_surjective _) f

lemma rational_periodic_coefficient {q : ℕ} [NeZero q] (b : ℚ) (hbq : b.den∣q)
    (v : ZMod q → ℂ) :
    periodicMean (fun m => v ((m+1 : ℕ) : ZMod q)*expPhase ((b : ℝ)*(m+1)^2)) q=
      𝔼 x : ZMod q, v x*rationalChar b (ZMod.castHom hbq (ZMod b.den) (x^2)) := by
  have he (m : ℕ) : v (m : ZMod q)*expPhase ((b : ℝ)*(m : ℝ)^2)=
      v (m : ZMod q)*rationalChar b (ZMod.castHom hbq (ZMod b.den) ((m : ZMod q)^2)) := by
    rw [map_pow,map_natCast,rationalChar_nat_square]
  have hs := periodicMean_shift_one
    (fun m : ℕ => v (m : ZMod q)*rationalChar b (ZMod.castHom hbq (ZMod b.den) ((m : ZMod q)^2))) q
    (zmod_natCast_periodic q (fun x => v x*rationalChar b (ZMod.castHom hbq (ZMod b.den) (x^2))))
  have he' (m : ℕ) : v ((m+1 : ℕ) : ZMod q)*expPhase ((b : ℝ)*(m+1)^2)=
      v ((m+1 : ℕ) : ZMod q)*rationalChar b (ZMod.castHom hbq (ZMod b.den) (((m+1 : ℕ) : ZMod q)^2)) := by
    simpa only [Nat.cast_add,Nat.cast_one] using he (m+1)
  simp_rw [he']
  rw [hs]
  exact (expect_zmod_range (fun x : ZMod q => v x*rationalChar b (ZMod.castHom hbq (ZMod b.den) (x^2)))).symm

section CRTRootSieve

variable {I : Type*} [Fintype I] [DecidableEq I]
    (p m : I → ℕ) [∀i, Fact (p i).Prime] [∀i, NeZero (m i)]
    (hm : ∀i, p i∣m i) (R : Finset I) (c : ∀i, ZMod (p i))

noncomputable def localRootWeight (i : I) (x : ZMod (m i)) : ℂ :=
  if i∈R then (residueDensity (hm i) (c i) x : ℂ) else 1

noncomputable def localSieveWeight (i : I) (x : ZMod (m i)) : ℂ :=
  if i∈R then 0 else (primeSieveWeight (p i) (ZMod.castHom (hm i) (ZMod (p i)) x) : ℂ)

omit [Fintype I] [∀i, NeZero (m i)] in
lemma localRootWeight_natCast (i : I) (n : ℕ) :
    localRootWeight p m hm R c i (n : ZMod (m i))=
      if i∈R then (if (n : ZMod (p i))=c i then (p i : ℂ) else 0) else 1 := by
  unfold localRootWeight residueDensity
  simp only [map_natCast]
  split_ifs <;> simp

omit [Fintype I] [∀i, NeZero (m i)] in
lemma localSieveWeight_natCast (i : I) (n : ℕ) :
    localSieveWeight p m hm R i (n : ZMod (m i))=
      if i∈R then 0 else (primeSieveWeight (p i) (n : ZMod (p i)) : ℂ) := by
  unfold localSieveWeight
  simp only [map_natCast]

lemma crt_root_sieve_coefficient {L : ℕ} [NeZero L]
    (e : ZMod L ≃+* ∀i, ZMod (m i)) (ψ : AddChar (ZMod L) ℂ) (H : ℝ) :
    (∑T∈(univ : Finset I).powerset, if ((∏i∈T, p i : ℕ) : ℝ)≤H then
      (-1)^T.card*(𝔼 x : ZMod L,
        (∏i, localRootWeight p m hm R c i (e x i))*
        (∏i∈T, localSieveWeight p m hm R i (e x i))*ψ (x^2)) else 0)=
      truncatedSieveMean univ p H
        (rootSieveA p m hm R c (fun i => coordinateChar (ψ.compAddMonoidHom e.symm.toAddMonoidHom) i))
        (rootSieveB p m hm R (fun i => coordinateChar (ψ.compAddMonoidHom e.symm.toAddMonoidHom) i)) := by
  have he (T : Finset I) := quadratic_mean_equiv e ψ
    (fun x => (∏i, localRootWeight p m hm R c i (x i))*(∏i∈T, localSieveWeight p m hm R i (x i)))
  simp_rw [he]
  rw [product_sieve_coefficient]
  congr 1 <;> funext i
  · unfold rootSieveA localRootWeight
    split_ifs <;> simp only [one_mul]
  · unfold rootSieveB localRootWeight localSieveWeight
    split_ifs <;> simp only [mul_zero,zero_mul,expect_const_zero,one_mul]

lemma periodicMean_crt_root_sieve {L : ℕ} [NeZero L]
    (e : ZMod L ≃+* ∀i, ZMod (m i)) (b : ℚ) (hbL : b.den∣L) (H : ℝ) :
    (∑T∈(univ : Finset I).powerset, if ((∏i∈T, p i : ℕ) : ℝ)≤H then
      (-1)^T.card*periodicMean (fun n : ℕ =>
        (∏i, localRootWeight p m hm R c i ((n+1 : ℕ) : ZMod (m i)))*
        (∏i∈T, localSieveWeight p m hm R i ((n+1 : ℕ) : ZMod (m i)))*
        expPhase ((b : ℝ)*(n+1)^2)) L else 0)=
      truncatedSieveMean univ p H
        (rootSieveA p m hm R c (fun i => coordinateChar
          (((rationalChar b).compAddMonoidHom (ZMod.castHom hbL (ZMod b.den)).toAddMonoidHom).compAddMonoidHom e.symm.toAddMonoidHom) i))
        (rootSieveB p m hm R (fun i => coordinateChar
          (((rationalChar b).compAddMonoidHom (ZMod.castHom hbL (ZMod b.den)).toAddMonoidHom).compAddMonoidHom e.symm.toAddMonoidHom) i)) := by
  rw [← crt_root_sieve_coefficient p m hm R c e
    ((rationalChar b).compAddMonoidHom (ZMod.castHom hbL (ZMod b.den)).toAddMonoidHom) H]
  apply sum_congr rfl
  intro T _
  split_ifs
  · congr 1
    have hn (n : ℕ) : e (n : ZMod L)=(fun i => (n : ZMod (m i))) := by
      rw [map_natCast]
      rfl
    have h := rational_periodic_coefficient b hbL
      (fun x => (∏i, localRootWeight p m hm R c i (e x i))*
        (∏i∈T, localSieveWeight p m hm R i (e x i)))
    simp only [hn] at h
    exact h
  · rfl

end CRTRootSieve

lemma primaryModuli_pairwise {I : Type*} (p : I → ℕ) [∀i, Fact (p i).Prime]
    (hinj : Function.Injective p) (q : ℕ) :
    Pairwise (fun i j => (primaryModulus q (p i)).Coprime (primaryModulus q (p j))) := by
  intro i j hij
  apply Nat.Coprime.pow
  exact (Nat.coprime_primes (Fact.out : (p i).Prime) (Fact.out : (p j).Prime)).mpr
    (fun h => hij (hinj h))

lemma primary_two_root_zero_of_eq {q p : ℕ} [Fact p.Prime]
    (hp : p=2) (c : ZMod p) (hc : c=1) (hm : ¬primaryModulus q p∣8)
    (ψ : AddChar (ZMod (primaryModulus q p)) ℂ) (hψ : ψ.IsPrimitive) :
    (𝔼 x : ZMod (primaryModulus q p),
      (residueDensity (prime_dvd_primaryModulus q p) c x : ℂ)*ψ (x^2))=0 := by
  subst p
  rw [hc]
  exact primary_root_two_zero q hm ψ hψ

section PrimaryCoefficient

variable {I : Type*} [Fintype I] [DecidableEq I]
  (p : I → ℕ) [∀i, Fact (p i).Prime] (hinj : Function.Injective p)
  (q : ℕ) [NeZero q]
  (hq : q∣∏i, primaryModulus q (p i))

noncomputable def primaryCoordinateChar (ψ : AddChar (ZMod q) ℂ)
    (i : I) : AddChar (ZMod (primaryModulus q (p i))) ℂ :=
  coordinateChar ((ψ.compAddMonoidHom (ZMod.castHom hq (ZMod q)).toAddMonoidHom).compAddMonoidHom
    (ZMod.prodEquivPi (fun i => primaryModulus q (p i)) (primaryModuli_pairwise p hinj q)).symm.toAddMonoidHom) i

lemma primaryCoordinateChar_primitive (ψ : AddChar (ZMod q) ℂ) (hψ : ψ.IsPrimitive)
    (i : I) (hi : p i∣q) : (primaryCoordinateChar p hinj q hq ψ i).IsPrimitive := by
  exact coordinateChar_inflation_primitive _ hq _ ψ hψ i
    (primaryModulus_dvd (NeZero.ne q) (Fact.out : (p i).Prime) hi)

omit [NeZero q] in
lemma primaryCoordinateChar_trivial (ψ : AddChar (ZMod q) ℂ)
    (i : I) (hi : ¬p i∣q) : primaryCoordinateChar p hinj q hq ψ i=1 := by
  exact coordinateChar_inflation_trivial _ hq _ ψ i
    (primaryModulus_coprime (Fact.out : (p i).Prime) hi)

noncomputable def primaryActive : Finset I := univ.filter (fun i => p i∣q)

omit [DecidableEq I] [∀i, Fact (p i).Prime] [NeZero q] in
@[simp] lemma mem_primaryActive (i : I) : i∈primaryActive p q ↔ p i∣q := by
  simp only [primaryActive,mem_filter,mem_univ,true_and]

lemma primary_root_sieve_decay (R : Finset I) (c : ∀i, ZMod (p i))
    (htwo : ∀i, p i=2 → i∈R) (ψ : AddChar (ZMod q) ℂ) (hψ : ψ.IsPrimitive) (H : ℝ) :
    ‖truncatedSieveMean univ p H
      (rootSieveA p (fun i => primaryModulus q (p i)) (fun i => prime_dvd_primaryModulus q (p i)) R c
        (primaryCoordinateChar p hinj q hq ψ))
      (rootSieveB p (fun i => primaryModulus q (p i)) (fun i => prime_dvd_primaryModulus q (p i)) R
        (primaryCoordinateChar p hinj q hq ψ))‖≤
      2^64*(∏i∈primaryActive p q\R, (primaryModulus q (p i) : ℝ))^(-(1 : ℝ)/3) := by
  apply rootSieve_decay p (fun i => primaryModulus q (p i))
    (fun i => prime_dvd_primaryModulus q (p i)) R c (primaryCoordinateChar p hinj q hq ψ)
    univ (primaryActive p q) (subset_univ _) H (hinj.injOn)
  · intro i _; exact primaryModulus_le (Fact.out : (p i).Prime)
  · intro i _ hi
    exact primaryCoordinateChar_trivial p hinj q hq ψ i (by simpa only [mem_primaryActive] using hi)
  · intro i hi
    exact primaryCoordinateChar_primitive p hinj q hq ψ hψ i (mem_primaryActive p q i |>.mp (mem_sdiff.mp hi).1)
  · intro i hi
    exact primaryModulus_odd_unit_two (Fact.out : (p i).Prime)
      (fun he => (mem_sdiff.mp hi).2 (htwo i he))

lemma primary_root_sieve_odd_zero (R : Finset I) (c : ∀i, ZMod (p i))
    (ψ : AddChar (ZMod q) ℂ) (hψ : ψ.IsPrimitive) (H : ℝ)
    (i : I) (hi : i∈R) (hqi : p i∣q) (hpi : p i≠2) (hci : c i≠0)
    (hei : primaryModulus q (p i)≠p i) :
    truncatedSieveMean univ p H
      (rootSieveA p (fun i => primaryModulus q (p i)) (fun i => prime_dvd_primaryModulus q (p i)) R c
        (primaryCoordinateChar p hinj q hq ψ))
      (rootSieveB p (fun i => primaryModulus q (p i)) (fun i => prime_dvd_primaryModulus q (p i)) R
        (primaryCoordinateChar p hinj q hq ψ))=0 := by
  apply rootSieve_zero_of_root p (fun i => primaryModulus q (p i))
    (fun i => prime_dvd_primaryModulus q (p i)) R c (primaryCoordinateChar p hinj q hq ψ)
    univ (primaryActive p q) (subset_univ _) H
    (fun j _ hj => primaryCoordinateChar_trivial p hinj q hq ψ j (by simpa only [mem_primaryActive] using hj)) i
    (mem_inter.mpr ⟨(mem_primaryActive p q i).mpr hqi,hi⟩)
  exact primary_root_odd_zero hpi (c i) hci hei _
    (primaryCoordinateChar_primitive p hinj q hq ψ hψ i hqi)

lemma primary_root_sieve_square_zero (R : Finset I) (c : ∀i, ZMod (p i))
    (ψ : AddChar (ZMod q) ℂ) (hψ : ψ.IsPrimitive) (H : ℝ)
    (hH : ((∏i∈primaryActive p q\R, p i : ℕ) : ℝ)≤H)
    (i : I) (hi : i∉R) (hqi : p i∣q) (hpi : p i≠2)
    (hei : primaryModulus q (p i)≠p i) :
    truncatedSieveMean univ p H
      (rootSieveA p (fun i => primaryModulus q (p i)) (fun i => prime_dvd_primaryModulus q (p i)) R c
        (primaryCoordinateChar p hinj q hq ψ))
      (rootSieveB p (fun i => primaryModulus q (p i)) (fun i => prime_dvd_primaryModulus q (p i)) R
        (primaryCoordinateChar p hinj q hq ψ))=0 := by
  exact rootSieve_zero_of_squarefactor p (fun i => primaryModulus q (p i))
    (fun i => prime_dvd_primaryModulus q (p i)) R c (primaryCoordinateChar p hinj q hq ψ)
    univ (primaryActive p q) (subset_univ _) H
    (fun j _ hj => primaryCoordinateChar_trivial p hinj q hq ψ j (by simpa only [mem_primaryActive] using hj)) hH i
    (mem_sdiff.mpr ⟨(mem_primaryActive p q i).mpr hqi,hi⟩) hpi
    ((primaryModulus_eq_or_square q (p i)).resolve_left hei)
    (primaryCoordinateChar_primitive p hinj q hq ψ hψ i hqi)

omit [NeZero q] in
lemma primary_root_sieve_complete (R : Finset I) (c : ∀i, ZMod (p i))
    (ψ : AddChar (ZMod q) ℂ) (H : ℝ)
    (hH : ((∏i∈primaryActive p q\R, p i : ℕ) : ℝ)≤H)
    (he : ∀i∈primaryActive p q\R, primaryModulus q (p i)=p i) :
    truncatedSieveMean univ p H
      (rootSieveA p (fun i => primaryModulus q (p i)) (fun i => prime_dvd_primaryModulus q (p i)) R c
        (primaryCoordinateChar p hinj q hq ψ))
      (rootSieveB p (fun i => primaryModulus q (p i)) (fun i => prime_dvd_primaryModulus q (p i)) R
        (primaryCoordinateChar p hinj q hq ψ))=
      (∏i∈primaryActive p q∩R,
        rootSieveA p (fun i => primaryModulus q (p i)) (fun i => prime_dvd_primaryModulus q (p i)) R c
          (primaryCoordinateChar p hinj q hq ψ) i)*
      ∏i∈primaryActive p q\R, unitQuadraticMean (primaryCoordinateChar p hinj q hq ψ i) := by
  rw [rootSieve_complete p (fun i => primaryModulus q (p i))
    (fun i => prime_dvd_primaryModulus q (p i)) R c (primaryCoordinateChar p hinj q hq ψ)
    univ (primaryActive p q) (subset_univ _) H
    (fun j _ hj => primaryCoordinateChar_trivial p hinj q hq ψ j (by simpa only [mem_primaryActive] using hj)) hH]
  congr 1
  apply prod_congr rfl
  intro i hi
  simp only [rootSieveA,rootSieveB,ite_eq_right (mem_sdiff.mp hi).2]
  exact prime_unit_quadratic_of_eq (prime_dvd_primaryModulus q (p i)) (he i hi) _

lemma primary_root_sieve_tail (R : Finset I) (c : ∀i, ZMod (p i))
    (htwo : ∀i, p i=2 → i∈R) (ψ : AddChar (ZMod q) ℂ) (hψ : ψ.IsPrimitive)
    (H : ℝ) (hH : 0<H) (htail : H≤∏i∈primaryActive p q\R, (p i : ℝ)) :
    ‖truncatedSieveMean univ p H
      (rootSieveA p (fun i => primaryModulus q (p i)) (fun i => prime_dvd_primaryModulus q (p i)) R c
        (primaryCoordinateChar p hinj q hq ψ))
      (rootSieveB p (fun i => primaryModulus q (p i)) (fun i => prime_dvd_primaryModulus q (p i)) R
        (primaryCoordinateChar p hinj q hq ψ))‖≤2^64*H^(-(1 : ℝ)/3) := by
  apply (primary_root_sieve_decay p hinj q hq R c htwo ψ hψ H).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.rpow_le_rpow_of_nonpos hH
  · exact htail.trans (Finset.prod_le_prod₀ (fun _ _ => Nat.cast_nonneg _) (fun i _ => by
      exact_mod_cast primaryModulus_le (q := q) (Fact.out : (p i).Prime)))
  · norm_num

lemma primary_root_sieve_two_zero (R : Finset I) (c : ∀i, ZMod (p i))
    (ψ : AddChar (ZMod q) ℂ) (hψ : ψ.IsPrimitive) (H : ℝ)
    (i : I) (hi : i∈R) (hqi : p i∣q) (hpi : p i=2) (hci : c i=1)
    (hei : ¬primaryModulus q (p i)∣8) :
    truncatedSieveMean univ p H
      (rootSieveA p (fun i => primaryModulus q (p i)) (fun i => prime_dvd_primaryModulus q (p i)) R c
        (primaryCoordinateChar p hinj q hq ψ))
      (rootSieveB p (fun i => primaryModulus q (p i)) (fun i => prime_dvd_primaryModulus q (p i)) R
        (primaryCoordinateChar p hinj q hq ψ))=0 := by
  apply rootSieve_zero_of_root p (fun i => primaryModulus q (p i))
    (fun i => prime_dvd_primaryModulus q (p i)) R c (primaryCoordinateChar p hinj q hq ψ)
    univ (primaryActive p q) (subset_univ _) H
    (fun j _ hj => primaryCoordinateChar_trivial p hinj q hq ψ j (by simpa only [mem_primaryActive] using hj)) i
    (mem_inter.mpr ⟨(mem_primaryActive p q i).mpr hqi,hi⟩)
  exact primary_two_root_zero_of_eq hpi (c i) hci hei _
    (primaryCoordinateChar_primitive p hinj q hq ψ hψ i hqi)

end PrimaryCoefficient

lemma nat_pairwise_coprime_prod_dvd {I : Type*} [DecidableEq I]
    (S : Finset I) (m : I → ℕ) (q : ℕ)
    (hc : (↑S : Set I).Pairwise (fun i j => (m i).Coprime (m j)))
    (hm : ∀i∈S, m i∣q) : (∏i∈S, m i)∣q := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a S ha ih =>
    rw [prod_insert ha]
    apply Nat.Coprime.mul_dvd_of_dvd_of_dvd
    · apply Nat.Coprime.prod_right
      intro i hi
      exact hc (mem_insert_self _ _) (mem_insert_of_mem hi) (ne_of_mem_of_not_mem hi ha).symm
    · exact hm a (mem_insert_self _ _)
    · apply ih
      · exact hc.mono (by intro i hi; exact mem_insert_of_mem hi)
      · intro i hi; exact hm i (mem_insert_of_mem hi)

lemma primary_denominator_factor {I : Type*} [Fintype I] [DecidableEq I]
    (p : I → ℕ) [∀i, Fact (p i).Prime] (hinj : Function.Injective p)
    (q : ℕ) [NeZero q] (hq : q∣∏i, primaryModulus q (p i)) :
    q=∏i∈primaryActive p q, primaryModulus q (p i) := by
  apply Nat.dvd_antisymm
  · have hc : q.Coprime (∏i∈(primaryActive p q)ᶜ, primaryModulus q (p i)) := by
      apply Nat.Coprime.prod_right
      intro i hi
      apply Nat.Coprime.symm
      exact primaryModulus_coprime (Fact.out : (p i).Prime)
        (by simpa only [mem_compl,mem_primaryActive] using hi)
    apply hc.dvd_of_dvd_mul_right
    rwa [prod_mul_prod_compl]
  · apply nat_pairwise_coprime_prod_dvd
    · intro i _ j _ hij; exact primaryModuli_pairwise p hinj q hij
    · intro i hi
      exact primaryModulus_dvd (NeZero.ne q) (Fact.out : (p i).Prime) ((mem_primaryActive p q i).mp hi)

lemma primary_denominator_root_factor {I : Type*} [Fintype I] [DecidableEq I]
    (p : I → ℕ) [∀i, Fact (p i).Prime] (hinj : Function.Injective p)
    (q : ℕ) [NeZero q] (hq : q∣∏i, primaryModulus q (p i)) (R : Finset I) :
    q=(∏i∈primaryActive p q∩R, primaryModulus q (p i))*
      (∏i∈primaryActive p q\R, primaryModulus q (p i)) := by
  rw [prod_inter_mul_prod_sdiff,← primary_denominator_factor p hinj q hq]

section KernelCoefficient

variable {I : Type*} [Fintype I] [DecidableEq I]
  (p : I → ℕ) [∀ i, Fact (p i).Prime] (hinj : Function.Injective p)
  (b : ℚ) (hb : b.den ∣ ∏ i, primaryModulus b.den (p i))
  (R : Finset I) (c : ∀ i, ZMod (p i))

noncomputable def primarySieveCoefficient (H : ℝ) : ℂ :=
  truncatedSieveMean univ p H
    (rootSieveA p (fun i => primaryModulus b.den (p i))
      (fun i => prime_dvd_primaryModulus b.den (p i)) R c
      (primaryCoordinateChar p hinj b.den hb (rationalChar b)))
    (rootSieveB p (fun i => primaryModulus b.den (p i))
      (fun i => prime_dvd_primaryModulus b.den (p i)) R
      (primaryCoordinateChar p hinj b.den hb (rationalChar b)))

noncomputable def primaryModelCoefficient (H : ℝ) : ℂ :=
  if ((∏ i ∈ primaryActive p b.den \ R, p i : ℕ) : ℝ) ≤ H ∧
       (∀ i ∈ primaryActive p b.den \ R, primaryModulus b.den (p i) = p i) then
    (∏ i ∈ primaryActive p b.den ∩ R,
      rootSieveA p (fun i => primaryModulus b.den (p i))
        (fun i => prime_dvd_primaryModulus b.den (p i)) R c
        (primaryCoordinateChar p hinj b.den hb (rationalChar b)) i) *
    ∏ i ∈ primaryActive p b.den \ R,
      unitQuadraticMean (primaryCoordinateChar p hinj b.den hb (rationalChar b) i)
  else 0

lemma primary_coefficient_small (H : ℝ)
    (htwo : ∀ i, p i = 2 → i ∈ R)
    (hH : ((∏ i ∈ primaryActive p b.den \ R, p i : ℕ) : ℝ) ≤ H) :
    primarySieveCoefficient p hinj b hb R c H =
      primaryModelCoefficient p hinj b hb R c H := by
  classical
  let : NeZero b.den := ⟨b.pos.ne'⟩
  unfold primaryModelCoefficient
  by_cases he : ∀ i ∈ primaryActive p b.den \ R, primaryModulus b.den (p i) = p i
  · rw [ite_eq_left ⟨hH, he⟩]
    exact primary_root_sieve_complete p hinj b.den hb R c (rationalChar b) H hH he
  · rw [ite_eq_right (fun h => he h.2)]
    push Not at he
    obtain ⟨i,hi,hei⟩ := he
    apply primary_root_sieve_square_zero p hinj b.den hb R c (rationalChar b)
      (rationalChar_primitive b) H hH i (mem_sdiff.mp hi).2
      ((mem_primaryActive p b.den i).mp (mem_sdiff.mp hi).1) _ hei
    exact fun h2 => (mem_sdiff.mp hi).2 (htwo i h2)

lemma primary_coefficient_uniform (H : ℝ) (hH : 0 < H)
    (htwo : ∀ i, p i = 2 → i ∈ R) :
    ‖primarySieveCoefficient p hinj b hb R c H -
      primaryModelCoefficient p hinj b hb R c H‖ ≤ 2^64 * H^(-(1 : ℝ)/3) := by
  classical
  let : NeZero b.den := ⟨b.pos.ne'⟩
  by_cases h : ((∏ i ∈ primaryActive p b.den \ R, p i : ℕ) : ℝ) ≤ H
  · rw [primary_coefficient_small p hinj b hb R c H htwo h, sub_self, norm_zero]
    positivity
  · rw [primaryModelCoefficient,ite_eq_right (fun hh => h hh.1),sub_zero]
    exact primary_root_sieve_tail p hinj b.den hb R c htwo (rationalChar b)
      (rationalChar_primitive b) H hH (by
        simpa only [Nat.cast_prod] using (le_of_lt (lt_of_not_ge h)))

noncomputable def actualRootWeight (n : ℕ) : ℂ :=
  ∏ i ∈ R, if (n : ZMod (p i)) = c i then (p i : ℂ) else 0

noncomputable def actualSieveWeight (T : Finset I) (n : ℕ) : ℂ :=
  ∏ i ∈ T, if i ∈ R then 0 else (primeSieveWeight (p i) (n : ZMod (p i)) : ℂ)

noncomputable def actualDivisorWeight (H : ℝ) (n : ℕ) : ℂ :=
  actualRootWeight p R c n *
    ∑ T ∈ (univ : Finset I).powerset,
      if ((∏ i ∈ T, p i : ℕ) : ℝ) ≤ H then
        (-1)^T.card * actualSieveWeight p R T n else 0

lemma actualRootWeight_local (n : ℕ) :
    (∏ i, localRootWeight p (fun i => primaryModulus b.den (p i))
      (fun i => prime_dvd_primaryModulus b.den (p i)) R c i
      (n : ZMod (primaryModulus b.den (p i)))) = actualRootWeight p R c n := by
  simp only [localRootWeight_natCast, actualRootWeight]
  rw [← prod_filter]
  simp only [filter_mem_eq_inter, univ_inter]

omit [Fintype I] in
lemma actualSieveWeight_local (T : Finset I) (n : ℕ) :
    (∏ i ∈ T, localSieveWeight p (fun i => primaryModulus b.den (p i))
      (fun i => prime_dvd_primaryModulus b.den (p i)) R i
      (n : ZMod (primaryModulus b.den (p i)))) = actualSieveWeight p R T n := by
  simp only [localSieveWeight_natCast, actualSieveWeight]

lemma actualDivisorWeight_coefficient (H : ℝ) :
    periodicMean (fun n => actualDivisorWeight p R c H (n+1) *
      expPhase ((b : ℝ)*(n+1)^2)) (∏ i, primaryModulus b.den (p i)) =
      primarySieveCoefficient p hinj b hb R c H := by
  classical
  let : NeZero (∏ i, primaryModulus b.den (p i)) :=
    ⟨(Finset.prod_pos (fun i _ => primaryModulus_pos (Fact.out : (p i).Prime))).ne'⟩
  have h := periodicMean_crt_root_sieve p (fun i => primaryModulus b.den (p i))
    (fun i => prime_dvd_primaryModulus b.den (p i)) R c
    (ZMod.prodEquivPi (fun i => primaryModulus b.den (p i))
      (primaryModuli_pairwise p hinj b.den)) b hb H
  change _ = primarySieveCoefficient p hinj b hb R c H at h
  rw [← h]
  unfold periodicMean actualDivisorWeight
  simp only [actualRootWeight_local,actualSieveWeight_local]
  simp only [mul_sum, sum_mul]
  rw [sum_comm]
  apply sum_congr rfl
  intro T _
  by_cases hT : ((∏ i ∈ T, p i : ℕ) : ℝ) ≤ H
  · simp only [ite_eq_left hT]
    apply sum_congr rfl
    intro n _
    ring
  · simp only [ite_eq_right hT,mul_zero,zero_mul,sum_const_zero]

lemma actualDivisorWeight_coefficient_uniform (H : ℝ) (hH : 0 < H)
    (htwo : ∀ i, p i = 2 → i ∈ R) :
    ‖periodicMean (fun n => actualDivisorWeight p R c H (n+1) *
        expPhase ((b : ℝ)*(n+1)^2)) (∏ i, primaryModulus b.den (p i)) -
      primaryModelCoefficient p hinj b hb R c H‖ ≤ 2^64 * H^(-(1 : ℝ)/3) := by
  rw [actualDivisorWeight_coefficient p hinj b hb R c]
  exact primary_coefficient_uniform p hinj b hb R c H hH htwo

noncomputable def rootSquareModulus : ℕ := ∏ i ∈ R, if p i = 2 then 8 else p i

omit [Fintype I] [DecidableEq I] in
lemma rootSquareModulus_pos : 0 < rootSquareModulus p R := by
  apply prod_pos
  intro i _
  split_ifs
  · norm_num
  · exact (Fact.out : (p i).Prime).pos

lemma unitQuadraticMean_norm {S : Type*} [CommRing S] [Fintype S] [DecidableEq S]
    (ψ : AddChar S ℂ) : ‖unitQuadraticMean ψ‖ ≤ 1 := by
  unfold unitQuadraticMean
  apply (RCLike.norm_expect_le (K := ℂ)).trans
  simp only [ψ.norm_apply, Fintype.expect_const]
  exact le_rfl

lemma primaryModelCoefficient_norm (H : ℝ) :
    ‖primaryModelCoefficient p hinj b hb R c H‖ ≤ 1 := by
  classical
  unfold primaryModelCoefficient
  split_ifs
  · rw [norm_mul, norm_prod, norm_prod]
    apply le_trans (mul_le_of_le_one_left (by positivity) ?_) ?_
    · apply prod_le_one₀ (fun _ _ => norm_nonneg _)
      intro index membership
      rw [rootSieveA, ite_eq_left (mem_inter.mp membership).2]
      exact residueDensity_quadratic_norm _ _ _
    · apply prod_le_one₀ (fun _ _ => norm_nonneg _)
      intro index _
      exact unitQuadraticMean_norm _
  · simp

lemma primaryModelCoefficient_denominator (H : ℝ)
    (htwo : ∀ i, p i = 2 → i ∈ R)
    (hc : ∀ i ∈ R, if p i = 2 then c i = 1 else c i ≠ 0)
    (hne : primaryModelCoefficient p hinj b hb R c H ≠ 0) :
    b.den ∣ rootSquareModulus p R * ∏ i ∈ primaryActive p b.den \ R, p i := by
  classical
  let : NeZero b.den := ⟨b.pos.ne'⟩
  have hd : ((∏ i ∈ primaryActive p b.den \ R, p i : ℕ) : ℝ) ≤ H ∧
      (∀ i ∈ primaryActive p b.den \ R, primaryModulus b.den (p i) = p i) := by
    by_contra hd
    exact hne (ite_eq_right hd)
  have hs : primarySieveCoefficient p hinj b hb R c H ≠ 0 := by
    rwa [primary_coefficient_small p hinj b hb R c H htwo hd.1]
  have hr (i : I) (hi : i ∈ primaryActive p b.den ∩ R) :
      primaryModulus b.den (p i) ∣ (if p i = 2 then 8 else p i) := by
    have hqi : p i ∣ b.den := (mem_primaryActive p b.den i).mp (mem_inter.mp hi).1
    have hiR := (mem_inter.mp hi).2
    by_cases h2 : p i = 2
    · rw [ite_eq_left h2]
      by_contra hlarge
      apply hs
      exact primary_root_sieve_two_zero p hinj b.den hb R c (rationalChar b)
        (rationalChar_primitive b) H i hiR hqi h2 (by simpa [h2] using hc i hiR) hlarge
    · rw [ite_eq_right h2]
      have hm : primaryModulus b.den (p i) = p i := by
        by_contra hlarge
        apply hs
        exact primary_root_sieve_odd_zero p hinj b.den hb R c (rationalChar b)
          (rationalChar_primitive b) H i hiR hqi h2 (by simpa [h2] using hc i hiR) hlarge
      rw [hm]
  have hrprod : (∏ i ∈ primaryActive p b.den ∩ R, primaryModulus b.den (p i)) ∣
      rootSquareModulus p R := by
    apply (prod_dvd_prod_of_dvd _ _ hr).trans
    exact prod_dvd_prod_of_subset (primaryActive p b.den ∩ R) R
      (fun i => if p i = 2 then 8 else p i) inter_subset_right
  nth_rw 1 [primary_denominator_root_factor p hinj b.den hb R]
  have he : (∏ i ∈ primaryActive p b.den \ R, primaryModulus b.den (p i)) =
      ∏ i ∈ primaryActive p b.den \ R, p i := prod_congr rfl hd.2
  rw [he]
  exact mul_dvd_mul_right hrprod _

lemma primaryModelCoefficient_denominator_le (H : ℝ)
    (htwo : ∀ i, p i = 2 → i ∈ R)
    (hc : ∀ i ∈ R, if p i = 2 then c i = 1 else c i ≠ 0)
    (hne : primaryModelCoefficient p hinj b hb R c H ≠ 0) :
    (b.den : ℝ) ≤ rootSquareModulus p R * H := by
  have hd : ((∏ i ∈ primaryActive p b.den \ R, p i : ℕ) : ℝ) ≤ H := by
    by_contra hd
    exact hne (ite_eq_right (fun h => hd h.1))
  have hp : 0 < rootSquareModulus p R * ∏ i ∈ primaryActive p b.den \ R, p i :=
    mul_pos (rootSquareModulus_pos p R) (prod_pos (fun i _ => (Fact.out : (p i).Prime).pos))
  calc
    _ ≤ ((rootSquareModulus p R * ∏ i ∈ primaryActive p b.den \ R, p i : ℕ) : ℝ) := by
      exact_mod_cast Nat.le_of_dvd hp (primaryModelCoefficient_denominator p hinj b hb R c H htwo hc hne)
    _ = (rootSquareModulus p R : ℝ) * ((∏ i ∈ primaryActive p b.den \ R, p i : ℕ) : ℝ) := by push_cast; rfl
    _ ≤ _ := mul_le_mul_of_nonneg_left hd (Nat.cast_nonneg _)

lemma primaryModelCoefficient_zero_of_denominator (H : ℝ)
    (htwo : ∀ i, p i = 2 → i ∈ R)
    (hc : ∀ i ∈ R, if p i = 2 then c i = 1 else c i ≠ 0)
    (hden : rootSquareModulus p R * H < (b.den : ℝ)) :
    primaryModelCoefficient p hinj b hb R c H = 0 := by
  by_contra hne
  exact (not_le_of_gt hden) (primaryModelCoefficient_denominator_le p hinj b hb R c H htwo hc hne)

end KernelCoefficient

end SquareDifference
end

end OAI
