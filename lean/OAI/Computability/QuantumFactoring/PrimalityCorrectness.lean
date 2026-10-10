import Mathlib
import OAI.Computability.QuantumFactoring.PrimalityArithmetic

namespace OAI

section


namespace ExactQuantumFactoring.Primality
open Polynomial
open scoped BigOperators

/-- The actual first rejection test in the appendix. -/
def PerfectPower (m : ℕ) : Prop := ∃ b e : ℕ, 2 ≤ b ∧ 2 ≤ e ∧ b^e = m

lemma other_prime_divisor {m p : ℕ} (_hm : 2 ≤ m) (hcom : ¬ m.Prime)
    (hpow : ¬ PerfectPower m) (hp : p.Prime) (hpm : p ∣ m) :
    ∃ q : ℕ, q.Prime ∧ q ∣ m ∧ p ≠ q := by
  by_contra hn
  have hu : IsPrimePow m := isPrimePow_iff_unique_prime_dvd.mpr
    ⟨p, ⟨hp,hpm⟩, fun q hq => by
      by_contra he
      exact hn ⟨q,hq.1,hq.2,Ne.symm he⟩⟩
  obtain ⟨q,e,hq,he,hqe⟩ := (isPrimePow_nat_iff m).mp hu
  have he2 : 2 ≤ e := by
    by_contra h
    have : e = 1 := by omega
    subst e
    simp only [pow_one] at hqe
    exact hcom (hqe ▸ hq)
  exact hpow ⟨q,e,hq.two_le,he2,hqe⟩

lemma sqrt_exponent_lt {n h : ℕ} (hn : 3 ≤ n) (hh : n^2 < h) :
    n * Nat.sqrt h < h := by
  have hsq := Nat.sqrt_le h
  have hnl : n ≤ Nat.sqrt h := Nat.le_sqrt'.mpr hh.le
  by_cases he : n = Nat.sqrt h
  · rw [← he]
    simpa [pow_two] using hh
  · have hlt : n < Nat.sqrt h := by omega
    have hpos : 0 < Nat.sqrt h := by omega
    calc
      n * Nat.sqrt h < Nat.sqrt h * Nat.sqrt h := Nat.mul_lt_mul_of_pos_right hlt hpos
      _ ≤ h := hsq

lemma upper_lt_lower {n m h : ℕ} (hn : 3 ≤ n) (hm : m < 2^n) (hh : n^2 < h) :
    m^(2*Nat.sqrt h) < 8^(h-1) := by
  have hnh := sqrt_exponent_lt hn hh
  have h3 : 3 < h := by nlinarith
  have hqpos : 0 < 2*Nat.sqrt h := by
    have := (Nat.sqrt_pos.mpr (show 0 < h by omega)); omega
  calc
    m^(2*Nat.sqrt h) < (2^n)^(2*Nat.sqrt h) := Nat.pow_lt_pow_left hm (by omega)
    _ = 2^(2*(n*Nat.sqrt h)) := by rw [← pow_mul]; congr 1; ring
    _ < 2^(2*h) := Nat.pow_lt_pow_right (by decide) (by omega)
    _ < 2^(3*(h-1)) := Nat.pow_lt_pow_right (by decide) (by omega)
    _ = 8^(h-1) := by rw [pow_mul]; norm_num

/-- This is the appendix's entire root-count contradiction, over an arbitrary
characteristic-p extension with a primitive s-th root. -/
lemma root_count_contradiction {F : Type*} [Field F] {n m s p q : ℕ}
    [Fact s.Prime] [Fact p.Prime] [CharP F p]
    (hn : 3 ≤ n) (hm : 2 ≤ m) (hmb : m < 2^n)
    (hms : (m : ZMod s) ≠ 0) (hps : (p : ZMod s) ≠ 0)
    (hpbig : 8*s < p) (hpm : p ∣ m) (hq : q.Prime) (hqm : q ∣ m) (hpq : p ≠ q)
    (horder : n^2 < orderOf (m : ZMod s))
    {w : F} (hw : IsPrimitiveRoot w s)
    (htest : ∀ a : ℕ, 1 ≤ a → a ≤ 8*s → Introspective s m (X+C (a : F))) : False := by
  classical
  let S : Finset F := (Finset.Icc 1 (8*s)).image (fun a : ℕ => -(a : F))
  have hScard : S.card = 8*s := by
    rw [Finset.card_image_of_injOn]
    · simp
    · intro a ha b hb he
      apply CharP.natCast_injOn_Iio F p
      · exact lt_of_le_of_lt (Finset.mem_Icc.mp ha).2 hpbig
      · exact lt_of_le_of_lt (Finset.mem_Icc.mp hb).2 hpbig
      · exact neg_injective he
  have hSm : ∀ a ∈ S, Introspective s m (X-C a) := by
    intro a ha
    obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp ha
    simpa using htest b (Finset.mem_Icc.mp hb).1 (Finset.mem_Icc.mp hb).2
  have hSp : ∀ a ∈ S, Introspective s p (X-C a) := by
    intro a ha
    obtain ⟨b,_,rfl⟩ := Finset.mem_image.mp ha
    simpa using (linear_frobenius (F := F) p s b)
  let h := Nat.card (residueOrbit s m p)
  have hlarge : n^2 < h := horder.trans_le (orbit_order_le s m p)
  have hsmall : h ≤ s-1 := orbit_card_le hms hps
  obtain ⟨u,v,u',v',hu,hv,hu',hv',hne,hcon⟩ := orbit_collision s m p
  have hne' : m^u*p^v ≠ m^u'*p^v' :=
    fun he => hne (exponent_pair_injective (by omega) Fact.out hq hqm hpq he)
  have hew : w^(m^u*p^v) = w^(m^u'*p^v') := by
    conv_lhs => rw [pow_eq_pow_mod _ hw.pow_eq_one]
    conv_rhs => rw [pow_eq_pow_mod _ hw.pow_eq_one]
    congr 1
    simpa only [ZMod.val_natCast] using congrArg ZMod.val hcon
  have hc := subset_count_le_collision hw S (t := h-1) (by change h-1 < h; omega)
    hSm hSp (fun a ha => ((hSm a ha).pow_exp u).mul_exp ((hSp a ha).pow_exp v))
    (fun a ha => ((hSm a ha).pow_exp u').mul_exp ((hSp a ha).pow_exp v')) hew hne'
  rw [hScard] at hc
  have hpmle : p ≤ m := Nat.le_of_dvd (by omega) hpm
  have hupp : max (m^u*p^v) (m^u'*p^v') ≤ m^(2*Nat.sqrt h) :=
    max_le (exponent_bound (by omega) hpmle hu hv)
      (exponent_bound (by omega) hpmle hu' hv')
  have hlow : 8^(h-1) ≤ (8*s).choose (h-1) := power_le_choose_mul (by omega)
  exact (not_lt_of_ge (hlow.trans (hc.trans hupp))) (upper_lt_lower hn hmb hlarge)

/-- The source congruence test, represented without an assumed polynomial
identity or an assumed primality oracle. -/
def CongruenceTest (m s a : ℕ) : Prop :=
  (X^s-1 : (ZMod m)[X]) ∣ (X+C (a : ZMod m))^m - (X^m+C (a : ZMod m))

lemma congruenceTest_to_introspective {F : Type*} [Field F] {m s p a : ℕ}
    [CharP F p] (hpm : p ∣ m) (ht : CongruenceTest m s a) :
    Introspective s m (X+C (a : F)) := by
  apply introspective_of_congruence
  have h := Polynomial.map_dvd (ZMod.castHom hpm F) ht
  simpa [CongruenceTest, Polynomial.add_comp] using h

/-- Soundness of the accepting, large-input branch of the exact appendix test.
The small branch is literal trial division. -/
theorem large_branch_prime {n m s : ℕ} (hn : 128 ≤ n) (hm : 2 ≤ m) (hmb : m < 2^n)
    (hs : s.Prime) (hcop : s.Coprime m) (horder : n^2 < orderOf (m : ZMod s))
    (hpow : ¬ PerfectPower m)
    (hsmall : ∀ d : ℕ, 2 ≤ d → d ≤ 8*s → ¬ d ∣ m)
    (htest : ∀ a : ℕ, 1 ≤ a → a ≤ 8*s → CongruenceTest m s a) : m.Prime := by
  by_contra hcom
  obtain ⟨p,hp,hpm⟩ := Nat.exists_prime_and_dvd (by omega : m ≠ 1)
  obtain ⟨q,hq,hqm,hpq⟩ := other_prime_divisor hm hcom hpow hp hpm
  let : Fact s.Prime := ⟨hs⟩
  let : Fact p.Prime := ⟨hp⟩
  have hpbig : 8*s < p := by
    by_contra h
    exact hsmall p hp.two_le (by omega) hpm
  have hms : (m : ZMod s) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    exact (hs.coprime_iff_not_dvd).mp hcop
  have hps : (p : ZMod s) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    intro hd
    have := (Nat.prime_dvd_prime_iff_eq hs hp).mp hd
    nlinarith [hs.two_le]
  have hsp : (s : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    exact Nat.not_dvd_of_pos_of_lt hs.pos (by nlinarith)
  let : NeZero (s : ZMod p) := ⟨hsp⟩
  obtain ⟨w,hw⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure (ZMod p)) s
  exact root_count_contradiction (by omega) hm hmb hms hps hpbig hpm hq hqm hpq horder hw
    (fun a ha hb => congruenceTest_to_introspective hpm (htest a ha hb))

end ExactQuantumFactoring.Primality


end

end OAI
