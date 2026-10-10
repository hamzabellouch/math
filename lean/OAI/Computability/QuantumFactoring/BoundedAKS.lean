import Mathlib
import OAI.Computability.QuantumFactoring.PrimalityAuxiliaryPrime
import OAI.Computability.QuantumFactoring.CyclicPrimality
import OAI.Computability.QuantumFactoring.AKSCriteria
import OAI.Computability.QuantumFactoring.AKSNetworks
import OAI.Computability.QuantumFactoring.CyclicTestBounds
import OAI.Computability.QuantumFactoring.PerfectPowerCircuit

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring.BitArithmetic
open BooleanNetwork Primality

/-- All static search parameters and constants fit polynomial-width words. -/
lemma aks_constants_fit {n : ℕ} (hn : 128 ≤ n) : 8*n^8 < 2^(rootWidth n) := by
  have hp : n < 2^n := Nat.lt_pow_self (by decide)
  have hp8 : n^8 < (2^n)^8 := Nat.pow_lt_pow_left hp (by decide)
  have he : 3+n*8 ≤ rootWidth n := by dsimp [rootWidth]; nlinarith
  calc
    8*n^8 < 8*(2^n)^8 := Nat.mul_lt_mul_of_pos_left hp8 (by decide)
    _ = 2^(3+n*8) := by rw [pow_add,pow_mul]; norm_num
    _ ≤ 2^(rootWidth n) := Nat.pow_le_pow_right (by decide) he

def allCongruences (s w : ℕ) [NeZero s] : BooleanNetwork w 1 :=
  all (List.ofFn (fun i : Fin (8*s) => cyclicTest s w (i.val+1)))

lemma allCongruences_value (s w : ℕ) [NeZero s] (x : Basis w) (hw : 0 < w)
    (hm : 2 ≤ (bitsValue x).toNat) (hs : 8*s < 2^w) :
    (allCongruences s w).eval x 0=true ↔
      ∀ a : ℕ, 1 ≤ a → a ≤ 8*s →
        (cyclicX (R := ZMod (bitsValue x).toNat) s+cyclicC s (a : ZMod (bitsValue x).toNat))^
          (bitsValue x).toNat=cyclicX s^(bitsValue x).toNat+cyclicC s (a : ZMod (bitsValue x).toNat) := by
  rw [allCongruences,all_ofFn_eval]
  constructor
  · intro h a ha has
    have hh := (cyclicTest_correct s w (a-1+1) x hw hm (by omega)).mp
      (h (⟨a-1,by omega⟩ : Fin (8*s)))
    simpa only [show a-1+1=a by omega] using hh
  · intro h i
    rw [cyclicTest_correct s w (i.val+1) x hw hm (by omega)]
    exact h _ (by omega) (by omega)

lemma allCongruences_count (s w : ℕ) [NeZero s] :
    (allCongruences s w).net.count ≤ 8*s*(cyclicTestBound s w+1)+1 := by
  simpa only [allCongruences,List.length_ofFn] using
    all_count (List.ofFn (fun i : Fin (8*s) => cyclicTest s w (i.val+1))) (by
      intro c hc
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hc
      exact cyclicTest_count s w (i.val+1))

/-- The auxiliary modulus branch. The bounded small-divisor test is performed
before the congruences. Evaluating every modulus is a polynomial unrolling of
(the first qualifying modulus in) the manuscript's bounded search. -/
def aksBranch (n s : ℕ) [NeZero s] : BooleanNetwork (rootWidth n) 1 :=
  let w := rootWidth n
  ((dividesNet w s).bnot.band (orderTests w s (n^2))).band
    ((noSmallDivisor w (8*s)).band (allCongruences s w))

lemma aksBranch_sound {n s : ℕ} [NeZero s] (hn : 128 ≤ n) (hs : s.Prime) (hsn : s ≤ n^8)
    (x : Basis (rootWidth n)) (hm : 2 ≤ (bitsValue x).toNat) (hmb : (bitsValue x).toNat < 2^n)
    (hpow : ¬ PerfectPower (bitsValue x).toNat) (h : (aksBranch n s).eval x 0=true) :
    (bitsValue x).toNat.Prime := by
  have hfit := aks_constants_fit hn
  have hsfit : 8*s < 2^(rootWidth n) := (Nat.mul_le_mul_left 8 hsn).trans_lt hfit
  have hsfit' : s < 2^(rootWidth n) := by omega
  have hkfit : n^2 < 2^(rootWidth n) := by
    have hh : rootWidth n < 2^(rootWidth n) := Nat.lt_pow_self (by decide)
    dsimp [rootWidth] at *
    nlinarith
  rw [aksBranch,eval_band,Bool.and_eq_true,eval_band,Bool.and_eq_true,
    eval_band,Bool.and_eq_true,bnot_value,dividesNet_value _ _ _ hsfit',
    orderTests_value _ _ _ _ hs.two_le hsfit' hkfit,
    noSmallDivisor_value _ _ _ hsfit,
    allCongruences_value _ _ _ (by dsimp [rootWidth];omega) hm hsfit] at h
  have hcop : s.Coprime (bitsValue x).toNat := hs.coprime_iff_not_dvd.mpr h.1.1
  have ho := (order_tests_iff hs hcop).mp h.1.2
  by_cases hb : (bitsValue x).toNat ≤ 8*s
  · exact prime_of_no_small_divisor hm hb h.2.1
  · exact cyclic_large_branch_prime hn hm hmb hs hcop ho hpow
      (fun d hd hdB => h.2.1 d hd hdB (by omega)) h.2.2

lemma aksBranch_complete {n s : ℕ} [NeZero s] (hn : 128 ≤ n) (hs : s.Prime) (hsn : s ≤ n^8)
    (x : Basis (rootWidth n)) (hm : (bitsValue x).toNat.Prime)
    (hcop : s.Coprime (bitsValue x).toNat) (ho : n^2 < orderOf ((bitsValue x).toNat : ZMod s)) :
    (aksBranch n s).eval x 0=true := by
  have hfit := aks_constants_fit hn
  have hsfit : 8*s < 2^(rootWidth n) := (Nat.mul_le_mul_left 8 hsn).trans_lt hfit
  have hsfit' : s < 2^(rootWidth n) := by omega
  have hkfit : n^2 < 2^(rootWidth n) := by
    have hh : rootWidth n < 2^(rootWidth n) := Nat.lt_pow_self (by decide)
    dsimp [rootWidth] at *
    nlinarith
  rw [aksBranch,eval_band,Bool.and_eq_true,eval_band,Bool.and_eq_true,
    eval_band,Bool.and_eq_true,bnot_value,dividesNet_value _ _ _ hsfit',
    orderTests_value _ _ _ _ hs.two_le hsfit' hkfit,
    noSmallDivisor_value _ _ _ hsfit,
    allCongruences_value _ _ _ (by dsimp [rootWidth];omega) hm.two_le hsfit]
  refine ⟨⟨hs.coprime_iff_not_dvd.mp hcop,(order_tests_iff hs hcop).mpr ho⟩,?_,?_⟩
  · intro d hd _hdb hdm hdiv
    have := hm.eq_one_or_self_of_dvd d hdiv
    omega
  · intro a _ha _has
    exact cyclic_prime_test hm a

/-- The condition is on the compile-time parameter s≤n^8, not on the possibly
exponentially large input integer. Decidable primality here is a finite bounded
search; its generation-cost proof is separate from circuit size. -/
def aksStaticBranch (n s : ℕ) : BooleanNetwork (rootWidth n) 1 :=
  if h : s.Prime then
    letI : NeZero s := ⟨h.ne_zero⟩
    aksBranch n s
  else constant false

def primalityNet (n : ℕ) : BooleanNetwork (rootWidth n) 1 :=
  (perfectPowerNet n).bnot.band
    (any (List.ofFn (fun s : Fin (n^8+1) => aksStaticBranch n s.val)))

/-- Full exact bounded AKS primality circuit, not an assumed decision procedure. -/
theorem primalityNet_correct {n : ℕ} (hn : 128 ≤ n) (x : Basis (rootWidth n))
    (hm : 2 ≤ (bitsValue x).toNat) (hmb : (bitsValue x).toNat < 2^n) :
    (primalityNet n).eval x 0=true ↔ (bitsValue x).toNat.Prime := by
  rw [primalityNet,eval_band,Bool.and_eq_true,bnot_value,perfectPowerNet_correct (by omega) _ hmb,
    any_ofFn_eval]
  constructor
  · rintro ⟨hpow,s,h⟩
    by_cases hs : s.val.Prime
    · let : NeZero s.val := ⟨hs.ne_zero⟩
      have he : aksStaticBranch n s.val=aksBranch n s.val := dite_eq_left hs
      rw [he] at h
      exact aksBranch_sound hn hs (by omega) x hm hmb hpow h
    · simp [aksStaticBranch,hs] at h
  · intro hp
    obtain ⟨s,hs,hsn,hcop,ho⟩ := auxiliary_prime_exists hn hm hmb
    let : NeZero s := ⟨hs.ne_zero⟩
    refine ⟨prime_not_perfectPower hp,⟨s,by omega⟩,?_⟩
    have he : aksStaticBranch n s=aksBranch n s := dite_eq_left hs
    change (aksStaticBranch n s).eval x 0=true
    rw [he]
    exact aksBranch_complete hn hs hsn x hp hcop ho

end ExactQuantumFactoring.BitArithmetic


end

end OAI
