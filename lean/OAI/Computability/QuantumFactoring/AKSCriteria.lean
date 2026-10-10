import Mathlib
import OAI.Computability.QuantumFactoring.PrimalityCorrectness

namespace OAI

section


namespace ExactQuantumFactoring.Primality

lemma prime_not_perfectPower {m : ℕ} (hm : m.Prime) : ¬ PerfectPower m := by
  rintro ⟨b,e,hb,he,h⟩
  have hd : b ∣ m := by rw [← h]; exact dvd_pow_self b (by omega)
  have hbm : b=m := (hm.eq_one_or_self_of_dvd b hd).resolve_left (by omega)
  subst b
  have hlt : m < m^e := by
    simpa using Nat.pow_lt_pow_right (by omega : 1 < m) (by omega : 1 < e)
  omega

lemma order_tests_iff {m s k : ℕ} (hs : s.Prime) (hcop : s.Coprime m) :
    (∀ j : ℕ, 1 ≤ j → j ≤ k → m^j%s ≠ 1) ↔ k < orderOf (m : ZMod s) := by
  let : Fact s.Prime := ⟨hs⟩
  have ho : 0 < orderOf (m : ZMod s) :=
    ((ZMod.isUnit_iff_coprime m s).mpr hcop.symm).isOfFinOrder.orderOf_pos
  have hp (j : ℕ) : m^j%s=1 ↔ (m : ZMod s)^j=1 := by
    constructor
    · intro h
      have : ((m^j%s : ℕ) : ZMod s)=(1 : ZMod s) := by
        simpa only [Nat.cast_one] using congrArg (fun a : ℕ => (a : ZMod s)) h
      simpa only [ZMod.natCast_mod,Nat.cast_pow,Nat.cast_one] using this
    · intro h
      have := congrArg ZMod.val h
      simpa only [← Nat.cast_pow,ZMod.val_natCast,ZMod.val_one] using this
  constructor
  · intro h
    by_contra hn
    exact h _ ho (by omega) ((hp _).mpr (pow_orderOf_eq_one (m : ZMod s)))
  · intro h j hj hk hh
    exact pow_ne_one_of_lt_orderOf (by omega) (hk.trans_lt h) ((hp j).mp hh)

lemma prime_of_no_small_divisor {m B : ℕ} (hm : 2 ≤ m) (hb : m ≤ B)
    (h : ∀ d : ℕ, 2 ≤ d → d ≤ B → d < m → ¬ d ∣ m) : m.Prime := by
  rw [Nat.prime_def_lt]
  refine ⟨hm,?_⟩
  intro d hd hdm
  by_contra hne
  have hd2 : 2 ≤ d := by
    by_contra hn
    have : d=0 := by omega
    subst d
    simp only [Nat.zero_dvd] at hdm
    omega
  exact h d hd2 (by omega) hd hdm

end ExactQuantumFactoring.Primality


end

end OAI
