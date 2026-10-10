import Mathlib
import OAI.Computability.QuantumFactoring.PrimalityCorrectness
import OAI.Computability.QuantumFactoring.CyclicAlgebra

namespace OAI

section


namespace ExactQuantumFactoring.Primality

theorem cyclic_large_branch_prime {n m s : ℕ} (hn : 128 ≤ n) (hm : 2 ≤ m) (hmb : m < 2^n)
    [NeZero s] (hs : s.Prime) (hcop : s.Coprime m) (horder : n^2 < orderOf (m : ZMod s))
    (hpow : ¬ PerfectPower m)
    (hsmall : ∀ d : ℕ, 2 ≤ d → d ≤ 8*s → ¬ d ∣ m)
    (htest : ∀ a : ℕ, 1 ≤ a → a ≤ 8*s →
      (cyclicX (R := ZMod m) s+cyclicC s (a : ZMod m))^m=
        cyclicX s^m+cyclicC s (a : ZMod m)) : m.Prime := by
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
    (fun a ha hb => cyclic_test_introspective hs.two_le hpm (htest a ha hb))


end ExactQuantumFactoring.Primality


end

end OAI
