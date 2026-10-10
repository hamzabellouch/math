import OAI.Analysis.MetricEntropy.SymmetricIndex
import Mathlib.GroupTheory.Perm.DomMulAct
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.Data.Nat.Prime.Factorial
import Mathlib.Data.ZMod.Basic

namespace OAI

/-!
# Multiplicities of symmetric indices

The tuples representing a fixed multiset form a permutation orbit. Its size is
positive and divides the factorial of the number of slots. Consequently the
coefficient multiplicity cannot vanish modulo a prime larger than that number.
-/

namespace MetricEntropyDuality

/-- Number of ordered tuples representing the given multiset. -/
def symFiberCard {r j : ℕ} (s : Sym (Fin r) j) : ℕ :=
  Fintype.card {a : Fin j → Fin r // tupleSym a = s}

/-- Every symmetric index has at least one ordered representative. -/
theorem symFiberCard_pos {r j : ℕ} (s : Sym (Fin r) j) : 0 < symFiberCard s := by
  obtain ⟨a, ha⟩ := tupleSym_surjective r j s
  exact Fintype.card_pos_iff.mpr ⟨⟨a, ha⟩⟩

/-- The actual tuple fiber is a permutation orbit, so its size divides `j!`. -/
theorem symFiberCard_dvd_factorial {r j : ℕ} (s : Sym (Fin r) j) :
    symFiberCard s ∣ j.factorial := by
  classical
  obtain ⟨a, rfl⟩ := tupleSym_surjective r j s
  let G := DomMulAct (Equiv.Perm (Fin j))
  let : Fintype G := Fintype.ofEquiv (Equiv.Perm (Fin j)) DomMulAct.mk
  let eOrbit : {b : Fin j → Fin r // tupleSym b = tupleSym a} ≃ MulAction.orbit G a :=
    Equiv.subtypeEquivRight fun b => by
      rw [eq_comm, tupleSym_eq_iff, MulAction.mem_orbit_iff]
      constructor
      · rintro ⟨σ, hσ⟩
        exact ⟨DomMulAct.mk σ, hσ⟩
      · rintro ⟨σ, hσ⟩
        exact ⟨DomMulAct.mk.symm σ, hσ⟩
  have hg : Fintype.card G = j.factorial := by
    calc
      Fintype.card G = Fintype.card (Equiv.Perm (Fin j)) :=
        Fintype.card_congr DomMulAct.mk.symm
      _ = j.factorial := by rw [Fintype.card_perm, Fintype.card_fin]
  have h := MulAction.card_orbit_mul_card_stabilizer_eq_card_group G a
  rw [← Fintype.card_congr eOrbit, hg] at h
  exact ⟨Fintype.card (MulAction.stabilizer G a), h.symm⟩

/-- No prime larger than the tuple length divides its multiplicity. -/
theorem not_dvd_symFiberCard {r j p : ℕ} (s : Sym (Fin r) j)
    (hp : p.Prime) (hjp : j < p) : ¬ p ∣ symFiberCard s := by
  intro h
  exact (Nat.not_le_of_lt hjp) (hp.dvd_factorial.mp (h.trans (symFiberCard_dvd_factorial s)))

/-- The diagonal coefficient multiplicity is nonzero in the required field. -/
theorem symFiberCard_cast_ne_zero {r j p : ℕ} (s : Sym (Fin r) j)
    (hp : p.Prime) (hjp : j < p) : (symFiberCard s : ZMod p) ≠ 0 := by
  intro h
  exact not_dvd_symFiberCard s hp hjp ((ZMod.natCast_eq_zero_iff _ _).mp h)

end MetricEntropyDuality

end OAI
