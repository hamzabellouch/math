import OAI.NumberTheory.Ostmann.Preliminaries.PrimeBlockFourier

namespace OAI

namespace Ostmann.Preliminaries
open scoped BigOperators

instance primeLE_neZero {Q : ℕ} (p : ↥(Q.primesLE)) : NeZero p.val :=
  ⟨(Nat.mem_primesLE.mp p.property).2.ne_zero⟩

def PrimeBlockFrequency (Q : ℕ) := Σ p : ↥(Q.primesLE), {a : ZMod p.val // a ≠ 0}

noncomputable instance (Q : ℕ) : Fintype (PrimeBlockFrequency Q) := by
  classical
  unfold PrimeBlockFrequency
  infer_instance

namespace PrimeBlockFrequency

noncomputable def toReduced {Q : ℕ} (f : PrimeBlockFrequency Q) :
    Ostmann.SharpSieve.ReducedFrequency Q := by
  refine ⟨(f.1.val, f.2.val.val), (Nat.mem_primesLE.mp f.1.property).2.pos,
    (Nat.mem_primesLE.mp f.1.property).1, f.2.val.val_lt, ?_⟩
  apply Nat.Coprime.symm
  apply (Nat.mem_primesLE.mp f.1.property).2.coprime_iff_not_dvd.mpr
  apply Nat.not_dvd_of_pos_of_lt
  · exact Nat.pos_of_ne_zero (fun h => f.2.property ((ZMod.val_eq_zero f.2.val).mp h))
  · exact f.2.val.val_lt

theorem toReduced_injective {Q : ℕ} :
    Function.Injective (@toReduced Q) := by
  rintro ⟨p, a⟩ ⟨q, b⟩ h
  have hpq : p = q := Subtype.ext (congrArg (fun f => f.val.1) h)
  subst q
  have hab : a = b := Subtype.ext (ZMod.val_injective p.val (congrArg (fun f => f.val.2) h))
  subst b
  rfl

@[simp] theorem toReduced_value {Q : ℕ} (f : PrimeBlockFrequency Q) :
    f.toReduced.value = (f.2.val.val : ℝ) / f.1.val := rfl

end PrimeBlockFrequency

theorem primeBlock_frequency_energy_le (U : Finset ℕ) (Q : ℕ)
    (hU : ∀ n ∈ U, n ≤ Q ^ 2) (hQ : 0 < Q) :
    (∑ f : PrimeBlockFrequency Q,
      ‖Ostmann.normalizedExpSum U ((f.2.val.val : ℝ) / f.1.val)‖ ^ 2) ≤
      96 * (Q : ℝ) ^ 2 / U.card := by
  classical
  let e : PrimeBlockFrequency Q ↪ Ostmann.SharpSieve.ReducedFrequency Q :=
    ⟨PrimeBlockFrequency.toReduced, PrimeBlockFrequency.toReduced_injective⟩
  calc
    (∑ f : PrimeBlockFrequency Q,
      ‖Ostmann.normalizedExpSum U ((f.2.val.val : ℝ) / f.1.val)‖ ^ 2) =
      ∑ f ∈ (Finset.univ : Finset (PrimeBlockFrequency Q)).map e,
        ‖Ostmann.normalizedExpSum U f.value‖ ^ 2 := by
      rw [Finset.sum_map]
      rfl
    _ ≤ ∑ f : Ostmann.SharpSieve.ReducedFrequency Q,
        ‖Ostmann.normalizedExpSum U f.value‖ ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun _ _ _ => sq_nonneg _)
    _ ≤ _ := Ostmann.sum_normalizedExpSum_sq_le_of_le_sq U Q hU hQ

end Ostmann.Preliminaries

end OAI
