import OAI.NumberTheory.Ostmann.Preliminaries.PrimeBlockCauchy
import OAI.NumberTheory.Ostmann.Preliminaries.PrimeBlockFrequencies
import OAI.NumberTheory.Ostmann.Preliminaries.PrimeBlockResidues

namespace OAI

namespace Ostmann.Preliminaries
open scoped BigOperators
open Filter

theorem actual_residue_density_sum_le (d : Decomposition) (U : Finset ℕ) (Q : ℕ)
    (hU : U.Nonempty) (hQ : 0 < Q)
    (hA : ∀ a ∈ U, a ∈ d.A)
    (hlarge : ∀ a ∈ U, Q + d.cutoff < a)
    (hbound : ∀ a ∈ U, a ≤ Q ^ 2) :
    (∑ p ∈ Q.primesLE, (allResidueCount d.B p : ℝ) / p) ≤
      96 * (Q : ℝ) ^ 2 / U.card := by
  classical
  calc
    (∑ p ∈ Q.primesLE, (allResidueCount d.B p : ℝ) / p) =
        ∑ p : ↥(Q.primesLE), (allResidueCount d.B p.val : ℝ) / p.val :=
      (Finset.sum_coe_sort _ _).symm
    _ ≤ ∑ p : ↥(Q.primesLE), ∑ a : {a : ZMod p.val // a ≠ 0},
        ‖Ostmann.normalizedExpSum U ((a.val.val : ℝ) / p.val)‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro p hp
      have h := actual_prime_nonzero_energy_lower d U hU p.val
        (Nat.mem_primesLE.mp p.property).2 hA
        (fun a ha => lt_of_le_of_lt (Nat.add_le_add_right
          (Nat.mem_primesLE.mp p.property).1 _) (hlarge a ha))
      rw [Finset.sum_subtype (p := fun a : ZMod p.val => a ≠ 0)
        ((Finset.univ : Finset (ZMod p.val)).erase 0)
        (by intro a; simp)] at h
      exact h
    _ = ∑ f : PrimeBlockFrequency Q,
        ‖Ostmann.normalizedExpSum U ((f.2.val.val : ℝ) / f.1.val)‖ ^ 2 := by
      unfold PrimeBlockFrequency
      rw [Fintype.sum_sigma]
    _ ≤ _ := primeBlock_frequency_energy_le U Q hbound hQ

theorem primeBlock_lower_algebra {q l m c π S H : ℝ}
    (hq : 0 < q) (hl : 0 < l) (hm : 0 < m) (hc : 0 ≤ c)
    (hπ : c * q / l ≤ π) (hH : 0 ≤ H)
    (hcs : (l / q) * π ^ 2 ≤ S * H)
    (hS : S ≤ 96 * q ^ 2 / m) :
    c ^ 2 * m / (96 * q * l) ≤ H := by
  have hlo : 0 ≤ c * q / l := div_nonneg (mul_nonneg hc hq.le) hl.le
  have hsquare := pow_le_pow_left₀ hlo hπ 2
  have hmain : (l / q) * (c * q / l) ^ 2 ≤ (96 * q ^ 2 / m) * H :=
    (mul_le_mul_of_nonneg_left hsquare (div_nonneg hl.le hq.le)).trans
      (hcs.trans (mul_le_mul_of_nonneg_right hS hH))
  have hden : 0 < 96 * q ^ 2 / m := by positivity
  calc
    c ^ 2 * m / (96 * q * l) =
        ((l / q) * (c * q / l) ^ 2) / (96 * q ^ 2 / m) := by
      field_simp
    _ ≤ H := (div_le_iff₀ hden).mpr (by simpa [mul_comm] using hmain)

theorem eventually_actual_residue_H_lower (d : Decomposition) :
    ∀ᶠ Q : ℕ in atTop, ∀ U : Finset ℕ, U.Nonempty →
      (∀ a ∈ U, a ∈ d.A) → (∀ a ∈ U, Q + d.cutoff < a) →
      (∀ a ∈ U, a ≤ Q ^ 2) →
      (Real.log 2 / 2) ^ 2 * U.card / (96 * Q * Real.log Q) ≤
        residueReciprocalSum d.B Q := by
  filter_upwards [eventually_primeCounting_lower, eventually_ge_atTop 4] with Q hπ hQ
  intro U hU hA hlarge hbound
  have hQpos : 0 < Q := by omega
  have hν : ∀ p ∈ Q.primesLE, 0 < (allResidueCount d.B p : ℝ) := by
    intro p hp
    have : NeZero p := ⟨(Nat.mem_primesLE.mp hp).2.ne_zero⟩
    exact_mod_cast allResidueCount_pos d.B d.infinite_B.nonempty p
  apply primeBlock_lower_algebra
    (by exact_mod_cast hQpos)
    (Real.log_pos (by exact_mod_cast (show 1 < Q by omega)))
    (by exact_mod_cast hU.card_pos)
    (by positivity : (0 : ℝ) ≤ Real.log 2 / 2) hπ
  · exact Finset.sum_nonneg (fun p hp => div_nonneg
      (Real.log_nonneg (by exact_mod_cast (Nat.mem_primesLE.mp hp).2.one_le))
      (hν p hp).le)
  · exact primeBlock_weighted_cauchy Q (fun p => (allResidueCount d.B p : ℝ)) hQ hν
  · exact actual_residue_density_sum_le d U Q hU hQpos hA hlarge hbound

end Ostmann.Preliminaries

end OAI
