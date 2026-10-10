import OAI.NumberTheory.Jacobsthal.Sieve.ResidueCountDifference

namespace OAI

namespace Erdos970

section

namespace ErdosStoppedArithmetic
open NumberTheoryLean ErdosInverseCounts ErdosInverseHits ErdosModulusRelative

theorem original_individual_upper :
    ∃ C : ℝ,0 < C ∧ ∃ P0 : ℕ,2 ≤ P0 ∧ ∀ P : ℕ,P0 ≤ P →
      ∀ (Y d : ℕ) (a : ℕ → ℕ),0 < Y → Squarefree d →
        (∀ t ∈ d.primeFactors,P ≤ t) → (P : ℝ)^2 ≤ (Y : ℝ)/(d : ℝ) →
        (modulusCount Y (LargePrimeDeletion.cutoffPrimes (P-1)) a d : ℝ) ≤
          C*((Y : ℝ)/(d : ℝ))*SmallSieveFinite.smallEuler (P-1) := by
  obtain ⟨C,hC,u0,hu0,hUpper⟩ := SmallSieveUpper.progression_small_upper 2 (by norm_num)
  refine ⟨C,hC,⌈u0⌉₊+3,by omega,?_⟩
  intro P hP Y d a _hY hd hlarge hJ
  have hd0 : 0 < d := Nat.pos_of_ne_zero hd.ne_zero
  have hP0 : 0 < P := by omega
  have hU : u0 ≤ ((P-1 : ℕ) : ℝ) := by
    exact (Nat.le_ceil u0).trans (by exact_mod_cast (show ⌈u0⌉₊ ≤ P-1 by omega))
  have hUp : ((P-1 : ℕ) : ℝ) < (P : ℝ) := by exact_mod_cast Nat.sub_lt hP0 (by decide : 0 < 1)
  have hU0 : 0 ≤ ((P-1 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hpow : ((P-1 : ℕ) : ℝ)^(2 : ℝ) ≤ (Y : ℝ)/(d : ℝ) := by
    rw [Real.rpow_two]
    exact (pow_le_pow_left₀ hU0 hUp.le 2).trans hJ
  have hcop (t : ℕ) (ht : t.Prime) (htu : (t : ℝ) ≤ ((P-1 : ℕ) : ℝ)) : d.Coprime t := by
    apply large_modulus_coprime_small ((P-1 : ℕ) : ℝ) d hd _ t ht htu
    intro q hq
    exact hUp.trans_le (by exact_mod_cast hlarge q hq)
  have hb := primeHitRepresentative_spec d hd a
  have hN := hitLength_error Y d (primeHitRepresentative d hd a) hd0 hb.1 hb.2.1
  have hh := hUpper (hitLength Y d (primeHitRepresentative d hd a)) ((P-1 : ℕ) : ℝ)
    ((Y : ℝ)/(d : ℝ)) (primeHitRepresentative d hd a : ℤ) d a hU hpow hN hcop
  simp only [Nat.floor_natCast] at hh
  rw [modulus_count_eq_offsets Y _ a d hd,offsets_eq_progression,Int.cast_natCast]
  exact hh

end ErdosStoppedArithmetic

end

end Erdos970

end OAI
