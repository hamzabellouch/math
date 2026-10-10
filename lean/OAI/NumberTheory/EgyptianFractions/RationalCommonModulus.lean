import Mathlib

namespace OAI
noncomputable section

open scoped BigOperators

namespace Problem337

/-- Finitely many rational points of the unit interval have a common positive
    modulus, which can be chosen arbitrarily large. -/
theorem exists_large_common_rational_modulus {Ω : Type*} [Fintype Ω]
    (x : Ω → ℚ) (hx0 : ∀ ω, 0 ≤ x ω) (hx1 : ∀ ω, x ω < 1) (B : ℕ) :
    ∃ q : ℕ, B ≤ q ∧ 0 < q ∧ ∃ a : Ω → ℕ,
      ∀ ω, a ω < q ∧ (a ω : ℚ) / (q : ℚ) = x ω := by
  classical
  let D : ℕ := ∏ ω : Ω, (x ω).den
  let q : ℕ := D * (B + 1)
  have hD : 0 < D := by
    exact Finset.prod_pos (fun ω _ => (x ω).den_pos)
  have hq : 0 < q := Nat.mul_pos hD (by omega)
  have hB : B ≤ q := by
    dsimp [q]
    have : 1 ≤ D := hD
    nlinarith
  have hdq (ω : Ω) : (x ω).den ∣ q := by
    apply dvd_mul_of_dvd_left
    exact Finset.dvd_prod_of_mem (fun ω : Ω => (x ω).den) (Finset.mem_univ ω)
  let a : Ω → ℕ := fun ω => (x ω).num.toNat * (q / (x ω).den)
  have hqQ : (0 : ℚ) < q := by exact_mod_cast hq
  have heq (ω : Ω) : (a ω : ℚ) / (q : ℚ) = x ω := by
    have hnum : ((x ω).num.toNat : ℚ) = ((x ω).num : ℚ) := by
      exact_mod_cast Int.toNat_of_nonneg (Rat.num_nonneg.mpr (hx0 ω))
    apply (div_eq_iff hqQ.ne').mpr
    calc
      (a ω : ℚ) = ((x ω).num : ℚ) / ((x ω).den : ℚ) * (q : ℚ) := by
        dsimp [a]
        rw [Nat.cast_mul, Nat.cast_div (hdq ω) (by exact_mod_cast (x ω).den_ne_zero), hnum]
        ring
      _ = x ω * (q : ℚ) := by rw [Rat.num_div_den]
  refine ⟨q, hB, hq, a, ?_⟩
  intro ω
  refine ⟨?_, heq ω⟩
  have hlt : (a ω : ℚ) < (q : ℚ) :=
    (div_lt_one hqQ).mp (by rw [heq]; exact hx1 ω)
  exact_mod_cast hlt

/-- A finite rational unit-interval family embeds in a cyclic group of an
    arbitrarily large order with its exact least-residue fractions preserved. -/
theorem exists_large_common_zmod {Ω : Type*} [Fintype Ω]
    (x : Ω → ℚ) (hx0 : ∀ ω, 0 ≤ x ω) (hx1 : ∀ ω, x ω < 1) (B : ℕ) :
    ∃ q : ℕ, B ≤ q ∧ 0 < q ∧ ∃ y : Ω → ZMod q,
      ∀ ω, ((y ω).val : ℚ) / (q : ℚ) = x ω := by
  obtain ⟨q, hB, hq, a, ha⟩ := exists_large_common_rational_modulus x hx0 hx1 B
  refine ⟨q, hB, hq, (fun ω => (a ω : ZMod q)), ?_⟩
  intro ω
  rw [ZMod.val_natCast_of_lt (ha ω).1]
  exact (ha ω).2

end Problem337

end

end OAI
