import Mathlib

namespace OAI

open scoped BigOperators

namespace PiExponent

theorem positive_rational_weights_common_denominator {d : ℕ}
    (ρ : Fin d → ℚ) (hρ : ∀ i, 0 < ρ i) :
    ∃ D : ℕ, 0 < D ∧ ∃ w : Fin d → ℕ,
      (∀ i, 0 < w i) ∧ ∀ i, (ρ i : ℝ) = (w i : ℝ) / (D : ℝ) := by
  classical
  let D : ℕ := ∏ i, (ρ i).den
  have hD : 0 < D := Finset.prod_pos (fun i _ => (ρ i).den_pos)
  have hd : ∀ i, (ρ i).den ∣ D :=
    fun i => Finset.dvd_prod_of_mem (fun j => (ρ j).den) (Finset.mem_univ i)
  choose k hk using hd
  have hkpos : ∀ i, 0 < k i := by
    intro i
    by_contra h
    have hkzero : k i = 0 := by omega
    have := hk i
    rw [hkzero, mul_zero] at this
    omega
  let w : Fin d → ℕ := fun i => (ρ i).num.toNat * k i
  refine ⟨D, hD, w, ?_, ?_⟩
  · intro i
    have hn : 0 < (ρ i).num := Rat.num_pos.mpr (hρ i)
    exact Nat.mul_pos (by omega) (hkpos i)
  · intro i
    have hnum : (((ρ i).num.toNat : ℕ) : ℝ) = ((ρ i).num : ℝ) := by
      exact_mod_cast (Int.toNat_of_nonneg (Rat.num_pos.mpr (hρ i)).le)
    have hcastD : (D : ℝ) = ((ρ i).den : ℝ) * (k i : ℝ) := by
      exact_mod_cast hk i
    have hkne : (k i : ℝ) ≠ 0 := by exact_mod_cast (hkpos i).ne'
    have hdenne : ((ρ i).den : ℝ) ≠ 0 := by exact_mod_cast (ρ i).den_ne_zero
    rw [Rat.cast_def, hcastD]
    change ((ρ i).num : ℝ) / ((ρ i).den : ℝ) =
      (((ρ i).num.toNat * k i : ℕ) : ℝ) / (((ρ i).den : ℝ) * (k i : ℝ))
    rw [Nat.cast_mul, hnum]
    field_simp

end PiExponent

end OAI
