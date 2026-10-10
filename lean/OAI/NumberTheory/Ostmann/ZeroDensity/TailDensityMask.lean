import OAI.NumberTheory.Ostmann.Preliminaries.TailStability
import OAI.NumberTheory.Ostmann.Preliminaries.SummandTails

namespace OAI

/-! # Actual residue masks for the positive endpoint tail -/

namespace Ostmann

open scoped Classical

noncomputable def tailDensityMask (A : Set ℕ) (N p : ℕ) : Finset (ZMod p) :=
  (tailSupport A N p).image fun r : ℕ => (r : ZMod p)

theorem tailDensityMask_card (A : Set ℕ) (N p : ℕ) :
    (tailDensityMask A N p).card = (tailSupport A N p).card := by
  apply Finset.card_image_of_injOn
  intro r hr s hs he
  have hrp := Finset.mem_range.mp (tailSupport_subset A N p hr)
  have hsp := Finset.mem_range.mp (tailSupport_subset A N p hs)
  have hmod := (ZMod.natCast_eq_natCast_iff' r s p).mp he
  simpa only [Nat.mod_eq_of_lt hrp, Nat.mod_eq_of_lt hsp] using hmod

theorem positiveSummandTail_mem_mask (A : Set ℕ) (N lo hi p : ℕ) (hp : 0 < p)
    (hlo : N + p ≤ lo) {x : ℤ} (hx : x ∈ positiveSummandTail A lo hi) :
    (x : ZMod p) ∈ tailDensityMask A N p := by
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨haA, halo, _⟩ := (mem_summandTail A lo hi a).mp ha
  apply Finset.mem_image.mpr
  refine ⟨a % p, mod_mem_tailSupport hp haA (lt_of_le_of_lt hlo halo), ?_⟩
  simp

theorem tailDensityMask_density (A : Set ℕ) (N p : ℕ) (hp : 0 < p)
    (hcard : ((tailSupport A N p).card : ℝ) ≤ 2 * p / 3) :
    (tailDensityMask A N p).card / (p : ℝ) ≤ 2 / 3 := by
  rw [tailDensityMask_card]
  apply (div_le_iff₀ (show (0 : ℝ) < p by exact_mod_cast hp)).mpr
  linarith

end Ostmann

end OAI
