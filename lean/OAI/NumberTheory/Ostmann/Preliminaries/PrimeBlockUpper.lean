import OAI.NumberTheory.Ostmann.Preliminaries.DivisorCollision
import OAI.NumberTheory.Ostmann.Preliminaries.PrimeBlockResidues

namespace OAI

namespace Ostmann.Preliminaries
open scoped BigOperators

theorem residue_inverse_le_uniform_collision (S : Set ℕ) (U : Finset ℕ)
    (hU : U.Nonempty) (hsubset : ∀ a ∈ U, a ∈ S) (p : ℕ) [NeZero p] :
    (allResidueCount S p : ℝ)⁻¹ ≤ congruenceCollisionEnergy p
      (fun a : U => a.val) (fun _ => (U.card : ℝ)⁻¹) := by
  classical
  have hR : (allResidues S p).Nonempty := by
    obtain ⟨a, ha⟩ := hU
    exact ⟨(a : ZMod p), (mem_allResidues S p _).mpr ⟨a, hsubset a ha, rfl⟩⟩
  have hsupp : ∀ r ∉ allResidues S p, uniformResidueMass U p r = 0 := by
    intro r hr
    exact projectedMass_eq_zero _ _ _ (fun a _ =>
      (mem_allResidues S p _).mpr ⟨a.val, hsubset a.val a.property, rfl⟩) hr
  have h := uniformDefect_nonneg (allResidues S p) (uniformResidueMass U p)
  rw [uniformDefect_eq_energy_sub _ hR _ (uniformResidueMass_sum U hU p) hsupp,
    ← allResidueCount_eq_card] at h
  rw [congruenceCollisionEnergy_eq_projected]
  change (allResidueCount S p : ℝ)⁻¹ ≤ massEnergy (uniformResidueMass U p)
  linarith

theorem residueReciprocalSum_le (S : Set ℕ) (Q Y : ℕ) (hY : 1 ≤ Y)
    (hcount : 0 < countUpTo S Y) :
    residueReciprocalSum S Q ≤
      Real.log Y + Real.log 4 * Q / countUpTo S Y := by
  classical
  let U := elementsUpTo S Y
  have hcard : 0 < U.card := hcount
  have hU : U.Nonempty := Finset.card_pos.mp hcard
  have hc : (U.card : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hcard
  have hmass : (∑ _a : U, (U.card : ℝ)⁻¹) = 1 := by simp [hc]
  have hbound (a : U) : a.val ≤ Y := (mem_elementsUpTo.mp a.property).2
  have hsubset : ∀ a ∈ U, a ∈ S := fun a ha => (mem_elementsUpTo.mp ha).1
  have hupper := weighted_prime_collision_energy_le Q Y (fun a : U => a.val)
    (fun _ => (U.card : ℝ)⁻¹) hY Subtype.val_injective hbound
    (by intro a; positivity) hmass (fun _ => le_rfl)
  calc
    residueReciprocalSum S Q ≤
        ∑ p ∈ Q.primesLE, Real.log p * congruenceCollisionEnergy p
          (fun a : U => a.val) (fun _ => (U.card : ℝ)⁻¹) := by
      apply Finset.sum_le_sum
      intro p hp
      have : NeZero p := ⟨(Nat.mem_primesLE.mp hp).2.ne_zero⟩
      exact mul_le_mul_of_nonneg_left
        (residue_inverse_le_uniform_collision S U hU hsubset p)
        (Real.log_nonneg (by exact_mod_cast (Nat.mem_primesLE.mp hp).2.one_le))
    _ ≤ Real.log Y + Real.log 4 * Q * (U.card : ℝ)⁻¹ := hupper
    _ = _ := by rfl

end Ostmann.Preliminaries

end OAI
