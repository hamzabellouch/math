import OAI.NumberTheory.Ostmann.QuadraticCenter.RootCollisions
import OAI.NumberTheory.Ostmann.Preliminaries.SummandTails

namespace OAI

/-! # The larger-sieve bound for the full residue support of a summand

The support is taken from the entire infinite summand, even when the probability
measure is supported on one finite prefix. This is the upper bound for H in
manuscript Lemma 2.4 and Elsholtz's summand-size argument.
-/

namespace Ostmann

open scoped BigOperators Classical

noncomputable def occupiedResidues (A : Set ℕ) (p : ℕ) : Finset ℕ :=
  (Finset.range p).filter fun r => ∃ a ∈ A, a % p = r

 theorem mem_occupiedResidues {A : Set ℕ} {p r : ℕ} :
    r ∈ occupiedResidues A p ↔ r < p ∧ ∃ a ∈ A, a % p = r := by
  classical
  simp only [occupiedResidues, Finset.mem_filter, Finset.mem_range]

 theorem occupiedResidues_nonempty {A : Set ℕ} (hA : A.Nonempty) {p : ℕ}
    (hp : 0 < p) : (occupiedResidues A p).Nonempty := by
  obtain ⟨a, ha⟩ := hA
  exact ⟨a % p, mem_occupiedResidues.mpr ⟨Nat.mod_lt a hp, a, ha, rfl⟩⟩

 theorem uniformResidueCollision_support_lower (A : Set ℕ) (s : Finset ℕ)
    (hs : s.Nonempty) (hsA : ∀ a ∈ s, a ∈ A) {p : ℕ} (hp : 0 < p) :
    1 / ((occupiedResidues A p).card : ℝ) ≤ uniformResidueCollision s p := by
  classical
  have hA : A.Nonempty := by obtain ⟨a, ha⟩ := hs; exact ⟨a, hsA a ha⟩
  have hmap : ∀ a ∈ s, a % p ∈ occupiedResidues A p := by
    intro a ha
    exact mem_occupiedResidues.mpr ⟨Nat.mod_lt a hp, a, hsA a ha, rfl⟩
  have hmass : (∑ r ∈ occupiedResidues A p,
      fiberMass s (fun _ => 1 / (s.card : ℝ)) (fun a => a % p) r) = 1 := by
    rw [sum_fiberMass s (occupiedResidues A p) _ _ hmap]
    exact sum_uniform_mass s hs
  have h := inverse_card_le_collision (occupiedResidues A p) _
    (occupiedResidues_nonempty hA hp) hmass
  rw [fiberMass_sq_eq_residueMass_sq s (occupiedResidues A p) _ _ hp hmap
    (fun _ _ _ _ => Iff.rfl)] at h
  exact h

 theorem occupiedResidues_reciprocal_bound (A : Set ℕ) (s P : Finset ℕ)
    (hs : s.Nonempty) (hsA : ∀ a ∈ s, a ∈ A) (Y : ℕ) (hY : 1 ≤ Y)
    (hbound : ∀ a ∈ s, a ≤ Y) (hP : ∀ p ∈ P, p.Prime) :
    (∑ p ∈ P, Real.log (p : ℝ) / ((occupiedResidues A p).card : ℝ)) ≤
      Real.log (Y : ℝ) + (1 / (s.card : ℝ)) * ∑ p ∈ P, Real.log (p : ℝ) := by
  have hdiam : ∀ a ∈ s, ∀ b ∈ s, Nat.dist a b ≤ Y := by
    intro a ha b hb
    rcases le_total a b with hab | hba
    · rw [Nat.dist_eq_sub_of_le hab]
      exact (Nat.sub_le b a).trans (hbound b hb)
    · rw [Nat.dist_eq_sub_of_le_right hba]
      exact (Nat.sub_le a b).trans (hbound a ha)
  have hupper := uniformResidueCollision_upper P s hs Y hY hP hdiam
  apply le_trans _ hupper
  apply Finset.sum_le_sum
  intro p hp
  rw [div_eq_mul_one_div]
  exact mul_le_mul_of_nonneg_left
    (uniformResidueCollision_support_lower A s hs hsA (hP p hp).pos)
    (Real.log_nonneg (by exact_mod_cast (hP p hp).one_le))

 theorem summandPrefix_occupied_bound (A : Set ℕ) (P : Finset ℕ) (Y : ℕ)
    (hY : 1 ≤ Y) (hs : (summandPrefix A Y).Nonempty) (hP : ∀ p ∈ P, p.Prime) :
    (∑ p ∈ P, Real.log (p : ℝ) / ((occupiedResidues A p).card : ℝ)) ≤
      Real.log (Y : ℝ) + (1 / ((summandPrefix A Y).card : ℝ)) *
        ∑ p ∈ P, Real.log (p : ℝ) :=
  occupiedResidues_reciprocal_bound A (summandPrefix A Y) P hs
    (fun a ha => (mem_summandPrefix A Y a).mp ha |>.1) Y hY
    (fun a ha => (mem_summandPrefix A Y a).mp ha |>.2) hP

end Ostmann

end OAI
