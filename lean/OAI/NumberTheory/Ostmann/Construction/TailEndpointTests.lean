import OAI.NumberTheory.Ostmann.Preliminaries.HarmonicTestTransfer
import OAI.NumberTheory.Ostmann.ZeroDensity.PrimeSumInputs
import OAI.NumberTheory.Ostmann.QuadraticCenter.RootCollisions

namespace OAI

/-! # The endpoint exceptional set for an eventual prime decomposition -/

namespace Ostmann

open scoped BigOperators Classical

theorem uniform_subset_tail_collision_bound {A B : Set ℕ}
    (hA : A.Infinite) (hB : B.Infinite) (N X Q K : ℕ)
    (hX : 1 ≤ X) (hQ : 1 ≤ Q) (hK : 0 < K)
    (hdis : ∀ p ∈ Nat.primesLE Q, Disjoint (tailResidues A N p) (negTailResidues B N p))
    (E D : Finset ℕ) (hE : K ≤ E.card) (hD : K ≤ D.card)
    (hEtail : ∀ a ∈ E, a ∈ A ∧ N + Q < a ∧ a ≤ X)
    (hDtail : ∀ b ∈ D, b ∈ B ∧ N + Q < b ∧ b ≤ X)
    (C : ℝ) (hM : MertensLowerBound C) :
    (∑ p ∈ Nat.primesLE Q, Real.log (p : ℝ) * tailCollisionDefect A N p E D
      (fun _ => 1 / (E.card : ℝ)) (fun _ => 1 / (D.card : ℝ))) ≤
      2 * Real.log X - 4 * Real.log Q + 4 * C + 2 * (1 / (K : ℝ)) * Real.log 4 * Q := by
  have hEne : E.Nonempty := Finset.card_pos.mp (hK.trans_le hE)
  have hDne : D.Nonempty := Finset.card_pos.mp (hK.trans_le hD)
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  apply finite_measure_collision_stability (Nat.primesLE Q) E D
    (fun _ => 1 / (E.card : ℝ)) (fun _ => 1 / (D.card : ℝ))
    (tailSupport A N) (fun p => Finset.range p \ tailSupport A N p)
    (fun p a => a % p) negativeResidue X Q (1 / (K : ℝ)) (Real.log 4) C hX
    (fun p hp => Nat.prime_of_mem_primesLE hp)
    (fun a ha => (hEtail a ha).2.2) (fun b hb => (hDtail b hb).2.2)
    (by intros; positivity) (by intros; positivity)
    (sum_uniform_mass E hEne) (sum_uniform_mass D hDne)
    (fun _ _ => one_div_le_one_div_of_le hKr (by exact_mod_cast hE))
    (fun _ _ => one_div_le_one_div_of_le hKr (by exact_mod_cast hD))
    (fun p hp => tailSupport_nonempty hA N p (Nat.prime_of_mem_primesLE hp).pos)
    (fun p hp => tailSupport_complement_nonempty hB (Nat.prime_of_mem_primesLE hp).pos (hdis p hp))
  · intro p hp a ha
    apply mod_mem_tailSupport (Nat.prime_of_mem_primesLE hp).pos (hEtail a ha).1
    have := Nat.le_of_mem_primesLE hp
    have := (hEtail a ha).2.1
    omega
  · intro p hp b hb
    apply negativeResidue_mem_complement (Nat.prime_of_mem_primesLE hp).pos (hdis p hp) (hDtail b hb).1
    have := Nat.le_of_mem_primesLE hp
    have := (hDtail b hb).2.1
    omega
  · intros; rfl
  · intro p hp a ha b hb
    exact negativeResidue_eq_iff (Nat.prime_of_mem_primesLE hp).pos
  · positivity
  · exact prime_log_weight_le Q
  · exact hM Q hQ

theorem few_bad_tail_endpoints {A B : Set ℕ} (hA : A.Infinite) (hB : B.Infinite)
    (N X Q K : ℕ) (hX : 1 ≤ X) (hQ : 1 ≤ Q) (hK : 0 < K)
    (hdis : ∀ p ∈ Nat.primesLE Q, Disjoint (tailResidues A N p) (negTailResidues B N p))
    (E D P : Finset ℕ) (hD : K ≤ D.card)
    (hEtail : ∀ a ∈ E, a ∈ A ∧ N + Q < a ∧ a ≤ X)
    (hDtail : ∀ b ∈ D, b ∈ B ∧ N + Q < b ∧ b ≤ X)
    (hP : P ⊆ Nat.primesLE Q) (b δ C : ℝ) (hb : 0 < b) (hδ : 0 < δ)
    (hM : MertensLowerBound C) (hlog : ∀ p ∈ P, b ≤ Real.log (p : ℝ))
    (F : ℕ → ℕ → ℝ) (hF : ∀ p ∈ P, ∀ r ∈ tailSupport A N p, |F p r| ≤ 1)
    (hmass : 0 < ∑ p ∈ P, (p : ℝ)⁻¹)
    (href : δ * (∑ p ∈ P, (p : ℝ)⁻¹) ≤
      ∑ p ∈ P, (p : ℝ)⁻¹ * residueTestMean (tailSupport A N p) (F p))
    (hsmall : 4 * ((2 * Real.log X - 4 * Real.log Q + 4 * C +
      2 * (1 / (K : ℝ)) * Real.log 4 * Q) / b) < δ ^ 2 * ∑ p ∈ P, (p : ℝ)⁻¹) :
    (badEndpoints E P (fun p => (p : ℝ)⁻¹) (fun a p => F p (a % p)) δ).card < K := by
  apply badEndpoints_card_lt E P (fun p => (p : ℝ)⁻¹)
    (fun p => residueTestMean (tailSupport A N p) (F p)) (fun a p => F p (a % p)) δ _ K hK hδ
    (by intros; positivity) hmass href hsmall
  intro E' hE'E hE'
  have hEtail' : ∀ a ∈ E', a ∈ A ∧ N + Q < a ∧ a ≤ X := fun a ha => hEtail a (hE'E ha)
  have hbudget := uniform_subset_tail_collision_bound hA hB N X Q K hX hQ hK hdis
    E' D hE' hD hEtail' hDtail C hM
  have herr := harmonic_collision_test_errors P (Nat.primesLE Q) hP
    (tailSupport A N) (fun p => Finset.range p \ tailSupport A N p)
    (fun p => residueMass E' (fun _ => 1 / (E'.card : ℝ)) p)
    (fun p => fiberMass D (fun _ => 1 / (D.card : ℝ)) (negativeResidue p)) F b _ hb
    (fun p hp => Nat.prime_of_mem_primesLE hp)
    (fun p hp => tailSupport_nonempty hA N p (Nat.prime_of_mem_primesLE hp).pos)
    (fun p hp => tailSupport_complement_nonempty hB (Nat.prime_of_mem_primesLE hp).pos (hdis p hp))
    (fun p _ => (tailSupport_card_add_complement A N p).le) hF hlog hbudget
  apply le_trans (le_of_eq ?_) herr
  apply Finset.sum_congr rfl
  intro p hp
  congr 2
  symm
  apply uniform_fiber_test_error
  intro a ha
  apply mod_mem_tailSupport (Nat.prime_of_mem_primesLE (hP hp)).pos (hEtail' a ha).1
  have := Nat.le_of_mem_primesLE (hP hp)
  have := (hEtail' a ha).2.1
  omega

end Ostmann

end OAI
