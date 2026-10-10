import OAI.NumberTheory.Ostmann.Preliminaries.Residues
import OAI.NumberTheory.Ostmann.Preliminaries.Stability

namespace OAI

/-!
# Collision stability on the two summand tails

This specializes the finite collision bound to the complementary supports
forced by an eventual prime decomposition. Prime-sum estimates remain
explicit hypotheses; no statement about the existence of a decomposition
is assumed as an analytic input.
-/

namespace Ostmann

open scoped BigOperators

/-- Natural-number label for the negative residue of a summand element. -/
def negativeResidue (p a : ℕ) : ℕ := (-(a : ZMod p)).val

theorem negativeResidue_eq_iff {p a b : ℕ} (hp : 0 < p) :
    negativeResidue p a = negativeResidue p b ↔ a ≡ b [MOD p] := by
  let : NeZero p := ⟨Nat.ne_of_gt hp⟩
  unfold negativeResidue
  rw [(ZMod.val_injective p).eq_iff, neg_inj, ZMod.natCast_eq_natCast_iff]

/-- All residues of the first summand's infinite tail, labeled in `[0,p)`. -/
noncomputable def tailSupport (A : Set ℕ) (N p : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range p).filter (fun r => (r : ZMod p) ∈ tailResidues A N p)

theorem tailSupport_subset (A : Set ℕ) (N p : ℕ) :
    tailSupport A N p ⊆ Finset.range p := by
  classical
  exact Finset.filter_subset _ _

theorem mod_mem_tailSupport {A : Set ℕ} {N p a : ℕ} (hp : 0 < p)
    (ha : a ∈ A) (hlarge : N + p < a) : a % p ∈ tailSupport A N p := by
  classical
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_range.mpr (Nat.mod_lt a hp), ?_⟩
  have heq : ((a % p : ℕ) : ZMod p) = (a : ZMod p) := by simp
  rw [heq]
  exact ⟨a, ⟨ha, hlarge⟩, rfl⟩

theorem tailSupport_nonempty {A : Set ℕ} (hA : A.Infinite) (N p : ℕ)
    (hp : 0 < p) : (tailSupport A N p).Nonempty := by
  obtain ⟨_, a, ⟨ha, hlarge⟩, rfl⟩ := tailResidues_nonempty hA N p
  exact ⟨a % p, mod_mem_tailSupport hp ha hlarge⟩

theorem negativeResidue_mem_complement {A B : Set ℕ} {N p b : ℕ}
    (hp : 0 < p) (hdisjoint : Disjoint (tailResidues A N p) (negTailResidues B N p))
    (hb : b ∈ B) (hlarge : N + p < b) :
    negativeResidue p b ∈ Finset.range p \ tailSupport A N p := by
  classical
  let : NeZero p := ⟨Nat.ne_of_gt hp⟩
  apply Finset.mem_sdiff.mpr
  refine ⟨Finset.mem_range.mpr (ZMod.val_lt _), ?_⟩
  intro hmem
  have ha := (Finset.mem_filter.mp hmem).2
  change ((-(b : ZMod p)).val : ZMod p) ∈ tailResidues A N p at ha
  rw [ZMod.natCast_zmod_val] at ha
  exact Set.disjoint_left.mp hdisjoint ha ⟨b, ⟨hb, hlarge⟩, rfl⟩

theorem tailSupport_complement_nonempty {A B : Set ℕ} (hB : B.Infinite)
    {N p : ℕ} (hp : 0 < p)
    (hdisjoint : Disjoint (tailResidues A N p) (negTailResidues B N p)) :
    (Finset.range p \ tailSupport A N p).Nonempty := by
  obtain ⟨_, b, ⟨hb, hlarge⟩, rfl⟩ := negTailResidues_nonempty hB N p
  exact ⟨negativeResidue p b, negativeResidue_mem_complement hp hdisjoint hb hlarge⟩

theorem tailSupport_card_add_complement (A : Set ℕ) (N p : ℕ) :
    (tailSupport A N p).card + (Finset.range p \ tailSupport A N p).card = p := by
  rw [Nat.add_comm, Finset.card_sdiff_add_card_eq_card (tailSupport_subset A N p)]
  exact Finset.card_range p

/-- The finite defect for the two summands, with the second one reflected. -/
noncomputable def tailCollisionDefect (A : Set ℕ) (N p : ℕ) (A₀ B₀ : Finset ℕ)
    (μ ν : ℕ → ℝ) : ℝ :=
  collisionDefect p (tailSupport A N p) (Finset.range p \ tailSupport A N p)
    (residueMass A₀ μ p) (fiberMass B₀ ν (negativeResidue p))

/-- The finite quantitative content of Lemma 2.5 for a hypothetical
decomposition. Only the two displayed prime-sum estimates are left as
published numerical inputs; the support and pair-count arguments are proved. -/
theorem EventuallyPrimeSumset.tail_collision_stability {A B : Set ℕ}
    (h : EventuallyPrimeSumset A B) (hA : A.Infinite) (hB : B.Infinite) :
    ∃ N, ∀ (P A₀ B₀ : Finset ℕ) (μ ν : ℕ → ℝ) (X Q : ℕ) (m K C : ℝ),
      1 ≤ X →
      (∀ p ∈ P, p.Prime ∧ p ≤ Q) →
      (∀ a ∈ A₀, a ∈ A ∧ N + Q < a ∧ a ≤ X) →
      (∀ b ∈ B₀, b ∈ B ∧ N + Q < b ∧ b ≤ X) →
      (∀ a ∈ A₀, 0 ≤ μ a) → (∀ b ∈ B₀, 0 ≤ ν b) →
      (∑ a ∈ A₀, μ a) = 1 → (∑ b ∈ B₀, ν b) = 1 →
      (∀ a ∈ A₀, μ a ≤ m) → (∀ b ∈ B₀, ν b ≤ m) →
      0 ≤ m →
      (∑ p ∈ P, Real.log (p : ℝ)) ≤ K * Q →
      Real.log (Q : ℝ) - C ≤ (∑ p ∈ P, Real.log (p : ℝ) / (p : ℝ)) →
      0 ≤ (∑ p ∈ P, Real.log (p : ℝ) * tailCollisionDefect A N p A₀ B₀ μ ν) ∧
      (∑ p ∈ P, Real.log (p : ℝ) * tailCollisionDefect A N p A₀ B₀ μ ν) ≤
        2 * Real.log (X : ℝ) - 4 * Real.log (Q : ℝ) + 4 * C + 2 * m * K * Q := by
  classical
  obtain ⟨N, hN⟩ := h.disjoint_tail_residues
  refine ⟨N, ?_⟩
  intro P A₀ B₀ μ ν X Q m K C hX hP hAtail hBtail hμ hν hmassμ hmassν hatomμ hatomν hm hθ hM
  have hs : ∀ p ∈ P, (tailSupport A N p).Nonempty :=
    fun p hp => tailSupport_nonempty hA N p (hP p hp).1.pos
  have ht : ∀ p ∈ P, (Finset.range p \ tailSupport A N p).Nonempty :=
    fun p hp => tailSupport_complement_nonempty hB (hP p hp).1.pos (hN p (hP p hp).1)
  constructor
  · apply Finset.sum_nonneg
    intro p hp
    apply mul_nonneg
    · exact Real.log_nonneg (by exact_mod_cast (hP p hp).1.one_le)
    · apply collisionDefect_nonneg _ _ _ _ (hs p hp) (ht p hp)
      exact (tailSupport_card_add_complement A N p).le
  · apply finite_measure_collision_stability P A₀ B₀ μ ν
      (tailSupport A N) (fun p => Finset.range p \ tailSupport A N p)
      (fun p a => a % p) negativeResidue X Q m K C hX
      (fun p hp => (hP p hp).1)
      (fun a ha => (hAtail a ha).2.2) (fun b hb => (hBtail b hb).2.2)
      hμ hν hmassμ hmassν hatomμ hatomν hs ht
    · intro p hp a ha
      apply mod_mem_tailSupport (hP p hp).1.pos (hAtail a ha).1
      have := (hP p hp).2
      have := (hAtail a ha).2.1
      omega
    · intro p hp b hb
      apply negativeResidue_mem_complement (hP p hp).1.pos (hN p (hP p hp).1) (hBtail b hb).1
      have := (hP p hp).2
      have := (hBtail b hb).2.1
      omega
    · intro p hp a ha b hb
      rfl
    · intro p hp a ha b hb
      exact negativeResidue_eq_iff (hP p hp).1.pos
    · exact hm
    · exact hθ
    · exact hM

end Ostmann

end OAI
