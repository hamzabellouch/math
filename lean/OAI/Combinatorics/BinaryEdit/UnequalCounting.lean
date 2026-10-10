import OAI.Combinatorics.BinaryEdit.MatchingSpanBudget

namespace OAI

namespace TreeEdit.BinaryLower.Code

/-- Sum the local large-pair charge, allowing a threshold-sized error for
every visited block pair.  Small pairs need no separation hypothesis. -/
theorem sum_counts_le_of_large_charge {β : Type*} (s : Finset β)
    (a g : β → ℕ) (a₀ : ℕ)
    (hlarge : ∀ b ∈ s, a₀ ≤ a b → a b ≤ 100 * g b) :
    (∑ b ∈ s, a b) ≤ 100 * (∑ b ∈ s, g b) + s.card * a₀ := by
  have hlocal : ∀ b ∈ s, a b ≤ 100 * g b + a₀ := by
    intro b hb
    by_cases h : a₀ ≤ a b
    · exact (hlarge b hb h).trans (Nat.le_add_right _ _)
    · omega
  calc
    (∑ b ∈ s, a b) ≤ ∑ b ∈ s, (100 * g b + a₀) := Finset.sum_le_sum hlocal
    _ = 100 * (∑ b ∈ s, g b) + s.card * a₀ := by
      simp [Finset.sum_add_distrib, Finset.mul_sum]

/-- The unequal-label count estimate once the actual segment separation has
been applied to each large block pair. All gap terms here are the concrete
interval-span losses, rather than arbitrary charged weights. -/
theorem block_pair_bad_count_le {r M P : ℕ} (hP : 0 < P)
    (f g : Fin r → Fin (M * P)) (hf : StrictMono f) (hg : StrictMono g)
    (bad : ℕ × ℕ → Prop) [DecidablePred bad] (a₀ : ℕ)
    (hlarge : ∀ b ∈ (Finset.univ.image (fun i => ((f i).val / P, (g i).val / P))).filter bad,
      a₀ ≤ (Finset.univ.filter (fun i => ((f i).val / P, (g i).val / P) = b)).card →
      (Finset.univ.filter (fun i => ((f i).val / P, (g i).val / P) = b)).card ≤
        100 * (((matchingSpan f (fun i => ((f i).val / P, (g i).val / P)) b).card -
          (Finset.univ.filter (fun i => ((f i).val / P, (g i).val / P) = b)).card) +
          ((matchingSpan g (fun i => ((f i).val / P, (g i).val / P)) b).card -
          (Finset.univ.filter (fun i => ((f i).val / P, (g i).val / P) = b)).card))) :
    (Finset.univ.filter (fun i => bad ((f i).val / P, (g i).val / P))).card ≤
      200 * (M * P - r) + 2 * M * a₀ := by
  classical
  let label := fun i => ((f i).val / P, (g i).val / P)
  let pairs := (Finset.univ.image label).filter bad
  let a := fun b => (Finset.univ.filter (fun i => label i = b)).card
  let gap := fun b => ((matchingSpan f label b).card - a b) +
      ((matchingSpan g label b).card - a b)
  have hsum := sum_counts_le_of_large_charge pairs a gap a₀ hlarge
  have hgap := block_pair_two_sided_gap_budget P f g hf hg pairs
  have hpair : pairs.card ≤ 2 * M := by
    have h := card_equal_block_pair_image_le hP (fun i => (f i).val)
      (fun i => (g i).val) hf.monotone hg.monotone
      (fun i => (f i).isLt) (fun i => (g i).isLt)
    exact (Finset.card_le_card (Finset.filter_subset _ _)).trans (h.trans (Nat.sub_le _ _))
  have hcount : (∑ b ∈ pairs, a b) =
      (Finset.univ.filter (fun i => bad (label i))).card := by
    rw [show (∑ b ∈ pairs, a b) =
        ∑ b ∈ pairs, (Finset.univ.filter (fun i => label i = b)).card from rfl]
    rw [Finset.sum_card_fiberwise_eq_card_filter]
    apply congrArg Finset.card
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, pairs]
    constructor
    · exact fun h => h.2
    · intro h
      exact ⟨Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩, h⟩
  rw [hcount] at hsum
  change (Finset.univ.filter (fun i => bad (label i))).card ≤ _
  dsimp only [gap, a] at hsum
  dsimp only at hgap
  nlinarith

end TreeEdit.BinaryLower.Code

end OAI
