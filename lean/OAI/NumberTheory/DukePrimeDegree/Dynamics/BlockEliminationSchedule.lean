import OAI.NumberTheory.DukePrimeDegree.Dynamics.BlockTransverseElimination
import Mathlib.Data.Finset.Max

namespace OAI

/-!
# A full within-block elimination schedule

Upper entries are cleared in increasing row order, and lower entries
in decreasing row order. Transitivity of the block relation ensures
that each affected earlier entry has an earlier zero source entry.
-/

noncomputable section
open Matrix Set Filter
open scoped Topology Classical

namespace DukePrimeDegree
open PrimeDegreePackets

def blockUpperEntries {n : ℕ} (r : Setoid (Fin n)) : Finset (Fin n × Fin n) :=
  Finset.univ.filter (fun p => p.1 < p.2 ∧ r p.1 p.2)

def blockLowerEntries {n : ℕ} (r : Setoid (Fin n)) : Finset (Fin n × Fin n) :=
  Finset.univ.filter (fun p => p.2 < p.1 ∧ r p.1 p.2)

def blockOffDiagonalEntries {n : ℕ} (r : Setoid (Fin n)) : Finset (Fin n × Fin n) :=
  blockUpperEntries r ∪ blockLowerEntries r

@[simp] lemma mem_blockUpperEntries {n : ℕ} (r : Setoid (Fin n)) (p : Fin n × Fin n) :
    p ∈ blockUpperEntries r ↔ p.1 < p.2 ∧ r p.1 p.2 := by
  simp [blockUpperEntries]

@[simp] lemma mem_blockLowerEntries {n : ℕ} (r : Setoid (Fin n)) (p : Fin n × Fin n) :
    p ∈ blockLowerEntries r ↔ p.2 < p.1 ∧ r p.1 p.2 := by
  simp [blockLowerEntries]

@[simp] lemma mem_blockOffDiagonalEntries {n : ℕ} (r : Setoid (Fin n))
    (p : Fin n × Fin n) :
    p ∈ blockOffDiagonalEntries r ↔ p.1 ≠ p.2 ∧ r p.1 p.2 := by
  simp only [blockOffDiagonalEntries, Finset.mem_union, mem_blockUpperEntries,
    mem_blockLowerEntries]
  constructor
  · rintro (h | h)
    · exact ⟨ne_of_lt h.1, h.2⟩
    · exact ⟨(ne_of_lt h.1).symm, h.2⟩
  · rintro ⟨hne, hr⟩
    rcases lt_or_gt_of_ne hne with h | h
    · exact Or.inl ⟨h, hr⟩
    · exact Or.inr ⟨h, hr⟩

private def UpperInitial {n : ℕ} (r : Setoid (Fin n))
    (P : Finset (Fin n × Fin n)) : Prop :=
  P ⊆ blockUpperEntries r ∧ ∀ p ∈ P, ∀ q ∈ blockUpperEntries r, q.1 < p.1 → q ∈ P

private theorem exists_upper_schedule {n : ℕ} (r : Setoid (Fin n))
    (P : Finset (Fin n × Fin n)) (hP : UpperInitial r P) :
    ∃ c : BlockEliminationChain r P, c.finalEntries = blockUpperEntries r := by
  suffices ∀ m : ℕ, ∀ P : Finset (Fin n × Fin n),
      (blockUpperEntries r \ P).card = m → UpperInitial r P →
      ∃ c : BlockEliminationChain r P, c.finalEntries = blockUpperEntries r by
    exact this _ P rfl hP
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    intro P hcard hP
    by_cases he : blockUpperEntries r \ P = ∅
    · refine ⟨.done, ?_⟩
      exact Finset.Subset.antisymm hP.1 (Finset.sdiff_eq_empty_iff_subset.mp he)
    · obtain ⟨p, hp, hmin⟩ := Finset.exists_min_image (blockUpperEntries r \ P)
        (fun q => q.1) (Finset.nonempty_iff_ne_empty.mpr he)
      have hpU := (Finset.mem_sdiff.mp hp).1
      have hpnot := (Finset.mem_sdiff.mp hp).2
      obtain ⟨hab, hr⟩ := (mem_blockUpperEntries r p).mp hpU
      have hsmall (q : Fin n × Fin n) (hq : q ∈ blockUpperEntries r)
          (hlt : q.1 < p.1) : q ∈ P := by
        by_contra hnot
        exact (not_le_of_gt hlt) (hmin q (Finset.mem_sdiff.mpr ⟨hq, hnot⟩))
      have hstable : ∀ j, (j, p.2) ∈ P → (j, p.1) ∈ P := by
        intro j hj
        have hjU := (mem_blockUpperEntries r (j, p.2)).mp (hP.1 hj)
        have hjlt : j < p.1 := by
          by_contra h
          have hle : p.1 ≤ j := le_of_not_gt h
          rcases eq_or_lt_of_le hle with heq | hlt
          · apply hpnot
            simpa only [← heq, Prod.eta] using hj
          · exact hpnot (hP.2 (j, p.2) hj p hpU hlt)
        exact hsmall (j, p.1) ((mem_blockUpperEntries r _).mpr
          ⟨hjlt, r.trans hjU.2 (r.symm hr)⟩) hjlt
      have hnew : UpperInitial r (insert p P) := by
        constructor
        · intro q hq
          rcases Finset.mem_insert.mp hq with rfl | hq
          · exact hpU
          · exact hP.1 hq
        · intro q hq z hz hlt
          apply Finset.mem_insert_of_mem
          rcases Finset.mem_insert.mp hq with rfl | hq
          · exact hsmall z hz hlt
          · exact hP.2 q hq z hz hlt
      have hless : (blockUpperEntries r \ insert p P).card < m := by
        rw [Finset.sdiff_insert, ← hcard]
        exact Finset.card_erase_lt_of_mem hp
      obtain ⟨tail, ht⟩ := ih _ hless (insert p P) rfl hnew
      exact ⟨.step p.1 p.2 (ne_of_lt hab) hr hstable tail, ht⟩

private def LowerInitial {n : ℕ} (r : Setoid (Fin n))
    (Q : Finset (Fin n × Fin n)) : Prop :=
  Q ⊆ blockLowerEntries r ∧ ∀ p ∈ Q, ∀ q ∈ blockLowerEntries r, p.1 < q.1 → q ∈ Q

private theorem exists_lower_schedule {n : ℕ} (r : Setoid (Fin n))
    (Q : Finset (Fin n × Fin n)) (hQ : LowerInitial r Q) :
    ∃ c : BlockEliminationChain r (blockUpperEntries r ∪ Q),
      c.finalEntries = blockOffDiagonalEntries r := by
  suffices ∀ m : ℕ, ∀ Q : Finset (Fin n × Fin n),
      (blockLowerEntries r \ Q).card = m → LowerInitial r Q →
      ∃ c : BlockEliminationChain r (blockUpperEntries r ∪ Q),
        c.finalEntries = blockOffDiagonalEntries r by
    exact this _ Q rfl hQ
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    intro Q hcard hQ
    by_cases he : blockLowerEntries r \ Q = ∅
    · have heq : Q = blockLowerEntries r :=
        Finset.Subset.antisymm hQ.1 (Finset.sdiff_eq_empty_iff_subset.mp he)
      exact ⟨.done, by simp only [BlockEliminationChain.finalEntries, heq,
        blockOffDiagonalEntries]⟩
    · obtain ⟨p, hp, hmax⟩ := Finset.exists_max_image (blockLowerEntries r \ Q)
        (fun q => q.1) (Finset.nonempty_iff_ne_empty.mpr he)
      have hpL := (Finset.mem_sdiff.mp hp).1
      have hpnot := (Finset.mem_sdiff.mp hp).2
      obtain ⟨hba, hr⟩ := (mem_blockLowerEntries r p).mp hpL
      have hlarge (q : Fin n × Fin n) (hq : q ∈ blockLowerEntries r)
          (hlt : p.1 < q.1) : q ∈ Q := by
        by_contra hnot
        exact (not_le_of_gt hlt) (hmax q (Finset.mem_sdiff.mpr ⟨hq, hnot⟩))
      have hstable : ∀ j, (j, p.2) ∈ blockUpperEntries r ∪ Q →
          (j, p.1) ∈ blockUpperEntries r ∪ Q := by
        intro j hj
        rcases Finset.mem_union.mp hj with hj | hj
        · have hjU := (mem_blockUpperEntries r _).mp hj
          exact Finset.mem_union_left _ ((mem_blockUpperEntries r _).mpr
            ⟨hjU.1.trans hba, r.trans hjU.2 (r.symm hr)⟩)
        · have hjL := (mem_blockLowerEntries r _).mp (hQ.1 hj)
          have hjgt : p.1 < j := by
            by_contra h
            have hle : j ≤ p.1 := le_of_not_gt h
            rcases eq_or_lt_of_le hle with heq | hlt
            · apply hpnot
              simpa only [heq, Prod.eta] using hj
            · exact hpnot (hQ.2 (j, p.2) hj p hpL hlt)
          exact Finset.mem_union_right _ (hlarge (j, p.1)
            ((mem_blockLowerEntries r _).mpr
              ⟨hjgt, r.trans hjL.2 (r.symm hr)⟩) hjgt)
      have hnew : LowerInitial r (insert p Q) := by
        constructor
        · intro q hq
          rcases Finset.mem_insert.mp hq with rfl | hq
          · exact hpL
          · exact hQ.1 hq
        · intro q hq z hz hlt
          apply Finset.mem_insert_of_mem
          rcases Finset.mem_insert.mp hq with rfl | hq
          · exact hlarge z hz hlt
          · exact hQ.2 q hq z hz hlt
      have hless : (blockLowerEntries r \ insert p Q).card < m := by
        rw [Finset.sdiff_insert, ← hcard]
        exact Finset.card_erase_lt_of_mem hp
      obtain ⟨tail, ht⟩ := ih _ hless (insert p Q) rfl hnew
      have heq : blockUpperEntries r ∪ insert p Q =
          insert p (blockUpperEntries r ∪ Q) := by ext q; simp
      have htail : ∃ c : BlockEliminationChain r (insert p (blockUpperEntries r ∪ Q)),
          c.finalEntries = blockOffDiagonalEntries r := by
        rw [← heq]
        exact ⟨tail, ht⟩
      obtain ⟨tail', ht'⟩ := htail
      exact ⟨.step p.1 p.2 (ne_of_lt hba).symm hr hstable tail', ht'⟩

/-- Every off-diagonal entry inside a block can be eliminated using
only roots from that block, with every earlier zero retained. -/
theorem exists_block_elimination_schedule {n : ℕ} (r : Setoid (Fin n)) :
    ∃ c : BlockEliminationChain r ∅, c.finalEntries = blockOffDiagonalEntries r := by
  obtain ⟨upper, hu⟩ := exists_upper_schedule r ∅ ⟨by simp, by simp⟩
  have hlower : ∃ c : BlockEliminationChain r upper.finalEntries,
      c.finalEntries = blockOffDiagonalEntries r := by
    rw [hu]
    have h := exists_lower_schedule r ∅ ⟨by simp, by simp⟩
    rw [Finset.union_empty] at h
    exact h
  obtain ⟨lower, hl⟩ := hlower
  exact ⟨upper.append lower, (BlockEliminationChain.finalEntries_append upper lower).trans hl⟩

/-- A near-identity sequence has an actual within-block root correction
which kills all its within-block off-diagonal entries. -/
theorem exists_block_transverse_sequence {n : ℕ} (r : Setoid (Fin n))
    (g : ℕ → G n) (hg : Tendsto g atTop (𝓝 1)) :
    ∃ s b : ℕ → G n,
      Tendsto s atTop (𝓝 1) ∧ Tendsto b atTop (𝓝 1) ∧
      (∀ k, s k = g k * b k) ∧ (∀ k, b k ∈ blockRootGroup r) ∧
      ∀ᶠ k in atTop, ∀ i j, i ≠ j → r i j → (s k).val i j = 0 := by
  obtain ⟨c, hc⟩ := exists_block_elimination_schedule r
  obtain ⟨s, b, hs, hb, he, hm, hz⟩ := c.normalize_sequence g hg
    (Filter.Eventually.of_forall (by intro k p hp; simp at hp))
  refine ⟨s, b, hs, hb, he, hm, ?_⟩
  filter_upwards [hz] with k hk i j hij hr
  apply hk (i, j)
  simpa only [hc] using (mem_blockOffDiagonalEntries r _).mpr ⟨hij, hr⟩

/-- The correction lies in the original subgroup and preserves being
outside it; membership of the full block group is not assumed. -/
theorem exists_subgroup_transverse_sequence {n : ℕ}
    (r : Setoid (Fin n)) (L : Subgroup (G n))
    (hroot : ∀ (i j : Fin n) (hij : i ≠ j), r i j → ∀ t : ℝ,
      Matrix.SpecialLinearGroup.transvection hij t ∈ L)
    (g : ℕ → G n) (hg : Tendsto g atTop (𝓝 1)) (hout : ∀ k, g k ∉ L) :
    ∃ s b : ℕ → G n,
      Tendsto s atTop (𝓝 1) ∧ Tendsto b atTop (𝓝 1) ∧
      (∀ k, s k = g k * b k) ∧ (∀ k, b k ∈ L) ∧ (∀ k, s k ∉ L) ∧
      ∀ᶠ k in atTop, ∀ i j, i ≠ j → r i j → (s k).val i j = 0 := by
  obtain ⟨s, b, hs, hb, he, hm, hz⟩ := exists_block_transverse_sequence r g hg
  have hle : blockRootGroup r ≤ L := by
    rw [blockRootGroup, Subgroup.closure_le]
    rintro _ ⟨i, j, hij, t, hr, rfl⟩
    exact hroot i j hij hr t
  refine ⟨s, b, hs, hb, he, fun k => hle (hm k), ?_, hz⟩
  intro k hk
  apply hout k
  have hh := L.mul_mem hk (L.inv_mem (hle (hm k)))
  simpa only [he k, mul_inv_cancel_right] using hh

end DukePrimeDegree

end

end OAI
