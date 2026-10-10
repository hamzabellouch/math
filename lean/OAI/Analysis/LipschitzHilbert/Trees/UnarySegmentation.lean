import OAI.Analysis.LipschitzHilbert.Estimates.IntervalSegmentCharging

namespace OAI

/-! Actual stopping indices for the greedy unary-segment decomposition. -/

noncomputable section

namespace LipschitzHilbert

/-- End a completed unary segment at the first accumulated unit drop.
Since each constituent drop is smaller than one, its total is below two. -/
theorem exists_first_unit_drop (n : ℕ → ℝ) (start finish : ℕ)
    (horder : start ≤ finish) (htotal : 1 ≤ n start - n finish)
    (hstep : ∀ j, start ≤ j → j < finish → n j - n (j + 1) < 1) :
    ∃ cut, start < cut ∧ cut ≤ finish ∧ 1 ≤ n start - n cut ∧
      n start - n cut < 2 ∧ ∀ j, start ≤ j → j < cut → n start - n j < 1 := by
  classical
  let P := fun j => start ≤ j ∧ j ≤ finish ∧ 1 ≤ n start - n j
  have hex : ∃ j, P j := ⟨finish, horder, le_rfl, htotal⟩
  let cut := Nat.find hex
  have hcut : P cut := Nat.find_spec hex
  have hstrict : start < cut := by
    have hne : start ≠ cut := by
      intro heq
      have h := hcut.2.2
      rw [← heq, sub_self] at h
      norm_num at h
    exact lt_of_le_of_ne hcut.1 hne
  have hbefore : ∀ j, start ≤ j → j < cut → n start - n j < 1 := by
    intro j hj hjcut
    have hnot : ¬P j := Nat.find_min hex hjcut
    have hjfinish : j ≤ finish := hjcut.le.trans hcut.2.1
    by_contra h
    exact hnot ⟨hj, hjfinish, le_of_not_gt h⟩
  have hpred : n start - n (cut - 1) < 1 := hbefore (cut - 1) (by omega) (by omega)
  have hlast := hstep (cut - 1) (by omega) (by omega)
  have hsucc : cut - 1 + 1 = cut := by omega
  rw [hsucc] at hlast
  exact ⟨cut, hstrict, hcut.2.1, hcut.2.2, by linarith, hbefore⟩

/-- A finite partition of a unary run into its actual successive segments. -/
structure UnarySegmentPartition (n : ℕ → ℝ) (start finish : ℕ) where
  blocks : Finset (ℕ × ℕ)
  bounds : ∀ b ∈ blocks, start ≤ b.1 ∧ b.1 < b.2 ∧ b.2 ≤ finish
  cover : ∀ j, start ≤ j → j < finish → ∃ b ∈ blocks, b.1 ≤ j ∧ j < b.2
  ordered : ∀ b ∈ blocks, ∀ c ∈ blocks, b ≠ c → b.2 ≤ c.1 ∨ c.2 ≤ b.1
  drop_lt_two : ∀ b ∈ blocks, n b.1 - n b.2 < 2
  completed : ∀ b ∈ blocks, b.2 < finish → 1 ≤ n b.1 - n b.2

/-- Greedy unit-drop stopping constructs the partition, with at most the
last segment incomplete. There is no bound on the number of tiny drops. -/
theorem exists_unary_segment_partition (n : ℕ → ℝ) (start finish : ℕ)
    (horder : start ≤ finish)
    (hstep : ∀ j, start ≤ j → j < finish → n j - n (j + 1) < 1) :
    Nonempty (UnarySegmentPartition n start finish) := by
  classical
  by_cases hempty : start = finish
  · subst finish
    exact ⟨{
      blocks := ∅
      bounds := by simp
      cover := by intro j hj hj'; omega
      ordered := by simp
      drop_lt_two := by simp
      completed := by simp }⟩
  have hstrict : start < finish := lt_of_le_of_ne horder hempty
  by_cases htotal : 1 ≤ n start - n finish
  · obtain ⟨cut, hcut, hcutend, hdrop, htwo, _⟩ :=
      exists_first_unit_drop n start finish horder htotal hstep
    obtain ⟨tail⟩ := exists_unary_segment_partition n cut finish hcutend
      (fun j hj hjf => hstep j (hcut.le.trans hj) hjf)
    refine ⟨{
      blocks := insert (start, cut) tail.blocks
      bounds := ?_
      cover := ?_
      ordered := ?_
      drop_lt_two := ?_
      completed := ?_ }⟩
    · intro b hb
      rcases Finset.mem_insert.mp hb with rfl | hb
      · exact ⟨le_rfl, hcut, hcutend⟩
      · have h := tail.bounds b hb
        exact ⟨hcut.le.trans h.1, h.2⟩
    · intro j hj hjf
      by_cases hjc : j < cut
      · exact ⟨(start,cut), Finset.mem_insert_self _ _, hj, hjc⟩
      · obtain ⟨b, hb, hbj, hjb⟩ := tail.cover j (by omega) hjf
        exact ⟨b, Finset.mem_insert_of_mem hb, hbj, hjb⟩
    · intro b hb c hc hbc
      rcases Finset.mem_insert.mp hb with rfl | hb
      · rcases Finset.mem_insert.mp hc with rfl | hc
        · exact False.elim (hbc rfl)
        · exact Or.inl (tail.bounds c hc).1
      · rcases Finset.mem_insert.mp hc with rfl | hc
        · exact Or.inr (tail.bounds b hb).1
        · exact tail.ordered b hb c hc hbc
    · intro b hb
      rcases Finset.mem_insert.mp hb with rfl | hb
      · exact htwo
      · exact tail.drop_lt_two b hb
    · intro b hb hbf
      rcases Finset.mem_insert.mp hb with rfl | hb
      · exact hdrop
      · exact tail.completed b hb hbf
  · refine ⟨{
      blocks := {(start,finish)}
      bounds := ?_
      cover := ?_
      ordered := ?_
      drop_lt_two := ?_
      completed := ?_ }⟩
    · intro b hb
      obtain rfl := Finset.mem_singleton.mp hb
      exact ⟨le_rfl, hstrict, le_rfl⟩
    · intro j hj hjf
      exact ⟨(start,finish), Finset.mem_singleton_self _, hj, hjf⟩
    · intro b hb c hc hbc
      exact False.elim (hbc ((Finset.mem_singleton.mp hb).trans (Finset.mem_singleton.mp hc).symm))
    · intro b hb
      obtain rfl := Finset.mem_singleton.mp hb
      exact (lt_of_not_ge htotal).trans (by norm_num)
    · intro b hb hbf
      obtain rfl := Finset.mem_singleton.mp hb
      exact False.elim (Nat.lt_irrefl _ hbf)
termination_by finish - start
decreasing_by omega

end LipschitzHilbert

end

end OAI
