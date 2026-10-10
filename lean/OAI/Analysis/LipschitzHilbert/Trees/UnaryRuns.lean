import OAI.Analysis.LipschitzHilbert.Trees.UnarySegmentation

namespace OAI

/-! Actual consecutive unary runs and their interruption endpoints. -/

noncomputable section

namespace LipschitzHilbert

structure UnaryRunPartition (unary : ℕ → Prop) (start finish : ℕ) where
  runs : Finset (ℕ × ℕ)
  bounds : ∀ r ∈ runs, start ≤ r.1 ∧ r.1 < r.2 ∧ r.2 ≤ finish
  inside : ∀ r ∈ runs, ∀ j, r.1 ≤ j → j < r.2 → unary j
  cover : ∀ j, start ≤ j → j < finish → unary j →
    ∃ r ∈ runs, r.1 ≤ j ∧ j < r.2
  ordered : ∀ r ∈ runs, ∀ s ∈ runs, r ≠ s → r.2 ≤ s.1 ∨ s.2 ≤ r.1
  interruption : ∀ r ∈ runs, r.2 < finish → ¬ unary r.2

namespace UnaryRunPartition

theorem separated {unary : ℕ → Prop} {start finish : ℕ}
    (P : UnaryRunPartition unary start finish) {r s : ℕ × ℕ}
    (hr : r ∈ P.runs) (hs : s ∈ P.runs) (hne : r ≠ s) :
    r.2 < s.1 ∨ s.2 < r.1 := by
  rcases P.ordered r hr s hs hne with h | h
  · left
    have hsf := (P.bounds s hs).2
    have hrf : r.2 < finish := h.trans_lt (hsf.1.trans_le hsf.2)
    have hneq : r.2 ≠ s.1 := by
      intro heq
      exact P.interruption r hr hrf (heq ▸ P.inside s hs s.1 le_rfl hsf.1)
    exact lt_of_le_of_ne h hneq
  · right
    have hrf := (P.bounds r hr).2
    have hsf : s.2 < finish := h.trans_lt (hrf.1.trans_le hrf.2)
    have hneq : s.2 ≠ r.1 := by
      intro heq
      exact P.interruption s hs hsf (heq ▸ P.inside r hr r.1 le_rfl hrf.1)
    exact lt_of_le_of_ne h hneq

theorem end_injective {unary : ℕ → Prop} {start finish : ℕ}
    (P : UnaryRunPartition unary start finish) :
    Function.Injective (fun r : P.runs => r.val.2) := by
  intro r s heq
  change r.val.2 = s.val.2 at heq
  by_contra hne
  have h := P.ordered r.val r.property s.val s.property (fun h => hne (Subtype.ext h))
  have hr := (P.bounds r.val r.property).2.1
  have hs := (P.bounds s.val s.property).2.1
  rcases h with h | h <;> omega

end UnaryRunPartition

theorem UnarySegmentPartition.end_injective {n : ℕ → ℝ} {start finish : ℕ}
    (P : UnarySegmentPartition n start finish) :
    Function.Injective (fun r : P.blocks => r.val.2) := by
  intro r s heq
  change r.val.2 = s.val.2 at heq
  by_contra hne
  have h := P.ordered r.val r.property s.val s.property (fun h => hne (Subtype.ext h))
  have hr := (P.bounds r.val r.property).2.1
  have hs := (P.bounds s.val s.property).2.1
  rcases h with h | h <;> omega

private theorem exists_unary_run_end (unary : ℕ → Prop) (start finish : ℕ)
    (hstart : start < finish) (hu : unary start) :
    ∃ stop, start < stop ∧ stop ≤ finish ∧
      (∀ j, start ≤ j → j < stop → unary j) ∧
      (stop < finish → ¬ unary stop) := by
  classical
  let P := fun k => start ≤ k ∧ k ≤ finish ∧ (k = finish ∨ ¬ unary k)
  have hex : ∃ k, P k := ⟨finish, hstart.le, le_rfl, Or.inl rfl⟩
  let stop := Nat.find hex
  have hs : P stop := Nat.find_spec hex
  have hstrict : start < stop := by
    have hne : start ≠ stop := by
      intro heq
      rcases hs.2.2 with h | h
      · omega
      · exact h (heq ▸ hu)
    omega
  refine ⟨stop, hstrict, hs.2.1, ?_, ?_⟩
  · intro j hj hjstop
    by_contra hnot
    exact Nat.find_min hex hjstop ⟨hj, hjstop.le.trans hs.2.1, Or.inr hnot⟩
  · intro hstop
    exact hs.2.2.resolve_left (by omega)

/-- Consecutive runs are constructed from the predicate itself, including
their first nonunary interruption or the final path endpoint. -/
theorem exists_unary_run_partition (unary : ℕ → Prop) (start finish : ℕ)
    (horder : start ≤ finish) : Nonempty (UnaryRunPartition unary start finish) := by
  classical
  by_cases heq : start = finish
  · subst finish
    exact ⟨{
      runs := ∅
      bounds := by simp
      inside := by simp
      cover := by intro j hj hj'; omega
      ordered := by simp
      interruption := by simp }⟩
  have hstrict : start < finish := by omega
  by_cases hu : unary start
  · obtain ⟨stop, hs, hsf, hin, hinterrupt⟩ := exists_unary_run_end unary start finish hstrict hu
    obtain ⟨tail⟩ := exists_unary_run_partition unary stop finish hsf
    refine ⟨{
      runs := insert (start, stop) tail.runs
      bounds := ?_
      inside := ?_
      cover := ?_
      ordered := ?_
      interruption := ?_ }⟩
    · intro r hr
      rcases Finset.mem_insert.mp hr with rfl | hr
      · exact ⟨le_rfl, hs, hsf⟩
      · have h := tail.bounds r hr
        exact ⟨hs.le.trans h.1, h.2⟩
    · intro r hr j hj hjr
      rcases Finset.mem_insert.mp hr with rfl | hr
      · exact hin j hj hjr
      · exact tail.inside r hr j hj hjr
    · intro j hj hjf hjunary
      by_cases hjstop : j < stop
      · exact ⟨(start,stop), Finset.mem_insert_self _ _, hj, hjstop⟩
      · obtain ⟨r, hr, hrj, hjr⟩ := tail.cover j (by omega) hjf hjunary
        exact ⟨r, Finset.mem_insert_of_mem hr, hrj, hjr⟩
    · intro r hr s hs' hrs
      rcases Finset.mem_insert.mp hr with rfl | hr
      · rcases Finset.mem_insert.mp hs' with rfl | hs'
        · exact False.elim (hrs rfl)
        · exact Or.inl (tail.bounds s hs').1
      · rcases Finset.mem_insert.mp hs' with rfl | hs'
        · exact Or.inr (tail.bounds r hr).1
        · exact tail.ordered r hr s hs' hrs
    · intro r hr hrf
      rcases Finset.mem_insert.mp hr with rfl | hr
      · exact hinterrupt hrf
      · exact tail.interruption r hr hrf
  · obtain ⟨tail⟩ := exists_unary_run_partition unary (start + 1) finish hstrict
    refine ⟨{
      runs := tail.runs
      bounds := ?_
      inside := tail.inside
      cover := ?_
      ordered := tail.ordered
      interruption := tail.interruption }⟩
    · intro r hr
      have h := tail.bounds r hr
      exact ⟨by omega, h.2⟩
    · intro j hj hjf hjunary
      have hne : j ≠ start := by intro he; exact hu (he ▸ hjunary)
      exact tail.cover j (by omega) hjf hjunary
termination_by finish - start
decreasing_by all_goals omega

end LipschitzHilbert

end

end OAI
