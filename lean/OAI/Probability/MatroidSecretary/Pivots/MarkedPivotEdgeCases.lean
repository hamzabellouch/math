import OAI.Probability.MatroidSecretary.Pivots.MarkedPivotContract

namespace OAI

/-! Explicit nonemptiness and zero-size cases of the actual pattern family. -/

namespace MatroidProphet.MarkedPivots

variable {α : Type*} [Fintype α] {r q n : ℕ}

/-- One legal interleaving: all old occurrences, followed by all movable occurrences. -/
def oldThenMovable (r q : ℕ) : Occurrences r q → ℕ :=
  Sum.elim Fin.val (fun i => r + i.val)

lemma oldThenMovable_ordered : OldOrdered (oldThenMovable r q) := by
  intro i j hij
  exact hij

lemma oldThenMovable_injective : Function.Injective (oldThenMovable r q) := by
  intro o p hop
  cases o with
  | inl i =>
    cases p with
    | inl j => exact congrArg Sum.inl (Fin.ext hop)
    | inr j => simp only [oldThenMovable, Sum.elim_inl, Sum.elim_inr] at hop; omega
  | inr i =>
    cases p with
    | inl j => simp only [oldThenMovable, Sum.elim_inl, Sum.elim_inr] at hop; omega
    | inr j =>
      apply congrArg Sum.inr
      apply Fin.ext
      simpa only [oldThenMovable, Sum.elim_inr, Nat.add_left_cancel_iff] using hop

omit [Fintype α] in
lemma records_mem_patterns (M : Matroid α) (old : Fin r → α) (movable : Fin q → α)
    (test : Fin n → α) (oldMark : Fin r → Bool) (time : Occurrences r q → ℕ)
    (horder : OldOrdered time) (htime : Function.Injective time)
    (movableMark : Fin q → Bool) {pattern : Finset (Fin n)}
    (hp : Records M old movable test time oldMark movableMark pattern) :
    pattern ∈ patterns M old movable test oldMark := by
  classical
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, time, horder, htime, movableMark, hp⟩

lemma patterns_nonempty (M : Matroid α) (old : Fin r → α) (movable : Fin q → α)
    (test : Fin n → α) (oldMark : Fin r → Bool)
    (hspan : M.closure (Set.range old) = M.E)
    (htest : ∀ f, test f ∈ M.E ∧ test f ∉ M.closure ∅) :
    (patterns M old movable test oldMark).Nonempty := by
  obtain ⟨pattern, hp, _⟩ := records_existsUnique M old movable test
    (oldThenMovable r q) oldThenMovable_injective oldMark (fun _ => false) hspan htest
  exact ⟨pattern, records_mem_patterns M old movable test oldMark _
    oldThenMovable_ordered oldThenMovable_injective _ hp⟩

omit [Fintype α] in
/-- With no tested labels there is exactly one (empty) mark vector, even on an empty type. -/
lemma card_patterns_zero_tests (M : Matroid α) (old : Fin r → α) (movable : Fin q → α)
    (test : Fin 0 → α) (oldMark : Fin r → Bool) :
    (patterns M old movable test oldMark).card = 1 := by
  have hp : (patterns M old movable test oldMark).Nonempty := by
    refine ⟨∅, records_mem_patterns M old movable test oldMark (oldThenMovable r q)
      oldThenMovable_ordered oldThenMovable_injective (fun _ => false) ?_⟩
    intro f
    exact Fin.elim0 f
  have hle : (patterns M old movable test oldMark).card ≤ 1 :=
    Finset.card_le_one.mpr fun _ _ _ _ => Subsingleton.elim _ _
  have hpos := Finset.card_pos.mpr hp
  omega

/-- The source's `s=0` endpoint has one actual pattern, not merely at most one. -/
lemma card_patterns_zero_movable (M : Matroid α) (old : Fin r → α)
    (movable : Fin 0 → α) (test : Fin n → α) (oldMark : Fin r → Bool)
    (hold : ∀ i, old i ∈ M.E) (hspan : M.closure (Set.range old) = M.E)
    (htest : ∀ f, test f ∈ M.E ∧ test f ∉ M.closure ∅) :
    (patterns M old movable test oldMark).card = 1 := by
  have hle := card_patterns_le M old movable test oldMark 0 (by omega) hold
    (fun i => Fin.elim0 i)
  have hz : Finset.Iic (0 : ℕ) = {0} := by
    ext k
    simp
  simp [hz] at hle
  have hpos := Finset.card_pos.mpr (patterns_nonempty M old movable test oldMark hspan htest)
  omega

end MatroidProphet.MarkedPivots

end OAI
