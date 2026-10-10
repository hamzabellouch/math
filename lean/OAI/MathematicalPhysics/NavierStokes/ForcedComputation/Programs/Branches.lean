import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.FiniteRecorder

namespace OAI

/-! The branch keys used to separate full source and target rectangles. -/

namespace ForcedComputation.Recorder

variable {Q A : Type*}

structure Branch (M : Machine Q A) where
  source : Control Q A
  read : Symbol Q A
  target : Control Q A
  write : Symbol Q A
  displacement : ℤ
  left : Symbol Q A
  rule : LocalStep M source read target write displacement

theorem Branch.source_key_injective [DecidableEq Q] [DecidableEq A] (M : Machine Q A) :
    Function.Injective (fun b : Branch M => (b.source, b.read, b.left)) := by
  intro b c he
  have hs : b.source = c.source := congrArg Prod.fst he
  have hr : b.read = c.read := congrArg (fun p => p.2.1) he
  have hl : b.left = c.left := congrArg (fun p => p.2.2) he
  have hc : LocalStep M b.source b.read c.target c.write c.displacement := by
    simpa only [hs, hr] using c.rule
  obtain ⟨ht, hw, hd⟩ := b.rule.successor_unique hc
  cases b
  cases c
  simp only at hs hr hl ht hw hd
  subst_vars
  rfl

theorem Branch.target_key_injective (M : Machine Q A) :
    Function.Injective (fun b : Branch M => (b.target, b.write, b.left)) := by
  intro b c he
  have ht : b.target = c.target := congrArg Prod.fst he
  have hw : b.write = c.write := congrArg (fun p => p.2.1) he
  have hl : b.left = c.left := congrArg (fun p => p.2.2) he
  have hc : LocalStep M c.source c.read b.target b.write c.displacement := by
    simpa only [ht, hw] using c.rule
  obtain ⟨hs, hr, hd⟩ := b.rule.predecessor_unique hc
  cases b
  cases c
  simp only at hs hr hl ht hw hd
  subst_vars
  rfl

theorem Branch.same_target_displacement {M : Machine Q A} {b c : Branch M}
    (ht : b.target = c.target) : b.displacement = c.displacement := by
  rw [← b.rule.incoming_eq, ht, c.rule.incoming_eq]

theorem Branch.source_symbols_differ [DecidableEq Q] [DecidableEq A]
    {M : Machine Q A} {b c : Branch M} (hne : b ≠ c) (hs : b.source = c.source) :
    b.read ≠ c.read ∨ b.left ≠ c.left := by
  by_contra h
  push Not at h
  exact hne (Branch.source_key_injective M (by simp [hs, h.1, h.2]))

instance [DecidableEq Q] [DecidableEq A] (M : Machine Q A) : DecidableEq (Branch M) :=
  fun b c => decidable_of_iff (b.source = c.source ∧ b.read = c.read ∧ b.left = c.left)
    ⟨fun h => Branch.source_key_injective M (by simp [h.1, h.2.1, h.2.2]),
      fun h => by subst c; simp⟩

theorem Branch.target_symbols_differ {M : Machine Q A} {b c : Branch M}
    (hne : b ≠ c) (ht : b.target = c.target) : b.write ≠ c.write ∨ b.left ≠ c.left := by
  by_contra h
  push Not at h
  exact hne (Branch.target_key_injective M (by simp [ht, h.1, h.2]))

def compileBranches (M : Alternating.Machine) (hM : M.WellFormed) :
    List (Branch (finiteMachine M hM)) :=
  (instructionTable M hM).attach.flatMap fun entry =>
    (allSymbols M).map fun l =>
      { source := entry.val.1.1
        read := entry.val.1.2
        target := entry.val.2.1
        write := entry.val.2.2.1
        displacement := entry.val.2.2.2
        left := l
        rule := (mem_instructionTable_iff M hM).mp entry.property }

theorem mem_compileBranches (M : Alternating.Machine) (hM : M.WellFormed)
    (b : Branch (finiteMachine M hM)) : b ∈ compileBranches M hM := by
  let entry := ((b.source, b.read), (b.target, b.write, b.displacement))
  have he : entry ∈ instructionTable M hM := localStep_mem_instructionTable M hM b.rule
  apply List.mem_flatMap.mpr
  refine ⟨⟨entry, he⟩, by simp, List.mem_map.mpr ?_⟩
  refine ⟨b.left, mem_allSymbols M b.left, ?_⟩
  cases b
  rfl

end ForcedComputation.Recorder

end OAI
