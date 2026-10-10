import OAI.Combinatorics.LowSpaceSubsetSum.Search.PreparedReaderContext

namespace OAI

/-! # Parent execution with shared prepared arrays

Both arrays and both initial tournaments are built once. The two contexts
are then passed by value to the counted join. Its returned dictionary and
counters have a type independent of the hidden tournament depths.
-/

namespace LowSpaceSubsetSum.PreparedParentExecution

variable {n : ℕ}

structure Result (I : Instance n) (C : ℕ) where
  dictionary : StoredEntry.Dictionary I C
  queries : ℕ
  reports : ℕ
  copies : ℕ
  done : Bool

def project {I : Instance n} {C : ℕ} {σ τ : Type*}
    (out : StreamJoin.StoppedResult σ τ (StoredEntry.Dictionary I C)) : Result I C :=
  ⟨out.state.user, out.state.queries, out.state.reports, out.state.copies, out.state.done⟩

def runContexts (I : Instance n) (F : IndexedMask n) (P t : ℤ) (C B : ℕ)
    (fuel₀ fuel₁ control : ℕ)
    (left : PreparedReaderContext.Context I F P .direct)
    (right : PreparedReaderContext.Context I F P (.complementary t)) : Result I C × ℕ :=
  let out := CountedParentJoin.run I F P t C B left.right right.right
    fuel₀ fuel₁ control left.state right.state
  (project out.1, out.2)

def collect (D : RepresentationParentData n) (F : IndexedMask n) (P : StoredRestriction n)
    (hF : F.semantic = D.signs) (B fuel₀ fuel₁ control : ℕ) : Result D.input D.capacity × ℕ :=
  let left := PreparedReaderContext.build D F P hF 0
  let right := PreparedReaderContext.build D F P hF 1
  let out := runContexts D.input F D.modulus D.parentResidue D.capacity B
    fuel₀ fuel₁ control left.1 right.1
  (out.1, left.2 + right.2 + out.2 + 5)

private theorem runContexts_source (D : RepresentationParentData n) (F : IndexedMask n)
    (hF : F.semantic = D.signs) (B : ℕ) :
    runContexts D.input F D.modulus D.parentResidue D.capacity B
      (D.pair 0).lengthBound (D.pair 1).lengthBound
      ((D.pair 0).lengthBound + (D.pair 1).lengthBound + 1)
      (PreparedReaderContext.source D F hF 0) (PreparedReaderContext.source D F hF 1) =
      (project (StoredParentExecution.collect D F hF B).1,
        (StoredParentExecution.collect D F hF B).2) := rfl

/-- Exact stored dictionary, counters and termination flag, after setup. -/
theorem collect_value (D : RepresentationParentData n) (F : IndexedMask n)
    (P : StoredRestriction n) (hF : F.semantic = D.signs) (B fuel₀ fuel₁ control : ℕ)
    (h₀ : fuel₀ = (D.pair 0).lengthBound) (h₁ : fuel₁ = (D.pair 1).lengthBound)
    (hcontrol : control = fuel₀ + fuel₁ + 1) :
    (collect D F P hF B fuel₀ fuel₁ control).1 =
      project (StoredParentExecution.collect {D with maskRestriction := P.semantic} F hF B).1 := by
  subst fuel₀
  subst fuel₁
  subst control
  simp only [collect, PreparedReaderContext.build_value]
  exact congrArg Prod.fst (runContexts_source {D with maskRestriction := P.semantic} F hF B)

/-- Setup is charged once per child stream, followed by the exact join ledger. -/
theorem collect_work (D : RepresentationParentData n) (F : IndexedMask n)
    (P : StoredRestriction n) (hF : F.semantic = D.signs) (B fuel₀ fuel₁ control C : ℕ)
    (h₀ : fuel₀ = (D.pair 0).lengthBound) (h₁ : fuel₁ = (D.pair 1).lengthBound)
    (hcontrol : control = fuel₀ + fuel₁ + 1) (hn : 10000 ≤ n)
    (hl : ∀ j, (D.pair j).left.occurrences.card ≤ C)
    (hr : ∀ j, (D.pair j).right.occurrences.card ≤ C) (hC : C ≤ 2 ^ n)
    (hd₀ : Nat.clog 2 ({D with maskRestriction := P.semantic}.pair 0).leftArray.size ≤ n)
    (hd₁ : Nat.clog 2 ({D with maskRestriction := P.semantic}.pair 1).leftArray.size ≤ n)
    (hcopy : (12 * n + 32) *
      2 ^ (Nat.clog 2 ({D with maskRestriction := P.semantic}.pair 1).leftArray.size + 1) ≤ B) :
    (collect D F P hF B fuel₀ fuel₁ control).2 ≤
      2 * inputScale D.input ^ 9 * (C + 1) + 5 + inputScale D.input ^ 6 *
        (({D with maskRestriction := P.semantic}.collect B).state.queries +
          ({D with maskRestriction := P.semantic}.collect B).state.reports + 1) +
        B * ({D with maskRestriction := P.semantic}.collect B).state.copies := by
  have hleft := PreparedReaderContext.build_work D F P hF 0 C hn (hl 0) (hr 0) hC
  have hright := PreparedReaderContext.build_work D F P hF 1 C hn (hl 1) (hr 1) hC
  have hjoin := StoredParentExecution.collect_work {D with maskRestriction := P.semantic}
    F hF B hn hd₀ hd₁ hcopy
  subst fuel₀
  subst fuel₁
  subst control
  simp only [collect, PreparedReaderContext.build_value]
  change (PreparedReaderContext.build D F P hF 0).2 +
    (PreparedReaderContext.build D F P hF 1).2 +
    (StoredParentExecution.collect {D with maskRestriction := P.semantic} F hF B).2 + 5 ≤ _
  dsimp only at hjoin
  simp only [Nat.mul_assoc]
  omega

end LowSpaceSubsetSum.PreparedParentExecution

end OAI
