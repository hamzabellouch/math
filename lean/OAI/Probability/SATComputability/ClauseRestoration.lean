import OAI.Probability.SATComputability.RestoredCandidates

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass
open scoped Classical

noncomputable def clauseMask {n k : ℕ} (c : Fin k → SignedLiteral n) :
    Finset (DeletionCandidate n) :=
  Finset.univ.filter (fun x => ¬∀ l, literalFalse x (c l))

def liftLiteral {n : ℕ} (l : SignedLiteral n) : SignedLiteral (n+1) := (l.1.succ,l.2)

def touchesDistinguished {n k : ℕ} (c : Fin k → SignedLiteral (n+1)) : Prop :=
  ∃ l, (c l).1 = 0

noncomputable def baseClauseMask {n k : ℕ} (c : Fin k → SignedLiteral (n+1)) :
    Finset (DeletionCandidate n) :=
  if touchesDistinguished c then Finset.univ else
    Finset.univ.filter (fun x => restoreCandidate none x ∈ clauseMask c)

noncomputable def incidentClauseMask {n k : ℕ} (c : Fin k → SignedLiteral (n+1))
    (b : Bool) : Finset (DeletionCandidate n) :=
  if touchesDistinguished c then
    Finset.univ.filter (fun x => restoreCandidate (some b) x ∈ clauseMask c)
  else Finset.univ

theorem literalFalse_lift {n : ℕ} (x : DeletionCandidate (n+1)) (l : SignedLiteral n) :
    literalFalse x (liftLiteral l) ↔ literalFalse (Fin.tail x) l := Iff.rfl

theorem clauseMask_lift {n k : ℕ} (x : DeletionCandidate (n+1))
    (c : Fin k → SignedLiteral n) :
    x ∈ clauseMask (fun l => liftLiteral (c l)) ↔ Fin.tail x ∈ clauseMask c := by
  simp only [clauseMask, Finset.mem_filter, Finset.mem_univ, true_and, literalFalse_lift]

theorem clauseMask_forget_zero {n k : ℕ} (c : Fin k → SignedLiteral (n+1))
    (hc : ¬ touchesDistinguished c) (x : DeletionCandidate (n+1)) (b : Option Bool) :
    restoreCandidate b (Fin.tail x) ∈ clauseMask c ↔ x ∈ clauseMask c := by
  have hn (l : Fin k) : (c l).1 ≠ 0 := fun h => hc ⟨l,h⟩
  have hl (l : Fin k) :
      literalFalse (restoreCandidate b (Fin.tail x)) (c l) ↔ literalFalse x (c l) := by
    obtain ⟨j,hj⟩ := Fin.exists_succ_eq_of_ne_zero (hn l)
    simp only [literalFalse, restoreCandidate, ← hj, Fin.cons_succ, Fin.tail_def]
  simp only [clauseMask, Finset.mem_filter, Finset.mem_univ, true_and, hl]

theorem clauseMask_deleted_zero {n k : ℕ} (c : Fin k → SignedLiteral (n+1))
    (hc : touchesDistinguished c) (x : DeletionCandidate n) :
    restoreCandidate none x ∈ clauseMask c := by
  obtain ⟨l,hl⟩ := hc
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  intro h
  have he := h l
  simp [literalFalse, restoreCandidate, hl] at he

theorem clauseMask_restored {n k : ℕ} (c : Fin k → SignedLiteral (n+1)) :
    clauseMask c = restoredMask (baseClauseMask c)
      (incidentClauseMask c false) (incidentClauseMask c true) := by
  ext x
  by_cases hc : touchesDistinguished c
  · simp only [baseClauseMask, incidentClauseMask, ite_eq_left hc, restoredMask,
      Finset.mem_filter, Finset.mem_univ, true_and]
    have he : restoreCandidate (x 0) (Fin.tail x) = x := Fin.cons_self_tail x
    cases hx : x 0 with
    | none =>
      apply iff_true_intro
      have hm := clauseMask_deleted_zero c hc (Fin.tail x)
      have he' : restoreCandidate none (Fin.tail x) = x := by simpa only [hx] using he
      exact he' ▸ hm
    | some b =>
      have he' : restoreCandidate (some b) (Fin.tail x) = x := by
        simpa only [hx] using he
      cases b
      · change (x ∈ clauseMask c) ↔ (restoreCandidate (some false) (Fin.tail x) ∈ clauseMask c)
        exact (congrArg (fun y => y ∈ clauseMask c) he').symm.to_iff
      · change (x ∈ clauseMask c) ↔ (restoreCandidate (some true) (Fin.tail x) ∈ clauseMask c)
        exact (congrArg (fun y => y ∈ clauseMask c) he').symm.to_iff

  · have he := clauseMask_forget_zero c hc x none
    simp only [baseClauseMask, incidentClauseMask, ite_eq_right hc, restoredMask,
      Finset.mem_filter, Finset.mem_univ, true_and]
    cases x 0 with
    | none => simpa only [and_true] using he.symm
    | some b =>
      cases b <;> simpa only [and_true] using he.symm

end FixedClauseThreshold.Computability

end OAI
