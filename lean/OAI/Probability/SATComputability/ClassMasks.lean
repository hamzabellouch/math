import OAI.Probability.SATComputability.ClauseClasses

namespace OAI

namespace FixedClauseThreshold.Computability

open scoped Classical

def classClause {n : ℕ} (c : TripleClasses (SignedLiteral n)) : Fin 3 → SignedLiteral (n+1) :=
  (clauseClassesEquiv n).symm c

noncomputable def classBaseMask {n : ℕ} : TripleClasses (SignedLiteral n) → Finset (DeletionCandidate n)
  | .inl c => clauseMask ((tripleVectorEquiv _).symm c)
  | .inr _ => Finset.univ

noncomputable def classIncidentMask {n : ℕ} (v : Bool) :
    TripleClasses (SignedLiteral n) → Finset (DeletionCandidate n)
  | .inl _ => Finset.univ
  | .inr (.inl (_,b,c,d)) => if v = b then Finset.univ else clauseMask ![c,d]
  | .inr (.inr (.inl (_,a,b,c))) => if v = a ∨ v = b then Finset.univ else clauseMask ![c]
  | .inr (.inr (.inr (a,b,c))) => if v = a ∨ v = b ∨ v = c then Finset.univ else ∅

theorem classClause_base {n : ℕ} (c : Triple (SignedLiteral n)) :
    classClause (.inl c) = fun j => liftLiteral ((tripleVectorEquiv _).symm c j) := by
  funext j
  fin_cases j <;> rfl

theorem literalFalse_distinguished {n : ℕ} (x : DeletionCandidate n) (v : Option Bool) (b : Bool) :
    literalFalse (restoreCandidate v x) (0,b) ↔ v = some (!b) := Iff.rfl

theorem literalFalse_restored {n : ℕ} (x : DeletionCandidate n) (v : Option Bool)
    (l : SignedLiteral n) :
    literalFalse (restoreCandidate v x) (liftLiteral l) ↔ literalFalse x l := Iff.rfl

theorem classClause_restored_base {n : ℕ} (c : Triple (SignedLiteral n)) :
    clauseMask (classClause (.inl c)) = restoredMask (classBaseMask (.inl c))
      (classIncidentMask false (.inl c)) (classIncidentMask true (.inl c)) := by
  rw [classClause_base]
  ext x
  simp only [clauseMask_lift, classBaseMask, classIncidentMask, restoredMask,
    Finset.mem_filter, Finset.mem_univ, true_and]
  cases x 0 with
  | none => simp
  | some b => cases b <;> simp

theorem classClause_restored_single {n : ℕ} (i : Fin 3) (b : Bool)
    (c d : SignedLiteral n) :
    clauseMask (classClause (.inr (.inl (i,b,c,d)))) =
      restoredMask (classBaseMask (.inr (.inl (i,b,c,d))))
        (classIncidentMask false (.inr (.inl (i,b,c,d))))
        (classIncidentMask true (.inr (.inl (i,b,c,d)))) := by
  ext x
  have hx : restoreCandidate (x 0) (Fin.tail x) = x := Fin.cons_self_tail x
  conv_lhs => rw [← hx]
  fin_cases i <;> cases b <;> rcases h0 : x 0 with _ | (_ | _)
  all_goals simp [classClause, clauseClassesEquiv, tripleClassesEquiv, joinTriple,
    tripleVectorEquiv, literalSplitEquiv, Equiv.arrowCongr, classBaseMask,
    classIncidentMask, restoredMask, clauseMask, literalFalse, restoreCandidate,
    Fin.forall_fin_succ, Fin.tail_def, h0, Bool.not_false, Bool.not_true]

theorem classClause_restored_double {n : ℕ} (i : Fin 3) (a b : Bool)
    (c : SignedLiteral n) :
    clauseMask (classClause (.inr (.inr (.inl (i,a,b,c))))) =
      restoredMask (classBaseMask (.inr (.inr (.inl (i,a,b,c)))))
        (classIncidentMask false (.inr (.inr (.inl (i,a,b,c)))))
        (classIncidentMask true (.inr (.inr (.inl (i,a,b,c))))) := by
  ext x
  have hx : restoreCandidate (x 0) (Fin.tail x) = x := Fin.cons_self_tail x
  conv_lhs => rw [← hx]
  fin_cases i <;> cases a <;> cases b <;> rcases h0 : x 0 with _ | (_ | _)
  all_goals simp [classClause, clauseClassesEquiv, tripleClassesEquiv, joinTriple,
    tripleVectorEquiv, literalSplitEquiv, Equiv.arrowCongr, classBaseMask,
    classIncidentMask, restoredMask, clauseMask, literalFalse, restoreCandidate,
    Fin.forall_fin_succ, Fin.tail_def, h0, Bool.not_false, Bool.not_true]

theorem classClause_restored_triple {n : ℕ} (a b c : Bool) :
    clauseMask (classClause (n := n) (.inr (.inr (.inr (a,b,c))))) =
      restoredMask (classBaseMask (.inr (.inr (.inr (a,b,c)))))
        (classIncidentMask false (.inr (.inr (.inr (a,b,c)))))
        (classIncidentMask true (.inr (.inr (.inr (a,b,c))))) := by
  ext x
  have hx : restoreCandidate (x 0) (Fin.tail x) = x := Fin.cons_self_tail x
  conv_lhs => rw [← hx]
  cases a <;> cases b <;> cases c <;> rcases h0 : x 0 with _ | (_ | _)
  all_goals simp [classClause, clauseClassesEquiv, tripleClassesEquiv, joinTriple,
    tripleVectorEquiv, literalSplitEquiv, Equiv.arrowCongr, classBaseMask,
    classIncidentMask, restoredMask, clauseMask, literalFalse, restoreCandidate,
    Fin.forall_fin_succ, Fin.tail_def, h0, Bool.not_false, Bool.not_true]

theorem classClause_restored {n : ℕ} (c : TripleClasses (SignedLiteral n)) :
    clauseMask (classClause c) = restoredMask (classBaseMask c)
      (classIncidentMask false c) (classIncidentMask true c) := by
  rcases c with c | (⟨i,b,c,d⟩ | (⟨i,a,b,c⟩ | ⟨a,b,c⟩))
  · exact classClause_restored_base c
  · exact classClause_restored_single i b c d
  · exact classClause_restored_double i a b c
  · exact classClause_restored_triple a b c

end FixedClauseThreshold.Computability

end OAI
