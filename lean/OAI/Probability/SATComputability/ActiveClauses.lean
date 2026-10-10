import OAI.Probability.SATComputability.ClassMasks

namespace OAI

namespace FixedClauseThreshold.Computability

open scoped Classical

abbrev IncidentClass (n : ℕ) :=
  (Fin 3 × SignedLiteral n × SignedLiteral n) ⊕ (Fin 3 × SignedLiteral n) ⊕ Unit
abbrev ActiveClause (n : ℕ) := Triple (SignedLiteral n) ⊕ Bool × IncidentClass n

def activeClass {n : ℕ} : ActiveClause n → TripleClasses (SignedLiteral n)
  | .inl c => .inl c
  | .inr (b,.inl (i,c,d)) => .inr (.inl (i,b,c,d))
  | .inr (b,.inr (.inl (i,c))) => .inr (.inr (.inl (i,b,b,c)))
  | .inr (b,.inr (.inr _)) => .inr (.inr (.inr (b,b,b)))

theorem activeClass_injective (n : ℕ) : Function.Injective (activeClass (n := n)) := by
  intro c d h
  rcases c with c | ⟨b,c | (c | c)⟩ <;>
    rcases d with d | ⟨a,d | (d | d)⟩ <;>
    simp_all [activeClass]
  all_goals exact Prod.ext h.1 h.2.2

noncomputable def incidentMask {n : ℕ} : IncidentClass n → Finset (DeletionCandidate n)
  | .inl (_,c,d) => clauseMask ![c,d]
  | .inr _ => ∅

noncomputable def strongerClassMask {n : ℕ} : ActiveClause n → Finset (DeletionCandidate (n+1))
  | .inl c => restoredMask (clauseMask ((tripleVectorEquiv _).symm c)) Finset.univ Finset.univ
  | .inr (false,c) => restoredMask Finset.univ Finset.univ (incidentMask c)
  | .inr (true,c) => restoredMask Finset.univ (incidentMask c) Finset.univ

theorem restoredMask_mono {n : ℕ}
    {B F T B' F' T' : Finset (DeletionCandidate n)}
    (hB : B ⊆ B') (hF : F ⊆ F') (hT : T ⊆ T') :
    restoredMask B F T ⊆ restoredMask B' F' T' := by
  intro x hx
  obtain ⟨hb,hx⟩ := (Finset.mem_filter.mp hx).2
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _,hB hb,?_⟩
  rcases h0 : x 0 with _ | (_ | _)
  · trivial
  · exact hF (by simpa only [h0] using hx)
  · exact hT (by simpa only [h0] using hx)

theorem strongerClassMask_subset {n : ℕ} (c : ActiveClause n) :
    strongerClassMask c ⊆ clauseMask (classClause (activeClass c)) := by
  rw [classClause_restored]
  rcases c with c | ⟨b,c | (⟨i,c⟩ | u)⟩
  · exact Finset.Subset.refl _
  · rcases c with ⟨i,c,d⟩
    cases b <;> exact Finset.Subset.refl _
  · cases b <;>
      simp only [strongerClassMask, activeClass, classBaseMask, classIncidentMask,
        Bool.false_eq_true, Bool.true_eq_false, or_self, ite_true, ite_false, incidentMask]
    all_goals apply restoredMask_mono <;> first | exact Finset.Subset.refl _ | exact Finset.empty_subset _
  · cases b <;> exact Finset.Subset.refl _

theorem inactiveClass_trivial {n : ℕ} (c : TripleClasses (SignedLiteral n))
    (hc : c ∉ Set.range (activeClass (n := n))) :
    clauseMask (classClause c) = Finset.univ := by
  rcases c with c | (⟨i,b,c,d⟩ | (⟨i,a,b,c⟩ | ⟨a,b,c⟩))
  · exact False.elim (hc ⟨.inl c,rfl⟩)
  · exact False.elim (hc ⟨.inr (b,.inl (i,c,d)),rfl⟩)
  · by_cases hab : a = b
    · subst b
      exact False.elim (hc ⟨.inr (a,.inr (.inl (i,c))),rfl⟩)
    · rw [classClause_restored_double]
      clear hc
      cases a <;> cases b <;> try contradiction
      all_goals
        ext x
        rcases h0 : x 0 with _ | (_ | _)
        all_goals simp [classBaseMask, classIncidentMask, restoredMask, h0]
  · by_cases habc : a = b ∧ b = c
    · rcases habc with ⟨hab,hbc⟩
      subst b
      subst c
      exact False.elim (hc ⟨.inr (a,.inr (.inr ())),rfl⟩)
    · rw [classClause_restored_triple]
      clear hc
      cases a <;> cases b <;> cases c <;> try simp_all
      all_goals
        ext x
        rcases h0 : x 0 with _ | (_ | _)
        all_goals simp [classBaseMask, classIncidentMask, restoredMask, h0]

end FixedClauseThreshold.Computability

end OAI
