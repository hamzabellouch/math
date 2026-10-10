import OAI.Probability.SATComputability.ActiveClauses
import OAI.Probability.SATComputability.PoissonMaskCounts

namespace OAI

namespace FixedClauseThreshold.Computability

open scoped Classical

theorem countsMask_mono {A X : Type*} [Fintype A] [Fintype X]
    {f g : A → Finset X} (h : ∀ a, f a ⊆ g a) (c : A → ℕ) :
    countsMask f c ⊆ countsMask g c := by
  intro x hx
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _,?_⟩
  intro a
  exact ((Finset.mem_filter.mp hx).2 a).imp_right (fun hx => h a hx)

theorem countsMask_equiv {A B X : Type*} [Fintype A] [Fintype B] [Fintype X]
    (e : A ≃ B) (f : B → Finset X) (c : A → ℕ) :
    countsMask (f ∘ e) c = countsMask f (c ∘ e.symm) := by
  ext x
  simp only [countsMask, Finset.mem_filter, Finset.mem_univ, true_and, Function.comp_def]
  constructor
  · intro h b
    simpa only [Equiv.apply_symm_apply] using h (e.symm b)
  · intro h a
    simpa only [Equiv.symm_apply_apply] using h (e a)

theorem countsMask_active {n : ℕ} (c : TripleClasses (SignedLiteral n) → ℕ) :
    countsMask (fun a => clauseMask (classClause (activeClass a))) (c ∘ activeClass) =
      countsMask (fun a => clauseMask (classClause a)) c := by
  ext x
  simp only [countsMask, Finset.mem_filter, Finset.mem_univ, true_and, Function.comp_def]
  constructor
  · intro h a
    by_cases ha : a ∈ Set.range (activeClass (n := n))
    · obtain ⟨b,rfl⟩ := ha
      exact h b
    · exact Or.inr (by rw [inactiveClass_trivial a ha]; exact Finset.mem_univ _)
  · intro h a
    exact h (activeClass a)

theorem countsMask_stronger {n : ℕ} (c : ActiveClause n → ℕ) :
    countsMask strongerClassMask c =
      restoredMask
        (countsMask (fun a => clauseMask ((tripleVectorEquiv _).symm a)) (fun a => c (.inl a)))
        (countsMask incidentMask (fun a => c (.inr (true,a))))
        (countsMask incidentMask (fun a => c (.inr (false,a)))) := by
  ext x
  rcases h0 : x 0 with _ | (_ | _)
  all_goals
    simp [countsMask, strongerClassMask, restoredMask, Sum.forall, Prod.forall,
      Bool.forall_bool, h0]

end FixedClauseThreshold.Computability

end OAI
