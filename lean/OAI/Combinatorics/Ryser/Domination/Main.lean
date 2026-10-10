import OAI.Combinatorics.Ryser.Domination.Extension
import OAI.Combinatorics.Ryser.Domination.Seed

namespace OAI

namespace RyserCoveringCounterexample.Selection

variable {V ι : Type*} [DecidableEq V] [DecidableEq ι]

theorem domination_certificate_of_no_transversal [Fintype V] [Fintype ι]
    (G : Graph V) (pool : V → ι) (hpool : Function.Surjective pool)
    (hno : ¬ ∃ U, IsTransversalOn G pool Finset.univ U) :
    DominationCertificate G pool := by
  classical
  by_contra hnocert
  obtain ⟨root, J, U, hroot, hU, hnoJ⟩ := exists_unextendable_transversal hno
  obtain ⟨v, hv⟩ := hpool root
  have htraces : ∀ k, Nonempty (DominationTrace G pool J root k) := by
    intro k
    induction k with
    | zero => exact ⟨DominationTrace.empty v hU⟩
    | succ k ih =>
      obtain ⟨t⟩ := ih
      exact t.extend hroot hnoJ hnocert
  obtain ⟨t⟩ := htraces (Fintype.card V + 1)
  exact Nat.not_succ_le_self (Fintype.card V) t.length_le_card

theorem domination_of_no_transversal [Fintype V] [Fintype ι]
    (G : Graph V) (pool : V → ι) (hpool : Function.Surjective pool)
    (hno : ¬ ∃ U, IsTransversalOn G pool Finset.univ U) :
    ∃ I : Finset ι, ∃ T : Finset V, I.Nonempty ∧
      T ⊆ Finset.univ.filter (fun x => pool x ∈ I) ∧
      T.card ≤ 2 * (I.card - 1) ∧ DominatesOn G pool I T := by
  obtain ⟨I, T, hI, hT, hcard, hdom⟩ :=
    domination_certificate_of_no_transversal G pool hpool hno
  refine ⟨I, T, hI, ?_, hcard, hdom⟩
  intro x hx
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hT x hx⟩

end RyserCoveringCounterexample.Selection

end OAI
