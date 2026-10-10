import OAI.Combinatorics.Ryser.Domination.Basic

namespace OAI

namespace RyserCoveringCounterexample.Selection

variable {V ι : Type*} [instDecidableEqV : DecidableEq V] [DecidableEq ι]
variable {G : Graph V} {pool : V → ι}

theorem transversal_insert_new {J : Finset ι} {U : Finset V} {root : ι} {x : V}
    (hU : IsTransversalOn G pool J U) (hroot : root ∉ J)
    (hpool : pool x = root) (hfree : ∀ y ∈ U, ¬ G.Adj x y) :
    IsTransversalOn G pool (insert root J) (insert x U) := by
  have hpool_ne (y : V) (hy : y ∈ U) : pool y ≠ root := by
    intro heq
    apply hroot
    rw [← hU.2.2]
    exact Finset.mem_image.mpr ⟨y, hy, heq⟩
  refine ⟨?_, ?_, ?_⟩
  · intro a ha b hb
    rcases Finset.mem_insert.mp ha with rfl | haU
    · rcases Finset.mem_insert.mp hb with rfl | hbU
      · exact G.irrefl
      · exact hfree b hbU
    · rcases Finset.mem_insert.mp hb with rfl | hbU
      · intro hab
        exact hfree a haU hab.symm
      · exact hU.1 a haU b hbU
  · intro a ha b hb hab
    change a ∈ insert x U at ha
    change b ∈ insert x U at hb
    rcases Finset.mem_insert.mp ha with rfl | haU
    · rcases Finset.mem_insert.mp hb with rfl | hbU
      · rfl
      · exact (hpool_ne b hbU (hab.symm.trans hpool)).elim
    · rcases Finset.mem_insert.mp hb with rfl | hbU
      · exact (hpool_ne a haU (hab.trans hpool)).elim
      · exact hU.2.1 haU hbU hab
  · rw [Finset.image_insert, hU.2.2, hpool]

theorem exists_unextendable_transversal [Fintype ι]
    (hfull : ¬ ∃ U : Finset V, IsTransversalOn G pool Finset.univ U) :
    ∃ root : ι, ∃ J : Finset ι, ∃ U : Finset V,
      root ∉ J ∧ IsTransversalOn G pool J U ∧
        ¬ ∃ U' : Finset V, IsTransversalOn G pool (insert root J) U' := let _ := instDecidableEqV; by
  classical
  let candidates : Finset (Finset ι) :=
    Finset.univ.filter (fun J => ∃ U : Finset V, IsTransversalOn G pool J U)
  have hempty : (∅ : Finset ι) ∈ candidates := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ∅, ?_⟩
    simp [IsTransversalOn, Set.InjOn]
  obtain ⟨J, hJ, hmax⟩ := Finset.exists_max_image candidates
    (fun J : Finset ι => J.card) ⟨∅, hempty⟩
  obtain ⟨U, hU⟩ := (Finset.mem_filter.mp hJ).2
  have hJne : J ≠ Finset.univ := by
    intro heq
    apply hfull
    exact ⟨U, heq ▸ hU⟩
  obtain ⟨root, hroot⟩ : ∃ root : ι, root ∉ J := by
    by_contra hnone
    apply hJne
    apply Finset.eq_univ_iff_forall.mpr
    intro i
    by_contra hi
    exact hnone ⟨i, hi⟩
  refine ⟨root, J, U, hroot, hU, ?_⟩
  intro hExt
  have hmem : insert root J ∈ candidates :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hExt⟩
  have hle := hmax (insert root J) hmem
  rw [Finset.card_insert_of_notMem hroot] at hle
  exact Nat.not_succ_le_self J.card hle

end RyserCoveringCounterexample.Selection

end OAI
