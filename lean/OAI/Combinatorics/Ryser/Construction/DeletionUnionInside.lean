import OAI.Combinatorics.Ryser.Construction.DeletionUnionBasic

namespace OAI

noncomputable section

namespace RyserCoveringCounterexample.Construction

variable {k F : Type*} [Field k] [Field F]
variable [Fintype k] [Fintype F] [DecidableEq k] [DecidableEq F]

theorem card_deletedLines_through_le (σ : k →+* F) (M : PlaneLinearMap F)
    (b : Point F) (a : GadgetOutcome k) (p : Point F) :
    ((deletedLines σ M b a).filter (fun ell => Incidence p ell)).card ≤
      Fintype.card k - 1 := by
  calc
    ((deletedLines σ M b a).filter (fun ell => Incidence p ell)).card ≤
        (alteredDirections σ M).card := by
      apply Finset.card_le_card_of_injOn (fun ell : AffineLine F => ell.1)
      · intro ell hell
        exact ((mem_deletedLines σ M b a ell).mp (Finset.mem_filter.mp hell).1).1
      · intro ell hell m hm hdir
        exact line_eq_of_direction_eq_of_incidence hdir
          (Finset.mem_filter.mp hell).2 (Finset.mem_filter.mp hm).2
    _ = Fintype.card k - 1 := card_alteredDirections σ M

variable {G : Type*} [Fintype G] [DecidableEq G]

theorem deletedPencil_eq_filter_of_mem_placedSubplane
    (σ : k →+* F) (M : G → PlaneLinearMap F) (b : G → Point F)
    (a : GadgetOutcome k) (hsep : DeletionSeparated σ M b a)
    (i : G) (p : Point F) (hp : p ∈ placedSubplane σ (M i) (b i)) :
    deletedPencil σ M b a p =
      (deletedLines σ (M i) (b i) a).filter (fun ell => Incidence p ell) := by
  ext ell
  constructor
  · intro hell
    obtain ⟨hglobal, hinc⟩ := (mem_deletedPencil σ M b a p ell).mp hell
    obtain ⟨j, hj⟩ := (mem_allDeletedLines σ M b a ell).mp hglobal
    by_cases hij : i = j
    · subst j
      exact Finset.mem_filter.mpr ⟨hj, hinc⟩
    · exact (not_incidence_deletedLines_of_mem_other_subplane
        σ M b a hsep hij hp hj hinc).elim
  · intro hell
    obtain ⟨hlocal, hinc⟩ := Finset.mem_filter.mp hell
    exact (mem_deletedPencil σ M b a p ell).mpr
      ⟨(mem_allDeletedLines σ M b a ell).mpr ⟨i, hlocal⟩, hinc⟩

theorem card_deletedPencil_le_of_mem_placedSubplane
    (σ : k →+* F) (M : G → PlaneLinearMap F) (b : G → Point F)
    (a : GadgetOutcome k) (hsep : DeletionSeparated σ M b a)
    (i : G) (p : Point F) (hp : p ∈ placedSubplane σ (M i) (b i)) :
    (deletedPencil σ M b a p).card ≤ Fintype.card k - 1 := by
  rw [deletedPencil_eq_filter_of_mem_placedSubplane σ M b a hsep i p hp]
  exact card_deletedLines_through_le σ (M i) (b i) a p

end RyserCoveringCounterexample.Construction

end

end OAI
