import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Lean.Elab.Tactic.Omega

namespace OAI

namespace SeymourSecondNeighborhood

variable {V : Type*} [DecidableEq V]

theorem strict_deficit_of_augmentation (E : Finset V) (hE : E.Nonempty)
    (g : Finset V → ℕ) (hempty : g ∅ = 0)
    (step : ∀ T : Finset V, T ⊆ E → T ≠ E →
      ∃ Q : Finset V, Q.Nonempty ∧ Q ⊆ E \ T ∧
        g (T ∪ Q) < g T + Q.card) :
    g E < E.card := by
  classical
  let feasible := E.powerset.filter fun T => T = ∅ ∨ g T < T.card
  have hfeasible : feasible.Nonempty := by
    refine ⟨∅, ?_⟩
    simp [feasible]
  obtain ⟨T, hT, hmax⟩ := Finset.exists_max_image feasible Finset.card hfeasible
  have hTE : T ⊆ E := Finset.mem_powerset.mp (Finset.mem_filter.mp hT).1
  have hinvariant : T = ∅ ∨ g T < T.card := (Finset.mem_filter.mp hT).2
  have hgle : g T ≤ T.card := by
    rcases hinvariant with ht | ht
    · subst T
      simp [hempty]
    · exact Nat.le_of_lt ht
  have heq : T = E := by
    by_contra hne
    obtain ⟨Q, hQnonempty, hQ, hstep⟩ := step T hTE hne
    have hdisjoint : Disjoint T Q := by
      apply Finset.disjoint_left.mpr
      intro v hvT hvQ
      exact (Finset.mem_sdiff.mp (hQ hvQ)).2 hvT
    have hcard : (T ∪ Q).card = T.card + Q.card :=
      Finset.card_union_of_disjoint hdisjoint
    have hunion : T ∪ Q ⊆ E := by
      intro v hv
      rcases Finset.mem_union.mp hv with hv | hv
      · exact hTE hv
      · exact (Finset.mem_sdiff.mp (hQ hv)).1
    have hstrict : g (T ∪ Q) < (T ∪ Q).card := by
      rw [hcard]
      omega
    have hnew : T ∪ Q ∈ feasible := by
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_powerset.mpr hunion, Or.inr hstrict⟩
    have hmax' := hmax (T ∪ Q) hnew
    have hpos : 0 < Q.card := Finset.card_pos.mpr hQnonempty
    omega
  rcases hinvariant with hempty' | hstrict
  · have : E = ∅ := heq.symm.trans hempty'
    exact (hE.ne_empty this).elim
  · simpa only [heq] using hstrict

end SeymourSecondNeighborhood

end OAI
