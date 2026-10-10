import OAI.Combinatorics.BalancedRyser.Probability.FiniteHistoryInvariant
import OAI.Combinatorics.BalancedRyser.Selection.SelectionHistory
import OAI.Combinatorics.BalancedRyser.Selection.SelectionState

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter

namespace Balanced.Selection.Process

variable {I V : Type*} [Fintype I] [Fintype V]

theorem ae_snapshot_state_invariant (p : Parameters) (q : ℕ) (G : Input I V) :
    ∀ᵐ ω ∂snapshotPathLaw p q G, ∀ t S, (ω t).1 = some S →
      StateInvariant G S ∧ S.remaining.card + t = Fintype.card I := by
  classical
  apply FiniteHistory.ae_all_invariant (fun t => snapshotPMF p q t G)
    initialSnapshot
    (fun t snap => ∀ S, snap.1 = some S →
      StateInvariant G S ∧ S.remaining.card + t = Fintype.card I)
  · intro S hS
    have heq : S = initialState := (Option.some.inj hS).symm
    subst S
    exact ⟨initialState_invariant G, by simp [initialState]⟩
  · intro t before out hpos hbefore S hout
    have hp : 0 < snapshotWeight p q t G before out := by
      have hn : snapshotWeight p q t G before out ≠ 0 := by
        intro hz
        apply hpos
        change ENNReal.ofReal (snapshotWeight p q t G before out) = 0
        rw [hz, ENNReal.ofReal_zero]
      exact lt_of_le_of_ne (snapshotWeight_nonnegative p q t G before out) (Ne.symm hn)
    obtain ⟨before, draw⟩ := before
    obtain ⟨out, draw'⟩ := out
    dsimp only at hout
    subst out
    cases before with
    | none =>
        rw [snapshotWeight_none_some] at hp
        exact False.elim (lt_irrefl 0 hp)
    | some S₀ =>
        obtain ⟨hinv, hcard⟩ := hbefore S₀ rfl
        refine ⟨positive_snapshotWeight_invariant p q t G S₀ S draw draw' hinv hp, ?_⟩
        have hstep := positive_snapshotWeight_card p q t G S₀ S draw draw' hp
        omega

theorem ae_snapshot_remaining_card (p : Parameters) (q : ℕ) (G : Input I V) :
    ∀ᵐ ω ∂snapshotPathLaw p q G, ∀ t S, (ω t).1 = some S →
      S.remaining.card = Fintype.card I - t := by
  filter_upwards [ae_snapshot_state_invariant p q G] with ω hω
  intro t S hS
  have h := (hω t S hS).2
  omega

end Balanced.Selection.Process

end

end OAI
