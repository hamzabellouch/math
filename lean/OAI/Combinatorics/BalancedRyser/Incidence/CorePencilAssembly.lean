import Mathlib.Tactic
import OAI.Combinatorics.BalancedRyser.Incidence.AffineMomentAlgebraLemmas
import OAI.Combinatorics.BalancedRyser.Incidence.CorePencil
import OAI.Combinatorics.BalancedRyser.Incidence.CorePencilReduction

namespace OAI

namespace Balanced
open scoped _root_.Balanced

universe u

namespace CorePencilAssembly

variable {F : Type u} [Field F] [Fintype F] [DecidableEq F]

theorem eventProbability_mono {k : ℕ} (Q : PMF (DeletionSet F k))
    {E E' : DeletionSet F k → Prop} (h : ∀ D, E D → E' D) :
    deletionEventProbability Q E ≤ deletionEventProbability Q E' := by
  classical
  unfold deletionEventProbability
  apply Finset.sum_le_sum
  intro D _
  by_cases hD : E D
  · simp [hD, h D hD]
  · simp only [ite_eq_right hD]
    split_ifs
    · exact ENNReal.toReal_nonneg
    · exact le_rfl

end CorePencilAssembly

theorem corePencilResult_of_robustDeletion_primeStability
    (hdeletion : RobustDeletionResult.{u}) (hstable : PrimeStability.{u}) :
    CorePencilResult.{u} := by
  intro k hk K hK ζ hζ ε hε
  have hδ : 0 < stabilityDensity ζ := StabilityArithmetic.delta_pos hζ
  obtain ⟨N, hN⟩ := (hdeletion k hk K hK).2.2 (stabilityDensity ζ) hδ ε hε
  obtain ⟨M, hM⟩ := exists_nat_ge (max (100 : ℝ) (4 / ζ))
  refine ⟨max N M, ?_⟩
  intro F _ _ _ hprime hq hkq Q hQ
  have hNq : N ≤ Fintype.card F := (le_max_left N M).trans hq
  have hMq : M ≤ Fintype.card F := (le_max_right N M).trans hq
  have hlarge : max (100 : ℝ) (4 / ζ) ≤ (Fintype.card F : ℝ) :=
    hM.trans (Nat.cast_le.mpr hMq)
  calc
    deletionEventProbability Q (fun D => ¬ CorePencilEvent ζ D.val) ≤
        deletionEventProbability Q (fun D => BadCoreCover (stabilityDensity ζ) D.val) := by
      apply CorePencilAssembly.eventProbability_mono
      intro D hD
      exact corePencilFailure_subset_nearCoverFailure hstable hprime hζ hlarge hD
    _ < ε := hN F hNq hkq Q hQ

end Balanced

end OAI
