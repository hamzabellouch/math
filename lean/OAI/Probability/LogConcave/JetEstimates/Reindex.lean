import Mathlib
import OAI.Probability.LogConcave.JetEstimates.AllSplitBound

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

section UpperProof
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
open Function MeasureTheory Set Filter
open scoped Topology NNReal

namespace LogConcaveSampling.TensorEnergy
open scoped Classical

universe u
variable {S R : Type u} [Fintype S] [Fintype R] {d : ℕ}

lemma AllSplitBound.reindex {T : (S → Fin d) → ℝ} {M : ℝ}
    (hT : AllSplitBound T M) (e : S ≃ R) :
    AllSplitBound (fun a : R → Fin d => T (a ∘ e)) M := by
  intro I O _ _ _ _ _ _ f
  exact hT I O (e.trans f)

lemma allSplitBound_reindex_iff {T : (S → Fin d) → ℝ} {M : ℝ} (e : S ≃ R) :
    AllSplitBound (fun a : R → Fin d => T (a ∘ e)) M ↔ AllSplitBound T M := by
  constructor
  · intro h
    simpa only [Function.comp_def,Equiv.symm_apply_apply] using h.reindex e.symm
  · intro h
    exact h.reindex e
end LogConcaveSampling.TensorEnergy

end UpperProof
end
end
end

end OAI
