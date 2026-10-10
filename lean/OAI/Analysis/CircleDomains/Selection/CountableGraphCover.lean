import OAI.Analysis.CircleDomains.Transfer.GraphGridCells
import Mathlib.MeasureTheory.Measure.Hausdorff

namespace OAI

/-! Reindex a countable graph cover by the natural numbers without
changing its quadratic cost or increasing its diameter bound. -/
open Set Function MeasureTheory Metric Encodable
open scoped ENNReal
noncomputable section
namespace CircleDomainRigidity

lemma nat_graph_cover_of_countable {ι : Type*} [Countable ι]
    (T : ι → Set GraphSpace) {D : ℝ≥0∞} (hD : ∀ i, ediam (T i) ≤ D) :
    ∃ S : ℕ → Set GraphSpace,
      (⋃ i, T i) = (⋃ n, S n) ∧ (∀ n, ediam (S n) ≤ D) ∧
      (∑' n, ediam (S n)^2) = ∑' i, ediam (T i)^2 := by
  let : Encodable ι := Encodable.ofCountable ι
  let S : ℕ → Set GraphSpace := fun n => ⋃ i ∈ Encodable.decode₂ ι n, T i
  refine ⟨S,?_,?_,?_⟩
  · exact (iUnion_decode₂ T).symm
  · intro n
    rw [show S n = ⋃ i ∈ Encodable.decode₂ ι n, T i from rfl, ediam_iUnion_mem_option]
    exact iSup_le fun i => iSup_le fun _ => hD i
  · exact tsum_iUnion_decode₂ (fun A : Set GraphSpace => ediam A^2) (by simp) T

end CircleDomainRigidity

end

end OAI
