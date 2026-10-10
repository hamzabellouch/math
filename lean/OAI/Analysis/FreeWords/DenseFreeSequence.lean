import Mathlib
import OAI.Analysis.FreeWords.CenteredMatrixDensity
import OAI.Analysis.FreeWords.CountableFreeLift
import OAI.Analysis.FreeWords.DenseFreeSequenceDefinitions

namespace OAI

noncomputable section

namespace KKFreeLiftFrontier

open KKTraceTransfer Filter Topology

noncomputable section

theorem dense_test_matrix_free_sequence : DenseTestMatrixFreeSequence := by
  intro H _ _ _ _ _ M τ hfac hdiff n hn
  classical
  obtain ⟨a,ha,hb,hd⟩ := centered_matrix_countable_dense M τ n
  let Code := {w : List (ℤ × ℕ) // w ≠ [] ∧ ∀ z ∈ w, z.1 ≠ 0}
  have : Nonempty Code := ⟨⟨[(1,0)],by simp⟩⟩
  obtain ⟨e,he⟩ := exists_surjective_nat Code
  let T (i:ℕ) : List (ℤ × MatrixAlgebra n M) :=
    (e i).val.map (fun z => (z.1,a z.2))
  have hT (i:ℕ) : IsCenteredTest τ (T i) := by
    constructor
    · intro hz
      exact (e i).property.1 (List.map_eq_nil_iff.mp hz)
    · intro z hz
      obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hz
      exact ⟨(e i).property.2 v hv,ha v.2⟩
  obtain ⟨d,hd',ρ,hρ,U,hU,hH,hM⟩ :=
    countable_matrix_free_approximation H M τ hfac hdiff n hn T hT
  refine ⟨a,ha,hb,hd,d,hd',ρ,hρ,U,hU,hH,?_⟩
  intro w hw hk
  obtain ⟨i,hi⟩ := he ⟨w,hw,hk⟩
  simpa only [T,hi] using hM i

end

end KKFreeLiftFrontier
end

end OAI
