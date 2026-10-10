import OAI.Analysis.LipschitzEquivalence.CompactReduction

namespace OAI

noncomputable section
open scoped BigOperators InnerProductSpace Topology ENNReal
open scoped Topology ENNReal NNReal
open scoped Classical ENNReal NNReal InnerProductSpace Topology
open Filter Set
open scoped NNReal Topology
open Filter Set

namespace LipschitzCounterexample.SeparatingStages
open LocalGeometry LocalizedLinearization

theorem D_localOrthogonality : LocalOrthogonality D := by
  intro I _ x hx
  obtain ⟨r,hr,l,S,hS,_,hD⟩ := D_local_orthogonality x hx
  refine ⟨r,hr,l,S,hS,fun i y hy => ?_⟩
  have he : CoordinateSpaces.tail l (D y) = HilbertSlots.tailCLM l (D y) := by
    apply lp.ext
    funext n
    apply PiLp.ext
    intro a
    rw [CoordinateSpaces.tail_coord,HilbertSlots.tailCLM_coord]
    split_ifs <;> rfl
  rw [he]
  exact hD i y hy

theorem q_completelyContinuous : WeakSequences.CompletelyContinuous q :=
  completely_continuous_of_compact_reduction FreeSpace.hasCompactReduction D
    D_lipschitz D_zero D_localOrthogonality

theorem main_of_free_wsc
    (hW : WeakSequences.WeakSequentiallyComplete (FreeSpace.Space M)) : MainClaim :=
  Criterion.assemble q h (fun x => q_point x) h_zero h_lipschitz h_symm_lipschitz q_norm hW
    q_completelyContinuous

end LipschitzCounterexample.SeparatingStages

end

end OAI
