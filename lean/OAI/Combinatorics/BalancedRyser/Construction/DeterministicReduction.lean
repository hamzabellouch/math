import OAI.Combinatorics.BalancedRyser.Construction.ConfigurationRealizationBridge
import OAI.Combinatorics.BalancedRyser.Probability.NoSmallBlockCover

namespace OAI

namespace Balanced
open scoped _root_.Balanced

universe u

theorem deterministicReduction_proof : DeterministicReduction.{u} := by
  classical
  intro F _ _ _ C ρ B hq hρ0 hρ1 hV hC hO hCore hLocal hsize
  refine ⟨C.constructedHypergraph hV hC hq,
    C.constructedHypergraph_intersecting hV hC hq,
    C.constructedHypergraph_nonisolated hV hC hq hρ0 hO,
    ?_, C.constructedHypergraph_realization hV hC hq hρ1 hO hsize⟩
  apply C.constructedHypergraph_hasCoverNumber hV hC hq
  intro A hA hCover
  apply C.block_cover_card_lower_bound hV hC hρ0 hq hO hsize hCore hLocal A
  · intro b hb
    exact (Finset.mem_filter.mp (hA hb)).2
  · intro x hx
    exact Finset.mem_biUnion.mp (hCover hx)

end Balanced

end OAI
