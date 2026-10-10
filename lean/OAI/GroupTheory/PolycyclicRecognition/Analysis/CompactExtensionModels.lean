import OAI.GroupTheory.PolycyclicRecognition.Geometry.CompactSemidirectModel

namespace OAI

/-! # The locally compact models in the compact-extension comparison -/

noncomputable section
namespace PolycyclicRecognition
open scoped Manifold
attribute [local instance] semidirectProductTopology

def SimplyConnectedSolvableLieModel.toLCModel (S : SimplyConnectedSolvableLieModel) :
    CompactlyGeneratedLCModel := by
  let tg : IsTopologicalGroup S.carrier := topologicalGroup_of_lieGroup (𝓘(ℝ,S.modelSpace)) ⊤
  let lc : LocallyCompactSpace S.carrier :=
    Manifold.locallyCompact_of_finiteDimensional (𝓘(ℝ,S.modelSpace))
  exact { carrier := S.carrier, compactlyGenerated := exists_compact_generating_set S.carrier }

def compactSemidirectLCModel (S : CompactlyGeneratedLCModel) (K : Type)
    [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [T2Space K]
    [CompactSpace K] [SecondCountableTopology K]
    (α : K →* MulAut S.carrier) (hα : Continuous (fun p : K × S.carrier => α p.1 p.2)) :
    CompactlyGeneratedLCModel := by
  let tg : IsTopologicalGroup (S.carrier ⋊[α] K) := semidirectProductTopologicalGroup α hα
  exact
    { carrier := (S.carrier ⋊[α] K)
      compactlyGenerated := compactlyGenerated_compact_semidirect α S.compactlyGenerated }

def ProperCocompactHom.id (G : Type*) [Group G] [TopologicalSpace G] : ProperCocompactHom G G where
  hom := MonoidHom.id G
  proper := isProperMap_id
  cover := ⟨{1},isCompact_singleton,fun g => ⟨g,1,Set.mem_singleton _,mul_one g⟩⟩

end PolycyclicRecognition

end

end OAI
