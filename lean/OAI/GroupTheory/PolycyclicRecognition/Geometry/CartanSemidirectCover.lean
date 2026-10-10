import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanFactorModel
import OAI.GroupTheory.PolycyclicRecognition.Geometry.SemidirectProductTopology
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.ReducedCohomologyDescent

namespace OAI

/-! # The genuine product cover of the Cartan factors

The factors in the ambient group may overlap. Their semidirect product instead
has unique product coordinates; the projection is surjective and has compact
lifts, which suffices to descend compact coboundary approximations.
-/

noncomputable section
namespace PolycyclicRecognition

universe v

open scoped Manifold

variable {EG G : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G]
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  {ExpG : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H ExpG)

attribute [local instance] semidirectProductTopology

local instance : IsTopologicalGroup F.N.carrier :=
  topologicalGroup_of_lieGroup (𝓘(ℝ, F.N.modelSpace)) ⊤
local instance : IsTopologicalGroup F.D.carrier :=
  topologicalGroup_of_lieGroup (𝓘(ℝ, F.D.modelSpace)) ⊤

theorem CartanFactorModel.continuous_action :
    Continuous (fun p : F.D.carrier × F.N.carrier => F.action p.1 p.2) := by
  let : IsTopologicalGroup G := topologicalGroup_of_lieGroup (𝓘(ℝ, EG)) ⊤
  apply F.closedN.isEmbedding.isInducing.continuous_iff.mpr
  have hi := F.closedD.continuous.comp (continuous_fst : Continuous (Prod.fst : F.D.carrier × F.N.carrier → _))
  have hn := F.closedN.continuous.comp (continuous_snd : Continuous (Prod.snd : F.D.carrier × F.N.carrier → _))
  have he : (F.inclusionN ∘ (fun p : F.D.carrier × F.N.carrier => F.action p.1 p.2)) =
      (fun p => F.inclusionD p.1 * F.inclusionN p.2 * (F.inclusionD p.1)⁻¹) := by
    funext p
    exact F.conjugation p.1 p.2
  rw [he]
  exact continuous_mul.comp ((continuous_mul.comp (hi.prodMk hn)).prodMk
    (continuous_inv.comp hi))

def CartanFactorModel.semidirectProjection :
    (F.N.carrier ⋊[F.action] F.D.carrier) →* G :=
  semidirectProductLift F.action F.inclusionN F.inclusionD F.conjugation

theorem CartanFactorModel.continuous_semidirectProjection :
    Continuous F.semidirectProjection := by
  let : IsTopologicalGroup G := topologicalGroup_of_lieGroup (𝓘(ℝ, EG)) ⊤
  exact continuous_semidirect_lift F.action F.inclusionN F.inclusionD
    F.closedN.continuous F.closedD.continuous F.conjugation

theorem CartanFactorModel.surjective_semidirectProjection :
    Function.Surjective F.semidirectProjection := by
  intro g
  obtain ⟨⟨n, d⟩, h⟩ := F.surjective g
  exact ⟨⟨n, d⟩, h⟩

theorem CartanFactorModel.compact_lifts_semidirectProjection
    (K : Set G) (hK : IsCompact K) :
    ∃ C : Set (F.N.carrier ⋊[F.action] F.D.carrier),
      IsCompact C ∧ K ⊆ F.semidirectProjection '' C := by
  obtain ⟨C, hC, hlift⟩ := F.compactLifts K hK
  refine ⟨(semidirectProductHomeomorph F.action).symm '' C,
    hC.image (semidirectProductHomeomorph F.action).symm.continuous, ?_⟩
  intro g hg
  obtain ⟨p, hp, hpg⟩ := hlift hg
  exact ⟨(semidirectProductHomeomorph F.action).symm p, ⟨p, hp, rfl⟩, hpg⟩

theorem CartanFactorModel.semidirect_topologicalGroup :
    IsTopologicalGroup (F.N.carrier ⋊[F.action] F.D.carrier) :=
  semidirectProductTopologicalGroup F.action F.continuous_action

theorem CartanFactorModel.unitaryReducedVanishing_of_cover
    (h : UnitaryReducedVanishing.{_, v} (F.N.carrier ⋊[F.action] F.D.carrier)) :
    UnitaryReducedVanishing.{_, v} G := by
  let := F.semidirect_topologicalGroup
  exact h.of_surjective_compact_lifts F.semidirectProjection
    F.continuous_semidirectProjection F.surjective_semidirectProjection
    F.compact_lifts_semidirectProjection

end PolycyclicRecognition

end

end OAI
