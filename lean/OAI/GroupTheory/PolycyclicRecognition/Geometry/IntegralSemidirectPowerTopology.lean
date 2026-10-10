import OAI.GroupTheory.PolycyclicRecognition.Lattices.IntegralLatticePowerIndex
import OAI.GroupTheory.PolycyclicRecognition.Geometry.SemidirectProductTopology

namespace OAI

/-! # The finite-index power subgroup is closed in the integral extension -/

noncomputable section
namespace PolycyclicRecognition
attribute [local instance] semidirectProductTopology
variable {L : Type} [Group L] [TopologicalSpace L]

private theorem latticePowerHom_isEmbedding (n : ℕ) {m : ℕ} (hm : 0 < m) :
    Topology.IsEmbedding (latticePowerHom n m) := by
  let e := MonoidHom.ofInjective (latticePowerHom_injective n hm)
  let h : IntegralLatticeGroup n ≃ₜ (latticePowerHom n m).range :=
    { e.toEquiv with
      continuous_toFun := continuous_of_discreteTopology
      continuous_invFun := continuous_of_discreteTopology }
  exact Topology.IsEmbedding.subtypeVal.comp h.isEmbedding

theorem integralSemidirectPowerMap_isClosedEmbedding {n m : ℕ}
    (ρ : IntegralLatticeGroup n →* MulAut L) (hm : 0 < m) :
    Topology.IsClosedEmbedding (integralSemidirectPowerMap ρ m) := by
  have hp : Topology.IsEmbedding (fun p : L × IntegralLatticeGroup n =>
      (p.1, latticePowerHom n m p.2)) :=
    Topology.IsEmbedding.id.prodMap (latticePowerHom_isEmbedding n hm)
  have he : Topology.IsEmbedding (integralSemidirectPowerMap ρ m) :=
    (semidirectProductHomeomorph ρ).symm.isEmbedding.comp
      (hp.comp (semidirectProductHomeomorph (ρ.comp (latticePowerHom n m))).isEmbedding)
  refine ⟨he, ?_⟩
  change IsClosed ((integralSemidirectPowerMap ρ m).range : Set (L ⋊[ρ] IntegralLatticeGroup n))
  rw [integralSemidirectPowerMap_range]
  exact (isClosed_discrete ((latticePowerHom n m).range : Set (IntegralLatticeGroup n))).preimage
    (continuous_semidirect_right ρ)

end PolycyclicRecognition

end

end OAI
