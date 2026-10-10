import OAI.GroupTheory.PolycyclicRecognition.Lattices.NilshadowPowerGraph
import OAI.GroupTheory.PolycyclicRecognition.Lattices.KernelCompletionEmbedding

namespace OAI

/-! # The original topology in the real nilshadow graph -/

noncomputable section
namespace PolycyclicRecognition.IntegralNilshadowData
open scoped Manifold ContDiff
attribute [local instance] factorExtensionTopology semidirectProductTopology
variable {L G : Type} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [P : PolynomialExponentialCoordinates L] [Group G] {n : ℕ}
  {E : GroupExtension L G (IntegralLatticeGroup n)} (D : IntegralNilshadowData E)
  {m : ℕ} (hm : 0 < m)
  (φ : Multiplicative (Fin n → ℝ) →* MulAut D.completion.carrier)
  (he : ∀ z x, D.completedAction (latticePowerHom n m z) x = φ (integerVectorHom n z) x)
  (hinv : ∀ v x, D.height (φ v x) = D.height x)

theorem powerGraphEmbedding_isEmbedding : Topology.IsEmbedding (D.powerGraphEmbedding hm φ he hinv) := by
  let hτ := (D.inverseScaledHeight_smooth m).continuous
  let e := rotationalTwistHomeomorph φ (D.inverseScaledHeight m)
    (fun v x => congrArg (scaleRealHeight n (-((m : ℝ)⁻¹))) (hinv v x)) hτ
  let c : FactorExtension (D.system.pullback (latticePowerHom n m)) ≃ₜ
      FactorExtension (D.twistedSystem.pullback (latticePowerHom n m)) :=
    (factorExtensionHomeomorph _).trans (factorExtensionHomeomorph _).symm
  have hc := kernelCompletion_isEmbedding D.twistedSystem D.completion D.height
    D.height_smooth D.height_embed
  have h := e.symm.isEmbedding.comp (hc.comp
    ((factorPowerMap_isClosedEmbedding D.twistedSystem hm).isEmbedding.comp c.isEmbedding))
  convert h using 1
  funext a
  apply e.injective
  rfl

end PolycyclicRecognition.IntegralNilshadowData

end

end OAI
