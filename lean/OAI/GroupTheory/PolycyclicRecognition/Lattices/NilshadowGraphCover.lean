import OAI.GroupTheory.PolycyclicRecognition.Lattices.NilshadowGraphTopology
import OAI.GroupTheory.PolycyclicRecognition.Analysis.ScaledIntegralCover

namespace OAI

/-! # A compact fundamental cover for the real nilshadow graph -/

noncomputable section
namespace PolycyclicRecognition.IntegralNilshadowData
open Set
open scoped Manifold ContDiff
attribute [local instance] factorExtensionTopology semidirectProductTopology
variable {L G : Type} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [P : PolynomialExponentialCoordinates L] [Group G] {n : ℕ}
  {E : GroupExtension L G (IntegralLatticeGroup n)} (D : IntegralNilshadowData E)
  {m : ℕ} (hm : 0 < m)
  (φ : Multiplicative (Fin n → ℝ) →* MulAut D.completion.carrier)
  (he : ∀ z x, D.completedAction (latticePowerHom n m z) x = φ (integerVectorHom n z) x)
  (hinv : ∀ v x, D.height (φ v x) = D.height x)
  (hfix : ∀ v w, φ v (D.quotientSection w) = D.quotientSection w)

include hfix in
theorem powerGraph_compact_cover :
    ∃ K : Set (rotationalTwist φ (D.inverseScaledHeight m)
      (fun v x => congrArg (scaleRealHeight n (-((m : ℝ)⁻¹))) (hinv v x))),
      IsCompact K ∧ ∀ g, ∃ a k, k ∈ K ∧ D.powerGraphEmbedding hm φ he hinv a * k = g := by
  let e := rotationalTwistHomeomorph φ (D.inverseScaledHeight m)
    (fun v x => congrArg (scaleRealHeight n (-((m : ℝ)⁻¹))) (hinv v x))
    (D.inverseScaledHeight_smooth m).continuous
  obtain ⟨K, hK, hc⟩ := scaledIntegral_compact_cover n hm
  refine ⟨(fun k => e.symm (D.quotientSection k)) '' K,
    hK.image (e.symm.continuous.comp D.quotientSection.toContinuousLinearMap.continuous), ?_⟩
  intro g
  obtain ⟨z, k, hk, hzk⟩ := hc (D.height (e g))
  let b := D.completion.embed (⟨1, latticePowerHom n m z⟩ : FactorExtension D.twistedSystem)
  let u := e g * (D.quotientSection k)⁻¹ * b⁻¹
  have hs : D.height (D.quotientSection k) = k :=
    (D.heightLinear_apply _).symm.trans (D.heightLinear_section k)
  have hu : u ∈ D.height.ker := by
    change D.height (e g * (D.quotientSection k)⁻¹ * b⁻¹) = 1
    rw [map_mul, map_mul, map_inv, map_inv, hs]
    change D.height (e g) + -k + -(D.height b) = 0
    have hb : D.height b = integralRealHeight (latticePowerHom n m z) := D.height_embed _
    rw [hb, ← hzk]
    abel
  rw [D.completion.height_kernel_eq (FactorExtension.groupExtension D.twistedSystem)
    D.height D.height_smooth D.height_embed D.dimension] at hu
  obtain ⟨l, hl⟩ := hu
  let a : FactorExtension (D.system.pullback (latticePowerHom n m)) := ⟨l, z⟩
  refine ⟨a, e.symm (D.quotientSection k), ⟨k, hk, rfl⟩, ?_⟩
  apply e.injective
  change D.completion.embed (⟨l, latticePowerHom n m z⟩ : FactorExtension D.twistedSystem) *
    φ (integerVectorHom n z) (D.quotientSection k) = e g
  rw [hfix, completion_factorization D.twistedSystem D.completion]
  change D.completion.embed (FactorExtension.inl D.twistedSystem l) * b * D.quotientSection k = e g
  change D.completion.embed (FactorExtension.inl D.twistedSystem l) = u at hl
  rw [hl]
  dsimp only [u]
  group

end PolycyclicRecognition.IntegralNilshadowData

end

end OAI
