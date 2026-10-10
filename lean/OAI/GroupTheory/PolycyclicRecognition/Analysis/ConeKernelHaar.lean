import OAI.GroupTheory.PolycyclicRecognition.Analysis.ConeIdealInnerHaar
import OAI.GroupTheory.PolycyclicRecognition.Analysis.KernelHaarTransport

namespace OAI

/-! # Conjugation-invariant Haar measure on the actual cone kernel -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieModule LieAlgebra MeasureTheory
open scoped Manifold

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)
  (C : Set (H →ₗ[ℝ] ℝ))

local instance kernelHaarNormedAddCommGroup : NormedAddCommGroup (cartanRootIdeal H) :=
  NormedAddCommGroup.induced _ _ (finBasis ℝ (cartanRootIdeal H)).equivFun.toLinearMap
    (finBasis ℝ (cartanRootIdeal H)).equivFun.injective
local instance kernelHaarNormedSpace : NormedSpace ℝ (cartanRootIdeal H) :=
  NormedSpace.induced ℝ _ _ (finBasis ℝ (cartanRootIdeal H)).equivFun.toLinearMap

variable {E I N Q A : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace I] [ChartedSpace E I] [Group I]
  [LieGroup (𝓘(ℝ, E)) ⊤ I] [T2Space I] [SimplyConnectedSpace I]
  [MeasurableSpace I] [BorelSpace I]
  [Group N] [TopologicalSpace N] [IsTopologicalGroup N]
  [MeasurableSpace N] [BorelSpace N] [Group Q]
  [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

attribute [local instance 100] LieRing.ofAssociativeRing

/-- The existing published exponential Haar input supplies an intrinsic
measure whose image on the actual kernel is Haar and invariant under every
ambient nilpotent conjugation. -/
theorem exists_cone_kernel_invariant_haar
    (e : M.coneWordIdeal C ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, E)) I)
    (ExpI : GroupLieAlgebra (𝓘(ℝ, E)) I → I) (hExpI : IsGroupExponential ExpI)
    (haar : NilpotentExponentialHaarInput E I)
    (b₀ : Basis (Fin (finrank ℝ (M.coneWordIdeal C))) ℝ (M.coneWordIdeal C))
    (π : N →* Q) (ι : I →* N) (hι : Topology.IsClosedEmbedding ι)
    (hrange : Set.range ι = (π.ker : Set N))
    (ExpN : cartanRootIdeal H → N) (hsurj : Function.Surjective ExpN)
    (hcompat : ∀ v : M.coneWordIdeal C, ι (ExpI (e v)) = ExpN v)
    (j : cartanRootIdeal H →ₗ⁅ℝ⁆ A) (ρ : N →* Aˣ) (hρ : Function.Injective ρ)
    (hmatch : ∀ x, ρ (ExpN x) = algebraExpUnit (j x)) :
    ∃ μ : Measure I, μ.IsHaarMeasure ∧
      (Measure.map (kernelRealization π ι hι hrange) μ).IsHaarMeasure ∧
      (∀ n : N, MeasurePreserving (quotientKernelConjugate π n)
        (Measure.map (kernelRealization π ι hι hrange) μ)
        (Measure.map (kernelRealization π ι hι hrange) μ)) ∧
      (Measure.map (kernelRealization π ι hι hrange) μ).IsMulRightInvariant := by
  obtain ⟨μ, hbij, hμ, hinv, _hvol⟩ :=
    M.exists_coneIdeal_inner_invariant_haar C e ExpI hExpI haar b₀
  let : IsTopologicalGroup I := topologicalGroup_of_lieGroup (𝓘(ℝ, E)) ⊤
  let : μ.IsHaarMeasure := hμ
  have hμk : (Measure.map (kernelRealization π ι hι hrange) μ).IsHaarMeasure :=
    (kernelRealization π ι hι hrange).toMulEquiv.isHaarMeasure_map μ
      (kernelRealization π ι hι hrange).continuous
      (kernelRealization π ι hι hrange).symm.continuous
  let : (Measure.map (kernelRealization π ι hι hrange) μ).IsHaarMeasure := hμk
  have hconj (n : N) : MeasurePreserving (quotientKernelConjugate π n)
      (Measure.map (kernelRealization π ι hι hrange) μ)
      (Measure.map (kernelRealization π ι hι hrange) μ) := by
    obtain ⟨x, rfl⟩ := hsurj n
    apply kernelRealization_conjugation_preserving π ι hι hrange μ (ExpN x)
      (exponentialConjugate e ExpI hbij (M.coneIdealInnerAutomorphism C x)) (hinv x)
    intro z
    obtain ⟨v, rfl⟩ := (hbij.comp e.bijective).surjective z
    change ι (exponentialConjugate e ExpI hbij (M.coneIdealInnerAutomorphism C x)
      (ExpI (e v))) = _
    rw [exponentialConjugate_apply_exp, hcompat]
    change ExpN _ = ExpN x * ι (ExpI (e v)) * _
    rw [hcompat]
    exact M.coneIdealInnerAutomorphism_exp_conjugation C ExpN j ρ hρ hmatch x v
  exact ⟨μ, hμ, hμk, hconj,
    kernel_measure_right_invariant π _ hconj⟩

end PolycyclicRecognition.CartanWordModel

end

end OAI
