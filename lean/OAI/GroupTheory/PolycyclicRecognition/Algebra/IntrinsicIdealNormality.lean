import OAI.GroupTheory.PolycyclicRecognition.Geometry.IntrinsicAdjointExponential
import OAI.GroupTheory.PolycyclicRecognition.Geometry.ExponentialIdeal
import OAI.GroupTheory.PolycyclicRecognition.Geometry.LieIdealNormalityInput
import OAI.GroupTheory.PolycyclicRecognition.Analysis.NilpotentHaarInput

namespace OAI

/-! # Ideal normality from the intrinsic adjoint flow

Normality of exponential images needs no faithful representation. The
actual adjoint action is the exponential of the bracket operator and
preserves every Lie ideal.
-/

noncomputable section
namespace PolycyclicRecognition

open scoped Manifold

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace G] [ChartedSpace E G]
  [Group G] [LieGroup (𝓘(ℝ, E)) ⊤ G] [T2Space G]

theorem normal_of_exponential_ideal_intrinsic
    {Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G} (hExp : IsGroupExponential Exp)
    (hsurj : Function.Surjective Exp)
    (I : LieIdeal ℝ (GroupLieAlgebra (𝓘(ℝ, E)) G)) (S : Subgroup G)
    (hS : (S : Set G) = Exp '' (I : Set (GroupLieAlgebra (𝓘(ℝ, E)) G))) : S.Normal := by
  constructor
  intro y hy g
  change y ∈ (S : Set G) at hy
  change g * y * g⁻¹ ∈ (S : Set G)
  rw [hS] at hy ⊢
  obtain ⟨v, hv, rfl⟩ := hy
  obtain ⟨x, rfl⟩ := hsurj g
  rw [conjugation_exponential hExp]
  change Exp (adjointLinearMap (E := E) (Exp x) v) ∈ _
  have he := adjointLinearMap_exponential hExp x 1
  simp only [one_smul] at he
  rw [he]
  refine ⟨NormedSpace.exp (groupAdjointOperator (E := E) x) v, ?_, rfl⟩
  let U : Submodule ℝ E := I.toSubmodule
  exact exp_apply_mem_of_stable U U.closed_of_finiteDimensional
    (groupAdjointOperator (E := E) x) (fun w hw => I.lie_mem hw) hv

variable {EN N : Type*} [NormedAddCommGroup EN] [NormedSpace ℝ EN]
  [FiniteDimensional ℝ EN] [TopologicalSpace N] [ChartedSpace EN N]
  [Group N] [LieGroup (𝓘(ℝ, EN)) ⊤ N] [T2Space N] [SimplyConnectedSpace N]
  [MeasurableSpace N] [BorelSpace N]

theorem nilpotentIdealNormalityInput_of_intrinsic_exponential
    (haarN : NilpotentExponentialHaarInput EN N)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G) (hExp : IsGroupExponential Exp)
    (hsurj : Function.Surjective Exp) :
    NilpotentIdealNormalityInput (EN := EN) (N := N) (EG := E) (G := G) := by
  intro _ _ hnil I j ι _ _ hsmooth hderiv hj
  obtain ⟨ExpN, hExpN⟩ := haarN.1 hnil
  obtain ⟨cN, hcN⟩ := (haarN.2 ExpN hExpN hnil).1
  have hι (x) : ι (ExpN x) = Exp (j x) := by
    have h := hExpN.map_of_mdifferentiable hExp ι (hsmooth.mdifferentiable (by simp)) x
    rw [hderiv] at h
    exact h
  apply normal_of_exponential_ideal_intrinsic hExp hsurj I ι.range
  ext g
  constructor
  · rintro ⟨n, rfl⟩
    obtain ⟨x, rfl⟩ := cN.surjective n
    rw [hcN, hι]
    exact ⟨j x, hj ▸ ⟨x, rfl⟩, rfl⟩
  · rintro ⟨v, hv, rfl⟩
    rw [← hj] at hv
    obtain ⟨x, rfl⟩ := hv
    exact ⟨ExpN x, hι x⟩

end PolycyclicRecognition

end

end OAI
