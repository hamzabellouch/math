import OAI.GroupTheory.PolycyclicRecognition.Geometry.ExponentialBasisGeneration
import OAI.GroupTheory.PolycyclicRecognition.Algebra.IntrinsicIdealNormality

namespace OAI

/-! # Normality of integrated ideals in a connected Lie group

The normalizer contains each exponential one-parameter subgroup, so the
basis-generation theorem makes it the whole group. Surjectivity of the
ambient exponential is not needed.
-/

noncomputable section
namespace PolycyclicRecognition

open scoped Manifold

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace G] [ChartedSpace E G]
  [Group G] [LieGroup (𝓘(ℝ, E)) ⊤ G] [T2Space G]
  [IsTopologicalGroup G] [PreconnectedSpace G]

theorem normal_of_exponential_ideal_connected
    {Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G} (hExp : IsGroupExponential Exp)
    (I : LieIdeal ℝ (GroupLieAlgebra (𝓘(ℝ, E)) G)) (S : Subgroup G)
    (hS : (S : Set G) = Exp '' (I : Set (GroupLieAlgebra (𝓘(ℝ, E)) G))) : S.Normal := by
  have hconj (x : GroupLieAlgebra (𝓘(ℝ, E)) G) (y : G) (hy : y ∈ S) :
      Exp x * y * (Exp x)⁻¹ ∈ S := by
    change y ∈ (S : Set G) at hy
    change Exp x * y * (Exp x)⁻¹ ∈ (S : Set G)
    rw [hS] at hy ⊢
    obtain ⟨v, hv, rfl⟩ := hy
    rw [conjugation_exponential hExp]
    change Exp (adjointLinearMap (E := E) (Exp x) v) ∈ _
    have he := adjointLinearMap_exponential hExp x 1
    simp only [one_smul] at he
    rw [he]
    refine ⟨NormedSpace.exp (groupAdjointOperator (E := E) x) v, ?_, rfl⟩
    let U : Submodule ℝ E := I.toSubmodule
    exact exp_apply_mem_of_stable U U.closed_of_finiteDimensional
      (groupAdjointOperator (E := E) x) (fun w hw => I.lie_mem hw) hv
  apply Subgroup.normalizer_eq_top_iff.mp
  apply subgroup_eq_top_of_exponential_basis hExp (Module.finBasis ℝ E)
  intro i t
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · exact hconj (t • Module.finBasis ℝ E i) y
  · intro hy
    have h := hconj (-(t • Module.finBasis ℝ E i)) _ hy
    have heq : Exp (-(t • Module.finBasis ℝ E i)) *
        (Exp (t • Module.finBasis ℝ E i) * y * (Exp (t • Module.finBasis ℝ E i))⁻¹) *
        (Exp (-(t • Module.finBasis ℝ E i)))⁻¹ = y := by
      erw [hExp.map_neg]
      group
    rwa [heq] at h

variable {EN N : Type*} [NormedAddCommGroup EN] [NormedSpace ℝ EN]
  [FiniteDimensional ℝ EN] [TopologicalSpace N] [ChartedSpace EN N]
  [Group N] [LieGroup (𝓘(ℝ, EN)) ⊤ N] [T2Space N] [SimplyConnectedSpace N]
  [MeasurableSpace N] [BorelSpace N]

omit [PreconnectedSpace G] in
theorem nilpotentIdealNormalityInput_of_connected_exponential
    (haarN : NilpotentExponentialHaarInput EN N)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G) (hExp : IsGroupExponential Exp) :
    NilpotentIdealNormalityInput (EN := EN) (N := N) (EG := E) (G := G) := by
  intro _ _ hnil I j ι _ _ hsmooth hderiv hj
  obtain ⟨ExpN, hExpN⟩ := haarN.1 hnil
  obtain ⟨cN, hcN⟩ := (haarN.2 ExpN hExpN hnil).1
  have hι (x) : ι (ExpN x) = Exp (j x) := by
    have h := hExpN.map_of_mdifferentiable hExp ι (hsmooth.mdifferentiable (by simp)) x
    rw [hderiv] at h
    exact h
  apply normal_of_exponential_ideal_connected hExp I ι.range
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
