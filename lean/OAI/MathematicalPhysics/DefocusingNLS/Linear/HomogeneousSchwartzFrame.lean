import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousYSpace
import Mathlib.Analysis.Normed.Module.FiniteDimension

namespace OAI

/-! # A finite family of Schwartz functions realizes every finite coordinate -/

open Set
open scoped SchwartzMap

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

theorem homogeneousSchwartz_coordinates_surjective (a k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k)
    (π : HomogeneousY a k →L[ℝ] F) (hπ : Function.Surjective π) :
    Function.Surjective (fun f : 𝓢(E, ℂ) => π (homogeneousSchwartzEmbedding a k ha ha1 hk f)) := by
  let A := π.comp ((homogeneousSchwartzEmbedding a k ha ha1 hk).restrictScalars ℝ)
  have hd : DenseRange A := hπ.denseRange.comp
    (homogeneousSchwartzEmbedding_dense a k ha ha1 hk) π.continuous
  have hc : IsClosed (Set.range A) := A.range.closed_of_finiteDimensional
  have hr : Set.range A = univ := by
    rw [← hc.closure_eq, hd.closure_range]
  exact Set.range_eq_univ.mp hr

theorem exists_homogeneousSchwartz_frame (a k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k)
    (π : HomogeneousY a k →L[ℝ] F) (hπ : Function.Surjective π) :
    ∃ B : F →ₗ[ℝ] 𝓢(E, ℂ), ∀ v,
      π (homogeneousSchwartzEmbedding a k ha ha1 hk (B v)) = v := by
  let A := π.comp ((homogeneousSchwartzEmbedding a k ha ha1 hk).restrictScalars ℝ)
  obtain ⟨B, hB⟩ := A.toLinearMap.exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr (homogeneousSchwartz_coordinates_surjective a k ha ha1 hk π hπ))
  refine ⟨B, fun v => ?_⟩
  exact congrArg (fun L : F →ₗ[ℝ] F => L v) hB

end DefocusingNLS

end OAI
