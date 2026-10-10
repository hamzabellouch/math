import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Topology.Algebra.Module.Basic

namespace OAI

/-! Two density facts used to transport the scalar and two-form spectral
families from L2 into their actual first-order energy spaces. -/

namespace PositiveEinsteinFour.Geometry

open Set

noncomputable section

variable {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
  [InnerProductSpace ℝ E] [InnerProductSpace ℝ F] [CompleteSpace E] [CompleteSpace F]

theorem adjoint_denseRange_of_injective (J : E →L[ℝ] F) (hJ : Function.Injective J) :
    DenseRange J.adjoint := by
  have h := J.orthogonal_ker
  rw [LinearMap.ker_eq_bot.mpr hJ, Submodule.bot_orthogonal_eq_top] at h
  apply denseRange_iff_closure_range.mpr
  exact congrArg (fun S : Submodule ℝ E => (S : Set E)) h.symm

omit [CompleteSpace E] [CompleteSpace F] in
theorem dense_span_continuousLinearMap_image {ι : Type*} (v : ι → E)
    (hv : (Submodule.span ℝ (range v)).topologicalClosure = ⊤)
    (A : E →L[ℝ] F) (hA : DenseRange A) :
    (Submodule.span ℝ (range (fun i => A (v i)))).topologicalClosure = ⊤ := by
  let S := (Submodule.span ℝ (range (fun i => A (v i)))).topologicalClosure
  have hs : IsClosed (S : Set F) := Submodule.isClosed_topologicalClosure _
  have hsub : Submodule.span ℝ (range v) ≤ S.comap A.toLinearMap := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨i, rfl⟩)
  have hfull : (⊤ : Submodule ℝ E) ≤ S.comap A.toLinearMap := by
    rw [← hv]
    exact Submodule.topologicalClosure_minimal _ hsub (hs.preimage A.continuous)
  apply top_unique
  intro y _
  apply hs.closure_subset_iff.mpr (show range A ⊆ S from ?_) (hA y)
  rintro _ ⟨x, rfl⟩
  exact hfull (by trivial)

omit [CompleteSpace E] [CompleteSpace F] in
theorem continuousLinearMap_mem_closed_of_total {ι : Type*} (v : ι → E)
    (hv : (Submodule.span ℝ (range v)).topologicalClosure = ⊤)
    (A : E →L[ℝ] F) (S : Submodule ℝ F) (hS : IsClosed (S : Set F))
    (h : ∀ i, A (v i) ∈ S) (u : E) : A u ∈ S := by
  have hs : Submodule.span ℝ (range v) ≤ S.comap A.toLinearMap := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact h i
  have ht := Submodule.topologicalClosure_minimal _ hs (hS.preimage A.continuous)
  rw [hv] at ht
  exact ht (by trivial)

end
end PositiveEinsteinFour.Geometry

end OAI
