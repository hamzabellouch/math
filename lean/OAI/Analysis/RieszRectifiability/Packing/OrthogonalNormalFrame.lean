import Mathlib
import OAI.Analysis.RieszRectifiability.Foundations.MeasureBounds

namespace OAI

namespace RieszRectifiability

noncomputable section

open Function

theorem isometric_range_starProjection {n d : ℕ} (L : Ambient n →ₗᵢ[ℝ] Ambient d)
    (x : Ambient d) :
    L.toLinearMap.range.starProjection x = L (L.toContinuousLinearMap.adjoint x) := by
  apply Submodule.eq_starProjection_of_mem_orthogonal
    (LinearMap.mem_range_self L.toLinearMap (L.toContinuousLinearMap.adjoint x))
  change x - L (L.toContinuousLinearMap.adjoint x) ∈ L.toContinuousLinearMap.rangeᗮ
  rw [L.toContinuousLinearMap.orthogonal_range]
  change L.toContinuousLinearMap.adjoint (x - L (L.toContinuousLinearMap.adjoint x)) = 0
  have hL : L.toContinuousLinearMap.adjoint (L (L.toContinuousLinearMap.adjoint x)) =
      L.toContinuousLinearMap.adjoint x :=
    DFunLike.congr_fun L.adjoint_comp_self (L.toContinuousLinearMap.adjoint x)
  rw [map_sub, hL, sub_self]

theorem exists_isometry_onto_subspace {q d : ℕ} (S : Submodule ℝ (Ambient d))
    (hdim : Module.finrank ℝ S = q) :
    ∃ N : Ambient q →ₗᵢ[ℝ] Ambient d, N.toLinearMap.range = S := by
  let b : OrthonormalBasis (Fin q) ℝ S :=
    (stdOrthonormalBasis ℝ S).reindex (finCongr hdim)
  let E : Ambient q ≃ₗᵢ[ℝ] S := b.repr.symm
  let N : Ambient q →ₗᵢ[ℝ] Ambient d :=
    { toLinearMap := S.subtype.comp E.toLinearEquiv.toLinearMap
      norm_map' := fun x => E.norm_map x }
  refine ⟨N, ?_⟩
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact (b.repr.symm y).property
  · intro hx
    refine ⟨b.repr ⟨x, hx⟩, ?_⟩
    change ((b.repr.symm (b.repr ⟨x, hx⟩) : S) : Ambient d) = x
    simp

theorem exists_isometric_normal_embedding {n d : ℕ} (L : Ambient n →ₗᵢ[ℝ] Ambient d) :
    ∃ N : Ambient (d - n) →ₗᵢ[ℝ] Ambient d,
      N.toLinearMap.range = L.toLinearMap.rangeᗮ := by
  let S := L.toLinearMap.range
  have hS : Module.finrank ℝ S = n := by
    rw [LinearMap.finrank_range_of_inj L.injective]
    exact finrank_euclideanSpace_fin
  have hdim : Module.finrank ℝ Sᗮ = d - n := by
    have h := S.finrank_add_finrank_orthogonal
    rw [hS, finrank_euclideanSpace_fin] at h
    omega
  exact exists_isometry_onto_subspace Sᗮ hdim

theorem exists_complete_normal_frame {n d : ℕ} (L : Ambient n →ₗᵢ[ℝ] Ambient d) :
    ∃ N : Ambient (d - n) →ₗᵢ[ℝ] Ambient d,
      (∀ y, L.toContinuousLinearMap.adjoint (N y) = 0) ∧
      ∀ x, L (L.toContinuousLinearMap.adjoint x) + N (N.toContinuousLinearMap.adjoint x) = x := by
  obtain ⟨N, hN⟩ := exists_isometric_normal_embedding L
  refine ⟨N, ?_, ?_⟩
  · intro y
    have hm : N y ∈ L.toLinearMap.rangeᗮ := by
      rw [← hN]
      exact LinearMap.mem_range_self N.toLinearMap y
    change N y ∈ L.toContinuousLinearMap.rangeᗮ at hm
    rw [L.toContinuousLinearMap.orthogonal_range] at hm
    exact hm
  · intro x
    have hL := isometric_range_starProjection L x
    have hP := isometric_range_starProjection N x
    have hP' : L.toLinearMap.rangeᗮ.starProjection x = N (N.toContinuousLinearMap.adjoint x) := by
      have heq := congrArg (fun S : Submodule ℝ (Ambient d) => S.starProjection x) hN
      exact heq.symm.trans hP
    rw [← hL, ← hP']
    exact L.toLinearMap.range.starProjection_add_starProjection_orthogonal x

end

end RieszRectifiability

end OAI
