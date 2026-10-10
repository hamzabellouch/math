import Mathlib

namespace OAI

section
section
noncomputable section
open Set Filter Manifold Bundle ContinuousLinearMap
open scoped Topology ContDiff

namespace WeakMTWTransport

lemma singularValues_le_of_bound {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] (A : E →ₗ[ℝ] F) {u : ℝ} (hu : 0 ≤ u)
    (h : ∀ v, ‖A v‖ ≤ u*‖v‖) {n : ℕ} (hn : Module.finrank ℝ E=n) (i : Fin n) :
    A.singularValues i ≤ u := by
  let hS := A.isSymmetric_adjoint_comp_self
  let v := hS.eigenvectorBasis hn i
  have hv : ‖v‖=1 := (hS.eigenvectorBasis hn).orthonormal.norm_eq_one i
  have he := congrArg (fun w => inner ℝ w v) (hS.apply_eigenvectorBasis hn i)
  simp only [LinearMap.comp_apply,LinearMap.adjoint_inner_left,
    real_inner_smul_left,RCLike.ofReal_real_eq_id,id_eq] at he
  change inner ℝ (A v) (A v)=hS.eigenvalues hn i*inner ℝ v v at he
  simp only [real_inner_self_eq_norm_sq] at he
  rw [←A.sq_singularValues_fin hn, hv] at he
  have HH := h v
  rw [hv,mul_one] at HH
  have hs := A.singularValues_nonneg i
  nlinarith [norm_nonneg (A v)]

end WeakMTWTransport
end
end
end

end OAI
