import OAI.Analysis.Unitarizability.Model
import Mathlib.Analysis.InnerProductSpace.Projection.Basic

namespace OAI

/-! A unitarizing similarity gives a bounded commuting projection
onto every closed invariant subspace. -/
noncomputable section
namespace Dixmier
namespace InvariantProjection
variable {G H : Type*} [Group G]
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
@[simp] theorem rep_inv (U : G →* (H →L[ℂ] H)) (g : G) (x : H) : U g (U g⁻¹ x) = x := by
  have h : U g * U g⁻¹ = 1 := by rw [← map_mul]; simp
  exact congrArg (fun T : H →L[ℂ] H => T x) h

theorem orthogonal_projection_commutes (U : G →* (H →L[ℂ] H))
    (hU : ∀ g x, ‖U g x‖ = ‖x‖) (M : ClosedSubmodule ℂ H)
    (hM : ∀ g x, x ∈ M → U g x ∈ M) (g : G) :
    Commute M.toSubmodule.starProjection (U g) := by
  change M.toSubmodule.starProjection * U g = U g * M.toSubmodule.starProjection
  apply ContinuousLinearMap.ext
  intro x
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · exact hM g _ (Submodule.starProjection_apply_mem _ _)
  · intro w hw
    have hi := (LinearMap.norm_map_iff_inner_map_map (U g)).mp (hU g)
    have hm : U g⁻¹ w ∈ M := hM g⁻¹ w hw
    have hz := M.toSubmodule.starProjection_inner_eq_zero x (U g⁻¹ w) hm
    have he := hi (x - M.toSubmodule.starProjection x) (U g⁻¹ w)
    rw [map_sub, rep_inv] at he
    exact he.trans hz

def conjugated (π : G →* (H →L[ℂ] H)) (S : H ≃L[ℂ] H) : G →* (H →L[ℂ] H) where
  toFun g := S.toContinuousLinearMap.comp ((π g).comp S.symm.toContinuousLinearMap)
  map_one' := by ext x; simp
  map_mul' g h := by ext x; simp [map_mul, mul_apply_eq_comp]

omit [CompleteSpace H] in
@[simp] theorem conjugated_apply (π : G →* (H →L[ℂ] H)) (S : H ≃L[ℂ] H) (g : G) (x : H) :
    conjugated π S g x = S (π g (S.symm x)) := rfl

/-- The conclusion supplies one bounded projection; it assumes only the
actual similarity and closed invariance, not a cocycle implementer. -/
theorem exists_commuting_projection (π : G →* (H →L[ℂ] H))
    (hπ : SimilarToUnitary π) (M : ClosedSubmodule ℂ H)
    (hM : ∀ g x, x ∈ M → π g x ∈ M) :
    ∃ P : H →L[ℂ] H, (∀ x, P x ∈ M) ∧
      (∀ x, x ∈ M → P x = x) ∧ ∀ g, Commute P (π g) := by
  rcases hπ with ⟨S, hS⟩
  let N : ClosedSubmodule ℂ H := M.mapEquiv S
  have hN : ∀ g x, x ∈ N → conjugated π S g x ∈ N := by
    intro g x hx
    rcases hx with ⟨y, hy, rfl⟩
    exact ⟨π g y, hM g y hy, by simp⟩
  let Q := N.toSubmodule.starProjection
  let P : H →L[ℂ] H := S.symm.toContinuousLinearMap.comp (Q.comp S.toContinuousLinearMap)
  have hmem (x : H) : P x ∈ M := by
    have h := Submodule.starProjection_apply_mem N.toSubmodule (S x)
    rcases h with ⟨y, hy, he⟩
    change S.symm (Q (S x)) ∈ M
    rw [← he]
    simpa using hy
  have hfix (x : H) (hx : x ∈ M) : P x = x := by
    have hn : S x ∈ N := ⟨x, hx, rfl⟩
    change S.symm (Q (S x)) = x
    rw [Submodule.starProjection_eq_self_iff.mpr hn]
    simp
  refine ⟨P, hmem, hfix, ?_⟩
  intro g
  have hq := orthogonal_projection_commutes (conjugated π S) hS N hN g
  change P * π g = π g * P
  ext x
  have h := congrArg (fun T : H →L[ℂ] H => S.symm (T (S x))) hq.eq
  simpa [P, Q, mul_apply_eq_comp] using h

end InvariantProjection
end Dixmier

end

end OAI
