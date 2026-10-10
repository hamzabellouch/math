import Mathlib

namespace OAI

section
section
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Real Set
open scoped NNReal ENNReal
open Filter
open scoped Topology
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius ENNReal NNReal
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius NNReal
noncomputable section
open MeasureTheory ProbabilityTheory Real Set Filter
open MeasureTheory.Measure
open scoped ENNReal NNReal MeasureTheory Topology
open MeasureTheory
noncomputable section
noncomputable section
open MeasureTheory Set NormedSpace
open scoped Topology
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius
noncomputable section
open Set Real
open scoped Topology
namespace SKRatioGaussian
section Projection
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

structure ClosedConvexNonempty (K : Set E) : Prop where
  nonempty : K.Nonempty
  complete : IsComplete K
  convex : Convex ℝ K

noncomputable def convexProject {K : Set E} (hK : ClosedConvexNonempty K) (x : E) : E :=
  Classical.choose (exists_norm_eq_iInf_of_complete_convex hK.nonempty hK.complete hK.convex x)

lemma convexProject_mem {K : Set E} (hK : ClosedConvexNonempty K) (x : E) :
    convexProject hK x ∈ K :=
  (Classical.choose_spec (exists_norm_eq_iInf_of_complete_convex hK.nonempty hK.complete hK.convex x)).1

lemma convexProject_minimal {K : Set E} (hK : ClosedConvexNonempty K) (x : E) :
    ‖x-convexProject hK x‖ = ⨅ y : K, ‖x-y‖ :=
  (Classical.choose_spec (exists_norm_eq_iInf_of_complete_convex hK.nonempty hK.complete hK.convex x)).2

lemma convexProject_inner {K : Set E} (hK : ClosedConvexNonempty K) (x : E)
    {y : E} (hy : y ∈ K) :
    inner ℝ (x-convexProject hK x) (y-convexProject hK x) ≤ 0 := by
  exact ((norm_eq_iInf_iff_real_inner_le_zero hK.convex (convexProject_mem hK x)).mp
    (convexProject_minimal hK x)) y hy

lemma convexProject_lipschitz {K : Set E} (hK : ClosedConvexNonempty K) :
    LipschitzWith 1 (convexProject hK) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [NNReal.coe_one,one_mul,dist_eq_norm]
  let p := convexProject hK x
  let q := convexProject hK y
  have hx := convexProject_inner hK x (convexProject_mem hK y)
  have hy := convexProject_inner hK y (convexProject_mem hK x)
  change inner ℝ (x-p) (q-p) ≤ 0 at hx
  change inner ℝ (y-q) (p-q) ≤ 0 at hy
  have hi : ‖p-q‖^2 ≤ inner ℝ (p-q) (x-y) := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [inner_sub_left,inner_sub_right,real_inner_comm] at *
    nlinarith
  have hb := real_inner_le_norm (p-q) (x-y)
  nlinarith [norm_nonneg (p-q),norm_nonneg (x-y)]

lemma convexProject_eq_self {K : Set E} (hK : ClosedConvexNonempty K) {x : E}
    (hx : x ∈ K) : convexProject hK x = x := by
  have hh := convexProject_inner hK x hx
  rw [real_inner_self_eq_norm_sq] at hh
  have hz : ‖x-convexProject hK x‖ = 0 := by nlinarith [norm_nonneg (x-convexProject hK x)]
  exact (sub_eq_zero.mp (norm_eq_zero.mp hz)).symm

lemma convexProject_unique {K : Set E} (hK : ClosedConvexNonempty K) {x p : E}
    (hp : p ∈ K) (hmin : ∀ y ∈ K, inner ℝ (x-p) (y-p) ≤ 0) :
    p = convexProject hK x := by
  let q := convexProject hK x
  have h₁ := hmin q (convexProject_mem hK x)
  have h₂ := convexProject_inner hK x hp
  change inner ℝ (x-q) (p-q) ≤ 0 at h₂
  have hh : ‖p-q‖^2 ≤ 0 := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [inner_sub_right,inner_sub_left,real_inner_comm] at *
    nlinarith
  have hz : ‖p-q‖ = 0 := by nlinarith [norm_nonneg (p-q)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hz)

lemma convexProject_equivariant {K : Set E} (hK : ClosedConvexNonempty K)
    (U : E ≃ₗᵢ[ℝ] E) (hU : ∀ x, U x ∈ K ↔ x ∈ K) (x : E) :
    convexProject hK (U x) = U (convexProject hK x) := by
  apply Eq.symm
  apply convexProject_unique hK ((hU _).mpr (convexProject_mem hK x))
  intro y hy
  have hy' : U.symm y ∈ K := (hU _).mp (by simpa using hy)
  have hh := convexProject_inner hK x hy'
  rw [← U.inner_map_map] at hh
  simpa only [map_sub,LinearIsometryEquiv.apply_symm_apply] using hh

end Projection
end SKRatioGaussian

end
end
end
end
end
end
end
end
end
end

end OAI
