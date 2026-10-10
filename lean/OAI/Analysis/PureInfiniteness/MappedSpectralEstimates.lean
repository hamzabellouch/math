import OAI.Analysis.PureInfiniteness.JointSpectralQuadratic
import OAI.Analysis.PureInfiniteness.ScalarSampling

namespace OAI

/-! Finite spectral error bounds are preserved by the unitization embedding. -/

noncomputable section
open scoped BigOperators

namespace WeakPureInfiniteness

variable {A B J : Type*} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B] [Fintype J]

lemma mapped_moment_norm_le (φ : A →⋆ₙₐ[ℂ] B) (a : A) (g : J → A) (t : J → ℂ)
    (r : ℝ) (hr : ‖a - ∑ j, t j • g j‖ ≤ r) :
    ‖φ a - ∑ j, t j • φ (g j)‖ ≤ r := by
  have he : φ (a - ∑ j, t j • g j) = φ a - ∑ j, t j • φ (g j) := by
    rw [map_sub, map_sum]
    congr 1
    exact Finset.sum_congr rfl (fun j _ => φ.map_smul _ _)
  rw [← he]
  exact (NonUnitalStarAlgHom.norm_apply_le φ _).trans hr

lemma mapped_quadratic_norm_le (φ : A →⋆ₙₐ[ℂ] B) (a : A) (f : J → A) (t : J → ℝ)
    (r : ℝ) (hr : ‖∑ j, sampledQuadraticError a (f j) (t j)‖ ≤ r) :
    ‖∑ j, sampledQuadraticError (φ a) (φ (f j)) (t j)‖ ≤ r := by
  have he : φ (∑ j, sampledQuadraticError a (f j) (t j)) =
      ∑ j, sampledQuadraticError (φ a) (φ (f j)) (t j) := by
    rw [map_sum]
    exact Finset.sum_congr rfl (fun j _ => map_sampledQuadraticError φ a (f j) (t j))
  rw [← he]
  exact (NonUnitalStarAlgHom.norm_apply_le φ _).trans hr

variable {D : Type*} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]
  [Nontrivial D] [DecidableEq J]

lemma scalarSample_norm_le (t : J → ℝ) (R : ℝ) (hR : 0 ≤ R)
    (ht0 : ∀ j, 0 ≤ t j) (htR : ∀ j, t j ≤ R) :
    ‖(scalarSample (A := D) t : CStarMatrix J J D)‖ ≤ R := by
  change ‖NonunitalGamma.diagonalHom (fun j => (t j : ℂ) • (1 : D))‖ ≤ R
  apply (NonUnitalStarAlgHom.norm_apply_le
    (NonunitalGamma.diagonalHom (A := D)) (fun j => (t j : ℂ) • (1 : D))).trans
  apply (pi_norm_le_iff_of_nonneg hR).mpr
  intro j
  rw [norm_smul, norm_one, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (ht0 j)]
  exact htR j

end WeakPureInfiniteness

end

end OAI
