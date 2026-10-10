import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Invertible
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd

namespace OAI

section

namespace Erdos3

variable {D : Type*} [Fintype D] {E : D → Type*}
  [∀ d, NormedAddCommGroup (E d)] [∀ d, NormedSpace ℝ (E d)]

noncomputable def axisDiagonalOperator (A : ∀ d, E d →L[ℝ] E d) :
    (∀ d, E d) →L[ℝ] (∀ d, E d) :=
  ContinuousLinearMap.pi (fun d => (A d).comp (ContinuousLinearMap.proj d))

omit [Fintype D] in
theorem axisDiagonalOperator_apply (A : ∀ d, E d →L[ℝ] E d) (x : ∀ d, E d) (d : D) :
    axisDiagonalOperator A x d = A d (x d) := rfl

theorem axisDiagonalOperator_norm_le (A : ∀ d, E d →L[ℝ] E d)
    {K : ℝ} (hK : 0 ≤ K) (hA : ∀ d, ‖A d‖ ≤ K) : ‖axisDiagonalOperator A‖ ≤ K := by
  apply ContinuousLinearMap.opNorm_le_bound _ hK
  intro x
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg hK (norm_nonneg x))).mpr
  intro d
  change ‖A d (x d)‖ ≤ K * ‖x‖
  exact ((A d).le_opNorm _).trans
    (mul_le_mul (hA d) (norm_le_pi_norm x d) (norm_nonneg _) hK)

omit [Fintype D] in
theorem axisDiagonalOperator_inverse_spec (A : ∀ d, E d →L[ℝ] E d)
    (hA : ∀ d, (A d).IsInvertible) :
    (axisDiagonalOperator A).IsInvertible ∧
      (axisDiagonalOperator A).inverse = axisDiagonalOperator (fun d => (A d).inverse) := by
  have hr : (axisDiagonalOperator A).comp (axisDiagonalOperator (fun d => (A d).inverse)) =
      ContinuousLinearMap.id ℝ (∀ d, E d) := by
    ext x d
    change A d ((A d).inverse (x d)) = x d
    exact (hA d).self_apply_inverse _
  have hl : (axisDiagonalOperator (fun d => (A d).inverse)).comp (axisDiagonalOperator A) =
      ContinuousLinearMap.id ℝ (∀ d, E d) := by
    ext x d
    change (A d).inverse (A d (x d)) = x d
    exact (hA d).inverse_apply_self _
  exact ⟨ContinuousLinearMap.IsInvertible.of_inverse hr hl, ContinuousLinearMap.inverse_eq hr hl⟩

theorem axisDiagonalOperator_inverse_norm_le (A : ∀ d, E d →L[ℝ] E d)
    (hA : ∀ d, (A d).IsInvertible) {K : ℝ} (hK : 0 ≤ K)
    (hbound : ∀ d, ‖(A d).inverse‖ ≤ K) :
    (axisDiagonalOperator A).IsInvertible ∧ ‖(axisDiagonalOperator A).inverse‖ ≤ K := by
  obtain ⟨hinv, heq⟩ := axisDiagonalOperator_inverse_spec A hA
  refine ⟨hinv, ?_⟩
  rw [heq]
  exact axisDiagonalOperator_norm_le _ hK hbound

end Erdos3

end

end OAI
