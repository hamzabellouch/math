import Mathlib
import OAI.Geometry.Borsuk.MatrixGeometry.MatrixReflection

namespace OAI

namespace BorsukNine
open scoped RealInnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator
section FibreTransport
variable {ν : Type*} [Fintype ν] [DecidableEq ν]
local notation "E" => EuclideanSpace ℝ ν
local notation "M" => Matrix ν ν ℝ
local notation "op" => Matrix.toEuclideanCLM (n := ν) (𝕜 := ℝ)

omit [DecidableEq ν] in
lemma householder_swap {c u : E} (h : ‖c‖ = ‖u‖) : householder c u u = c := by
  calc
    householder c u u = householder c u (householder c u c) := congrArg (householder c u) (householder_send h).symm
    _ = c := householder_involutive c u c

lemma matrixConjugate_householder_self {c : E} {Q : M} (hQ : IsSelfAdjoint Q)
    (hc : op Q c = 0) : matrixConjugate (householder c c) Q = Q := by
  apply (Matrix.toEuclideanCLM (n := ν) (𝕜 := ℝ)).injective
  change op (matrixConjugate (householder c c) Q) = op Q
  apply ContinuousLinearMap.ext
  intro v
  rw [matrixConjugate_action]
  have hs : (householder c c).symm v = householder c c v := by
    apply (householder c c).injective
    rw [LinearIsometryEquiv.apply_symm_apply]
    exact (householder_involutive c c v).symm
  have hcz : op Q (c+c) = 0 := by rw [map_add,hc,add_zero]
  have hact : op Q (householder c c v) = -(op Q v) := by
    rw [householder_apply,map_sub,map_smul,hcz,smul_zero,zero_sub]
  rw [hs,hact,map_neg]
  have ho : ⟪c,op Q v⟫ = 0 := by
    rw [← ContinuousLinearMap.adjoint_inner_left,← ContinuousLinearMap.star_eq_adjoint,
      ← map_star,hQ.star_eq,hc,inner_zero_left]
  rw [householder_at_self ho,neg_neg]

noncomputable def fibreTransport (c u v : E) (Q : M) : M :=
  matrixConjugate (householder c v) (matrixConjugate (householder c u) Q)

lemma fibreTransport_nonneg (c u v : E) {Q : M} (hQ : 0 ≤ Q) :
    0 ≤ fibreTransport c u v Q :=
  matrixConjugate_nonneg _ (matrixConjugate_nonneg _ hQ)

lemma fibreTransport_trace (c u v : E) (Q : M) :
    Matrix.trace (fibreTransport c u v Q) = Matrix.trace Q := by
  simp only [fibreTransport,matrixConjugate_trace]

lemma fibreTransport_kernel {c u v : E} {Q : M} (hu : ‖c‖ = ‖u‖) (hv : ‖c‖ = ‖v‖)
    (hQ : op Q u = 0) : op (fibreTransport c u v Q) v = 0 := by
  have hQc : op (matrixConjugate (householder c u) Q) c = 0 := by
    simpa only [householder_swap hu] using matrixConjugate_kernel (householder c u) hQ
  simpa only [fibreTransport,householder_send hv] using matrixConjugate_kernel (householder c v) hQc

lemma fibreTransport_self (c u : E) (Q : M) : fibreTransport c u u Q = Q :=
  matrixConjugate_involutive (householder_involutive c u) Q

lemma fibreTransport_center {c u : E} {Q : M} (hQ : IsSelfAdjoint Q) (hu : ‖c‖ = ‖u‖)
    (hz : op Q u = 0) : fibreTransport c u c Q = matrixConjugate (householder c u) Q := by
  apply matrixConjugate_householder_self (matrixConjugate_selfAdjoint _ hQ)
  simpa only [householder_swap hu] using matrixConjugate_kernel (householder c u) hz

lemma fibreTransport_unit_iff {c u v : E} {Q : M} (hu : ‖c‖ = ‖u‖) (hv : ‖c‖ = ‖v‖) :
    IsUnit (rankOne v + fibreTransport c u v Q) ↔ IsUnit (rankOne u + Q) := by
  have he : rankOne v + fibreTransport c u v Q =
      matrixConjugate (householder c v) (matrixConjugate (householder c u) (rankOne u + Q)) := by
    rw [map_add,map_add,matrixConjugate_rankOne,householder_swap hu,
      matrixConjugate_rankOne,householder_send hv]; rfl
  rw [he]
  exact (isUnit_map_iff (matrixConjugate (householder c v)) _).trans
    (isUnit_map_iff (matrixConjugate (householder c u)) _)

lemma fibreTransport_continuousOn (c : E) :
    ContinuousOn (fun p : E × E × M => fibreTransport c p.1 p.2.1 p.2.2)
      {p | c+p.1 ≠ 0 ∧ c+p.2.1 ≠ 0} := by
  have hR₁ : ContinuousOn (fun p : E × E × M => reflectionMatrix c p.1)
      {p | c+p.1 ≠ 0 ∧ c+p.2.1 ≠ 0} :=
    (reflectionMatrix_continuousOn c).comp continuous_fst.continuousOn (fun _ h => h.1)
  have hR₂ : ContinuousOn (fun p : E × E × M => reflectionMatrix c p.2.1)
      {p | c+p.1 ≠ 0 ∧ c+p.2.1 ≠ 0} :=
    (reflectionMatrix_continuousOn c).comp continuous_snd.fst.continuousOn (fun _ h => h.2)
  simp only [fibreTransport,reflectionMatrix_conjugate]
  exact (hR₂.mul ((hR₁.mul continuous_snd.snd.continuousOn).mul hR₁)).mul hR₂

end FibreTransport
end BorsukNine

end OAI
