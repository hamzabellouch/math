import Mathlib
import OAI.Geometry.Borsuk.MatrixGeometry.MatrixTransport
import OAI.Geometry.Borsuk.MatrixGeometry.ReflectionTransport

namespace OAI

namespace BorsukNine
open scoped RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator
section MatrixReflection
variable {ν : Type*} [Fintype ν] [DecidableEq ν]
local notation "E" => EuclideanSpace ℝ ν
local notation "M" => Matrix ν ν ℝ
local notation "op" => Matrix.toEuclideanCLM (n := ν) (𝕜 := ℝ)

omit [Fintype ν] [DecidableEq ν] in
lemma rankOne_continuous : Continuous (rankOne (ν := ν)) := by
  apply continuous_matrix
  intro i j
  exact (PiLp.continuous_apply 2 (fun _ : ν => ℝ) i).mul
    (PiLp.continuous_apply 2 (fun _ : ν => ℝ) j)

noncomputable def reflectionMatrix (c u : E) : M :=
  (2 / ‖c+u‖^2) • rankOne (c+u) - 1

lemma reflectionMatrix_action (c u v : E) :
    op (reflectionMatrix c u) v = householder c u v := by
  rw [reflectionMatrix,map_sub,map_smul,map_one,sub_apply,
    smul_apply,one_apply_eq_self,rankOne_action,householder_apply,
    smul_smul]
  congr 2
  ring

lemma reflectionMatrix_eq (c u : E) :
    op (reflectionMatrix c u) = (householder c u).toContinuousLinearEquiv.toContinuousLinearMap := by
  apply ContinuousLinearMap.ext
  intro v
  exact reflectionMatrix_action c u v

omit [DecidableEq ν] in
lemma householder_involutive (c u : E) : Function.Involutive (householder c u) :=
  (Submodule.span ℝ {c+u}).reflection_involutive

lemma reflectionMatrix_conjugate (c u : E) (B : M) :
    matrixConjugate (householder c u) B = reflectionMatrix c u * B * reflectionMatrix c u := by
  apply (Matrix.toEuclideanCLM (n := ν) (𝕜 := ℝ)).injective
  change op (matrixConjugate (householder c u) B) = op (reflectionMatrix c u * B * reflectionMatrix c u)
  rw [map_mul,map_mul]
  apply ContinuousLinearMap.ext
  intro v
  rw [matrixConjugate_action]
  change _ = op (reflectionMatrix c u) (op B (op (reflectionMatrix c u) v))
  rw [reflectionMatrix_action,reflectionMatrix_action]
  congr 2

lemma reflectionMatrix_continuousOn (c : E) :
    ContinuousOn (reflectionMatrix c) {u | c+u ≠ 0} := by
  have hn : Continuous (fun u : E => ‖c+u‖^2) := (continuous_const.add continuous_id).norm.pow 2
  have hd : ContinuousOn (fun u : E => 2 / ‖c+u‖^2) {u | c+u ≠ 0} :=
    continuous_const.continuousOn.div hn.continuousOn
      (fun u hu => pow_ne_zero 2 (norm_ne_zero_iff.mpr hu))
  exact (hd.smul (rankOne_continuous.comp (continuous_const.add continuous_id)).continuousOn).sub
    continuous_const.continuousOn

lemma householder_matrix_joint_continuousOn (c : E) :
    ContinuousOn (fun p : E × M => matrixConjugate (householder c p.1) p.2)
      {p | c+p.1 ≠ 0} := by
  simp_rw [reflectionMatrix_conjugate]
  have hR : ContinuousOn (fun p : E × M => reflectionMatrix c p.1) {p | c+p.1 ≠ 0} :=
    (reflectionMatrix_continuousOn c).comp continuous_fst.continuousOn (fun _ h => h)
  exact (hR.mul continuous_snd.continuousOn).mul hR

end MatrixReflection
end BorsukNine

end OAI
