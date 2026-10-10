import Mathlib
import OAI.Analysis.MatrixSigning.Potential.Coordinates
import OAI.Analysis.MatrixSigning.Matrices.NormRetractH
import OAI.Analysis.MatrixSigning.Calculus.NormSmulRightId
import OAI.Analysis.MatrixSigning.Arithmetic.EventuallyInterior

namespace OAI

open Matrix

namespace CurrentKS.State
noncomputable section
open CurrentKS.Hermitian CurrentKS.Scalar CurrentKS.Calculus Matrix
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius

variable {d N : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private local instance : NormedAddCommGroup (H d) := inferInstance
private local instance : NormedSpace ℝ (H d) := inferInstance
private local instance : TopologicalSpace (H d) :=
  (inferInstance : NormedAddCommGroup (H d)).toUniformSpace.toTopologicalSpace

local instance normCoordinateOperatorNormedAddCommGroup : NormedAddCommGroup (H d →L[ℝ] H d) := inferInstance
local instance normCoordinateOperatorNormedSpace : NormedSpace ℝ (H d →L[ℝ] H d) := inferInstance

lemma norm_coordinate_le (i : Fin N) :
    ‖(ContinuousLinearMap.proj i : Coordinates N →L[ℝ] ℝ)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  simp only [one_mul]
  exact norm_le_pi_norm x i

lemma jetBound_S (A : Fin N → H d) (hA : ∀ i, ‖A i‖ ≤ 1)
    (L : E →L[ℝ] Coordinates N) (hL : ‖L‖ ≤ 1) {z : E} (hz : Cube (L z)) :
    JetBound (S A ∘ L) z (N:ℝ) := by
  have hc (i : Fin N) : JetBound ((ContinuousLinearMap.proj i).comp L) z 1 := by
    apply JetBound.linear _ _ (norm_comp_contractions _ L (norm_coordinate_le i) hL)
    exact hz i
  have hh (i : Fin N) : JetBound (fun v => L v i • A i) z 1 := by
    have hhh := (hc i).smul_const (A i)
      ((ContinuousLinearMap.proj i).comp L).contDiff.contDiffAt (hA i)
    simp only [one_mul] at hhh
    exact hhh
  have hs := JetBound.sum Finset.univ
    (fun i _ => (((ContinuousLinearMap.proj i).comp L).contDiff.contDiffAt.smul
      (contDiffAt_const (c := A i)))) (fun i _ => hh i)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,
    nsmul_eq_mul,mul_one] at hs
  exact hs

lemma jetBound_psi_coordinate
    (L : E →L[ℝ] Coordinates N) (hL : ‖L‖ ≤ 1) {z : E} {σ : ℝ}
    (hσ : 0 < σ) (i : Fin N) (hz : |L z i| ≤ 1-σ/2) :
    JetBound (fun v => psi (L v i)) z (1+800/σ^3) := by
  exact (jetBound_psi hσ hz).comp_linear ((ContinuousLinearMap.proj i).comp L)
    (contDiffAt_psi (strip_interior hσ hz))
    (norm_comp_contractions _ L (norm_coordinate_le i) hL)

lemma norm_sandwich_coefficient (c : ℝ) (A : H d) (hA : ‖A‖ ≤ 1) :
    ‖c • sandwichCLM A‖ ≤ |c| := by
  rw [norm_smul, Real.norm_eq_abs]
  have hn : ‖sandwichCLM A‖ ≤ 1 := (norm_sandwichCLM_le A).trans
    (by nlinarith [norm_nonneg A,hA])
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hn (abs_nonneg c)

lemma contDiffAt_psi_coordinate
    (L : E →L[ℝ] Coordinates N) {z : E} {σ : ℝ}
    (hσ : 0 < σ) (i : Fin N) (hz : |L z i| ≤ 1-σ/2) :
    ContDiffAt ℝ 3 (fun v => psi (L v i)) z :=
  (contDiffAt_psi (strip_interior hσ hz)).comp z
    (((ContinuousLinearMap.proj i).comp L).contDiff.contDiffAt)

lemma jetBound_eta_term (c : ℝ) (A : H d) (hA : ‖A‖ ≤ 1)
    (L : E →L[ℝ] Coordinates N) (hL : ‖L‖ ≤ 1) {z : E} {σ : ℝ}
    (hσ : 0 < σ) (i : Fin N) (hz : |L z i| ≤ 1-σ/2) :
    JetBound (fun v => psi (L v i) • (c • sandwichCLM A)) z
      (|c| *(1+800/σ^3)) :=
  (jetBound_psi_coordinate L hL hσ i hz).smul_const (c • sandwichCLM A)
    (contDiffAt_psi_coordinate L hσ i hz) (norm_sandwich_coefficient c A hA)

lemma jetBound_eta (c : ℝ) (A : Fin N → H d) (hA : ∀ i, ‖A i‖ ≤ 1)
    (L : E →L[ℝ] Coordinates N) (hL : ‖L‖ ≤ 1) {z : E} {σ : ℝ}
    (hσ : 0 < σ) (hz : ∀ i, |L z i| ≤ 1-σ/2) :
    JetBound (eta c A ∘ L) z ((N:ℝ)* |c| *(1+800/σ^3)) := by
  have hs := JetBound.sum Finset.univ
    (fun i _ => (contDiffAt_psi_coordinate L hσ i (hz i)).smul
      (contDiffAt_const (c := c • sandwichCLM (A i))))
    (fun i _ => jetBound_eta_term c (A i) (hA i) L hL hσ i (hz i))
  convert hs using 1
  · funext v
    change (∑ i : Fin N, (c * psi (L v i)) • sandwichCLM (A i)) =
      (∑ i : Fin N, psi (L v i) • (c • sandwichCLM (A i)))
    apply Finset.sum_congr rfl
    intro i _
    rw [smul_smul,mul_comm]
  · simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    ring
end
end CurrentKS.State

end OAI
