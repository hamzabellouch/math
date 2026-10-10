import OAI.Analysis.Mahler.ExteriorCoefficient
import OAI.Analysis.Mahler.WedgeEven
import Mathlib.Analysis.Normed.Module.FiniteDimension

namespace OAI

open scoped BigOperators

namespace Mahler
variable {E J ι κ : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] [FiniteDimensional ℝ E]
  [Fintype J] [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

noncomputable def continuousCovectorVolume (l : ι → E →ₗ[ℝ] ℂ) : E [⋀^ι]→L[ℝ] ℂ :=
  { covectorVolume l with
    cont := by
      change Continuous (fun v => covectorVolume l v)
      simp only [covectorVolume_apply]
      apply Continuous.matrix_det
      fun_prop }

omit [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] in
@[simp] lemma continuousCovectorVolume_toAlternatingMap [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] (l : ι → E →ₗ[ℝ] ℂ) :
    (continuousCovectorVolume l).toAlternatingMap = covectorVolume l := rfl

noncomputable def basisContinuousWedge (basis : Module.Basis J ℝ E)
    (A : E [⋀^ι]→L[ℝ] ℂ) (B : E [⋀^κ]→L[ℝ] ℂ) : E [⋀^ι ⊕ κ]→L[ℝ] ℂ :=
  ∑ q : ι → J, ∑ r : κ → J,
    ((A (basis ∘ q) / (Fintype.card ι).factorial) *
      (B (basis ∘ r) / (Fintype.card κ).factorial)) •
      continuousCovectorVolume (Sum.elim (complexCoord basis ∘ q) (complexCoord basis ∘ r))

omit [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] in
lemma basisContinuousWedge_toAlternatingMap [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] (basis : Module.Basis J ℝ E)
    (A : E [⋀^ι]→L[ℝ] ℂ) (B : E [⋀^κ]→L[ℝ] ℂ) :
    (basisContinuousWedge basis A B).toAlternatingMap = wedge A.toAlternatingMap B.toAlternatingMap := by
  rw [alternating_basis_expansion_normalized basis A.toAlternatingMap,
    alternating_basis_expansion_normalized basis B.toAlternatingMap]
  simp only [wedge_sum_left, wedge_sum_right, wedge_smul_left, wedge_smul_right,
    wedge_covectorVolume, Finset.smul_sum, smul_smul]
  unfold basisContinuousWedge
  ext v
  simp only [ContinuousAlternatingMap.sum_apply, alternating_sum_eval,
    continuousCovectorVolume, ContinuousAlternatingMap.smul_apply, AlternatingMap.smul_apply, smul_eq_mul,
    ContinuousAlternatingMap.coe_toAlternatingMap]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r hr
  apply Finset.sum_congr rfl
  intro q hq
  ring_nf
  rfl

omit [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] in
lemma contDiffAt_basisContinuousWedge [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] (basis : Module.Basis J ℝ E) {n : WithTop ℕ∞}
    {A : E → E [⋀^ι]→L[ℝ] ℂ} {B : E → E [⋀^κ]→L[ℝ] ℂ} {x : E}
    (hA : ContDiffAt ℝ n A x) (hB : ContDiffAt ℝ n B x) :
    ContDiffAt ℝ n (fun y => basisContinuousWedge basis (A y) (B y)) x := by
  unfold basisContinuousWedge
  apply ContDiffAt.sum
  intro q hq
  apply ContDiffAt.sum
  intro r hr
  apply ContDiffAt.smul_const
  apply ContDiffAt.mul
  · exact ((ContinuousAlternatingMap.apply ℝ E ℂ (basis ∘ q)).contDiff.contDiffAt.comp x hA).div_const _
  · exact ((ContinuousAlternatingMap.apply ℝ E ℂ (basis ∘ r)).contDiff.contDiffAt.comp x hB).div_const _

end Mahler

end OAI
