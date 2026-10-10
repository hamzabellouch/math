import OAI.Geometry.NodalSets.Coefficients.IntrinsicCoefficientMetric

namespace OAI

namespace Yau.Target
open Manifold Matrix Yau.Geometry Filter
open scoped ContDiff Topology
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule

variable (A : IntrinsicTensor) (hA : IntrinsicTensorSmooth A)
    (hs : ∀ x v w, A x v w = A x w v)
    (hp : ∀ x v, v ≠ 0 → 0 < A x v v)

include hA hs hp in
lemma intrinsicSphereChartTensor_smoothAt (p : Base) {z : BaseModel}
    (hz : z ∈ (extChartAt (𝓡 4) p).target) (i j : Fin 4) :
    ContDiffAt ℝ ∞ (fun w ↦ intrinsicSphereChartTensor A p w i j) z := by
  have h := baseChartMetric_inverse_smooth_at (intrinsicAmbientMatrix A) (fun _ ↦ 1)
    (intrinsicAmbientMatrix_smooth A hA) (intrinsicAmbientMatrix_posDef A hs hp)
    contMDiff_const (fun _ ↦ zero_lt_one) p hz i j
  apply h.congr_of_eventuallyEq
  filter_upwards [(isOpen_extChartAt_target p).mem_nhds hz] with w hw
  have he := intrinsic_horizontal_inverse A hs hp (fun _ ↦ 1) (fun _ ↦ zero_lt_one) p hw
  simpa only [inv_one,one_smul,baseChartMetric] using (congrArg (fun B : Matrix (Fin 4) (Fin 4) ℝ ↦ B i j) he).symm

include hA hs hp in
lemma intrinsicChartCoefficient_smoothAt (ρ : Base → ℝ)
    (hρ : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ ρ) (p : Base) {z : BaseModel}
    (hz : z ∈ (extChartAt (𝓡 4) p).target) :
    ContDiffAt ℝ ∞ (intrinsicChartCoefficient A ρ p) z := by
  apply ContDiffAt.prodMk _ (smooth_inverse_chart_comp ρ hρ p hz)
  change ContDiffAt ℝ ∞ (fun w ↦ matrixContravariant (intrinsicSphereChartTensor A p w)) z
  unfold matrixContravariant
  apply ContDiffAt.sum
  intro i _
  apply ContDiffAt.sum
  intro j _
  let : IsBoundedSMul ℝ ((BaseModel →L[ℝ] ℝ) →L[ℝ] BaseModel) :=
    IsBoundedSMul.of_norm_smul_le ContinuousLinearMap.opNorm_smul_le
  exact (intrinsicSphereChartTensor_smoothAt A hA hs hp p hz i j).smul contDiffAt_const

include hA hs hp in
lemma intrinsicChartCoefficient_actual_jet (ρ : Base → ℝ)
    (hρ : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ ρ) (hρp : ∀ x, 0 < ρ x)
    (p : Base) {z : BaseModel} (hz : z ∈ (extChartAt (𝓡 4) p).target) :
    coefficientMetricJet (intrinsicChartCoefficient A ρ p z,
      fderiv ℝ (intrinsicChartCoefficient A ρ p) z) =
      (matrixCovariant (baseChartMetric (intrinsicAmbientMatrix A) ρ p z),
        fderiv ℝ (fun w ↦ matrixCovariant (baseChartMetric (intrinsicAmbientMatrix A) ρ p w)) z) :=
  intrinsicChartCoefficient_metric_jet A hs hp ρ hρp p hz
    ((intrinsicChartCoefficient_smoothAt A hA hs hp ρ hρ p hz).differentiableAt (by simp))

end
end Yau.Target

end OAI
