import OAI.Geometry.NodalSets.Coefficients.IntrinsicCoefficientMap

namespace OAI

namespace Yau.Target
open Manifold Matrix Yau.Geometry Filter
open scoped ContDiff Topology
noncomputable section

variable (A : IntrinsicTensor) (hs : ∀ x v w, A x v w = A x w v)
    (hp : ∀ x v, v ≠ 0 → 0 < A x v v)
    (ρ : Base → ℝ) (hρ : ∀ x, 0 < ρ x)

include hs hp hρ in
lemma intrinsicChartCoefficient_metric (p : Base) {z : BaseModel}
    (hz : z ∈ (extChartAt (𝓡 4) p).target) :
    coefficientMetricValue (intrinsicChartCoefficient A ρ p z) =
      matrixCovariant (baseChartMetric (intrinsicAmbientMatrix A) ρ p z) := by
  let B := intrinsicSphereChartTensor A p z
  let G := baseChartMetric (intrinsicAmbientMatrix A) ρ p z
  let r := ρ ((extChartAt (𝓡 4) p).symm z)
  have hr : 0 < r := hρ _
  have hB : B.PosDef := intrinsicSphereChartTensor_posDef A hs hp p hz
  have hG : G.PosDef := sphereWeightedChartMatrix_posDef _
    (intrinsicAmbientMatrix_posDef A hs hp _) hr p hz
  have hi : G⁻¹ = r⁻¹ • B := intrinsic_horizontal_inverse A hs hp ρ hρ p hz
  have hb : B = r • G⁻¹ := by rw [hi,smul_smul,mul_inv_cancel₀ hr.ne',one_smul]
  have hbi : B⁻¹ = r⁻¹ • G := by
    apply Matrix.inv_eq_left_inv
    rw [hb,smul_mul_assoc,mul_smul_comm,smul_smul,inv_mul_cancel₀ hr.ne',one_smul,
      mul_nonsing_inv G (isUnit_iff_ne_zero.mpr hG.det_pos.ne')]
  change coefficientMetricValue (matrixContravariant B,r) = matrixCovariant G
  rw [coefficientMetric_matrix B hB r,hbi,smul_smul,mul_inv_cancel₀ hr.ne',one_smul]

include hs hp hρ in
lemma intrinsicChartCoefficient_metric_eventually (p : Base) {z : BaseModel}
    (hz : z ∈ (extChartAt (𝓡 4) p).target) :
    (coefficientMetricValue ∘ intrinsicChartCoefficient A ρ p) =ᶠ[𝓝 z]
      (fun w ↦ matrixCovariant (baseChartMetric (intrinsicAmbientMatrix A) ρ p w)) := by
  filter_upwards [(isOpen_extChartAt_target p).mem_nhds hz] with w hw
  exact intrinsicChartCoefficient_metric A hs hp ρ hρ p hw

include hs hp hρ in
lemma intrinsicChartCoefficient_metric_fderiv (p : Base) {z : BaseModel}
    (hz : z ∈ (extChartAt (𝓡 4) p).target) :
    fderiv ℝ (coefficientMetricValue ∘ intrinsicChartCoefficient A ρ p) z =
      fderiv ℝ (fun w ↦ matrixCovariant (baseChartMetric (intrinsicAmbientMatrix A) ρ p w)) z :=
  (intrinsicChartCoefficient_metric_eventually A hs hp ρ hρ p hz).fderiv_eq

include hs hp hρ in
lemma intrinsicChartCoefficient_metric_jet (p : Base) {z : BaseModel}
    (hz : z ∈ (extChartAt (𝓡 4) p).target)
    (hc : DifferentiableAt ℝ (intrinsicChartCoefficient A ρ p) z) :
    coefficientMetricJet (intrinsicChartCoefficient A ρ p z,
      fderiv ℝ (intrinsicChartCoefficient A ρ p) z) =
      (matrixCovariant (baseChartMetric (intrinsicAmbientMatrix A) ρ p z),
        fderiv ℝ (fun w ↦ matrixCovariant (baseChartMetric (intrinsicAmbientMatrix A) ρ p w)) z) := by
  rw [coefficientMetricJet_actual _ z hc
    (positiveContravariantEquiv _ (intrinsicChartCoefficient_positive A hs hp ρ p hz)) rfl,
    intrinsicChartCoefficient_metric A hs hp ρ hρ p hz,
    intrinsicChartCoefficient_metric_fderiv A hs hp ρ hρ p hz]

end
end Yau.Target

end OAI
