import OAI.MeasureTheory.Falconer.Graphs.GraphOriginalFubini
import OAI.MeasureTheory.Falconer.Graphs.GraphFourTransformExpansion

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

theorem sourceGraphFourTransform_chart
    (ρ : Fin 4 → Measure Plane) [∀ i, IsFiniteMeasure (ρ i)]
    (X : Fin 4 → Set Plane) (M : Fin 4 → ℝ)
    (b : Fin 4 → Plane → UnitCircle → ℂ) (W : UnitCircle × UnitCircle → ℂ)
    (hb : ∀ i, Measurable (fun p : Plane × UnitCircle => b i p.1 p.2))
    (hbcont : ∀ i x, Continuous (b i x)) (hW : Continuous W)
    (B : Fin 4 → ℝ) (hB : ∀ i, 0 ≤ B i) (hbound : ∀ i x ω, ‖b i x ω‖ ≤ B i)
    (hw : ∀ p, ‖W p‖ ≤ 1) {Ψ : ℝ → ℝ} (hΨ : Continuous Ψ)
    (hsupp : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4:ℝ) 4)
    {C : ℝ} (hC : 0 ≤ C) (hc : ∀ t, |Ψ t| ≤ C) {R : ℝ} (hR : 0 < R) (axis : ℝ)
    (hchart : ∀ φ z, W (sourceUnitDirection (φ+Real.arctan z),
      sourceUnitDirection (φ-Real.arctan z+axis)) ≠ 0 → |z| ≤ 4) :
    R⁻¹ • (∫ r : ℝ, ∫ u, ∫ v, Ψ (r/R) • sourceGraphFourTransform ρ X M b W r u v
      ∂sourceArcLength ∂sourceArcLength) =
      ((M 0*M 1)*(M 2*M 3))⁻¹ •
        (∫ p : ℝ × Plane, ∫ x, graphTransport (graphFourKernel b W x) Ψ R axis p
          ∂Measure.pi (fun i => (ρ i).restrict (X i))) := by
  let μ := Measure.pi (fun i => (ρ i).restrict (X i))
  let c := ((M 0*M 1)*(M 2*M 3))⁻¹
  have he (r : ℝ) (u v : UnitCircle) :
      Ψ (r/R) • sourceGraphFourTransform ρ X M b W r u v =
        c • (∫ x, graphOriginalKernel b W Ψ R (r,(u,v)) x ∂μ) := by
    rw [sourceGraphFourTransform_endpoint_integral]
    change Ψ (r/R) • (c • (∫ x, graphFourKernel b W x r u v ∂μ)) = _
    rw [smul_comm]
    apply congrArg (fun value : ℂ => c • value)
    exact (integral_smul _ _).symm
  simp_rw [he, integral_smul]
  rw [smul_comm (R⁻¹) c]
  apply congrArg (fun value : ℂ => c • value)
  rw [graphOriginalKernel_spatial_swap μ b W hb hW.measurable B hB hbound hw
    hΨ.measurable hsupp hC hc hR]
  exact graphFourKernel_spatial_chart μ b W hb hbcont hW B hB hbound hw hΨ hsupp hC hc hR axis hchart

end PlanarFalconer

end OAI
