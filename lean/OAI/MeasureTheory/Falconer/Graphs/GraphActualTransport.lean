import OAI.MeasureTheory.Falconer.Fourier.GraphKernelBounds
import OAI.MeasureTheory.Falconer.Graphs.GraphTransportIntegrability

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ComplexConjugate

theorem graphFourKernel_weight_ne_zero (b : Fin 4 → Plane → UnitCircle → ℂ)
    (W : UnitCircle × UnitCircle → ℂ) (x : Fin 4 → Plane) (r : ℝ) (u v : UnitCircle)
    (h : graphFourKernel b W x r u v ≠ 0) : W (u,v) ≠ 0 := by
  intro hz
  exact h (by simp [graphFourKernel, graphFourAmplitude, hz])

theorem graphDistanceWeight_parameter (axis : ℝ) (n j k : ℕ) (φ z : ℝ)
    (h : graphDistanceWeight axis n j k
      (sourceUnitDirection (φ+Real.arctan z), sourceUnitDirection (φ-Real.arctan z)) ≠ 0) :
    |z| ≤ 4 := by
  have hu : sourceConeCircle axis (sourceUnitDirection (φ+Real.arctan z)) ≠ 0 := by
    intro hz; exact h (by simp [graphDistanceWeight, hz])
  have hv : sourceConeCircle axis (sourceUnitDirection (φ-Real.arctan z)) ≠ 0 := by
    intro hz; exact h (by simp [graphDistanceWeight, hz])
  have hb := sourceConeCircle_plus_nondegenerate axis _ _ (subset_closure hu) (subset_closure hv)
  exact (graph_parameter_bound φ z ((by norm_num : (1/2:ℝ) ≤ 6/5).trans hb)).2

theorem graphProductWeight_parameter (plus : Bool) (n j k : ℕ) (φ z : ℝ)
    (h : graphProductWeight plus n j k
      (sourceUnitDirection (φ+Real.arctan z),
        sourceUnitDirection (φ-Real.arctan z+(if plus then 0 else Real.pi))) ≠ 0) :
    |z| ≤ 4 := by
  cases plus
  · apply graph_minus_support_parameter φ z
    apply subset_closure
    intro hz
    exact h (by simp [graphProductWeight, hz])
  · apply graph_plus_support_parameter φ z
    apply subset_closure
    intro hz
    exact h (by simp [graphProductWeight, hz])

theorem graphFourKernel_transport_integrable
    (b : Fin 4 → Plane → UnitCircle → ℂ) (W : UnitCircle × UnitCircle → ℂ)
    (hb : ∀ i x, Continuous (b i x)) (hW : Continuous W)
    (B : Fin 4 → ℝ) (hB : ∀ i, 0 ≤ B i) (hbound : ∀ i x ω, ‖b i x ω‖ ≤ B i)
    (hw : ∀ p, ‖W p‖ ≤ 1) {Ψ : ℝ → ℝ} (hΨ : Continuous Ψ)
    (hsupp : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4:ℝ) 4)
    {C : ℝ} (hC : 0 ≤ C) (hc : ∀ t, |Ψ t| ≤ C) (R axis : ℝ)
    (hchart : ∀ φ z, W (sourceUnitDirection (φ+Real.arctan z),
      sourceUnitDirection (φ-Real.arctan z+axis)) ≠ 0 → |z| ≤ 4)
    (x : Fin 4 → Plane) :
    Integrable (graphTransport (graphFourKernel b W x) Ψ R axis) := by
  apply graphTransport_integrable (graphFourKernel_continuous b W x
    (fun i => hb i (x i)) hW).measurable hΨ.measurable hsupp
    (mul_nonneg (mul_nonneg (hB 0) (hB 1)) (mul_nonneg (hB 2) (hB 3))) hC
    (graphFourKernel_norm_le b W B hB hbound hw x) hc R axis
  intro r φ z hn
  exact hchart φ z (graphFourKernel_weight_ne_zero b W x r _ _ hn)

theorem graphFourKernel_chart_product
    (b : Fin 4 → Plane → UnitCircle → ℂ) (W : UnitCircle × UnitCircle → ℂ)
    (hb : ∀ i x, Continuous (b i x)) (hW : Continuous W)
    (B : Fin 4 → ℝ) (hB : ∀ i, 0 ≤ B i) (hbound : ∀ i x ω, ‖b i x ω‖ ≤ B i)
    (hw : ∀ p, ‖W p‖ ≤ 1) {Ψ : ℝ → ℝ} (hΨ : Continuous Ψ)
    (hsupp : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4:ℝ) 4)
    {C : ℝ} (hC : 0 ≤ C) (hc : ∀ t, |Ψ t| ≤ C) {R : ℝ} (hR : 0 < R) (axis : ℝ)
    (hchart : ∀ φ z, W (sourceUnitDirection (φ+Real.arctan z),
      sourceUnitDirection (φ-Real.arctan z+axis)) ≠ 0 → |z| ≤ 4)
    (x : Fin 4 → Plane) :
    R⁻¹ • (∫ r : ℝ, ∫ u, ∫ v, Ψ (r/R) • graphFourKernel b W x r u v
      ∂sourceArcLength ∂sourceArcLength) =
      ∫ p : ℝ × Plane, graphTransport (graphFourKernel b W x) Ψ R axis p := by
  have hi := graphFourKernel_transport_integrable b W hb hW B hB hbound hw hΨ
    hsupp hC hc R axis hchart x
  rw [Measure.volume_eq_prod] at hi ⊢
  rw [integral_prod _ hi]
  calc
    _ = ∫ z : ℝ, ∫ η in graphGlobalAnnulus (1/4) 4 z,
        graphTransport (graphFourKernel b W x) Ψ R axis (z,η) :=
      graphFourKernel_chart b W x (fun i => hb i (x i)) hW hΨ hsupp hR axis
    _ = _ := integral_congr_ae (Filter.Eventually.of_forall fun parameter =>
      graphTransport_annulus_integral _ hsupp R axis parameter)

end PlanarFalconer

end OAI
