import OAI.GroupTheory.PolycyclicRecognition.Geometry.GradedFlowLimit
import OAI.GroupTheory.PolycyclicRecognition.Analysis.RescaledMetricSmallness
import Mathlib.Topology.MetricSpace.IsometricSMul

namespace OAI

/-! # Metric convergence for pairs of rescaled chart points -/

noncomputable section

namespace PolycyclicRecognition

open Module Filter
open scoped Topology

variable {L G : Type*} [LieRing L] [LieAlgebra ℝ L]
  [Group G] [PseudoMetricSpace G] [IsIsometricSMul G G] {n c : ℕ}

omit [PseudoMetricSpace G] [IsIsometricSMul G G] in
/-- The coordinate of a quotient of exponential-chart points is the exact
Dynkin product. This identity transfers polynomial convergence to distance. -/
theorem exp_chart_difference (b : Basis (Fin n) ℝ L)
    (Exp : L → G) (hneg : ∀ x, Exp (-x) = (Exp x)⁻¹)
    (a : DynkinCoefficients c 2)
    (hm : ∀ x y, Exp (finiteDynkinPolynomial a ![x, y]) = Exp x * Exp y)
    (x y : Fin n → ℝ) :
    Exp (b.equivFun.symm (dynkinProduct a (basisBracket b) (-x) y)) =
      (Exp (b.equivFun.symm x))⁻¹ * Exp (b.equivFun.symm y) := by
  have he := basis_dynkinProduct b a (b.equivFun.symm (-x)) (b.equivFun.symm y)
  simp only [LinearEquiv.apply_symm_apply] at he
  rw [he, LinearEquiv.symm_apply_apply, hm, map_neg, hneg]

/-- If two normalized chart points approach the same point, their distance
in the original group, divided by the dilation, tends to zero. -/
theorem rescaled_chart_distance_tendsto_zero
    (b : Basis (Fin n) ℝ L) (cost : Fin n → ℝ)
    (hweight : ∀ i j k, b.repr ⁅b i, b j⁆ k ≠ 0 → cost i + cost j ≤ cost k)
    (Exp : L → G) (hinj : Function.Injective Exp) (hzero : Exp 0 = 1)
    (hneg : ∀ x, Exp (-x) = (Exp x)⁻¹)
    (hadd : ∀ x (s t : ℝ), Exp ((s + t) • x) = Exp (s • x) * Exp (t • x))
    (a : DynkinCoefficients c 2)
    (hm : ∀ x y, Exp (finiteDynkinPolynomial a ![x, y]) = Exp x * Exp y)
    {C : ℝ} (hC : 0 ≤ C)
    (hmetric : ∀ r : ℝ, 0 ≤ r → ∀ v : L,
      ‖(exponentialRescaleBasis b cost r).equivFun v‖ ≤ 1 →
        dist 1 (Exp v) ≤ C * Real.exp r)
    {ι : Type*} {l : Filter ι} (scale : ι → ℝ) (hscale : Tendsto scale l atTop)
    (x y : ι → Fin n → ℝ) {z : Fin n → ℝ}
    (hx : Tendsto x l (𝓝 z)) (hy : Tendsto y l (𝓝 z)) :
    Tendsto (fun i =>
      dist (Exp ((exponentialRescaleBasis b cost (scale i)).equivFun.symm (x i)))
        (Exp ((exponentialRescaleBasis b cost (scale i)).equivFun.symm (y i))) /
          Real.exp (scale i)) l (𝓝 0) := by
  let B₀ := gradedCoordinateBracket b cost
  let B := fun i => basisBracket (exponentialRescaleBasis b cost (scale i))
  have hB : Tendsto B l (𝓝 B₀) := by
    simpa only [B, B₀, Function.comp_def] using
      (basisBracket_rescale_tendsto b cost hweight).comp hscale
  have hcont : Continuous (fun p :
      ((Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) ×
        ((Fin n → ℝ) × (Fin n → ℝ)) => dynkinProduct a p.1 (-p.2.1) p.2.2) :=
    continuous_dynkinProduct
      (P := ((Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) ×
        ((Fin n → ℝ) × (Fin n → ℝ))) a (fun p => p.1) (fun p => -p.2.1) (fun p => p.2.2)
      continuous_fst continuous_snd.fst.neg continuous_snd.snd
  have hlim := gradedCoordinateBracket_groupLaws b cost hweight Exp hinj hzero hneg hadd a hm
  have hq : Tendsto (fun i => dynkinProduct a (B i) (-x i) (y i)) l (𝓝 0) := by
    have ht := (hcont.tendsto (B₀, (z, z))).comp (hB.prodMk_nhds (hx.prodMk_nhds hy))
    simpa only [Function.comp_def, B₀, hlim.2.2.2.1 z] using ht
  let v := fun i => (exponentialRescaleBasis b cost (scale i)).equivFun.symm
    (dynkinProduct a (B i) (-x i) (y i))
  have hv : Tendsto (fun i => (exponentialRescaleBasis b cost (scale i)).equivFun (v i))
      l (𝓝 0) := by simpa only [v, LinearEquiv.apply_symm_apply] using hq
  have ht := metric_sublinear_of_rescaled_coordinates_tendsto_zero b cost Exp hC hmetric
    scale hscale v hv
  convert ht using 1
  funext i
  congr 1
  rw [show Exp (v i) =
      (Exp ((exponentialRescaleBasis b cost (scale i)).equivFun.symm (x i)))⁻¹ *
        Exp ((exponentialRescaleBasis b cost (scale i)).equivFun.symm (y i)) from
      exp_chart_difference _ Exp hneg a hm (x i) (y i)]
  simpa only [inv_mul_cancel] using
    (dist_mul_left
      (Exp ((exponentialRescaleBasis b cost (scale i)).equivFun.symm (x i)))⁻¹
      (Exp ((exponentialRescaleBasis b cost (scale i)).equivFun.symm (x i)))
      (Exp ((exponentialRescaleBasis b cost (scale i)).equivFun.symm (y i)))).symm

end PolycyclicRecognition

end

end OAI
