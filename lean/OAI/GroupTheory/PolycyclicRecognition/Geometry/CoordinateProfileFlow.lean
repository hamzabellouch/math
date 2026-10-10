import OAI.GroupTheory.PolycyclicRecognition.Geometry.GradedFlowLimit
import OAI.GroupTheory.PolycyclicRecognition.Analysis.CoordinateChartSampling
import OAI.GroupTheory.PolycyclicRecognition.Analysis.BasisDynkinHaar
import OAI.GroupTheory.PolycyclicRecognition.Algebra.MappedBasisBrackets

namespace OAI

/-! # The actual coordinate flows used by the profile cutoffs -/

noncomputable section

namespace PolycyclicRecognition

open Module MeasureTheory Filter
open scoped Manifold Topology NNReal

/-- The full rescaled flow converges as a continuous map, so the cutoff
construction applies simultaneously to every compact time interval. -/
theorem rescaled_horizontal_flow_tendsto
    {L : Type*} [LieRing L] [LieAlgebra ℝ L] {n c : ℕ}
    (a : DynkinCoefficients c 2) (b : Basis (Fin n) ℝ L) (cost : Fin n → ℝ)
    (hweight : ∀ i j k, b.repr ⁅b i, b j⁆ k ≠ 0 → cost i + cost j ≤ cost k)
    (v : L) (hv : ∀ j, b.repr v j ≠ 0 → 1 ≤ cost j) :
    Tendsto (fun r => dynkinFlowMap a (basisBracket (exponentialRescaleBasis b cost r))
      ((exponentialRescaleBasis b cost r).equivFun (Real.exp r • v))) atTop
      (𝓝 (dynkinFlowMap a (gradedCoordinateBracket b cost) (gradedGenerator b cost 1 v))) := by
  apply dynkinFlowMap_tendsto a (basisBracket_rescale_tendsto b cost hweight)
  simpa only [mul_one] using rescaled_generator_tendsto b cost 1 v hv

/-- In actual exponential coordinates the horizontal flow preserves the
same Lebesgue measure at every scale and time. -/
theorem measurePreserving_model_horizontal_flow
    {E D L : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace D] [ChartedSpace E D] [Group D]
    [LieGroup (𝓘(ℝ, E)) ⊤ D] [T2Space D] [SimplyConnectedSpace D]
    [MeasurableSpace D] [BorelSpace D] [LieRing L] [LieAlgebra ℝ L]
    (haar : NilpotentExponentialHaarInput E D)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) D → D) (hExp : IsGroupExponential Exp)
    (e : L ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, E)) D)
    (hnil : LieRing.IsNilpotent (GroupLieAlgebra (𝓘(ℝ, E)) D))
    {n c : ℕ} (b : Basis (Fin n) ℝ L) (a : DynkinCoefficients c 2)
    (hm : ∀ x y, Exp (finiteDynkinPolynomial a ![x, y]) = Exp x * Exp y)
    (r t : ℝ) (v : L) :
    MeasurePreserving (fun z => dynkinFlowMap a (basisBracket b) (b.equivFun (r • v)) (z, t))
      volume volume := by
  have h := measurePreserving_basis_dynkin_right haar Exp hExp hnil
    (b.map e.toLinearEquiv) a hm (t • b.equivFun (r • v))
  rw [basisBracket_map_lieEquiv] at h
  exact h

/-- Right translation in the ambient group changes the second coordinate
by exactly the polynomial flow used in the cutoff construction. -/
theorem coordinateChartPoint_horizontal_flow
    {G N D LN LD : Type*} [Group G] [MetricSpace G]
    [IsTopologicalGroup G] [IsIsometricSMul G G] [Group N] [Group D]
    [LieRing LN] [LieAlgebra ℝ LN] [LieRing LD] [LieAlgebra ℝ LD]
    {n m c : ℕ} {Λ : ℝ≥0}
    (p : NormalizedPair G Λ) (x : G) (ι : N →* G) (κ : D →* G)
    (ExpN : LN → N) (ExpD : LD → D)
    (bN : Basis (Fin n) ℝ LN) (bD : Basis (Fin m) ℝ LD) (k : N)
    (a : DynkinCoefficients c 2)
    (hm : ∀ x y, ExpD (finiteDynkinPolynomial a ![x, y]) = ExpD x * ExpD y)
    (v : LD) (r t : ℝ) (z : (Fin n → ℝ) × (Fin m → ℝ)) :
    (κ (ExpD ((r * t) • v)))⁻¹ • coordinateChartPoint p x ι κ ExpN ExpD bN bD k z =
      coordinateChartPoint p x ι κ ExpN ExpD bN bD k
        (z.1, dynkinFlowMap a (basisBracket bD) (bD.equivFun (r • v)) (z.2, t)) := by
  rw [coordinateChartPoint_right p x ι κ ExpN ExpD bN bD k a hm]
  have he : bD.equivFun ((r * t) • v) = t • bD.equivFun (r • v) := by
    simp only [map_smul, smul_smul, mul_comm r t]
  rw [he]
  rfl

end PolycyclicRecognition

end

end OAI
