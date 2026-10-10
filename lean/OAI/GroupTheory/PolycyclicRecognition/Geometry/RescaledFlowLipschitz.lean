import OAI.GroupTheory.PolycyclicRecognition.Geometry.SupportedFlowLipschitz
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CoordinateFlowProfileIdentity
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CoarseFlowBounds

namespace OAI

/-! # Coarse one-parameter bounds give Lipschitz limiting profiles -/

noncomputable section
namespace PolycyclicRecognition

open Module Filter MeasureTheory
open scoped Topology NNReal

theorem rescaled_profile_flow_dist_le
    {L D G W : Type*} [LieRing L] [LieAlgebra ℝ L] [Group D]
    [Group G] [PseudoMetricSpace G] [IsIsometricSMul G G]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    {n c : ℕ} (Exp : L → D) (κ : D →* G) (b : Basis (Fin n) ℝ L)
    (a : DynkinCoefficients c 2)
    (hm : ∀ x y, Exp (finiteDynkinPolynomial a ![x, y]) = Exp x * Exp y)
    (v : L) {C : ℝ}
    (hcoarse : ∀ s t : ℝ, dist (κ (Exp (s • v))) (κ (Exp (t • v))) ≤
      C * (1 + |t - s|))
    {K : ℝ≥0} (J : G → W) (hJ : LipschitzWith K J)
    (x k : G) (r : ℝ) (z : Fin n → ℝ) (s t : ℝ) :
    let φ := fun y => κ (Exp (b.equivFun.symm y))
    let F := dynkinFlowMap a (basisBracket b) (b.equivFun (Real.exp r • v))
    dist (rescaledMapProfile J x k r φ (F (z, s)))
      (rescaledMapProfile J x k r φ (F (z, t))) ≤
        (K : ℝ) * C * |s - t| + (K : ℝ) * C / Real.exp r := by
  dsimp only
  have hb := rescaledMapProfile_dist_le hJ x k r
    (fun y => κ (Exp (b.equivFun.symm y)))
    (dynkinFlowMap a (basisBracket b) (b.equivFun (Real.exp r • v)) (z, s))
    (dynkinFlowMap a (basisBracket b) (b.equivFun (Real.exp r • v)) (z, t))
  simp only [exp_basis_horizontal_flow Exp b a hm, map_mul, dist_mul_left] at hb
  apply hb.trans
  calc
    _ ≤ (K : ℝ) * (C * (1 + |Real.exp r * t - Real.exp r * s|) / Real.exp r) :=
      mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_right (hcoarse _ _) (Real.exp_pos r).le) K.coe_nonneg
    _ = _ := by
      rw [← mul_sub, abs_mul, abs_of_pos (Real.exp_pos r), abs_sub_comm t s]
      field_simp
      ring

/-- All supported weak limits of the actual rescaled profiles are
Lipschitz along the graded flow. The constant is independent of the base
point and of the supported profile. -/
theorem lipschitz_supported_rescaled_flow
    {L D G W A : Type*} [LieRing L] [LieAlgebra ℝ L] [Group D]
    [Group G] [PseudoMetricSpace G] [IsIsometricSMul G G]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [MeasurableSpace A]
    {n c : ℕ} (Exp : L → D) (κ : D →* G) (b : Basis (Fin n) ℝ L)
    (cost : Fin n → ℝ)
    (hweight : ∀ i j k, b.repr ⁅b i, b j⁆ k ≠ 0 → cost i + cost j ≤ cost k)
    (a : DynkinCoefficients c 2)
    (hm : ∀ x y, Exp (finiteDynkinPolynomial a ![x, y]) = Exp x * Exp y)
    (v : L) (hv : ∀ j, b.repr v j ≠ 0 → 1 ≤ cost j)
    (hd : Continuous (fun t : ℝ => κ (Exp (t • v))))
    (hd0 : κ (Exp ((0 : ℝ) • v)) = 1)
    (hmul : ∀ s t : ℝ, κ (Exp ((s + t) • v)) = κ (Exp (s • v)) * κ (Exp (t • v)))
    (scale : ℕ → ℝ) (hscale : Tendsto scale atTop atTop)
    {K : ℝ≥0} (J : ℕ → A → G → W) (hJ : ∀ n u, LipschitzWith K (J n u))
    (x suffix : ℕ → A → G)
    (S : Set C((Fin n → ℝ), W)) (hS : IsCompact S)
    [MeasurableSpace S] [BorelSpace S] [HasOuterApproxClosed S]
    (samples : ℕ → ProbabilityMeasure A) (profile : ℕ → A → S)
    (hp : ∀ n, Measurable (profile n)) (ν : ProbabilityMeasure S)
    (hν : Tendsto (fun n => ProbabilityMeasure.map (samples n) (profile n)) atTop (𝓝 ν))
    (hactual : ∀ i u z, (profile i u).val z =
      rescaledMapProfile (J i u) (x i u) (suffix i u) (scale i)
        (fun z => κ (Exp ((exponentialRescaleBasis b cost (scale i)).equivFun.symm z))) z) :
    ∃ C : ℝ≥0, ∀ (f : S), f ∈ (ν : Measure S).support → ∀ z,
      LipschitzWith C (fun t : ℝ => f.val
        (dynkinFlowMap a (gradedCoordinateBracket b cost) (gradedGenerator b cost 1 v) (z, t))) := by
  obtain ⟨C, hC, hcoarse⟩ := continuous_flow_coarse_dist _ hd hd0 hmul
  let C' : ℝ≥0 := ⟨K * C, mul_nonneg K.coe_nonneg hC⟩
  let Fn := fun i => dynkinFlowMap a (basisBracket (exponentialRescaleBasis b cost (scale i)))
    ((exponentialRescaleBasis b cost (scale i)).equivFun (Real.exp (scale i) • v))
  let F := dynkinFlowMap a (gradedCoordinateBracket b cost) (gradedGenerator b cost 1 v)
  have hF : Tendsto Fn atTop (𝓝 F) := (rescaled_horizontal_flow_tendsto a b cost hweight v hv).comp hscale
  let ε := fun i => (K : ℝ) * C / Real.exp (scale i)
  have hε : Tendsto ε atTop (𝓝 0) :=
    (Real.tendsto_exp_atTop.comp hscale).const_div_atTop _
  refine ⟨C', fun f hf z => ?_⟩
  apply lipschitz_supported_profile_flow S hS samples profile hp ν hν Fn F hF ε hε C' z ?_ hf
  apply Eventually.of_forall
  intro i u s t
  simp only [hactual]
  exact rescaled_profile_flow_dist_le Exp κ (exponentialRescaleBasis b cost (scale i))
    a hm v hcoarse (J i u) (hJ i u) (x i u) (suffix i u) (scale i) z s t

end PolycyclicRecognition

end

end OAI
