import OAI.GroupTheory.PolycyclicRecognition.Geometry.ExponentialRepresentationInput
import OAI.GroupTheory.PolycyclicRecognition.Analysis.CoordinateChartSampling

namespace OAI

/-! # Actual factor-chart continuity and the exponential Cartan action -/

noncomputable section

namespace PolycyclicRecognition

open Module
open scoped Manifold

/-- The published nilpotent exponential chart makes every identified
linear coordinate chart continuous. -/
theorem continuous_model_exp_coordinates
    {E N L : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace N] [ChartedSpace E N] [Group N]
    [LieGroup (𝓘(ℝ, E)) ⊤ N] [T2Space N] [SimplyConnectedSpace N]
    [MeasurableSpace N] [BorelSpace N] [LieRing L] [LieAlgebra ℝ L]
    (haar : NilpotentExponentialHaarInput E N)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) N → N) (hExp : IsGroupExponential Exp)
    (e : L ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, E)) N)
    (hnil : LieRing.IsNilpotent (GroupLieAlgebra (𝓘(ℝ, E)) N))
    {n : ℕ} (b : Basis (Fin n) ℝ L) :
    Continuous (fun z => Exp (e (b.equivFun.symm z))) := by
  obtain ⟨⟨chart, hchart⟩, _⟩ := haar.2 Exp hExp hnil
  have hc := chart.continuous.comp
    ((b.map e.toLinearEquiv).equivFun.symm.toContinuousLinearEquiv.continuous)
  convert hc using 1
  ext z
  change Exp (e (b.equivFun.symm z)) = chart ((b.map e.toLinearEquiv).equivFun.symm z)
  rw [hchart]
  rfl

variable {EG G : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {ExpG : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H ExpG)

include M in
/-- The exact exponential action needed by the chart normalization formula
follows from the published faithful realization, with no new action input. -/
theorem cartan_action_exp_of_published_realization
    (hExpG : IsGroupExponential ExpG)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
    (haarD : NilpotentExponentialHaarInput F.D.modelSpace F.D.carrier)
    (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
    (h : H) (v : cartanRootIdeal H) :
    F.action (F.ExpD (F.D.equiv h)) (F.ExpN (F.N.equiv v)) =
      F.ExpN (F.N.equiv (cartanIdealAdjointAutomorphism T H h v)) := by
  obtain ⟨⟨chartN, hchartN⟩, _⟩ := haarN.2 F.ExpN F.isExpN
    (F.N.tangent_nilpotent (cartanRootIdeal_nilpotent H T))
  obtain ⟨⟨chartD, hchartD⟩, _⟩ := haarD.2 F.ExpD F.isExpD
    (F.D.tangent_nilpotent inferInstance)
  have hbijN : Function.Bijective F.ExpN := funext hchartN ▸ chartN.bijective
  have hbijD : Function.Bijective F.ExpD := funext hchartD ▸ chartD.bijective
  rw [cartan_action_eq_adjoint_of_published_realization T M F hExpG realize
    hbijN hbijD dynkinN, cartanLog_exp]
  exact integrateNilpotentLieEquiv_apply_exp F.N.equiv F.ExpN hbijN dynkinN F.isExpN
    M.bound_zero (cartanIdealAdjointAutomorphism T H h) v

end PolycyclicRecognition

end

end OAI
