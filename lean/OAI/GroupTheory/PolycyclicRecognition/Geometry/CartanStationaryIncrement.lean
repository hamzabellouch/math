import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanErgodicIncrement
import OAI.GroupTheory.PolycyclicRecognition.Analysis.ErgodicMixtureLimits
import OAI.GroupTheory.PolycyclicRecognition.Analysis.PairErgodic
import Mathlib.MeasureTheory.Measure.RegularityCompacts

namespace OAI

/-! # Stationary increments through the actual ergodic decomposition -/

noncomputable section

namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule MeasureTheory Metric Set
open scoped Manifold NNReal ENNReal Pointwise

attribute [local instance] stationaryL2Action zeroMeanL2Action

variable {EG G W : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G] [IsIsometricSMul G G]
  [ProperSpace G] [SecondCountableTopology G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  [MeasurableSpace W] [BorelSpace W] [SecondCountableTopology W]
  {Λ : ℝ≥0} [MeasurableSpace (NormalizedPair G Λ)] [BorelSpace (NormalizedPair G Λ)]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H Exp)
  (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G,
    LinearMap.trace ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G) (ad ℝ _ x) = 0)
  (eW : HeightSpace T.character ≃ₗ[ℝ] W) (π : G →* Multiplicative W)
  (hπExp : ∀ x, (π (Exp x)).toAdd = eW (heightProjection T.character x))
  (chartN : GroupLieAlgebra (𝓘(ℝ, F.N.modelSpace)) F.N.carrier ≃ₜ F.N.carrier)
  (hchartN : ∀ x, chartN x = F.ExpN x)
  (chartD : GroupLieAlgebra (𝓘(ℝ, F.D.modelSpace)) F.D.carrier ≃ₜ F.D.carrier)
  (hchartD : ∀ x, chartD x = F.ExpD x)
  (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
  (dynkinD : NilpotentDynkinExpansionInput F.D.modelSpace F.D.carrier)
  (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
  (haarD : NilpotentExponentialHaarInput F.D.modelSpace F.D.carrier)

include hunimod hπExp hchartN hchartD dynkinN dynkinD haarN haarD in
/-- Along each actual Cartan exponential ray, normalized increments
approach the finite canonical label set for every fixed invariant probability. The integrand uses the whole finite
label set, so no measurable choice of component labels is needed. -/
theorem increments_tendsto_labels_of_invariant_probability
    (hExp : IsGroupExponential Exp)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (m : Measure G) [m.IsHaarMeasure] [m.IsMulRightInvariant]
    (μ : Measure (NormalizedPair G Λ)) [IsProbabilityMeasure μ]
    [SMulInvariantMeasure G (NormalizedPair G Λ) μ]
    (hdec : ErgodicDecompositionInput G (NormalizedPair G Λ))
    (hvan : ∀ (ν : Measure (NormalizedPair G Λ)) [IsProbabilityMeasure ν]
      [ErgodicSMul G (NormalizedPair G Λ) ν],
      ReducedCohomologyInput G (ZeroMeanL2 (W := W) ν))
    (hΛ : 0 < (Λ : ℝ)) {K : ℝ≥0}
    (hLip : LipschitzWith K (fun g => (π g).toAdd))
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (hφ : ∀ d, F.action d = M.adjointGroupAutomorphism T F.N.equiv F.ExpN F.isExpN
      (by rw [← show chartN = F.ExpN from funext hchartN]; exact chartN.bijective) dynkinN
      (cartanLog H F.D.equiv F.ExpD
        (by rw [← show chartD = F.ExpD from funext hchartD]; exact chartD.bijective) d))
    (hpath : ∀ g : G, ∃ γ : ℝ → G, γ 0 = 1 ∧ γ 1 = g ∧
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ u ∈ Icc (0 : ℝ) 1,
        dist (γ t) (γ u) ≤ dist 1 g * |t - u|)
    (v : H) :
    Filter.Tendsto (fun r : ℝ => ∫⁻ p,
      ENNReal.ofReal (infDist (r⁻¹ • pairHeight π (Exp (r • (v : GroupLieAlgebra (𝓘(ℝ, EG)) G))) p)
        (Set.range (fun A : supportSymmetryGroup (M.supportIn T hunimod eW) =>
          A.val (eW (heightProjection T.character v))))) ∂μ)
      Filter.atTop (nhds 0) := by
  let w := eW (heightProjection T.character v)
  let S := Set.range (fun A : supportSymmetryGroup (M.supportIn T hunimod eW) => A.val w)
  let f : ℝ → NormalizedPair G Λ → ℝ≥0∞ := fun r p =>
    ENNReal.ofReal (infDist (r⁻¹ • pairHeight π
      (Exp (r • (v : GroupLieAlgebra (𝓘(ℝ, EG)) G))) p) S)
  obtain ⟨κ, hκ, _, hbary⟩ := hdec μ inferInstance inferInstance
  have hκm : ∀ s : Set (NormalizedPair G Λ), MeasurableSet s →
      Measurable (fun x => κ x s) := fun s hs => (hbary s hs).1
  have hκb : ∀ s : Set (NormalizedPair G Λ), MeasurableSet s →
      μ s = ∫⁻ x, κ x s ∂μ := fun s hs => (hbary s hs).2
  let g : ℝ → G := fun r => Exp (r • (v : GroupLieAlgebra (𝓘(ℝ, EG)) G))
  have hd : Continuous g := continuous_exp_line_of_published_realization T Exp hExp realize v
  obtain ⟨C, hC, hb⟩ := continuous_flow_coarse_bound g hd
    (by simp [g, hExp.map_zero]) (fun s t => hExp.map_add_smul v s t)
  have hsize (r : ℝ) (hr : 1 ≤ r) : dist 1 (g r) ≤ (2 * C) * r := by
    have h := hb r
    rw [abs_of_nonneg (by linarith : 0 ≤ r)] at h
    exact h.trans (by nlinarith)
  have hw : w ∈ S := ⟨1, rfl⟩
  apply tendsto_lintegral_of_componentwise_bounded μ κ hκm hκb f
    (fun r => ENNReal.measurable_ofReal.comp
      (continuous_pair_label_distance π hLip.continuous (g r) r S).measurable)
    (B := ENNReal.ofReal ((K : ℝ) * Λ * (2 * C) + ‖w‖)) ENNReal.ofReal_ne_top
  · filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with r hr
    intro x
    let := (hκ x).1
    calc
      ∫⁻ y, f r y ∂κ x ≤ ∫⁻ _, ENNReal.ofReal ((K : ℝ) * Λ * (2 * C) + ‖w‖) ∂κ x := by
        apply lintegral_mono
        intro p
        exact ENNReal.ofReal_le_ofReal
          (pair_label_distance_le π hLip hr (by positivity) (hsize r hr) hw p)
      _ = _ := by simp
  · intro x
    let := (hκ x).1
    let := (hκ x).2
    exact M.increments_tendsto_labels_of_ergodic_probability
      T F hunimod eW π hπExp chartN hchartN chartD hchartD dynkinN dynkinD haarN haarD
      hExp realize m (κ x) (hvan (κ x)) hΛ hLip b₀ hφ hpath v

end PolycyclicRecognition.CartanWordModel

end

end OAI
