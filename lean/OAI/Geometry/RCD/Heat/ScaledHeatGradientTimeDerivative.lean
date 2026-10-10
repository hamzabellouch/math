import OAI.Geometry.RCD.Heat.ScaledHeatContinuousHamiltonJacobi
import OAI.Geometry.RCD.Heat.CompactTimePairingDerivative
import OAI.Geometry.RCD.Heat.ScaledHeatHamiltonJacobiFromCompactness
import OAI.Geometry.RCD.Heat.ScaledHeatMeasurableSobolev
import OAI.Geometry.RCD.Heat.ScaledHeatIteratedFromCompactness
import OAI.Geometry.RCD.Harmonic.SubtypeL2PairingLimit
import OAI.Geometry.RCD.Heat.ScaledHeatCutoffEnergyLimit
import OAI.Geometry.RCD.Sobolev.WeightedSobolevIntegralLower

namespace OAI

/-! # Compact gradient energy bounded by ordinary time derivatives

The continuous small-noise limit has absolutely continuous compact spatial
pairings. Their almost-everywhere derivatives replace the distributional
time derivative in the weighted Hamilton--Jacobi inequality.
-/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped NNReal ENNReal Topology
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X)
  (hn : 2 ≤ n) (p : X) [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]

theorem scaled_heat_gradient_time_derivative_of_compactness (hK : K ≤ 0)
    {S : Set X} [CompactSpace S] (ν : Measure S) [IsProbabilityMeasure ν]
    (ρ : X → ℝ) (hρ : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x) {B : ℝ≥0}
    (hB : ∀ᵐ x ∂hausdorff n X, |ρ x| ≤ B)
    (hν : ν.map Subtype.val = (hausdorff n X).withDensity (fun x => ENNReal.ofReal (ρ x)))
    (F : ℕ → C(S,ℝ)) (hF : ∀ k a, 0 < F k a)
    (ε : ℕ → ℝ) (hε : ∀ k, 0 < ε k) (hε1 : ∀ k, ε k ≤ 1)
    (hε0 : Tendsto ε atTop (𝓝 0))
    (z : X) {R : ℝ} (hR : 0 ≤ R) (hdist : ∀ a : S, dist z a ≤ R)
    (G : ℝ → X → ℝ) (ι : ℕ → ℕ) (hι : StrictMono ι) (N : Set ℝ) (hN : N.Countable)
    (hG : Measurable (Function.uncurry G))
    (hdata : ∀ r : ℝ, 0 ≤ r → ∀ δ : ℝ, (hδ : 0 < δ) →
      ∃ (L : ℝ≥0) (M : ℝ), 0 ≤ M ∧ ∀ t, t ∈ Ioo δ 1 → t ∉ N →
        LipschitzOnWith L (G t) (closedBall z r) ∧
        (∀ x ∈ closedBall z r, |G t x| ≤ M) ∧
        TendstoUniformly (fun k (x : closedBall z r) =>
          hX.fixedGaugeScaledPotential hn p ν (F (ι k)) (ε (ι k)) (hε (ι k)) δ hδ z t x)
          (fun x => G t x) atTop) :
    let H := goodTimeExtension N G
    let μ := hausdorff n X
    let Q := hX.quadratic
    ContinuousOn (Function.uncurry H) (Ioo 0 1 ×ˢ univ) ∧
      Measurable (Function.uncurry H) ∧
      (∀ r : ℝ, 0 < r → ∀ δ : ℝ, 0 < δ →
        ∃ L : ℝ≥0, LipschitzOnWith L (Function.uncurry H) (Ioo δ 1 ×ˢ closedBall z r)) ∧
      ∀ r : ℝ, 0 < r → ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
        ∃ (v : Ioo δ 1 → SobolevSpace μ Q) (C : ℝ),
          0 ≤ C ∧ AEStronglyMeasurable v (volume.comap Subtype.val) ∧
          (∀ t, ‖v t‖ ≤ C) ∧
          (∀ t : Ioo δ 1, (t:ℝ) ∉ N → SobolevSpace.toLp μ Q (v t) =ᵐ[μ]
            fun x => radialCutoff z r x*H t x) ∧
          ∀ (φ : SobolevSpace μ Q) (ξ : Lp ℝ 2 μ), IsWeakLaplacian μ Q φ ξ →
            (∀ᵐ x ∂μ, x ∉ closedBall z r → SobolevSpace.toLp μ Q φ x = 0) →
            (∀ᵐ x ∂μ, x ∉ closedBall z r → ξ x = 0) →
            ∀ Bφ : ℝ≥0, (∀ᵐ x ∂μ, |SobolevSpace.toLp μ Q φ x| ≤ Bφ) →
            (∀ᵐ x ∂μ, 0 ≤ SobolevSpace.toLp μ Q φ x) →
            ∀ (A : ℝ≥0) (θ θ' : ℝ → ℝ), LipschitzOnWith A θ (Icc δ 1) → ContinuousOn θ' (Icc δ 1) →
              (∀ t ∈ Ioo δ 1, HasDerivAt θ (θ' t) t) → θ δ = 0 → θ 1 = 0 →
              (∀ t ∈ Ioo δ 1, 0 ≤ θ t) →
              (∫ t : Ioo δ 1, θ t*weightedGamma μ Q (SobolevSpace.toLp μ Q φ) (v t) (v t)
                ∂volume.comap Subtype.val) ≤
                2*(∫ t in Ioo δ 1, θ t*deriv
                  (fun s => ∫ x in closedBall z r, SobolevSpace.toLp μ Q φ x*H s x ∂μ) t) := by
  intro H μ Q
  obtain ⟨hc,hm,hlocal,hj⟩ := hX.scaled_heat_continuous_hamilton_jacobi_of_compactness hn p hK
    ν ρ hρ hρ0 hB hν F hF ε hε hε1 hε0 z hR hdist G ι hι N hN hG hdata
  refine ⟨hc,hm,hlocal,?_⟩
  intro r hr δ hδ hδ1
  obtain ⟨v,C,hC,hv,hvb,hrep,hineq⟩ := hj r hr δ hδ hδ1
  refine ⟨v,C,hC,hv,hvb,hrep,?_⟩
  intro φ ξ hξ hφs hξs Bφ hBφ hφ0 A θ θ' hθ hθ' hder hθδ hθ1 hθ0
  have hh := hineq φ ξ hξ hφs hξs Bφ hBφ hφ0 θ θ' hθ.continuousOn hθ' hder hθδ hθ1 hθ0
  obtain ⟨L,hH⟩ := hlocal r hr δ hδ
  have hi : IntegrableOn (SobolevSpace.toLp μ Q φ) (closedBall z r) μ :=
    lp_integrableOn_of_finite μ _ _ (isCompact_closedBall z r).measure_lt_top.ne
  have he := compact_time_pairing_derivative_identity μ (isCompact_closedBall z r) H hδ1
    hH (SobolevSpace.toLp μ Q φ) hi θ θ' hθ hder hθδ hθ1
  linarith only [hh,he]

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
