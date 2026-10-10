import OAI.Geometry.RCD.Heat.ScaledHeatGradientTimeDerivative
import OAI.Geometry.RCD.Sobolev.TimeEnergyIntervalBound
import OAI.Geometry.RCD.Coordinates.IntervalBilinearEnergy
import OAI.Geometry.RCD.Heat.CompactTimePairingDerivative
import OAI.Geometry.RCD.Heat.ScaledHeatHamiltonJacobiFromCompactness
import OAI.Geometry.RCD.Heat.ScaledHeatMeasurableSobolev
import OAI.Geometry.RCD.Heat.ScaledHeatIteratedFromCompactness
import OAI.Geometry.RCD.Harmonic.SubtypeL2PairingLimit
import OAI.Geometry.RCD.Heat.ScaledHeatCutoffEnergyLimit
import OAI.Geometry.RCD.Sobolev.WeightedSobolevIntegralLower

namespace OAI

/-! # Integrated gradient energy on every interior time interval

The original Sobolev time family and compact spatial test retain their
full weighted energy. Its integral is controlled by the actual endpoint
values of the continuous small-noise heat limit.
-/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped NNReal ENNReal Topology ContDiff
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X)
  (hn : 2 ≤ n) (p : X) [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]

theorem scaled_heat_interval_energy_of_compactness (hK : K ≤ 0)
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
            ∀ s t : ℝ, δ < s → s < t → t < 1 →
              (∫ u in Icc s t, intervalExtension
                (fun τ => weightedGamma μ Q (SobolevSpace.toLp μ Q φ) (v τ) (v τ)) u) ≤
                2*((∫ x in closedBall z r, SobolevSpace.toLp μ Q φ x*H t x ∂μ) -
                  (∫ x in closedBall z r, SobolevSpace.toLp μ Q φ x*H s x ∂μ)) := by
  intro H μ Q
  obtain ⟨hc,hm,hlocal,hj⟩ := hX.scaled_heat_gradient_time_derivative_of_compactness hn p hK
    ν ρ hρ hρ0 hB hν F hF ε hε hε1 hε0 z hR hdist G ι hι N hN hG hdata
  refine ⟨hc,hm,hlocal,?_⟩
  intro r hr δ hδ hδ1
  obtain ⟨v,C,hC,hv,hvb,hrep,hineq⟩ := hj r hr δ hδ hδ1
  refine ⟨v,C,hC,hv,hvb,hrep,?_⟩
  intro φ ξ hξ hφs hξs Bφ hBφ hφ0 s t hs hst ht
  let Φ := SobolevSpace.toLp μ Q φ
  let P := fun u => ∫ x in closedBall z r, Φ x*H u x ∂μ
  let E := intervalExtension (fun τ => weightedGamma μ Q Φ (v τ) (v τ))
  obtain ⟨L,hH⟩ := hlocal r hr δ hδ
  have hiΦ : IntegrableOn Φ (closedBall z r) μ :=
    lp_integrableOn_of_finite μ Φ _ (isCompact_closedBall z r).measure_lt_top.ne
  have hP := compact_set_pairing_lipschitz μ (isCompact_closedBall z r) H hH Φ hiΦ
  have hE : IntegrableOn E (Ioo δ 1) := by
    let Bform := weightedGammaCLM μ Q (Lp.aestronglyMeasurable Φ)
      (hBφ.mono fun x hx => by simpa only [Real.norm_eq_abs] using hx)
    exact interval_bilinear_energy_integrable Bform v hv hC hvb
  have htest : ∀ θ : ℝ → ℝ, ContDiff ℝ ∞ θ → HasCompactSupport θ →
      tsupport θ ⊆ Ioo δ 1 → (∀ u, 0 ≤ θ u) →
      (∫ u in Ioo δ 1, θ u*E u) ≤ 2*(∫ u in Ioo δ 1, θ u*deriv P u) := by
    intro θ hθ hθc hθs hθ0
    obtain ⟨A,hA⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hθc hθ (by simp)
    have hzδ : θ δ = 0 := by
      by_contra hn
      have hh := hθs (subset_tsupport θ hn)
      exact (lt_irrefl δ) hh.1
    have hz1 : θ 1 = 0 := by
      by_contra hn
      have hh := hθs (subset_tsupport θ hn)
      exact (lt_irrefl (1:ℝ)) hh.2
    have hh := hineq φ ξ hξ hφs hξs Bφ hBφ hφ0 A θ (deriv θ) hA.lipschitzOnWith
      (hθ.continuous_deriv (by simp)).continuousOn
      (fun u _ => (hθ.differentiable (by simp) u).hasDerivAt) hzδ hz1 (fun u _ => hθ0 u)
    simpa only [E,integral_intervalExtension,P] using hh
  have hleft : (s+t)/2-(t-s)/2 = s := by ring
  have hright : (s+t)/2+(t-s)/2 = t := by ring
  have hres := time_energy_interval_bound (c := (s+t)/2) (r := (t-s)/2)
    (by linarith) (by linarith) (by linarith) P E hP hE htest
  simpa only [Real.closedBall_eq_Icc,hleft,hright,P,E] using hres

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
