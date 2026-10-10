import OAI.Geometry.RCD.Heat.ScaledHeatCutoffEnergy

namespace OAI

/-! # The energy limit on the measurable radial representatives

The exact value-pairing limit fixes the same global function and
subsequence as the Sobolev construction.
-/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped NNReal ENNReal Topology
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X)
  (hn : 2 ≤ n) (p : X) [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]

theorem scaled_heat_cutoff_energy_limit
    {S : Set X} [CompactSpace S] (ν : Measure S) [IsProbabilityMeasure ν]
    (ρ : X → ℝ) (hρ : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x) {B : ℝ≥0}
    (hB : ∀ᵐ x ∂hausdorff n X, |ρ x| ≤ B)
    (hν : ν.map Subtype.val = (hausdorff n X).withDensity (fun x => ENNReal.ofReal (ρ x)))
    (F : ℕ → C(S,ℝ)) (hF : ∀ k a, 0 < F k a)
    (ε : ℕ → ℝ) (hε : ∀ k, 0 < ε k) (hε0 : Tendsto ε atTop (𝓝 0))
    (G : ℝ → X → ℝ) (ι : ℕ → ℕ) (hι : StrictMono ι)
    (z : X) {r δ : ℝ} (hr : 0 < r) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (u : ℕ → Ioo δ 1 → SobolevSpace (hausdorff n X) hX.quadratic)
    (hu : ∀ k t, SobolevSpace.toLp (hausdorff n X) hX.quadratic (u k t) =ᵐ[hausdorff n X]
      fun x => radialCutoff z r x*hX.fixedGaugeScaledPotential hn p ν (F (ι k))
        (ε (ι k)) (hε (ι k)) δ hδ z t x)
    (hconv : ∀ ψ : ℝ → ℝ, Integrable ψ (volume.restrict (Ioo δ 1)) →
      ∀ v : Lp ℝ 2 (hausdorff n X),
        Tendsto (fun k => ∫ t in Ioo δ 1, ψ t*∫ x in closedBall z r, v x*
          hX.fixedGaugeScaledPotential hn p ν (F (ι k)) (ε (ι k)) (hε (ι k)) δ hδ z t x ∂hausdorff n X)
          atTop (𝓝 (∫ t in Ioo δ 1, ψ t*∫ x in closedBall z r, v x*G t x ∂hausdorff n X)))
    (φ : SobolevSpace (hausdorff n X) hX.quadratic) (ξ : Lp ℝ 2 (hausdorff n X))
    (hξ : IsWeakLaplacian (hausdorff n X) hX.quadratic φ ξ)
    (hφs : ∀ᵐ x ∂hausdorff n X, x ∉ closedBall z r → SobolevSpace.toLp _ _ φ x = 0)
    (hξs : ∀ᵐ x ∂hausdorff n X, x ∉ closedBall z r → ξ x = 0)
    (Bφ : ℝ) (hBφ : ∀ᵐ x ∂hausdorff n X, |SobolevSpace.toLp _ _ φ x| ≤ Bφ)
    (θ θ' : ℝ → ℝ) (hθ : ContinuousOn θ (Icc δ 1)) (hθ' : ContinuousOn θ' (Icc δ 1))
    (hder : ∀ t ∈ Ioo δ 1, HasDerivAt θ (θ' t) t) (hθδ : θ δ = 0) (hθ1 : θ 1 = 0) :
    Tendsto (fun k => ∫ t : Ioo δ 1, θ t*weightedGamma (hausdorff n X) hX.quadratic
      (SobolevSpace.toLp _ _ φ) (u k t) (u k t) ∂volume.comap Subtype.val) atTop
      (𝓝 (-2*(∫ t in Ioo δ 1, θ' t*∫ x in closedBall z r,
        SobolevSpace.toLp _ _ φ x*G t x ∂hausdorff n X))) := by
  have hθI : Integrable θ (volume.restrict (Ioo δ 1)) :=
    (hθ.integrableOn_compact isCompact_Icc).mono_set Ioo_subset_Icc_self
  have hθ'I : Integrable θ' (volume.restrict (Ioo δ 1)) :=
    (hθ'.integrableOn_compact isCompact_Icc).mono_set Ioo_subset_Icc_self
  have hA := hconv θ' hθ'I (SobolevSpace.toLp _ _ φ)
  have hV := hconv θ hθI ξ
  have heq (k : ℕ) := hX.compact_heat_scaled_cutoff_energy hn p ν ρ hρ hρ0 hB hν
    (F (ι k)) (hF (ι k)) (hε (ι k)) z hr hδ hδ1 (u k) (hu k) φ ξ hξ hφs hξs Bφ hBφ
    θ θ' hθ hθ' hder hθδ hθ1
  simp_rw [heq]
  have hh := (hA.const_mul (-2)).sub ((hε0.comp hι.tendsto_atTop).mul hV)
  simpa only [Function.comp_def,zero_mul,sub_zero] using hh

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
