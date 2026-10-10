import OAI.Geometry.RCD.Heat.ScaledHeatAveragedHamiltonJacobi
import OAI.Geometry.RCD.Metric.HamiltonJacobiDensity

namespace OAI

/-! # The actual averaged heat limit satisfies Hamilton--Jacobi almost everywhere

The gradient and time derivative come from the same Sobolev average.
The strict interior ball avoids any assertion at the cutoff boundary.
-/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped NNReal ENNReal Topology ContDiff
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X)
  (hn : 2 ≤ n) (p : X) [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]

theorem scaled_heat_averaged_gradient_of_compactness (hK : K ≤ 0)
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
          (∀ h : ℝ, Continuous (timeIntervalAverage (intervalVectorExtension v) h)) ∧
          (∀ h t : ℝ, 0 < h → δ < t-h → t+h < 1 →
            SobolevSpace.toLp μ Q (timeIntervalAverage (intervalVectorExtension v) h t) =ᵐ[μ]
              fun x => radialCutoff z r x*timeIntervalAverage (fun q => H q x) h t) ∧
          ∀ h t : ℝ, 0 < h → δ < t-h → t+h < 1 →
            ∃ D : Lp ℝ 2 μ,
              HasDerivAt (fun s => SobolevSpace.toLp μ Q
                (timeIntervalAverage (intervalVectorExtension v) h s)) D t ∧
              (D =ᵐ[μ] fun x => radialCutoff z r x*((H (t+h) x-H (t-h) x)/(2*h))) ∧
              ∀ᵐ x ∂μ.restrict (closedBall z (r/4)),
                (SobolevSpace.minimalSlope μ Q
                  (timeIntervalAverage (intervalVectorExtension v) h t) x)^2 ≤ 2*D x := by
  intro H μ Q
  obtain ⟨hc,hm,hlocal,henergy⟩ := hX.scaled_heat_averaged_hamilton_jacobi_of_compactness hn p hK
    ν ρ hρ hρ0 hB hν F hF ε hε hε1 hε0 z hR hdist G ι hι N hN hG hdata
  refine ⟨hc,hm,hlocal,?_⟩
  intro r hr δ hδ hδ1
  obtain ⟨v,C,hC,hv,hvb,hrep,havgc,havgr,hder⟩ := henergy r hr δ hδ hδ1
  refine ⟨v,C,hC,hv,hvb,hrep,havgc,havgr,?_⟩
  intro h t hh ha hb
  obtain ⟨D,hD,hDr,hineq⟩ := hder h t hh ha hb
  exact ⟨D,hD,hDr,hamilton_jacobi_density_of_tests μ Q z hr _ D hineq⟩

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
