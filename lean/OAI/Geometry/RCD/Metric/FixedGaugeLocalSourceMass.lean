import OAI.Geometry.RCD.Heat.CompactHeatLocalSourceMass
import OAI.Geometry.RCD.Coordinates.CompactHeatGaugeNormalization

namespace OAI

/-! # Uniform local source mass of the fixed-gauge heat potentials -/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped NNReal ENNReal
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X)
  (hn : 2 ≤ n) (p : X) [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]

theorem fixed_gauge_local_source_mass (hK : K ≤ 0)
    {S : Set X} [CompactSpace S] (ν : Measure S) [IsProbabilityMeasure ν]
    (ρ : X → ℝ) (hρ : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x) {B : ℝ≥0}
    (hB : ∀ᵐ x ∂hausdorff n X, |ρ x| ≤ B)
    (hν : ν.map Subtype.val=(hausdorff n X).withDensity (fun x => ENNReal.ofReal (ρ x)))
    (z : X) {R r δ : ℝ} (hR : 0 ≤ R) (hr : 0<r)
    (hdist : ∀ y:S, dist z y ≤ R) (hδ : 0<δ)
    (χ : SobolevSpace (hausdorff n X) hX.quadratic) (v : X → ℝ)
    (hv : SobolevSpace.toLp (hausdorff n X) hX.quadratic χ =ᵐ[hausdorff n X] v)
    (hvi : Integrable v (hausdorff n X)) (hv0 : ∀ x, 0 ≤ v x)
    (hvzero : ∀ x ∉ closedBall z r, v x=0) (M : ℝ≥0)
    (hχM : ∀ᵐ x ∂hausdorff n X,
      SobolevSpace.minimalSlope (hausdorff n X) hX.quadratic χ x ≤ M) :
    ∃ (L : ℝ≥0) (A : ℝ), 0 ≤ A ∧ ∀ (F : C(S,ℝ)), (∀ y, 0<F y) →
      ∀ {ε s : ℝ} (hε : 0<ε) (_hε1 : ε ≤ 1) (_hδs : δ ≤ s) (_hs1 : s ≤ 1),
      ∃ (u : SobolevSpace (hausdorff n X) hX.quadratic) (q : Lp ℝ 2 (hausdorff n X)),
        IsWeakLaplacian (hausdorff n X) hX.quadratic u q ∧
        (SobolevSpace.toLp (hausdorff n X) hX.quadratic u
          =ᵐ[(hausdorff n X).restrict (closedBall z r)]
            hX.fixedGaugeScaledPotential hn p ν F ε hε δ hδ z s) ∧
        (∀ᵐ x ∂(hausdorff n X).restrict (closedBall z r),
          SobolevSpace.minimalSlope (hausdorff n X) hX.quadratic u x ≤ L) ∧
        Integrable (fun x => v x*|q x|) (hausdorff n X) ∧
        (∫ x, v x*|q x| ∂hausdorff n X) ≤ A := by
  obtain ⟨L,A,hA,hdata⟩ := hX.compact_heat_local_source_mass hn p hK ν ρ hρ hρ0 hB hν
    z hR hr hdist hδ χ v hv hvi hv0 hvzero M hχM
  refine ⟨L,A,hA,?_⟩
  intro F hF ε s hε hε1 hδs hs1
  obtain ⟨G,hG,hFG⟩ := hX.fixedGaugeScaledPotential_normalized hn p ν F hF hε hδ hδs z
  obtain ⟨u,q,hq,hu,hL,hi,hm⟩ := hdata G hG hε hε1 hδs hs1
  refine ⟨u,q,hq,?_,hL,hi,hm⟩
  filter_upwards [hu] with x hx
  exact hx.trans (hFG x).symm

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
