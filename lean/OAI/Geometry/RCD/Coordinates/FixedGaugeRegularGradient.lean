import OAI.Geometry.RCD.Coordinates.FixedGaugeHeatRegular
import OAI.Geometry.RCD.Heat.CompactScaledLogBound

namespace OAI

/-! # Uniform local gradient bounds for every fixed-gauge realization -/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology NNReal ENNReal
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X)
  (hn : 2 ≤ n) (p : X) [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]

theorem fixed_gauge_gradient_bound
    {S : Set X} [CompactSpace S] (ν : Measure S) [IsProbabilityMeasure ν]
    (ρ : X → ℝ) (hρ : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x) {B : ℝ≥0}
    (hB : ∀ᵐ x ∂hausdorff n X, |ρ x| ≤ B)
    (hν : ν.map Subtype.val = (hausdorff n X).withDensity (fun x => ENNReal.ofReal (ρ x)))
    (z : X) {R r δ : ℝ} (hR : 0 ≤ R) (hdist : ∀ y:S, dist z y ≤ R) (hδ : 0 < δ) :
    ∃ P : ℝ, 0 ≤ P ∧ ∀ (F : C(S,ℝ)), (∀ y, 0 < F y) →
      ∀ ε (hε : 0 < ε), ε ≤ 1 → ∀ t ∈ Icc δ 1,
      ∀ u : SobolevSpace (hausdorff n X) hX.quadratic,
        (SobolevSpace.toLp (hausdorff n X) hX.quadratic u
          =ᵐ[(hausdorff n X).restrict (closedBall z r)]
            hX.fixedGaugeScaledPotential hn p ν F ε hε δ hδ z t) →
        ∀ᵐ x ∂(hausdorff n X).restrict (closedBall z r),
          localGamma (hausdorff n X) hX.quadratic u u x ≤ P := by
  let m := hausdorff n X
  let Q := hX.quadratic
  obtain ⟨P,hP,hdata⟩ := hX.compact_scaled_log_uniform_bound hn p ν ρ hρ hρ0 hB hν
    z (r := r) hR hdist hδ
  refine ⟨P,hP,?_⟩
  intro F hF ε hε hε1 t ht u hu
  obtain ⟨G,hG,hFG⟩ := hX.fixedGaugeScaledPotential_normalized hn p ν F hF hε hδ ht.1 z
  have hc : 0 < ε/2 := half_pos hε
  have h2 : 2*(ε/2) = ε := by ring
  have htime : ε/2*t = ε*t/2 := by ring
  obtain ⟨v,hv,hvP⟩ := hdata G hG hc (by simpa only [h2] using hε1) ht.1 ht.2
  have hv' : SobolevSpace.toLp m Q v =ᵐ[m.restrict (closedBall z r)] fun x =>
      ε*Real.log (hX.compactHeatFactor hn p ν G (ε*t/2)
        (div_pos (mul_pos hε (hδ.trans_le ht.1)) (by norm_num)) x) := by
    simpa only [h2,htime] using hv
  have huv : SobolevSpace.toLp m Q u =ᵐ[m.restrict (closedBall z r)] SobolevSpace.toLp m Q v := by
    filter_upwards [hu,hv'] with x hu hv
    exact hu.trans ((hFG x).trans hv.symm)
  filter_upwards [localGamma_pair_congr_ae m Q huv huv,hvP,
    ae_restrict_of_ae (localGamma_self m Q v)] with x he hb hs
  rw [he,hs]
  exact hb

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
