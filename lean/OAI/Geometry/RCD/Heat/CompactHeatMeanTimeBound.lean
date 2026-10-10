import OAI.Geometry.RCD.Heat.CompactHeatLogarithmicContinuity
import OAI.Geometry.RCD.Sobolev.LocalProbabilityGammaBound
import Mathlib.Analysis.Calculus.MeanValue

namespace OAI

/-! # Uniform time bounds for compact Sobolev tests of the interpolation

The mass-one identity and the actual logarithmic velocity gradient bound
control the derivative uniformly in the noise index on each interior time
window. This supplies time compactness without a presumed limit curve.
-/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology NNReal ENNReal
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD.CompactHeatScalingData
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {K : ℝ} {n : ℕ} {hX : NoncollapsedRCD K n X}
  {hn : 2 ≤ n} {p : X} [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]
  {S T : Set X} [CompactSpace S] [CompactSpace T]
  {μ : Measure S} {ν : Measure T} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
  {ε : ℕ → ℝ} {hε : ∀ k, 0 < ε k}
  (D : hX.CompactHeatScalingData hn p μ ν ε hε)

theorem interpolationMean_uniform_lipschitz (hε1 : ∀ k, ε k ≤ 1)
    (ρ₀ ρ₁ : X → ℝ) (hm₀ : Measurable ρ₀) (hm₁ : Measurable ρ₁)
    (hp₀ : ∀ x, 0 ≤ ρ₀ x) (hp₁ : ∀ x, 0 ≤ ρ₁ x) {C₀ C₁ : ℝ≥0}
    (hC₀ : ∀ᵐ x ∂hausdorff n X, |ρ₀ x| ≤ C₀)
    (hC₁ : ∀ᵐ x ∂hausdorff n X, |ρ₁ x| ≤ C₁)
    (hμ : μ.map Subtype.val = (hausdorff n X).withDensity (fun x => ENNReal.ofReal (ρ₀ x)))
    (hν : ν.map Subtype.val = (hausdorff n X).withDensity (fun x => ENNReal.ofReal (ρ₁ x)))
    (z : X) {R r δ : ℝ} (hR : 0 ≤ R)
    (hS : ∀ y:S, dist z y ≤ R) (hT : ∀ y:T, dist z y ≤ R) (hδ : 0 < δ)
    (w : SobolevSpace (hausdorff n X) hX.quadratic) (C M : ℝ≥0)
    (hw : ∀ᵐ x ∂hausdorff n X, |SobolevSpace.toLp (hausdorff n X) hX.quadratic w x| ≤ C)
    (hM : ∀ᵐ x ∂hausdorff n X, SobolevSpace.minimalSlope (hausdorff n X) hX.quadratic w x ≤ M)
    (hz : ∀ᵐ x ∂hausdorff n X, x ∉ closedBall z r → SobolevSpace.toLp (hausdorff n X) hX.quadratic w x = 0) :
    ∃ L : ℝ≥0, ∀ k, LipschitzOnWith L
      (D.interpolationMean (SobolevSpace.toLp (hausdorff n X) hX.quadratic w) k) (Icc δ (1-δ)) := by
  let m := hausdorff n X
  let q := hX.quadratic
  obtain ⟨H,hH,hgrad⟩ := D.velocity_local_gradient hε1 ρ₀ ρ₁ hm₀ hm₁ hp₀ hp₁ hC₀ hC₁
    hμ hν z (r := r) hR hS hT hδ
  let L : ℝ≥0 := ⟨Real.sqrt H,Real.sqrt_nonneg H⟩*M
  have hd (k : ℕ) (s : ℝ) (hs : s ∈ Icc δ (1-δ)) :
      ∃ d : ℝ, HasDerivAt (D.interpolationMean (SobolevSpace.toLp m q w) k) d s ∧ |d| ≤ L := by
    have hs0 : 0 < s := hδ.trans_le hs.1
    have hs1 : s < 1 := by linarith [hs.2]
    let t : Ioo (0:ℝ) 1 := ⟨s,hs0,hs1⟩
    let t' : InteriorHeatTime δ := ⟨t,hs.1,by linarith [hs.2]⟩
    obtain ⟨θ,hθ,hder⟩ := D.interpolationMean_logarithmic_continuity
      ρ₀ ρ₁ hm₀ hm₁ hp₀ hp₁ hC₀ hC₁ hμ hν k t (isCompact_closedBall z r)
    have hθg := hgrad k t' θ (Subset.refl _) hθ
    have hθs : ∀ᵐ x ∂m.restrict (closedBall z r), SobolevSpace.minimalSlope m q θ x ≤ Real.sqrt H := by
      filter_upwards [hθg,ae_restrict_of_ae (localGamma_self m q θ)] with x hx he
      rw [he] at hx
      nlinarith [Real.sq_sqrt hH,Real.sqrt_nonneg H]
    let := D.interpolationDensity_probability k t
    have hb := local_probability_gamma_bound m q measurableSet_closedBall (D.interpolationDensity k t)
      (D.interpolationDensity_continuous k t).measurable (fun x => (D.interpolationDensity_pos k t x).le)
      θ w (Real.sqrt_nonneg H) hθs hM hz
    have he : (∫ x, localGamma m q θ w x*D.interpolationDensity k t x ∂m) =
        ∫ x, D.interpolationDensity k t x*localGamma m q θ w x ∂m :=
      integral_congr_ae (Eventually.of_forall fun x => mul_comm _ _)
    refine ⟨_,hder w C hw hz,?_⟩
    rw [he] at hb
    exact hb
  refine ⟨L,fun k => ?_⟩
  apply Convex.lipschitzOnWith_of_nnnorm_deriv_le
    (fun s hs => (hd k s hs).choose_spec.1.differentiableAt) _ (convex_Icc _ _)
  intro s hs
  have hh := (hd k s hs).choose_spec
  rw [hh.1.deriv]
  exact_mod_cast hh.2

end RegularPointCoordinates.NoncollapsedRCD.CompactHeatScalingData

end

end OAI
