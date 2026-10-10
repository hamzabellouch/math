import OAI.Geometry.RCD.Heat.CompactHeatSecondVariationLimit
import OAI.Geometry.RCD.Heat.CompactHeatLimitMeanDerivative
import OAI.Geometry.RCD.Heat.CompactHeatIntrinsicSecondDerivative

namespace OAI

/-! # Intrinsic second variation of the actual limiting law mean -/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology NNReal ENNReal BoundedContinuousFunction
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

theorem intrinsic_limit_mean_second_variation (a₀ : S) (b₀ : T) (hK : K ≤ 0) (hε1 : ∀ k, ε k ≤ 1)
    (hε0 : Tendsto ε atTop (𝓝 0))
    (ρ₀ ρ₁ : X → ℝ) (hm₀ : Measurable ρ₀) (hm₁ : Measurable ρ₁)
    (hp₀ : ∀ x, 0 ≤ ρ₀ x) (hp₁ : ∀ x, 0 ≤ ρ₁ x) {C₀ C₁ : ℝ≥0}
    (hC₀ : ∀ᵐ x ∂hausdorff n X, |ρ₀ x| ≤ C₀)
    (hC₁ : ∀ᵐ x ∂hausdorff n X, |ρ₁ x| ≤ C₁)
    (hμ : μ.map Subtype.val=(hausdorff n X).withDensity (fun x => ENNReal.ofReal (ρ₀ x)))
    (hν : ν.map Subtype.val=(hausdorff n X).withDensity (fun x => ENNReal.ofReal (ρ₁ x)))
    {R : ℝ} (hR : 1 ≤ R) (hS : ∀ y:S, dist p y ≤ R) (hT : ∀ y:T, dist p y ≤ R)
    (j : ℕ → ℕ) (hj : StrictMono j) (Q₀ : Ioo (0:ℝ) 1 → ProbabilityMeasure X)
    (hweak : ∀ t, Tendsto (fun k => D.interpolationLaw (D.index (j k)) t) atTop (𝓝 (Q₀ t)))
    (f : Lp ℝ 2 (hausdorff n X)) (A : ℝ≥0)
    (hf : ∀ᵐ x ∂hausdorff n X, |f x| ≤ A) {s : ℝ} (hs : 0 < s) :
    let H := kernelHeat (hausdorff n X) hX.quadratic
      (hX.canonicalHeatKernel_isContinuousHeatKernel hn p) s f
    let F t := if ht : t ∈ Ioo (0:ℝ) 1 then ∫ x, H x ∂(Q₀ ⟨t,ht⟩ : Measure X) else 0
    let m := hausdorff n X
    let q := hX.quadratic
    let w := heatSobolev m q s hs f
    ∃ G : ℝ → ℝ,
      (∀ t ∈ Ioo (0:ℝ) 1, DifferentiableAt ℝ F t) ∧
      (∀ a b : ℝ, 0 < a → b < 1 → ∃ L : ℝ≥0, LipschitzOnWith L (deriv F) (Icc a b)) ∧
      (∀ t : Ioo (0:ℝ) 1, ∃ (v₀ : SobolevSpace m q) (V : X → ℝ) (Lv Av : ℝ≥0)
        (J : Lp ℝ 1 (m.restrict (closedBall p (6*R)))),
        LipschitzWith Lv V ∧ HasCompactSupport V ∧
        (SobolevSpace.toLp m q v₀ =ᵐ[m] V) ∧
        (∀ᵐ x ∂m, |SobolevSpace.toLp m q v₀ x| ≤ Av) ∧
        (SobolevSpace.toLp m q v₀ =ᵐ[m.restrict (closedBall p (6*R))]
          D.forward.potential ((t:ℝ)/2)) ∧
        IsCanonicalHeatHessian m q w v₀ p (6*R) (radialCutoff p (3*R)) J ∧
        G t = (1/4:ℝ)*(∫ x in closedBall p (6*R), J x ∂(Q₀ t : Measure X))) ∧
      ∀ a b : ℝ, 0 < a → a ≤ b → b < 1 →
        IntervalIntegrable G volume a b ∧ (∫ t in a..b, G t) = deriv F b-deriv F a := by
  intro H F m q w
  obtain ⟨G,hder,hlim,hLip,hint⟩ := D.limit_mean_second_variation hK hε1 hε0
    ρ₀ ρ₁ hm₀ hm₁ hp₀ hp₁ hC₀ hC₁ hμ hν hR hS hT j hj Q₀ hweak f A hf hs
  refine ⟨G,hder,hLip,?_,hint⟩
  intro t
  let δ := min (t:ℝ) (1-t)/2
  have hδ : 0 < δ := half_pos (lt_min t.property.1 (sub_pos.mpr t.property.2))
  have hδt : δ < (t:ℝ) := by
    have hh := min_le_left (t:ℝ) (1-t)
    dsimp only [δ]
    linarith [t.property.1]
  have hδb : δ ≤ 1-(t:ℝ) := by
    have hh := min_le_right (t:ℝ) (1-t)
    dsimp only [δ]
    linarith [t.property.2]
  let t' : InteriorHeatTime δ := ⟨t,hδt.le,hδb⟩
  obtain ⟨v₀,V,Lv,Av,J,hV,hc,hv₀,hAv,hvloc,hcan,hJ⟩ :=
    D.intrinsic_second_derivative_limit a₀ b₀ hK hε1 hε0
      ρ₀ ρ₁ hm₀ hm₁ hp₀ hp₁ hC₀ hC₁ hμ hν hR hδ hS hT f A hf hs
      j hj t' hδt (Q₀ t) (hweak t)
  exact ⟨v₀,V,Lv,Av,J,hV,hc,hv₀,hAv,hvloc,hcan,tendsto_nhds_unique (hlim t t.property) hJ⟩

end RegularPointCoordinates.NoncollapsedRCD.CompactHeatScalingData

end

end OAI
