import OAI.Geometry.RCD.Heat.CompactHeatSecondVariationLimit
import OAI.Geometry.RCD.Sobolev.LipschitzDerivativeValueLimit

namespace OAI

/-! # The actual limiting law mean has a locally Lipschitz derivative -/

open Set Filter MeasureTheory TopologicalSpace
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

theorem limit_mean_second_variation (hK : K ≤ 0) (hε1 : ∀ k, ε k ≤ 1)
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
    ∃ G : ℝ → ℝ,
      (∀ t ∈ Ioo (0:ℝ) 1, DifferentiableAt ℝ F t) ∧
      (∀ t ∈ Ioo (0:ℝ) 1,
        Tendsto (fun k => deriv (deriv (D.interpolationMean H (D.index (j k)))) t)
          atTop (𝓝 (G t))) ∧
      (∀ a b : ℝ, 0 < a → b < 1 → ∃ L : ℝ≥0, LipschitzOnWith L (deriv F) (Icc a b)) ∧
      ∀ a b : ℝ, 0 < a → a ≤ b → b < 1 →
        IntervalIntegrable G volume a b ∧ (∫ t in a..b, G t) = deriv F b-deriv F a := by
  intro H F
  obtain ⟨V,G,hV,hG,hVL,hint⟩ := D.integrated_second_variation_limit hK hε1 hε0
    ρ₀ ρ₁ hm₀ hm₁ hp₀ hp₁ hC₀ hC₁ hμ hν hR hS hT j hj Q₀ hweak f A hf hs
  obtain ⟨hLip,hBound⟩ := hX.kernelHeat_bounded_regularity hn p
    (hX.canonicalHeatKernel_isContinuousHeatKernel hn p) f A hf s hs
  let Hb : X →ᵇ ℝ := BoundedContinuousFunction.ofNormedAddCommGroup H hLip.continuous A
    (fun x => by simpa only [Real.norm_eq_abs] using hBound x)
  have hder (t : ℝ) (ht : t ∈ Ioo (0:ℝ) 1) : HasDerivAt F (V t) t := by
    let a := t/2
    let b := (1+t)/2
    have ha : 0 < a := by dsimp only [a]; linarith [ht.1]
    have hb : b < 1 := by dsimp only [b]; linarith [ht.2]
    have htt : t ∈ Ioo a b := by
      dsimp only [a,b]
      constructor <;> linarith [ht.1,ht.2]
    have hwin (x : ℝ) (hx : x ∈ Icc a b) : x ∈ Ioo (0:ℝ) 1 :=
      ⟨ha.trans_le hx.1,hx.2.trans_lt hb⟩
    obtain ⟨L,hL⟩ := D.first_derivative_uniform_lipschitz hK hε1 ρ₀ ρ₁ hm₀ hm₁ hp₀ hp₁
      hC₀ hC₁ hμ hν hR hS hT f A hf hs ha hb
    apply hasDerivAt_of_common_lipschitz_derivatives
      (fun k => D.interpolationMean H (D.index (j k))) F V L
      (fun k => hL (D.index (j k))) _ _ (fun x hx => hV x (hwin x hx)) htt
    · intro k x hx
      exact D.interpolationMean_differentiable ρ₀ ρ₁ hm₀ hm₁ hp₀ hp₁ hC₀ hC₁ hμ hν Hb
        (D.index (j k)) ⟨x,hwin x ⟨hx.1.le,hx.2.le⟩⟩
    · intro x hx
      have hx' := hwin x ⟨hx.1.le,hx.2.le⟩
      simpa only [F,dite_eq_left hx'] using D.heat_interpolationMean_law_limit
        (fun k => D.index (j k)) ⟨x,hx'⟩ (Q₀ ⟨x,hx'⟩) (hweak ⟨x,hx'⟩) f A hf hs
  refine ⟨G,fun t ht => (hder t ht).differentiableAt,hG,?_,?_⟩
  · intro a b ha hb
    obtain ⟨L,hL⟩ := hVL a b ha hb
    refine ⟨L,LipschitzOnWith.of_dist_le_mul (fun x hx y hy => ?_)⟩
    rw [(hder x ⟨ha.trans_le hx.1,hx.2.trans_lt hb⟩).deriv,
      (hder y ⟨ha.trans_le hy.1,hy.2.trans_lt hb⟩).deriv]
    exact hL.dist_le_mul x hx y hy
  · intro a b ha hab hb
    rw [(hder a ⟨ha,hab.trans_lt hb⟩).deriv,(hder b ⟨ha.trans_le hab,hb⟩).deriv]
    exact hint a b ha hab hb

end RegularPointCoordinates.NoncollapsedRCD.CompactHeatScalingData

end

end OAI
