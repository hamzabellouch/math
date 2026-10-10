import OAI.Geometry.RCD.Heat.CompactHeatFirstDerivativeLimit
import OAI.Geometry.RCD.Heat.CompactHeatSecondDerivativeLimit
import OAI.Geometry.RCD.Sobolev.LipschitzDerivativeLimit

namespace OAI

/-! # Integrated second variation on the original heat-law subsequence

The two limiting derivatives are constructed from actual interpolation
means. All strict interior intervals share these same limits.
-/

open Set Filter MeasureTheory TopologicalSpace
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

theorem integrated_second_variation_limit (hK : K ≤ 0) (hε1 : ∀ k, ε k ≤ 1)
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
    ∃ V G : ℝ → ℝ,
      (∀ t ∈ Ioo (0:ℝ) 1,
        Tendsto (fun k => deriv (D.interpolationMean H (D.index (j k))) t) atTop (𝓝 (V t))) ∧
      (∀ t ∈ Ioo (0:ℝ) 1,
        Tendsto (fun k => deriv (deriv (D.interpolationMean H (D.index (j k)))) t)
          atTop (𝓝 (G t))) ∧
      (∀ a b : ℝ, 0 < a → b < 1 → ∃ L : ℝ≥0, LipschitzOnWith L V (Icc a b)) ∧
      ∀ a b : ℝ, 0 < a → a ≤ b → b < 1 →
        IntervalIntegrable G volume a b ∧ (∫ t in a..b, G t) = V b-V a := by
  intro H
  let F k := D.interpolationMean H (D.index (j k))
  let V t := limUnder atTop (fun k => deriv (F k) t)
  let G t := limUnder atTop (fun k => deriv (deriv (F k)) t)
  have hV (t : ℝ) (ht : t ∈ Ioo (0:ℝ) 1) :
      Tendsto (fun k => deriv (F k) t) atTop (𝓝 (V t)) := by
    exact tendsto_nhds_limUnder (D.first_derivative_limit hK hε1 ρ₀ ρ₁ hm₀ hm₁ hp₀ hp₁
      hC₀ hC₁ hμ hν hR hS hT (fun k => D.index (j k)) Q₀ hweak f A hf hs ⟨t,ht⟩)
  have hG (t : ℝ) (ht : t ∈ Ioo (0:ℝ) 1) :
      Tendsto (fun k => deriv (deriv (F k)) t) atTop (𝓝 (G t)) := by
    let δ := min t (1-t)/2
    have hδ : 0 < δ := half_pos (lt_min ht.1 (sub_pos.mpr ht.2))
    have hδt : δ < t := by
      have hh := min_le_left t (1-t)
      dsimp only [δ]
      linarith [ht.1]
    have hδb : δ ≤ 1-t := by
      have hh := min_le_right t (1-t)
      dsimp only [δ]
      linarith [ht.2]
    let t' : InteriorHeatTime δ := ⟨⟨t,ht⟩,hδt.le,hδb⟩
    exact tendsto_nhds_limUnder (D.second_derivative_limit hK hε1 hε0 ρ₀ ρ₁ hm₀ hm₁ hp₀ hp₁
      hC₀ hC₁ hμ hν hR hδ hS hT f A hf hs j hj t' hδt (Q₀ ⟨t,ht⟩) (hweak ⟨t,ht⟩))
  refine ⟨V,G,hV,hG,?_,?_⟩
  · intro a b ha hb
    obtain ⟨L,hL⟩ := D.first_derivative_uniform_lipschitz hK hε1 ρ₀ ρ₁ hm₀ hm₁ hp₀ hp₁
      hC₀ hC₁ hμ hν hR hS hT f A hf hs ha hb
    refine ⟨L,LipschitzOnWith.of_dist_le_mul (fun x hx y hy => ?_)⟩
    exact le_of_tendsto ((hV x ⟨ha.trans_le hx.1,hx.2.trans_lt hb⟩).dist
      (hV y ⟨ha.trans_le hy.1,hy.2.trans_lt hb⟩))
      (Eventually.of_forall fun k => (hL (D.index (j k))).dist_le_mul x hx y hy)
  · intro a b ha hab hb
    obtain ⟨L,hL⟩ := D.first_derivative_uniform_lipschitz hK hε1 ρ₀ ρ₁ hm₀ hm₁ hp₀ hp₁
      hC₀ hC₁ hμ hν hR hS hT f A hf hs ha hb
    exact lipschitz_derivative_limit (fun k => deriv (F k)) G L hab
      (fun k => hL (D.index (j k))) (hV a ⟨ha,hab.trans_lt hb⟩)
      (hV b ⟨ha.trans_le hab,hb⟩)
      (fun t ht => hG t ⟨ha.trans ht.1,ht.2.trans hb⟩)

end RegularPointCoordinates.NoncollapsedRCD.CompactHeatScalingData

end

end OAI
