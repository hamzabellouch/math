import OAI.Geometry.RCD.Heat.CompactHeatGlobalHessianLimit
import OAI.Geometry.RCD.Heat.CompactHeatScaledHessian

namespace OAI
/-! # Convergence of the actual second derivative of heat interpolation -/

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

theorem second_derivative_limit (hK : K ≤ 0) (hε1 : ∀ k, ε k ≤ 1)
    (hε0 : Tendsto ε atTop (𝓝 0))
    (ρ₀ ρ₁ : X → ℝ) (hm₀ : Measurable ρ₀) (hm₁ : Measurable ρ₁)
    (hp₀ : ∀ x, 0 ≤ ρ₀ x) (hp₁ : ∀ x, 0 ≤ ρ₁ x) {C₀ C₁ : ℝ≥0}
    (hC₀ : ∀ᵐ x ∂hausdorff n X, |ρ₀ x| ≤ C₀)
    (hC₁ : ∀ᵐ x ∂hausdorff n X, |ρ₁ x| ≤ C₁)
    (hμ : μ.map Subtype.val=(hausdorff n X).withDensity (fun x => ENNReal.ofReal (ρ₀ x)))
    (hν : ν.map Subtype.val=(hausdorff n X).withDensity (fun x => ENNReal.ofReal (ρ₁ x)))
    {R δ : ℝ} (hR : 1 ≤ R) (hδ : 0 < δ)
    (hS : ∀ y:S, dist p y ≤ R) (hT : ∀ y:T, dist p y ≤ R)
    (f : Lp ℝ 2 (hausdorff n X)) (A : ℝ≥0)
    (hf : ∀ᵐ x ∂hausdorff n X, |f x| ≤ A) {a : ℝ} (ha : 0 < a)
    (j : ℕ → ℕ) (hj : StrictMono j) (t : InteriorHeatTime δ) (ht : δ < (t.val:ℝ))
    (Q₀ : ProbabilityMeasure X)
    (hweak : Tendsto (fun k => D.interpolationLaw (D.index (j k)) t.val) atTop (𝓝 Q₀)) :
    let H := kernelHeat (hausdorff n X) hX.quadratic
      (hX.canonicalHeatKernel_isContinuousHeatKernel hn p) a f
    ∃ I : ℝ, Tendsto (fun k => deriv (deriv (D.interpolationMean H (D.index (j k))))
      (t.val:ℝ)) atTop (𝓝 I) := by
  intro H
  let m := hausdorff n X
  let q := hX.quadratic
  let w := heatSobolev m q a ha f
  let i k := D.index (j k)
  choose u v UV WU WV hu hv hUV hWU hWV hd using fun k (s : InteriorHeatTime δ) =>
    D.interpolationMean_hessian ρ₀ ρ₁ hm₀ hm₁ hp₀ hp₁ hC₀ hC₁ hμ hν f A hf ha k s.val
  obtain ⟨I,hI⟩ := D.global_scaled_hessian_limit hK hε1 hε0 ρ₀ ρ₁ hm₀ hm₁ hp₀ hp₁ hC₀ hC₁ hμ hν
    hR hδ hS hT f A hf ha u v WU WV UV hu hv hWU hWV hUV j hj t ht Q₀ hweak
  have hrem := ((D.laplacianRemainder_tendstoUniformly hK f A hf ha hε0).tendsto_at t.val).comp
    (D.strict.comp hj).tendsto_atTop
  have heq (k : ℕ) : deriv (deriv (D.interpolationMean H (i k))) (t.val:ℝ)=
      D.laplacianRemainder f a (i k) t.val-
        ∫ x, (ε (i k)/2)^2*localHessianAction m q w (u (i k) t) (v (i k) t)
          (WU (i k) t) (WV (i k) t) (UV (i k) t) x ∂m := by
    rw [(hd (i k) t).deriv,← integral_const_mul]
    congr 1
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by ring
  refine ⟨-I,?_⟩
  have hl := hrem.sub hI
  simp only [zero_sub] at hl
  exact hl.congr' (Eventually.of_forall fun k => (heq k).symm)

end RegularPointCoordinates.NoncollapsedRCD.CompactHeatScalingData

end

end OAI
