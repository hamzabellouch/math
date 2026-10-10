import OAI.Geometry.RCD.Heat.CompactHeatInterpolationLaws
import OAI.Geometry.RCD.Metric.DominatedProbabilityCompactness
import OAI.Geometry.RCD.Metric.ProbabilityDominationL1

namespace OAI

/-! # Weak limits of the actual interpolation laws and their L1 pairings -/

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

theorem interpolationLaw_limits (hK : K ≤ 0) (hε1 : ∀ k, ε k ≤ 1)
    (ρ₀ ρ₁ : X → ℝ) (hm₀ : Measurable ρ₀) (hm₁ : Measurable ρ₁)
    (hp₀ : ∀ x, 0 ≤ ρ₀ x) (hp₁ : ∀ x, 0 ≤ ρ₁ x) {C₀ C₁ : ℝ≥0}
    (hC₀ : ∀ᵐ x ∂hausdorff n X, |ρ₀ x| ≤ C₀)
    (hC₁ : ∀ᵐ x ∂hausdorff n X, |ρ₁ x| ≤ C₁)
    (hμ : μ.map Subtype.val = (hausdorff n X).withDensity (fun x => ENNReal.ofReal (ρ₀ x)))
    (hν : ν.map Subtype.val = (hausdorff n X).withDensity (fun x => ENNReal.ofReal (ρ₁ x)))
    (z : X) {R : ℝ} (hR : 1 ≤ R)
    (hS : ∀ y:S, dist z y ≤ R) (hT : ∀ y:T, dist z y ≤ R)
    (i : ℕ → ℕ) (t : ℕ → Ioo (0:ℝ) 1) :
    ∃ (C : ℝ) (Q : ProbabilityMeasure X) (j : ℕ → ℕ), 0 < C ∧ StrictMono j ∧
      Tendsto (fun k => D.interpolationLaw (i (j k)) (t (j k))) atTop (𝓝 Q) ∧
      (Q : Measure X) ≤ ENNReal.ofReal C • hausdorff n X ∧
      ∀ f : X → ℝ, Integrable f (hausdorff n X) →
        Tendsto (fun k => ∫ x, D.interpolationDensity (i (j k)) (t (j k)) x*f x ∂hausdorff n X)
          atTop (𝓝 (∫ x, f x ∂(Q : Measure X))) := by
  let m := hausdorff n X
  obtain ⟨σ,hσ⟩ := D.interpolationLaw_finite_dominator hK hε1
    ρ₀ ρ₁ hm₀ hm₁ hp₀ hp₁ hC₀ hC₁ hμ hν z hR hS hT
  obtain ⟨Q,j,hj,hlim⟩ := probability_subsequence_of_finite_dominator σ
    (fun k => D.interpolationLaw (i k) (t k)) (fun k => hσ (i k) (t k))
  obtain ⟨C,hC,hbound⟩ := D.interpolationDensity_uniform_bound hK hε1
    ρ₀ ρ₁ hm₀ hm₁ hp₀ hp₁ hC₀ hC₁ hμ hν z hR hS hT
  have hdom (k : ℕ) : (D.interpolationLaw (i (j k)) (t (j k)) : Measure X) ≤ ENNReal.ofReal C • m := by
    rw [← withDensity_const]
    apply withDensity_mono
    exact Eventually.of_forall fun x => ENNReal.ofReal_le_ofReal (hbound _ _ x)
  have hlim' : Tendsto (fun k => D.interpolationLaw (i (j k)) (t (j k))) atTop (𝓝 Q) := hlim
  refine ⟨C,Q,j,hC,hj,hlim',weak_probability_domination m _ Q hlim' ENNReal.ofReal_ne_top hdom,?_⟩
  intro f hf
  have he := weak_probability_integral_L1 m _ Q hlim' ENNReal.ofReal_ne_top hdom hf
  simpa only [D.interpolationLaw_integral] using he

theorem interpolationLaw_countable_limits (hK : K ≤ 0) (hε1 : ∀ k, ε k ≤ 1)
    (ρ₀ ρ₁ : X → ℝ) (hm₀ : Measurable ρ₀) (hm₁ : Measurable ρ₁)
    (hp₀ : ∀ x, 0 ≤ ρ₀ x) (hp₁ : ∀ x, 0 ≤ ρ₁ x) {C₀ C₁ : ℝ≥0}
    (hC₀ : ∀ᵐ x ∂hausdorff n X, |ρ₀ x| ≤ C₀)
    (hC₁ : ∀ᵐ x ∂hausdorff n X, |ρ₁ x| ≤ C₁)
    (hμ : μ.map Subtype.val = (hausdorff n X).withDensity (fun x => ENNReal.ofReal (ρ₀ x)))
    (hν : ν.map Subtype.val = (hausdorff n X).withDensity (fun x => ENNReal.ofReal (ρ₁ x)))
    (z : X) {R : ℝ} (hR : 1 ≤ R)
    (hS : ∀ y:S, dist z y ≤ R) (hT : ∀ y:T, dist z y ≤ R)
    (i : ℕ → ℕ) (t : ℕ → Ioo (0:ℝ) 1) :
    ∃ (C : ℝ) (Q : ℕ → ProbabilityMeasure X) (j : ℕ → ℕ), 0 < C ∧ StrictMono j ∧
      ∀ l, Tendsto (fun k => D.interpolationLaw (i (j k)) (t l)) atTop (𝓝 (Q l)) ∧
      (Q l : Measure X) ≤ ENNReal.ofReal C • hausdorff n X ∧
      ∀ f : X → ℝ, Integrable f (hausdorff n X) →
        Tendsto (fun k => ∫ x, D.interpolationDensity (i (j k)) (t l) x*f x ∂hausdorff n X)
          atTop (𝓝 (∫ x, f x ∂(Q l : Measure X))) := by
  let m := hausdorff n X
  obtain ⟨σ,hσ⟩ := D.interpolationLaw_finite_dominator hK hε1
    ρ₀ ρ₁ hm₀ hm₁ hp₀ hp₁ hC₀ hC₁ hμ hν z hR hS hT
  obtain ⟨Q,j,hj,hlim⟩ := countable_probability_subsequence_of_finite_dominator σ
    (fun l k => D.interpolationLaw (i k) (t l)) (fun l k => hσ (i k) (t l))
  obtain ⟨C,hC,hbound⟩ := D.interpolationDensity_uniform_bound hK hε1
    ρ₀ ρ₁ hm₀ hm₁ hp₀ hp₁ hC₀ hC₁ hμ hν z hR hS hT
  have hdom (l k : ℕ) : (D.interpolationLaw (i (j k)) (t l) : Measure X) ≤ ENNReal.ofReal C • m := by
    rw [← withDensity_const]
    apply withDensity_mono
    exact Eventually.of_forall fun x => ENNReal.ofReal_le_ofReal (hbound _ _ x)
  refine ⟨C,Q,j,hC,hj,fun l => ?_⟩
  have hlim' : Tendsto (fun k => D.interpolationLaw (i (j k)) (t l)) atTop (𝓝 (Q l)) := hlim l
  refine ⟨hlim',weak_probability_domination m _ (Q l) hlim' ENNReal.ofReal_ne_top (hdom l),?_⟩
  intro f hf
  have he := weak_probability_integral_L1 m _ (Q l) hlim' ENNReal.ofReal_ne_top (hdom l) hf
  simpa only [D.interpolationLaw_integral] using he

end RegularPointCoordinates.NoncollapsedRCD.CompactHeatScalingData

end

end OAI
