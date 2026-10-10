import OAI.Geometry.RCD.Heat.CompactHeatJointLaw
import OAI.Geometry.RCD.Metric.CompactFiberProbability
import OAI.Geometry.RCD.Heat.CompactHeatLawLimits

namespace OAI

/-! # Joint heat-bridge limits preserve the already selected interior law -/

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

theorem joint_limit (hK : K ≤ 0) (hε1 : ∀ k, ε k ≤ 1)
    (ρ₀ ρ₁ : X → ℝ) (hm₀ : Measurable ρ₀) (hm₁ : Measurable ρ₁)
    (hp₀ : ∀ x, 0 ≤ ρ₀ x) (hp₁ : ∀ x, 0 ≤ ρ₁ x) {C₀ C₁ : ℝ≥0}
    (hC₀ : ∀ᵐ x ∂hausdorff n X, |ρ₀ x| ≤ C₀)
    (hC₁ : ∀ᵐ x ∂hausdorff n X, |ρ₁ x| ≤ C₁)
    (hμ : μ.map Subtype.val = (hausdorff n X).withDensity (fun x => ENNReal.ofReal (ρ₀ x)))
    (hν : ν.map Subtype.val = (hausdorff n X).withDensity (fun x => ENNReal.ofReal (ρ₁ x)))
    {R : ℝ} (hR : 1 ≤ R) (hS : ∀ a:S, dist p a ≤ R) (hT : ∀ b:T, dist p b ≤ R)
    (i : ℕ → ℕ) (t : Ioo (0:ℝ) 1) (Q₀ : ProbabilityMeasure X)
    (hweak : Tendsto (fun k => D.interpolationLaw (D.index (i k)) t) atTop (𝓝 Q₀)) :
    ∃ (Q : ProbabilityMeasure (X × (S × T))) (j : ℕ → ℕ), StrictMono j ∧
      Tendsto (fun k => D.jointLaw (D.index (i (j k))) t) atTop (𝓝 Q) ∧
      Q.map Prod.fst = Q₀ ∧
      Tendsto (fun k => D.coupling (i (j k))) atTop (𝓝 (Q.map Prod.snd)) := by
  obtain ⟨σ,hσ⟩ := D.interpolationLaw_finite_dominator hK hε1
    ρ₀ ρ₁ hm₀ hm₁ hp₀ hp₁ hC₀ hC₁ hμ hν p hR hS hT
  obtain ⟨Q,j,hj,hlim⟩ := probability_subsequence_compact_fiber σ
    (fun k => D.jointLaw (D.index (i k)) t) (fun k => by
      change (D.jointMeasure (D.index (i k)) t).map Prod.fst ≤ σ
      rw [D.jointMeasure_fst]
      exact hσ _ _)
  have hlim' : Tendsto (fun k => D.jointLaw (D.index (i (j k))) t) atTop (𝓝 Q) := hlim
  have hfst := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ Q hlim' continuous_fst
  have hsnd := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ Q hlim' continuous_snd
  have he k : (D.jointLaw (D.index (i (j k))) t).map Prod.fst =
      D.interpolationLaw (D.index (i (j k))) t :=
    ProbabilityMeasure.toMeasure_injective (D.jointMeasure_fst _ _)
  have he' k : (D.jointLaw (D.index (i (j k))) t).map Prod.snd = D.coupling (i (j k)) :=
    ProbabilityMeasure.toMeasure_injective (D.jointMeasure_snd _ _)
  simp only [he] at hfst
  simp only [he'] at hsnd
  exact ⟨Q,j,hj,hlim',tendsto_nhds_unique hfst (hweak.comp hj.tendsto_atTop),hsnd⟩

end RegularPointCoordinates.NoncollapsedRCD.CompactHeatScalingData

end

end OAI
