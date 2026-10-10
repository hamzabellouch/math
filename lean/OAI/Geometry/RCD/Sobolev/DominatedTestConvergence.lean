import OAI.Geometry.RCD.Sobolev.FiniteMeasureCompactLipschitzDensity
import OAI.Geometry.RCD.Metric.DominatedProbabilityCompactness
import OAI.Geometry.RCD.Metric.ProbabilityDominationL1

namespace OAI

/-! # Compact Lipschitz tests determine dominated probability limits -/

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal NNReal BoundedContinuousFunction CompactlySupported
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] [SeparableSpace X]
  (σ : FiniteMeasure X) [(σ : Measure X).Regular]

omit [SeparableSpace X] in
theorem dominated_test_cauchy (P : ℕ → ProbabilityMeasure X)
    (hP : ∀ k, (P k : Measure X) ≤ σ)
    (hT : ∀ (g : X →ᵇ ℝ) (L : ℝ≥0), LipschitzWith L g → HasCompactSupport g →
      CauchySeq (fun k => ∫ x, g x ∂(P k : Measure X))) (f : X →ᵇ ℝ) :
    CauchySeq (fun k => ∫ x, f x ∂(P k : Measure X)) := by
  have hf : MemLp f 2 (σ : Measure X) := MemLp.of_bound f.continuous.aestronglyMeasurable ‖f‖
    (Eventually.of_forall f.norm_coe_le_norm)
  rw [Metric.cauchySeq_iff]
  intro ε hε
  obtain ⟨g,L,hL,hgc,hgi,hclose⟩ := finite_measure_compact_lipschitz_L1 (σ : Measure X) hf
    (ε := ε/4) (by positivity)
  let G : C_c(X,ℝ) := ⟨⟨g,hL.continuous⟩,hgc⟩
  let b := G.toBoundedContinuousFunction
  have hbc : CauchySeq (fun k => ∫ x, g x ∂(P k : Measure X)) := hT b L hL hgc
  obtain ⟨N,hN⟩ := Metric.cauchySeq_iff.mp hbc (ε/2) (half_pos hε)
  have he (k : ℕ) : dist (∫ x, f x ∂(P k : Measure X)) (∫ x, g x ∂(P k : Measure X)) < ε/4 := by
    have hb := integral_difference_le_of_domination (σ : Measure X) (P k : Measure X)
      (C := 1) (by simp) (by simpa using hP k) (hf.integrable (by norm_num)) hgi
    have hb' : dist (∫ x, f x ∂(P k : Measure X)) (∫ x, g x ∂(P k : Measure X)) ≤
        ∫ x, |f x-g x| ∂(σ : Measure X) := by simpa using hb
    exact hb'.trans_lt hclose
  refine ⟨N,fun a ha b hb => ?_⟩
  have htri := dist_triangle4 (∫ x, f x ∂(P a : Measure X)) (∫ x, g x ∂(P a : Measure X))
    (∫ x, g x ∂(P b : Measure X)) (∫ x, f x ∂(P b : Measure X))
  rw [dist_comm (∫ x, g x ∂(P b : Measure X))] at htri
  have := hN a ha b hb
  have := he a
  have := he b
  linarith

theorem dominated_probability_limit_of_test_cauchy (P : ℕ → ProbabilityMeasure X)
    (hP : ∀ k, (P k : Measure X) ≤ σ)
    (hT : ∀ (g : X →ᵇ ℝ) (L : ℝ≥0), LipschitzWith L g → HasCompactSupport g →
      CauchySeq (fun k => ∫ x, g x ∂(P k : Measure X))) :
    ∃ Q : ProbabilityMeasure X, Tendsto P atTop (𝓝 Q) ∧ (Q : Measure X) ≤ σ := by
  obtain ⟨Q,j,hj,hlim⟩ := probability_subsequence_of_finite_dominator σ P hP
  have hfull : Tendsto P atTop (𝓝 Q) := by
    apply ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr
    intro f
    exact tendsto_nhds_of_cauchySeq_of_subseq (dominated_test_cauchy σ P hP hT f)
      hj.tendsto_atTop (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hlim f)
  refine ⟨Q,hfull,?_⟩
  simpa using weak_probability_domination (σ : Measure X) P Q hfull (C := 1) (by simp)
    (fun k => by simpa using hP k)

end RegularPointCoordinates

end

end OAI
