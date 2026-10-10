import OAI.Geometry.RCD.Sobolev.DominatedTestConvergence
import OAI.Geometry.RCD.Sobolev.LocalLipschitzDenseCauchy

namespace OAI

/-! # A common-time curve from dominated laws and local test bounds -/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology ENNReal NNReal BoundedContinuousFunction CompactlySupported
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] [SeparableSpace X]
  (σ : FiniteMeasure X) [(σ : Measure X).Regular]

omit [SeparableSpace X] in
theorem dominated_probability_continuous {T : Type*} [TopologicalSpace T]
    (Q : T → ProbabilityMeasure X) (hQ : ∀ t, (Q t : Measure X) ≤ σ)
    (hT : ∀ (g : X →ᵇ ℝ) (L : ℝ≥0), LipschitzWith L g → HasCompactSupport g →
      Continuous (fun t => ∫ x, g x ∂(Q t : Measure X))) : Continuous Q := by
  apply ProbabilityMeasure.continuous_iff_forall_continuous_integral.mpr
  intro f
  have hf : MemLp f 2 (σ : Measure X) := MemLp.of_bound f.continuous.aestronglyMeasurable ‖f‖
    (Eventually.of_forall f.norm_coe_le_norm)
  apply continuous_iff_continuousAt.mpr
  intro t
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨g,L,hL,hgc,hgi,hclose⟩ := finite_measure_compact_lipschitz_L1 (σ : Measure X) hf
    (ε := ε/4) (by positivity)
  let G : C_c(X,ℝ) := ⟨⟨g,hL.continuous⟩,hgc⟩
  let b := G.toBoundedContinuousFunction
  have he (s : T) : dist (∫ x, f x ∂(Q s : Measure X)) (∫ x, g x ∂(Q s : Measure X)) < ε/4 := by
    have hb := integral_difference_le_of_domination (σ : Measure X) (Q s : Measure X)
      (C := 1) (by simp) (by simpa using hQ s) (hf.integrable (by norm_num)) hgi
    have hb' : dist (∫ x, f x ∂(Q s : Measure X)) (∫ x, g x ∂(Q s : Measure X)) ≤
        ∫ x, |f x-g x| ∂(σ : Measure X) := by simpa using hb
    exact hb'.trans_lt hclose
  have hg : Tendsto (fun s => ∫ x, g x ∂(Q s : Measure X)) (𝓝 t)
      (𝓝 (∫ x, g x ∂(Q t : Measure X))) := (hT b L hL hgc).continuousAt
  filter_upwards [Metric.tendsto_nhds.mp hg (ε/2) (half_pos hε)] with s hs
  have htri := dist_triangle4 (∫ x, f x ∂(Q s : Measure X)) (∫ x, g x ∂(Q s : Measure X))
    (∫ x, g x ∂(Q t : Measure X)) (∫ x, f x ∂(Q t : Measure X))
  rw [dist_comm (∫ x, g x ∂(Q t : Measure X))] at htri
  have := he s
  have := he t
  linarith

theorem finite_dominated_curve_limit {T : Type*} [MetricSpace T]
    (P : ℕ → T → ProbabilityMeasure X) (s : ℕ → T) (hs : DenseRange s)
    (hP : ∀ k t, (P k t : Measure X) ≤ σ)
    (hL : ∀ (g : X →ᵇ ℝ) (L : ℝ≥0), LipschitzWith L g → HasCompactSupport g →
      ∀ t, ∃ (A : ℝ≥0) (r : ℝ), 0 < r ∧ ∀ k,
        LipschitzOnWith A (fun t => ∫ x, g x ∂(P k t : Measure X)) (ball t r))
    (hD : ∀ j, ∃ Q : ProbabilityMeasure X, Tendsto (fun k => P k (s j)) atTop (𝓝 Q)) :
    ∃ Q : T → ProbabilityMeasure X, Continuous Q ∧
      ∀ t, Tendsto (fun k => P k t) atTop (𝓝 (Q t)) ∧ (Q t : Measure X) ≤ σ := by
  have hc (g : X →ᵇ ℝ) (j : ℕ) : CauchySeq (fun k => ∫ x, g x ∂(P k (s j) : Measure X)) := by
    obtain ⟨Q,hQ⟩ := hD j
    exact (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hQ g).cauchySeq
  have ht (t : T) := dominated_probability_limit_of_test_cauchy σ (fun k => P k t)
    (fun k => hP k t) (fun g L hg hgc => local_lipschitz_cauchy_of_dense
      (fun k t => ∫ x, g x ∂(P k t : Measure X)) s hs (hL g L hg hgc) (hc g) t)
  choose Q hlim hQ using ht
  refine ⟨Q,dominated_probability_continuous σ Q hQ ?_,fun t => ⟨hlim t,hQ t⟩⟩
  intro g L hg hgc
  obtain ⟨f,hfc,hf⟩ := local_lipschitz_limit_of_dense
    (fun k t => ∫ x, g x ∂(P k t : Measure X)) s hs (hL g L hg hgc) (hc g)
  have he : (fun t => ∫ x, g x ∂(Q t : Measure X)) = f := by
    funext t
    exact tendsto_nhds_unique (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp (hlim t) g) (hf t)
  rw [he]
  exact hfc

end RegularPointCoordinates

end

end OAI
