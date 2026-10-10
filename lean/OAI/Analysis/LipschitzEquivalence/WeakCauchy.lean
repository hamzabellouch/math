import OAI.Analysis.LipschitzEquivalence.LinearizationContinuity

namespace OAI

universe uE uM

noncomputable section
open scoped BigOperators InnerProductSpace Topology ENNReal
open scoped Topology ENNReal NNReal
open scoped Classical ENNReal NNReal InnerProductSpace Topology
open Filter Set
open scoped NNReal Topology
open Filter Set

namespace LipschitzCounterexample.WeakSequences
open Filter Topology
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem WeakNull.cauchy {u : ℕ → E} (h : WeakNull u) : WeakCauchy u :=
  fun f => (h f).cauchySeq

theorem WeakCauchy.subseq {u : ℕ → E} (h : WeakCauchy u) {a : ℕ → ℕ}
    (ha : StrictMono a) : WeakCauchy (fun n => u (a n)) :=
  fun f => (h f).comp_tendsto ha.tendsto_atTop

theorem weakCauchy_of_uniform_approx {u : ℕ → E}
    (h : ∀ ε : ℝ, 0 < ε → ∃ v : ℕ → E, WeakCauchy v ∧ ∀ i, ‖u i-v i‖ < ε) :
    WeakCauchy u := by
  intro f
  apply Metric.cauchySeq_iff.mpr
  intro ε hε
  obtain ⟨v,hv,herr⟩ := h (ε/(4*(‖f‖+1))) (by positivity)
  have hferr (i : ℕ) : dist (f (u i)) (f (v i)) < ε/4 := by
    rw [dist_eq_norm,← map_sub]
    have hh := (lt_div_iff₀ (show 0 < 4*(‖f‖+1) by positivity)).mp (herr i)
    have hb := f.le_opNorm (u i-v i)
    nlinarith [norm_nonneg (u i-v i)]
  obtain ⟨N,hN⟩ := Metric.cauchySeq_iff.mp (hv f) (ε/2) (half_pos hε)
  refine ⟨N,fun m hm n hn => ?_⟩
  have h₁ := dist_triangle (f (u m)) (f (v m)) (f (u n))
  have h₂ := dist_triangle (f (v m)) (f (v n)) (f (u n))
  have h₃ := hferr m
  have h₄ := hferr n
  have h₅ := hN m hm n hn
  rw [dist_comm (f (v n)) (f (u n))] at h₂
  linarith

end LipschitzCounterexample.WeakSequences

namespace LipschitzCounterexample.LocalizedLinearization
open scoped Topology NNReal
open Filter WeakSequences
variable {M : Type uM} [MetricSpace M] [Zero M]

theorem disjoint_tests_vanish_cauchy {h : ℕ → M → ℝ} (hd : DisjointTests h)
    {K : ℝ≥0} (hh : ∀ i, LipschitzWith K (h i)) {μ : ℕ → FreeSpace.Space M}
    (hw : WeakCauchy μ) :
    Tendsto (fun i => test (normalized (h i) (hh i)) (μ i)) atTop (𝓝 0) := by
  let T := disjointOperator hd
  obtain ⟨x,hx⟩ := cauchySeq_tendsto_of_complete (schur_cauchy (hw.map T))
  have hdiff : Tendsto (fun n => T (μ n)-x) atTop (𝓝 0) := by
    simpa using hx.sub (tendsto_const_nhds (x := x))
  have hcoord : Tendsto (fun n => (T (μ n)-x) n) atTop (𝓝 0) :=
    squeeze_zero_norm (fun n => lp.norm_apply_le_norm (by norm_num) (T (μ n)-x) n)
      (by simpa only [norm_zero] using hdiff.norm)
  have hxcoord : Tendsto (fun n => x n) atTop (𝓝 0) :=
    squeeze_zero_norm (fun n => le_rfl) ((summable_norm x).tendsto_atTop_zero)
  have hsum := hcoord.add hxcoord
  simp only [zero_add] at hsum
  convert hsum using 1
  funext n
  rw [← disjointOperator_coord hd hh]
  change T (μ n) n = (T (μ n) n-x n)+x n
  abel

end LipschitzCounterexample.LocalizedLinearization

end

end OAI
