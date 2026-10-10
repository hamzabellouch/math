import OAI.Probability.GammaPassage.FiniteTails
import OAI.Probability.FirstPassage.PathWitnesses

namespace OAI

namespace GammaFPP
open MeasureTheory ProbabilityTheory PlanarFPP Finset
open scoped ENNReal

lemma trace_edge_length (p : Vertex) (ds : List Step) :
    ((trace p ds).map traversalEdge).length = ds.length := by
  induction ds generalizing p with
  | nil => rfl
  | cons d ds ih =>
    simpa only [trace, List.map_cons, List.length_cons] using
      (congrArg Nat.succ (ih (p + d.delta)))

lemma pathCost_trace_edge_sum (w : Edge → ℝ) (p : Vertex) (ds : List Step) :
    pathCost w p ds = (((trace p ds).map traversalEdge).map w).sum := by
  induction ds generalizing p with
  | nil => rfl
  | cons d ds ih => simp only [pathCost, trace, List.map_cons, List.sum_cons,
      traversalEdge, ih]

/-- Only a trail's traversal sum can be replaced by its distinct-edge set sum. -/
lemma pathCost_eq_distinct_edgeSum (w : Edge → ℝ) (p : Vertex) (ds : List Step)
    (hn : ((trace p ds).map traversalEdge).Nodup) :
    pathCost w p ds = ∑ e ∈ ((trace p ds).map traversalEdge).toFinset, w e := by
  classical
  rw [pathCost_trace_edge_sum]
  exact (List.sum_toFinset w hn).symm

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
variable {τ : Edge → Ω → ℝ} {shape rate : ℝ}

/-- Genuine Gamma lower tail for any fixed trail, with arbitrary real threshold.
The positive parameter s uses the native MGF at theta=-s. -/
theorem GammaEnvironment.cheap_path_probability
    (h : GammaEnvironment shape rate P τ) (hs : 0 < shape) (hr : 0 < rate)
    (s : ℝ) (hsp : 0 < s) (p : Vertex) (ds : List Step)
    (hn : ((trace p ds).map traversalEdge).Nodup) (t : ℝ) :
    P {ω | pathCost (fun e => τ e ω) p ds ≤ t} ≤
      (ENNReal.ofReal ((rate / (rate + s)) ^ shape)) ^ ds.length /
        ENNReal.ofReal (Real.exp (-s * t)) := by
  classical
  have hc : ((trace p ds).map traversalEdge).toFinset.card = ds.length := by
    rw [List.toFinset_card_of_nodup hn, trace_edge_length]
  have he (ω : Ω) : edgeSum ((trace p ds).map traversalEdge).toFinset τ ω =
      pathCost (fun e => τ e ω) p ds := by
    exact (pathCost_eq_distinct_edgeSum (fun e => τ e ω) p ds hn).symm
  have hb := h.lower_tail_edgeSum hs hr (neg_neg_of_pos hsp)
    ((trace p ds).map traversalEdge).toFinset t
  simpa only [he, hc, sub_neg_eq_add] using hb

/-- Conversion keeps the upper bound finite before passing to real probability. -/
theorem GammaEnvironment.cheap_path_probability_real
    (h : GammaEnvironment shape rate P τ) (hs : 0 < shape) (hr : 0 < rate)
    (s : ℝ) (hsp : 0 < s) (p : Vertex) (ds : List Step)
    (hn : ((trace p ds).map traversalEdge).Nodup) (t : ℝ) :
    P.real {ω | pathCost (fun e => τ e ω) p ds ≤ t} ≤
      ((rate / (rate + s)) ^ shape) ^ ds.length * Real.exp (s * t) := by
  have hbase : 0 ≤ (rate / (rate + s)) ^ shape :=
    (Real.rpow_pos_of_pos (div_pos hr (add_pos hr hsp)) shape).le
  have hden : ENNReal.ofReal (Real.exp (-s * t)) ≠ 0 :=
    ENNReal.ofReal_ne_zero_iff.mpr (Real.exp_pos _)
  have hfin : (ENNReal.ofReal ((rate / (rate + s)) ^ shape)) ^ ds.length /
      ENNReal.ofReal (Real.exp (-s * t)) ≠ ⊤ :=
    ENNReal.div_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top) hden
  have hb := ENNReal.toReal_mono hfin (h.cheap_path_probability hs hr s hsp p ds hn t)
  simp only [ENNReal.toReal_div, ENNReal.toReal_pow,
    ENNReal.toReal_ofReal hbase, ENNReal.toReal_ofReal (Real.exp_pos _).le] at hb
  change P.real _ ≤ _ at hb
  rw [show -s * t = -(s * t) by ring, Real.exp_neg, div_inv_eq_mul] at hb
  exact hb

/-- The probability that a finite family contains a cheap trail is bounded by
its cardinality times the single-trail estimate. -/
theorem GammaEnvironment.cheap_path_family_probability
    (h : GammaEnvironment shape rate P τ) (hs : 0 < shape) (hr : 0 < rate)
    (s : ℝ) (hsp : 0 < s) (p : Vertex) (F : Finset (List Step)) (n : ℕ)
    (hF : ∀ ds ∈ F, ((trace p ds).map traversalEdge).Nodup ∧ ds.length = n)
    (t : ℝ) :
    P {ω | ∃ ds ∈ F, pathCost (fun e => τ e ω) p ds ≤ t} ≤
      (F.card : ℝ≥0∞) * ((ENNReal.ofReal ((rate / (rate + s)) ^ shape)) ^ n /
        ENNReal.ofReal (Real.exp (-s * t))) := by
  classical
  have he : {ω | ∃ ds ∈ F, pathCost (fun e => τ e ω) p ds ≤ t} =
      ⋃ ds ∈ F, {ω | pathCost (fun e => τ e ω) p ds ≤ t} := by
    ext ω
    simp
  rw [he]
  refine (measure_biUnion_finset_le _ _).trans ?_
  calc
    _ ≤ ∑ _ds ∈ F, ((ENNReal.ofReal ((rate / (rate + s)) ^ shape)) ^ n /
        ENNReal.ofReal (Real.exp (-s * t))) := by
      apply Finset.sum_le_sum
      intro ds hds
      simpa only [(hF ds hds).2] using
        h.cheap_path_probability hs hr s hsp p ds (hF ds hds).1 t
    _ = _ := by simp

end GammaFPP

end OAI
