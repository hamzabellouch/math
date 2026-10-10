import OAI.Probability.GammaPassage.CheapPathDecay
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Analysis.SpecificLimits.Normed

namespace OAI

namespace GammaFPP
open MeasureTheory ProbabilityTheory PlanarFPP Filter
open scoped ENNReal Topology

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
variable {τ : Edge → Ω → ℝ} {shape rate : ℝ}

/-- Cheap trails at one exact length and one deterministic starting vertex. -/
def cheapTrailEvent (shape rate : ℝ) (τ : Edge → Ω → ℝ)
    (p : Vertex) (n : ℕ) : Set Ω :=
  {ω | ∃ ds : List Step, ds.length = n ∧
    ((trace p ds).map traversalEdge).Nodup ∧
      pathCost (fun e => τ e ω) p ds ≤ cheapSlope shape rate * (n : ℝ)}

/-- Exponential decay is summable, including the nonempty bad event at n=0. -/
theorem GammaEnvironment.summable_cheapTrailEvent_real
    (h : GammaEnvironment shape rate P τ) (hs : 0 < shape) (hr : 0 < rate)
    (p : Vertex) : Summable (fun n => P.real (cheapTrailEvent shape rate τ p n)) := by
  have hg : Summable (fun n : ℕ => (1 / 2 : ℝ) ^ n) :=
    summable_geometric_of_norm_lt_one (by norm_num)
  exact hg.of_nonneg_of_le (fun _ => measureReal_nonneg)
    (fun n => h.cheap_fixed_length_decay_real hs hr p n)

/-- At each fixed start, almost surely all sufficiently long trails have
strictly positive linear cost. No independence across lengths is used. -/
theorem GammaEnvironment.ae_long_trails_cost
    (h : GammaEnvironment shape rate P τ) (hs : 0 < shape) (hr : 0 < rate)
    (p : Vertex) :
    ∀ᵐ ω ∂P, ∃ N : ℕ, ∀ ds : List Step, N ≤ ds.length →
      ((trace p ds).map traversalEdge).Nodup →
        cheapSlope shape rate * (ds.length : ℝ) < pathCost (fun e => τ e ω) p ds := by
  let := h.probability
  have hsum : (∑' n, P (cheapTrailEvent shape rate τ p n)) ≠ ⊤ := by
    simpa only [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)] using
      (h.summable_cheapTrailEvent_real hs hr p).tsum_ofReal_ne_top
  filter_upwards [ae_eventually_notMem hsum] with ω hω
  obtain ⟨N, hN⟩ := eventually_atTop.1 hω
  refine ⟨N, ?_⟩
  intro ds hlen htrail
  by_contra hc
  exact hN ds.length hlen ⟨ds, rfl, htrail, le_of_not_gt hc⟩

/-- Countably many lattice starts may share one event; the length cutoff can
depend on both the environment and the start. -/
theorem GammaEnvironment.ae_all_starts_long_trails_cost
    (h : GammaEnvironment shape rate P τ) (hs : 0 < shape) (hr : 0 < rate) :
    ∀ᵐ ω ∂P, ∀ p : Vertex, ∃ N : ℕ, ∀ ds : List Step, N ≤ ds.length →
      ((trace p ds).map traversalEdge).Nodup →
        cheapSlope shape rate * (ds.length : ℝ) < pathCost (fun e => τ e ω) p ds := by
  rw [ae_all_iff]
  intro p
  exact h.ae_long_trails_cost hs hr p

/-- On the same probability-one event, every real cost budget bounds the length
of all trails starting at any fixed lattice vertex. -/
theorem GammaEnvironment.ae_bounded_cost_trail_lengths
    (h : GammaEnvironment shape rate P τ) (hs : 0 < shape) (hr : 0 < rate) :
    ∀ᵐ ω ∂P, ∀ p : Vertex, ∀ M : ℝ, ∃ R : ℕ, ∀ ds : List Step,
      ((trace p ds).map traversalEdge).Nodup →
      pathCost (fun e => τ e ω) p ds ≤ M → ds.length < R := by
  filter_upwards [h.ae_all_starts_long_trails_cost hs hr] with ω hω
  intro p M
  obtain ⟨N, hN⟩ := hω p
  have hc : 0 < cheapSlope shape rate := cheapSlope_pos hs hr
  obtain ⟨k, hk⟩ := exists_nat_gt (M / cheapSlope shape rate)
  refine ⟨max N k, ?_⟩
  intro ds htrail hcost
  by_contra hlen
  have hlarge : max N k ≤ ds.length := Nat.le_of_not_gt hlen
  have hNk : N ≤ ds.length := (le_max_left N k).trans hlarge
  have hklen : (k : ℝ) ≤ (ds.length : ℝ) := by
    exact_mod_cast (le_max_right N k).trans hlarge
  have hM : M < cheapSlope shape rate * (k : ℝ) := by
    simpa only [mul_comm] using (div_lt_iff₀ hc).mp hk
  have hlower := mul_le_mul_of_nonneg_left hklen hc.le
  have hstrict := hN ds hNk htrail
  linarith

end GammaFPP

end OAI
