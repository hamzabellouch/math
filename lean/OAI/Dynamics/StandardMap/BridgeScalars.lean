import OAI.Dynamics.StandardMap.ForwardChart

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open Set Filter Metric
open scoped Topology
namespace StandardMapEntropy
structure BridgeScalarControl (k : ℝ) : Prop where
  nonneg : 0 ≤ k
  prefix_geom : growthBase k^(-(49/25:ℝ)) ≤ 1/2
  prefix_small : 3*growthBase k^(-(47/50:ℝ)) ≤ 1/4
  graph_geom : growthBase k^(-(3/5:ℝ)) ≤ 1/2
  graph_small : (384*Real.pi)*growthBase k^(-(7/10:ℝ)) ≤ 1/2
  slope_small : 24/growthBase k^((4/5:ℝ)) ≤ 1/2
lemma BridgeScalarControl.prefix_dirichlet {k : ℝ} (h : BridgeScalarControl k)
    (B n : ℕ) (hn : 1 ≤ n) (hB : B=n ∨ B=n+1) (hBn : 2 ≤ B)
    (z : ℝ × ℝ) (hz : prefixEligible k B (n+1) z) :
    tSolution (orbitCoefficient k z.1 z.2) (n+1) ≠ 0 ∧ ∀ p, 1 ≤ p → p ≤ n →
      |dirichletSolution (orbitCoefficient k z.1 z.2) (n+1) p| ≤
        12*growthBase k^(-(9/10:ℝ)*(p:ℝ)) := by
  have hJ : n+1=B ∨ n+1=B+1 := by rcases hB with rfl|rfl <;> omega
  have hh := eligible_prefix_dirichlet (orbitCoefficient k z.1 z.2) (growthBase k) B (n+1)
    hBn hJ (by have := growthBase_ge_four k h.nonneg; linarith) h.prefix_geom h.prefix_small
    (fun i _ _ => potential_bound k _ h.nonneg) hz.1 hz.2
  exact ⟨hh.1,fun p hp hpn => hh.2 p hp (by omega)⟩
lemma eventually_bridgeScalarControl : ∀ᶠ k : ℝ in atTop, BridgeScalarControl k := by
  have he (a C ε : ℝ) (ha : 0 < a) (hε : 0 < ε) :
      ∀ᶠ k : ℝ in atTop, C*growthBase k^(-a) ≤ ε := by
    have ht := ((tendsto_rpow_neg_atTop ha).comp tendsto_growthBase).const_mul C
    have hh := ht.eventually (gt_mem_nhds (show C*0 < ε by simpa using hε))
    exact hh.mono fun k hk => hk.le
  filter_upwards [eventually_ge_atTop (0:ℝ),he (49/25) 1 (1/2) (by norm_num) (by norm_num),
    he (47/50) 3 (1/4) (by norm_num) (by norm_num),he (3/5) 1 (1/2) (by norm_num) (by norm_num),
    he (7/10) (384*Real.pi) (1/2) (by norm_num) (by norm_num),he (4/5) 24 (1/2) (by norm_num) (by norm_num)]
    with k hk h1 h2 h3 h4 h5
  refine ⟨hk,by simpa only [one_mul] using h1,h2,by simpa only [one_mul] using h3,h4,?_⟩
  simpa only [Real.rpow_neg (by have := growthBase_ge_four k hk; linarith : 0 ≤ growthBase k),div_eq_mul_inv] using h5
end StandardMapEntropy

end OAI
