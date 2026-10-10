import OAI.Probability.SLE.Stochastic.DrivingEndpointUniqueness

namespace OAI

/-! A diagonal choice for the two limits used at a slit tip. -/
noncomputable section
open Set Filter Function Complex Metric
open scoped Topology

namespace SLEExactGauge

lemma diagonal_complex_limit {f : ℕ → ℕ → ℂ} {g : ℕ → ℂ} {b : ℂ}
    (hf : ∀ k, Tendsto (fun n => f n k) atTop (𝓝 (g k)))
    (hg : Tendsto g atTop (𝓝 b)) :
    ∃ φ : ℕ → ℕ, (∀ n, n≤φ n) ∧ Tendsto (fun n => f (φ n) n) atTop (𝓝 b) := by
  have hN (k : ℕ) : ∃ N : ℕ, ∀ n≥N, dist (f n k) (g k)<1/((k:ℝ)+1) := by
    exact eventually_atTop.mp ((Metric.tendsto_nhds.mp (hf k)) _ (by positivity))
  choose N hN using hN
  let φ := fun n => max n (N n)
  refine ⟨φ,fun n => le_max_left _ _,Metric.tendsto_nhds.mpr ?_⟩
  intro ε hε
  filter_upwards [(Metric.tendsto_nhds.mp hg) (ε/2) (half_pos hε),
    tendsto_one_div_add_atTop_nhds_zero_nat.eventually (gt_mem_nhds (half_pos hε))] with n hn he
  have hd := hN n (φ n) (le_max_right _ _)
  exact (dist_triangle _ (g n) b).trans_lt (by linarith)

end SLEExactGauge

end

end OAI
