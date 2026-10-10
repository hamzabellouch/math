import OAI.Analysis.CircleDomains.Selection.PriorityTermination

namespace OAI

/-! Cutoffs whose centers lie in a closed set and whose radii tend to
zero have a common finite tail vanishing near each point of its complement. -/
open Set Function Filter Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem concentrated_cutoffs_eventually_zero
    {X : Type*} [MetricSpace X] {B : Set X} (hB : IsClosed B)
    (c : ℕ → X) (hc : ∀ n, c n ∈ B) (r : ℕ → ℝ) (hr : Tendsto r atTop (𝓝 0))
    (χ : ℕ → X → ℝ) (hs : ∀ n, support (χ n) ⊆ ball (c n) (r n))
    {x : X} (hx : x ∉ B) :
    ∃ V : Set X, IsOpen V ∧ x ∈ V ∧ ∃ N : ℕ, ∀ n, N ≤ n → ∀ y ∈ V, χ n y = 0 := by
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp (hB.isOpen_compl.mem_nhds hx)
  have hsmall : ∀ᶠ n in atTop, r n < δ/2 := hr.eventually (gt_mem_nhds (by linarith))
  obtain ⟨N, hN⟩ := eventually_atTop.mp hsmall
  refine ⟨ball x (δ/2), isOpen_ball, mem_ball_self (by linarith), N, ?_⟩
  intro n hn y hy
  by_contra hne
  have hyc := hs n hne
  have hcx : dist (c n) x < δ := by
    calc
      dist (c n) x ≤ dist (c n) y+dist y x := dist_triangle _ _ _
      _ < δ/2+δ/2 := add_lt_add (by simpa only [dist_comm] using hyc.trans (hN n hn)) hy
      _ = δ := by ring
  exact (hball hcx) (hc n)

end CircleDomainRigidity

end

end OAI
