import OAI.Probability.LatticePassage.Geodesic

namespace OAI

namespace CompanionFPP

private lemma sublist_length_of_cost {α : Type*} (f : α → ℝ)
    {l₁ l₂ : List α} (h : l₁.Sublist l₂) (hpos : ∀ a ∈ l₂, 0 < f a)
    (hcost : (l₂.map f).sum ≤ (l₁.map f).sum) : l₂.length ≤ l₁.length := by
  induction h with
  | slnil => simp
  | @cons l₁ l₂ a h ih =>
    have hnonneg : ∀ b ∈ l₂, 0 ≤ f b := fun b hb => (hpos b (by simp [hb])).le
    have hle := (h.map f).sum_le_sum (by
      intro b hb
      obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hb
      exact hnonneg c hc)
    have ha := hpos a (by simp)
    simp only [List.map_cons, List.sum_cons] at hcost
    linarith
  | @cons_cons l₁ l₂ a h ih =>
    have ht : ∀ b ∈ l₂, 0 < f b := fun b hb => hpos b (by simp [hb])
    have hs : (l₂.map f).sum ≤ (l₁.map f).sum := by
      simpa only [List.map_cons, List.sum_cons, add_le_add_iff_left] using hcost
    simpa using ih ht hs

theorem minimizing_walk_isPath (ω : Environment) (hω : ∀ e, 0 < ω e)
    {x y : Vertex} (p : lattice.Walk x y)
    (hp : pathCost ω p = passageTime ω x y) : p.IsPath := by
  classical
  have hcost : pathCost ω p ≤ pathCost ω p.bypass := by
    rw [hp]
    exact passageTime_le_pathCost ω (fun e => (hω e).le) p.bypass
  rw [pathCost_eq_darts_sum, pathCost_eq_darts_sum] at hcost
  have hl := sublist_length_of_cost (fun d : lattice.Dart => edgeCost ω d.adj)
    p.darts_bypass_sublist_darts (by intro d _; exact hω _) hcost
  have he := p.length_le_bypass_length_iff.mp (by simpa using hl)
  rw [← he]
  exact p.bypass_isPath

theorem all_minimizing_walks_simple : ∀ᵐ ω ∂environmentLaw, ∀ x y : Vertex,
    ∀ p : lattice.Walk x y, pathCost ω p = passageTime ω x y → p.IsPath := by
  filter_upwards [all_edge_weights_positive] with ω hω
  exact fun _ _ p hp => minimizing_walk_isPath ω hω p hp

end CompanionFPP

end OAI
