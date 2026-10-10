import OAI.Probability.SwitchChain.PairProjectionCell

namespace OAI

noncomputable section
open scoped BigOperators RealInnerProductSpace

namespace Problem315.PairResampling

attribute [local instance] Classical.propDecidable
variable {n : ℕ} {d : Fin n → ℕ}

theorem starProjection_restrictCell
    (M : Submodule ℝ (StateSpace n d)) (C : GraphState n d → Prop)
    (hM : ∀ f ∈ M, restrictCell C f ∈ M) (f : StateSpace n d) :
    M.starProjection (restrictCell C f) = restrictCell C (M.starProjection f) := by
  apply M.eq_starProjection_of_mem_of_inner_eq_zero
    (hM _ (M.starProjection_apply_mem f))
  intro w hw
  rw [← restrictCell_sub, restrictCell_inner]
  exact M.starProjection_inner_eq_zero f _ (hM w hw)

theorem map_norm_sq_eq_sum_cells {β : Type*} [Fintype β]
    (k : GraphState n d → β) (A : StateSpace n d → StateSpace n d)
    (hA : ∀ c f, A (restrictCell (fun G => k G = c) f) =
      restrictCell (fun G => k G = c) (A f)) (f : StateSpace n d) :
    ‖A f‖ ^ 2 = ∑ c : β, ‖A (restrictCell (fun G => k G = c) f)‖ ^ 2 := by
  simp_rw [hA]
  exact norm_sq_eq_sum_cell_norm_sq k (A f)

theorem starProjection_norm_sq_eq_sum_cells {β : Type*} [Fintype β]
    (k : GraphState n d → β) (M : Submodule ℝ (StateSpace n d))
    (hM : ∀ c f, f ∈ M → restrictCell (fun G => k G = c) f ∈ M)
    (f : StateSpace n d) :
    ‖M.starProjection f‖ ^ 2 =
      ∑ c : β, ‖M.starProjection (restrictCell (fun G => k G = c) f)‖ ^ 2 := by
  exact map_norm_sq_eq_sum_cells k M.starProjection
    (fun c f => starProjection_restrictCell M _ (hM c) f) f

theorem disjoint_interaction_of_cellwise {β : Type*} [Fintype β]
    (k : GraphState n d → β) (a b : Finset (Fin n))
    (ha : ∀ c, CellInvariant a (fun G => k G = c))
    (hb : ∀ c, CellInvariant b (fun G => k G = c))
    (g R S : StateSpace n d → StateSpace n d)
    (hg : ∀ c f, g (restrictCell (fun G => k G = c) f) =
      restrictCell (fun G => k G = c) (g f))
    (hR : ∀ c f, R (restrictCell (fun G => k G = c) f) =
      restrictCell (fun G => k G = c) (R f))
    (hS : ∀ c f, S (restrictCell (fun G => k G = c) f) =
      restrictCell (fun G => k G = c) (S f))
    (hlocal : ∀ c f, (∀ G, k G ≠ c → f G = 0) →
      2 * ‖g f‖ ^ 2 - ‖R f‖ ^ 2 - ‖S f‖ ^ 2 ≤
        2 * ⟪fluctuation n d a f, fluctuation n d b f⟫)
    (f : StateSpace n d) :
    2 * ‖g f‖ ^ 2 - ‖R f‖ ^ 2 - ‖S f‖ ^ 2 ≤
      2 * ⟪fluctuation n d a f, fluctuation n d b f⟫ := by
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun c _ =>
    hlocal c (restrictCell (fun G => k G = c) f)
      (by intro G hG; simp [hG]))
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum] at hsum
  rw [← map_norm_sq_eq_sum_cells k g hg f,
    ← map_norm_sq_eq_sum_cells k R hR f,
    ← map_norm_sq_eq_sum_cells k S hS f,
    ← fluctuation_interaction_eq_sum_cells k a b ha hb f] at hsum
  exact hsum

end Problem315.PairResampling

end

end OAI
