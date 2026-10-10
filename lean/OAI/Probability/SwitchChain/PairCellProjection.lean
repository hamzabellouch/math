import OAI.Probability.SwitchChain.FiniteCellProjection
import OAI.Probability.SwitchChain.PairProjectionCell

namespace OAI

noncomputable section
open scoped BigOperators RealInnerProductSpace
attribute [local instance] Classical.propDecidable

namespace Problem315.PairResampling
open FiniteCellProjection
variable {n : ℕ} {d : Fin n → ℕ}

theorem extend_restrict_eq_restrictCell (p : GraphState n d → Prop)
    (f : StateSpace n d) : extend p (restrict p f) = restrictCell p f := by
  ext G
  by_cases h : p G <;> simp [h]

def cellFiberSpace (a : Finset (Fin n)) (p : GraphState n d → Prop) :
    Submodule ℝ (EuclideanSpace ℝ {G // p G}) where
  carrier := {f | ∀ G H, SameFiber a G.val.val H.val.val → f G = f H}
  zero_mem' := by intro G H h; rfl
  add_mem' := by
    intro f g hf hg G H h
    change f G + g G = f H + g H
    rw [hf G H h, hg G H h]
  smul_mem' := by
    intro c f hf G H h
    change c * f G = c * f H
    rw [hf G H h]

theorem restrict_mem_cellFiberSpace (a : Finset (Fin n))
    (p : GraphState n d → Prop) (f : StateSpace n d)
    (hf : f ∈ fiberSpace n d a) : restrict p f ∈ cellFiberSpace a p := by
  intro G H h
  exact hf G.val H.val h

theorem extend_mem_fiberSpace (a : Finset (Fin n))
    (p : GraphState n d → Prop)
    (hp : ∀ G H : GraphState n d, SameFiber a G.val H.val → (p G ↔ p H))
    (f : EuclideanSpace ℝ {G // p G}) (hf : f ∈ cellFiberSpace a p) :
    extend p f ∈ fiberSpace n d a := by
  intro G H hGH
  by_cases hG : p G
  · have hH : p H := (hp G H hGH).mp hG
    rw [extend_apply_mem p f G hG, extend_apply_mem p f H hH]
    exact hf ⟨G,hG⟩ ⟨H,hH⟩ hGH
  · have hH : ¬ p H := fun h => hG ((hp G H hGH).mpr h)
    rw [extend_apply_not_mem p f G hG, extend_apply_not_mem p f H hH]

theorem restrict_expectation_eq_cellProjection (a : Finset (Fin n))
    (p : GraphState n d → Prop)
    (hp : ∀ G H : GraphState n d, SameFiber a G.val H.val → (p G ↔ p H))
    (f : StateSpace n d) :
    restrict p (expectation n d a f) =
      (cellFiberSpace a p).starProjection (restrict p f) := by
  exact restrict_starProjection p (fiberSpace n d a) (cellFiberSpace a p)
    (restrict_mem_cellFiberSpace a p) (extend_mem_fiberSpace a p hp) f

theorem restrict_fluctuation_eq_cellProjection (a : Finset (Fin n))
    (p : GraphState n d → Prop)
    (hp : ∀ G H : GraphState n d, SameFiber a G.val H.val → (p G ↔ p H))
    (f : StateSpace n d) :
    restrict p (fluctuation n d a f) =
      (cellFiberSpace a p)ᗮ.starProjection (restrict p f) := by
  rw [fluctuation_eq_sub, map_sub, restrict_expectation_eq_cellProjection a p hp]
  exact ((cellFiberSpace a p).starProjection_orthogonal_val (restrict p f)).symm

theorem expectation_fixes_cell_function {K : Type*}
    (a : Finset (Fin n)) (key : GraphState n d → K)
    (hk : ∀ G H : GraphState n d, SameFiber a G.val H.val → key G = key H)
    (g : K → ℝ) :
    expectation n d a (WithLp.toLp 2 (fun G => g (key G))) =
      WithLp.toLp 2 (fun G => g (key G)) := by
  apply (expectation_eq_self_iff a _).mpr
  intro G H h
  change g (key G) = g (key H)
  rw [hk G H h]

theorem fluctuation_sum_square_of_cells
    {ι K : Type*} [Fintype ι] [Fintype K]
    (a : ι → Finset (Fin n)) (key : GraphState n d → K)
    (hk : ∀ i (G H : GraphState n d),
      SameFiber (a i) G.val H.val → key G = key H)
    (hlocal : ∀ k (g : EuclideanSpace ℝ {G // key G = k}),
      ⟪g, ∑ i, (cellFiberSpace (a i) (fun G => key G = k))ᗮ.starProjection g⟫ ≤
      ‖∑ i, (cellFiberSpace (a i) (fun G => key G = k))ᗮ.starProjection g‖ ^ 2)
    (f : StateSpace n d) :
    ⟪f, ∑ i, fluctuation n d (a i) f⟫ ≤
      ‖∑ i, fluctuation n d (a i) f‖ ^ 2 := by
  apply inner_le_norm_sq_of_cells key
  intro k
  have hp i : ∀ G H : GraphState n d,
      SameFiber (a i) G.val H.val → ((key G = k) ↔ (key H = k)) := by
    intro G H h
    rw [hk i G H h]
  simp only [map_sum]
  simp_rw [restrict_fluctuation_eq_cellProjection _ _ (hp _)]
  exact hlocal k (restrict (fun G => key G = k) f)

end Problem315.PairResampling

end

end OAI
