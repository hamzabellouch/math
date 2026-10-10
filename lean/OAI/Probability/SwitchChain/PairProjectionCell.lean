import OAI.Probability.SwitchChain.OrthogonalPairResampling

namespace OAI

noncomputable section
open scoped BigOperators RealInnerProductSpace

namespace Problem315.PairResampling

attribute [local instance] Classical.propDecidable

variable {n : ℕ} {d : Fin n → ℕ}

def restrictCell (C : GraphState n d → Prop) (f : StateSpace n d) : StateSpace n d :=
  WithLp.toLp 2 (fun G => if C G then f G else 0)

@[simp] theorem restrictCell_apply (C : GraphState n d → Prop)
    (f : StateSpace n d) (G : GraphState n d) :
    restrictCell C f G = if C G then f G else 0 := rfl

@[simp] theorem restrictCell_idempotent (C : GraphState n d → Prop)
    (f : StateSpace n d) : restrictCell C (restrictCell C f) = restrictCell C f := by
  ext G
  by_cases h : C G <;> simp [h]

@[simp] theorem restrictCell_sub (C : GraphState n d → Prop)
    (f g : StateSpace n d) : restrictCell C (f - g) = restrictCell C f - restrictCell C g := by
  ext G
  by_cases h : C G <;> simp [restrictCell, h]

def CellInvariant (a : Finset (Fin n)) (C : GraphState n d → Prop) : Prop :=
  ∀ G H, SameFiber a G.val H.val → (C G ↔ C H)

theorem expectation_restrictCell (a : Finset (Fin n))
    (C : GraphState n d → Prop) (hC : CellInvariant a C) (f : StateSpace n d) :
    expectation n d a (restrictCell C f) = restrictCell C (expectation n d a f) := by
  ext G
  rw [expectation_eq_average, restrictCell_apply]
  by_cases hG : C G
  · rw [ite_eq_left hG, expectation_eq_average]
    congr 1
    apply Finset.sum_congr rfl
    intro H hH
    have hH' : C H := (hC G H ((mem_fiberStates a G H).mp hH)).mp hG
    exact ite_eq_left hH'
  · rw [ite_eq_right hG]
    have hs : (∑ H ∈ fiberStates a G, restrictCell C f H) = 0 := by
      apply Finset.sum_eq_zero
      intro H hH
      have hH' : ¬ C H := fun hh => hG ((hC G H ((mem_fiberStates a G H).mp hH)).mpr hh)
      exact ite_eq_right hH'
    rw [hs, zero_div]

theorem fluctuation_restrictCell (a : Finset (Fin n))
    (C : GraphState n d → Prop) (hC : CellInvariant a C) (f : StateSpace n d) :
    fluctuation n d a (restrictCell C f) = restrictCell C (fluctuation n d a f) := by
  rw [fluctuation_eq_sub, expectation_restrictCell a C hC,
      fluctuation_eq_sub, restrictCell_sub]

theorem restrictCell_eq_self_iff (C : GraphState n d → Prop) (f : StateSpace n d) :
    restrictCell C f = f ↔ ∀ G, ¬ C G → f G = 0 := by
  constructor
  · intro h G hG
    have hh := congrArg (fun v : StateSpace n d => v G) h
    simpa [hG] using hh.symm
  · intro h
    ext G
    by_cases hG : C G
    · exact ite_eq_left hG
    · simp [hG, h G hG]

theorem expectation_preserves_cell_support (a : Finset (Fin n))
    (C : GraphState n d → Prop) (hC : CellInvariant a C) (f : StateSpace n d)
    (hf : ∀ G, ¬ C G → f G = 0) :
    ∀ G, ¬ C G → expectation n d a f G = 0 := by
  apply (restrictCell_eq_self_iff C _).mp
  rw [← expectation_restrictCell a C hC, (restrictCell_eq_self_iff C f).mpr hf]

theorem fluctuation_preserves_cell_support (a : Finset (Fin n))
    (C : GraphState n d → Prop) (hC : CellInvariant a C) (f : StateSpace n d)
    (hf : ∀ G, ¬ C G → f G = 0) :
    ∀ G, ¬ C G → fluctuation n d a f G = 0 := by
  apply (restrictCell_eq_self_iff C _).mp
  rw [← fluctuation_restrictCell a C hC, (restrictCell_eq_self_iff C f).mpr hf]

theorem restrictCell_inner (C : GraphState n d → Prop) (f g : StateSpace n d) :
    inner ℝ (restrictCell C f) g = inner ℝ f (restrictCell C g) := by
  rw [state_inner, state_inner]
  apply Finset.sum_congr rfl
  intro G hG
  by_cases h : C G <;> simp [h]

theorem sum_restrictCell {β : Type*} [Fintype β] (k : GraphState n d → β)
    (f : StateSpace n d) :
    (∑ b : β, restrictCell (fun G => k G = b) f) = f := by
  classical
  ext G
  simp [restrictCell]

theorem inner_eq_sum_cell_inner {β : Type*} [Fintype β]
    (k : GraphState n d → β) (f g : StateSpace n d) :
    inner ℝ f g = ∑ b : β,
      inner ℝ (restrictCell (fun G => k G = b) f)
        (restrictCell (fun G => k G = b) g) := by
  classical
  simp_rw [state_inner]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro G hG
  simp [restrictCell]

theorem norm_sq_eq_sum_cell_norm_sq {β : Type*} [Fintype β]
    (k : GraphState n d → β) (f : StateSpace n d) :
    ‖f‖ ^ 2 = ∑ b : β, ‖restrictCell (fun G => k G = b) f‖ ^ 2 := by
  simpa only [real_inner_self_eq_norm_sq] using inner_eq_sum_cell_inner k f f

theorem fluctuation_interaction_eq_sum_cells {β : Type*} [Fintype β]
    (k : GraphState n d → β) (a b : Finset (Fin n))
    (ha : ∀ c, CellInvariant a (fun G => k G = c))
    (hb : ∀ c, CellInvariant b (fun G => k G = c)) (f : StateSpace n d) :
    inner ℝ (fluctuation n d a f) (fluctuation n d b f) =
      ∑ c : β, inner ℝ (fluctuation n d a (restrictCell (fun G => k G = c) f))
        (fluctuation n d b (restrictCell (fun G => k G = c) f)) := by
  rw [inner_eq_sum_cell_inner k]
  apply Finset.sum_congr rfl
  intro c hc
  rw [fluctuation_restrictCell a _ (ha c), fluctuation_restrictCell b _ (hb c)]

end Problem315.PairResampling

end

end OAI
