import OAI.Probability.FKPressure.Basic

namespace OAI

 

noncomputable section
open Finset SimpleGraph
open scoped Classical
namespace BelowOne.FKPressure
attribute [local instance] Classical.propDecidable
variable {V I : Type*} [Fintype V]

lemma reachable_image_of_adj_reachable {U W : Type*} (K : SimpleGraph U)
    (H : SimpleGraph W) (f : U → W)
    (hf : ∀ a b, K.Adj a b → H.Reachable (f a) (f b))
    {a b : U} (h : K.Reachable a b) : H.Reachable (f a) (f b) := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => exact Reachable.rfl
  | @cons a b c hab p ih => exact (hf a b hab).trans ih

omit [Fintype V] in
lemma connected_types_of_component_count {n : ℕ} (hn : 0 < n)
    (τ : Fin n → V) (ends : I → V × V) (E : Finset I)
    {D : Finset (I × Fin n × Fin n)} (hD : D ⊆ liftEdges τ ends E)
    {L : Finset (Fin n × Fin n)} (hL : L ⊆ hardEdges τ)
    (hc : components (graph ⊥ Prod.snd D) id L = 1) :
    ((graph ⊥ ends E).induce (Set.range τ)).Connected := by
  let H := (graph ⊥ ends E).induce (Set.range τ)
  let f : Fin n → Set.range τ := fun i => ⟨τ i, ⟨i, rfl⟩⟩
  let K := graph (graph ⊥ Prod.snd D) id L
  have hf : ∀ a b, K.Adj a b → H.Reachable (f a) (f b) := by
    intro a b hab
    rcases (graph_adj_iff _ id L a b).mp hab with ho | ⟨e, he, hedge⟩
    · rcases (graph_adj_iff ⊥ Prod.snd D a b).mp ho with hno | ⟨e, he, hedge⟩
      · exact False.elim hno
      have he' := (mem_liftEdges τ ends E e).mp (hD he)
      by_cases hsame : τ a = τ b
      · have hab' : f a = f b := Subtype.ext hsame
        rw [hab']
      · apply Adj.reachable
        change (graph ⊥ ends E).Adj (τ a) (τ b)
        apply (graph_adj_iff ⊥ ends E _ _).mpr
        refine Or.inr ⟨e.1, he'.1, ?_⟩
        apply (edge_adj _ _ _ _).mpr
        refine ⟨?_, hsame⟩
        rcases (edge_adj _ _ _ _).mp hedge with ⟨⟨ha,hb⟩ | ⟨ha,hb⟩, _⟩
        · exact Or.inl ⟨(congrArg τ ha).trans he'.2.1, (congrArg τ hb).trans he'.2.2⟩
        · exact Or.inr ⟨(congrArg τ ha).trans he'.2.2, (congrArg τ hb).trans he'.2.1⟩
    · have he' : τ e.1 = τ e.2 := by
        have hh : e.1 < e.2 ∧ τ e.1 = τ e.2 := by
          simpa only [hardEdges, mem_filter, mem_univ, true_and] using hL he
        exact hh.2
      have hab' : f a = f b := by
        apply Subtype.ext
        rcases (edge_adj _ _ _ _).mp hedge with ⟨⟨ha,hb⟩ | ⟨ha,hb⟩, _⟩
        · exact (congrArg τ ha).trans (he'.trans (congrArg τ hb).symm)
        · exact (congrArg τ ha).trans (he'.symm.trans (congrArg τ hb).symm)
      rw [hab']
  have : Subsingleton K.ConnectedComponent :=
    (Nat.card_eq_one_iff_unique.mp hc).1
  have : Nonempty (Set.range τ) := ⟨f ⟨0, hn⟩⟩
  refine ⟨?_⟩
  intro x y
  obtain ⟨a, ha⟩ := x.property
  obtain ⟨b, hb⟩ := y.property
  have hk : K.Reachable a b := ConnectedComponent.exact (Subsingleton.elim _ _)
  have him := reachable_image_of_adj_reachable K H f hf hk
  have hax : f a = x := Subtype.ext ha
  have hby : f b = y := Subtype.ext hb
  simpa only [hax, hby] using him

omit [Fintype V] in
lemma connectedSum_eq_zero_of_disconnected_types {n : ℕ} (hn : 0 < n)
    (τ : Fin n → V) (ends : I → V × V) (E : Finset I) (s : ℝ) (v : I → ℝ)
    (h : ¬ ((graph ⊥ ends E).induce (Set.range τ)).Connected) :
    connectedSum ⊥ Prod.snd id (liftEdges τ ends E) (hardEdges τ) s (v ∘ Prod.fst) = 0 := by
  let : DecidableEq (I × Fin n × Fin n) := Classical.decEq _
  unfold connectedSum
  apply sum_eq_zero
  intro A hA
  apply sum_eq_zero
  intro B hB
  apply mul_eq_zero_of_right
  unfold hardSum
  apply sum_eq_zero
  intro L hL
  apply ite_eq_right
  intro hc
  apply h
  exact connected_types_of_component_count hn τ ends E
    (union_subset (mem_powerset.mp hA) (mem_powerset.mp hB)) (mem_powerset.mp hL) hc

lemma pressure_derivative_eq_zero_of_disconnected_types {n : ℕ} (hn : 0 < n)
    (τ : Fin n → V) (ends : I → V × V) (E : Finset I)
    (u : ℝ) (v : I → ℝ) (hv : ∀ e ∈ E, 0 ≤ v e)
    (h : ¬ ((graph ⊥ ends E).induce (Set.range τ)).Connected) :
    iteratedFDeriv ℝ n (pressure ends E u v) 0
      (MultiaffineDerivative.coordinate ∘ τ) = 0 := by
  have heq : Real.log ∘ percolationSitePolynomial ends E (-u) v =
      fun x => (Real.log ∘ unscaledSitePolynomial ends E (-u) v)
        (fun i => incidentScale ends E v i * x i) := by
    funext x
    simp only [Function.comp_apply, percolationSitePolynomial_rescale ends E (-u) v hv]
  have hl : iteratedFDeriv ℝ n (Real.log ∘ percolationSitePolynomial ends E (-u) v) 0
      (MultiaffineDerivative.coordinate ∘ τ) = 0 := by
    rw [heq, MultiaffineDerivative.iteratedFDeriv_diagonal]
    · rw [unscaledSitePolynomial_log_derivative hn,
        connectedSum_eq_zero_of_disconnected_types hn τ ends E (-u) v h, mul_zero]
    · intro i
      exact ne_of_gt (inv_pos.mpr (incidentProduct_pos ends E v hv i))
  change iteratedFDeriv ℝ n (-(Real.log ∘ percolationSitePolynomial ends E (-u) v)) 0
    (MultiaffineDerivative.coordinate ∘ τ) = 0
  rw [iteratedFDeriv_neg_apply, neg_apply, hl, neg_zero]

lemma taylor_coordinate_connected {n : ℕ} (hn : 0 < n)
    (τ : Fin n → V) (ends : I → V × V) (E : Finset I)
    (u : ℝ) (v : I → ℝ) (hv : ∀ e ∈ E, 0 ≤ v e)
    (h : PositiveAnalyticCube.taylor (pressure ends E u v) n
      (MultiaffineDerivative.coordinate ∘ τ) ≠ 0) :
    ((graph ⊥ ends E).induce (Set.range τ)).Connected := by
  by_contra hd
  apply h
  simp only [PositiveAnalyticCube.taylor, _root_.smul_apply, smul_eq_mul,
    pressure_derivative_eq_zero_of_disconnected_types hn τ ends E u v hv hd, mul_zero]

end BelowOne.FKPressure

end

end OAI
