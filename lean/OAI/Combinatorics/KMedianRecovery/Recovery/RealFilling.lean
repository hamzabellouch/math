import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.Virtual

namespace OAI

namespace MetricKMedianRecovery.Completion
variable {V : Type*} [PseudoMetricSpace V] [DecidableEq V]

lemma exists_real_filling {E : Type*} [DecidableEq E] {a : ℕ}
    (F : Finset V) (part : E → Fin a) (hp : Function.Surjective part)
    (loc : E → V) (w : Fin a → V) (radius : Fin a → ℝ)
    (hloc : ∀ e, loc e ∈ F) (hball : ∀ e, dist (w (part e)) (loc e) ≤ radius (part e))
    (X : Finset E) (hX : ∀ j, (X.filter (fun e => part e = j)).card ≤ 1) :
    ∃ Filled : Finset V, Filled ⊆ F ∧ Filled.card ≤ a ∧
      (∀ e ∈ X, loc e ∈ Filled) ∧
      (∀ i, ∃ x ∈ Filled, dist (w i) x ≤ radius i) := by
  have hc : ∀ j : Fin a, ∃ e, part e = j ∧ ∀ f ∈ X, part f = j → f = e := by
    intro j
    by_cases hn : (X.filter (fun e => part e = j)).Nonempty
    · obtain ⟨e,he⟩ := hn
      refine ⟨e,(Finset.mem_filter.mp he).2,?_⟩
      intro f hf hj
      exact (Finset.card_le_one.mp (hX j)) _ (Finset.mem_filter.mpr ⟨hf,hj⟩) _ he
    · obtain ⟨e,he⟩ := hp j
      refine ⟨e,he,?_⟩
      intro f hf hj
      exact (hn ⟨f,Finset.mem_filter.mpr ⟨hf,hj⟩⟩).elim
  choose o ho hfill using hc
  refine ⟨Finset.univ.image (loc ∘ o),?_,?_,?_,?_⟩
  · intro x hx
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hx
    exact hloc _
  · exact (Finset.card_image_le).trans (by simp)
  · intro e he
    apply Finset.mem_image.mpr
    refine ⟨part e,Finset.mem_univ _,?_⟩
    simp only [Function.comp_apply,← hfill (part e) e he rfl]
  · intro i
    refine ⟨loc (o i),Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩,?_⟩
    simpa only [ho] using hball (o i)

omit [PseudoMetricSpace V] in
lemma padded_completion (F S Q Red Blue Add : Finset V)
    (hS : S ⊆ F) (hn : S.Nonempty)
    (hQ : Q ⊆ S) (hRed : Red ⊆ S \ Q) (hBlue : Blue ⊆ S \ Q)
    (hRB : Disjoint Red Blue) (hAdd : Add ⊆ F)
    (hcount : Add.card ≤ Q.card + Red.card + Blue.card) :
    ∃ U : Finset V, U ⊆ F ∧ U.card = S.card ∧ U.Nonempty ∧
      ((S \ (Q ∪ Red ∪ Blue)) ∪ Add) ⊆ U := by
  let U₀ := (S \ (Q ∪ Red ∪ Blue)) ∪ Add
  have h₀ : U₀ ⊆ F := Finset.union_subset (Finset.sdiff_subset.trans hS) hAdd
  obtain ⟨U,hU₀,hUF,hUc⟩ := Finset.exists_subsuperset_card_eq h₀
    (completion_cardinality S Q Red Blue Add hQ hRed hBlue hRB hcount)
    (Finset.card_le_card hS)
  exact ⟨U,hUF,hUc,Finset.card_pos.mp (by rw [hUc]; exact Finset.card_pos.mpr hn),hU₀⟩

lemma virtual_domination {a : ℕ} (F U G : Finset V) (hU : U.Nonempty)
    (w : Fin a → V) (radius : Fin a → ℝ) (M : ℝ)
    (hUF : U ⊆ F) (hG : G ⊆ U)
    (hfill : ∀ i, ∃ u ∈ U, dist (w i) u ≤ radius i)
    (hM : ∀ x, ∀ f ∈ F, dist x f ≤ M) (x : V) :
    ∀ t ∈ withGhosts G, distanceTo U hU x ≤ virtualDistance w radius M x t := by
  intro t ht
  cases t with
  | real s => exact distanceTo_le hU x (hG (real_mem_withGhosts.mp ht))
  | ball i =>
    obtain ⟨u,hu,hb⟩ := hfill i
    exact (distanceTo_le hU x hu).trans
      ((dist_triangle x (w i) u).trans (by change dist x (w i) + dist (w i) u ≤ dist x (w i) + radius i; linarith))
  | permanent =>
    obtain ⟨u,hu⟩ := hU
    exact (distanceTo_le ⟨u,hu⟩ x hu).trans (hM x u (hUF hu))

lemma nearest_le_virtualNearest {a : ℕ} (F U G : Finset V) (hU : U.Nonempty)
    (w : Fin a → V) (radius : Fin a → ℝ) (M : ℝ)
    (hUF : U ⊆ F) (hG : G ⊆ U)
    (hfill : ∀ i, ∃ u ∈ U, dist (w i) u ≤ radius i)
    (hM : ∀ x, ∀ f ∈ F, dist x f ≤ M) (x : V) :
    distanceTo U hU x ≤ virtualNearest G w radius M x := by
  apply Finset.le_inf'
  exact virtual_domination F U G hU w radius M hUF hG hfill hM x

lemma nearest_le_redCost {E : Type*} {a : ℕ} (F U G : Finset V) (hU : U.Nonempty)
    (w : Fin a → V) (radius : Fin a → ℝ) (M : ℝ) (loc : E → V) (X : Finset E)
    (hUF : U ⊆ F) (hG : G ⊆ U)
    (hfill : ∀ i, ∃ u ∈ U, dist (w i) u ≤ radius i)
    (hM : ∀ x, ∀ f ∈ F, dist x f ≤ M) (hX : ∀ e ∈ X, loc e ∈ U) (s : V) :
    distanceTo U hU s ≤ cappedCost (virtualNearest G w radius M s) (fun e => dist s (loc e)) X := by
  apply le_cappedCost
  · exact nearest_le_virtualNearest F U G hU w radius M hUF hG hfill hM s
  · intro e he
    exact distanceTo_le hU s (hX e he)

omit [PseudoMetricSpace V] in

lemma sum_assignment_charges {a : ℕ} {R : Type*} (D : Finset V)
    (assignment : V → Virtual V a) (T : Finset R) (loc : R → V) (charge : R → ℝ) :
    (∑ p ∈ D, ∑ r ∈ T, if assignment p = Virtual.real (loc r) then charge r else 0) =
      ∑ r ∈ T, assignmentWeight D assignment (loc r) * charge r := by
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun r _ => assignmentWeight_sum D assignment (loc r) (charge r))

end MetricKMedianRecovery.Completion

end OAI
