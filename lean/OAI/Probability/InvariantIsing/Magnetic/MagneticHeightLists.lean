import OAI.Probability.InvariantIsing.Fields.FieldHeightLists

namespace OAI

/-! The literal two-increment decomposition of a positive-index height
update after removing the ordinary Gaussian root. -/

noncomputable section
open Set
open scoped NNReal

namespace InvariantIsing

private lemma allIncrements_toNNReal (h : FieldStep) :
    fieldAllIncrements h = List.ofFn (fun j : Fin (h.depth + 1) =>
      (h.cut j.castSucc, Real.toNNReal (fieldHeightIncrement h.height j))) := by
  unfold fieldAllIncrements
  apply congrArg List.ofFn
  funext j
  apply Prod.ext
  · rfl
  · exact (Real.toNNReal_of_nonneg (fieldIncrement_nonneg h j)).symm

private lemma allIncrements_take_positive (h : FieldStep) (k : ℕ) (hk : 0 < k) :
    (fieldAllIncrements h).take k =
      (0, NNReal.mk (h.height 0) (h.nonneg 0)) ::
        (scalarFieldIncrements h).take (k - 1) := by
  cases k with
  | zero => omega
  | succ k => simp only [fieldAllIncrements_root, List.take_succ_cons, Nat.add_sub_cancel]

private lemma scalarIncrements_of_adjacent (h k : FieldStep) (j : Fin h.depth)
    (hj : 0 < j.val) (t : ℝ) (hroot : k.height 0 = h.height 0)
    (hall : fieldAllIncrements k =
      fieldAdjacentIncrements ((fieldAllIncrements h).take j.val)
        ((fieldAllIncrements h).drop (j.val + 2))
        (fieldIncrement h j.castSucc).2 (fieldIncrement h j.succ).2
        (fieldIncrement h j.castSucc).1 (fieldIncrement h j.succ).1 t) :
    scalarFieldIncrements k = (scalarFieldIncrements h).take (j.val - 1) ++
      ((fieldIncrement h j.castSucc).1, Real.toNNReal ((fieldIncrement h j.castSucc).2 + t)) ::
      ((fieldIncrement h j.succ).1, Real.toNNReal ((fieldIncrement h j.succ).2 - t)) ::
      (scalarFieldIncrements h).drop (j.val + 1) := by
  have ht := allIncrements_take_positive h j.val hj
  have hd : (fieldAllIncrements h).drop (j.val + 2) =
      (scalarFieldIncrements h).drop (j.val + 1) := by
    rw [fieldAllIncrements_root]
    exact List.drop_succ_cons
  rw [fieldAllIncrements_root k, ht, hd, fieldAdjacentIncrements_root] at hall
  have hr : (NNReal.mk (k.height 0) (k.nonneg 0)) =
      (NNReal.mk (h.height 0) (h.nonneg 0)) := Subtype.ext hroot
  rw [hr] at hall
  exact (List.cons.inj hall).2

lemma scalarFieldIncrements_interior_layout (h : FieldStep) (j : Fin h.depth)
    (hj : 0 < j.val) :
    scalarFieldIncrements h = (scalarFieldIncrements h).take (j.val - 1) ++
      ((fieldIncrement h j.castSucc).1, Real.toNNReal (fieldIncrement h j.castSucc).2) ::
      ((fieldIncrement h j.succ).1, Real.toNNReal (fieldIncrement h j.succ).2) ::
      (scalarFieldIncrements h).drop (j.val + 1) := by
  have he := updated_increments_interior h j 0
  simp only [add_zero, Function.update_eq_self] at he
  rw [← allIncrements_toNNReal h] at he
  simpa only [add_zero, sub_zero] using scalarIncrements_of_adjacent h h j hj 0 rfl he

lemma scalarFieldIncrements_update_interior (h : FieldStep) (j : Fin h.depth)
    (hj : 0 < j.val) (t : ℝ)
    (ht : Function.update h.height j.castSucc (h.height j.castSucc + t) ∈
      fieldStrictHeightCone h.depth) :
    scalarFieldIncrements (fieldStepOfStrictHeights h
      (Function.update h.height j.castSucc (h.height j.castSucc + t)) ht) =
      (scalarFieldIncrements h).take (j.val - 1) ++
      ((fieldIncrement h j.castSucc).1, Real.toNNReal ((fieldIncrement h j.castSucc).2 + t)) ::
      ((fieldIncrement h j.succ).1, Real.toNNReal ((fieldIncrement h j.succ).2 - t)) ::
      (scalarFieldIncrements h).drop (j.val + 1) := by
  apply scalarIncrements_of_adjacent h _ j hj t ?_
    (fieldAllIncrements_update_interior h j t ht)
  change Function.update h.height j.castSucc (h.height j.castSucc + t) 0 = h.height 0
  apply Function.update_of_ne
  intro he
  have hv := congrArg Fin.val he
  simp only [Fin.val_zero, Fin.val_castSucc] at hv
  omega

private lemma scalarIncrements_of_terminal (h k : FieldStep) (hn : 0 < h.depth)
    (t : ℝ) (hroot : k.height 0 = h.height 0)
    (hall : fieldAllIncrements k =
      fieldTerminalIncrements ((fieldAllIncrements h).take h.depth)
        (fieldIncrement h (Fin.last h.depth)).2 (fieldIncrement h (Fin.last h.depth)).1 t) :
    scalarFieldIncrements k = (scalarFieldIncrements h).take (h.depth - 1) ++
      [((fieldIncrement h (Fin.last h.depth)).1,
        Real.toNNReal ((fieldIncrement h (Fin.last h.depth)).2 + t))] := by
  rw [fieldAllIncrements_root k, allIncrements_take_positive h h.depth hn] at hall
  simp only [fieldTerminalIncrements, List.cons_append] at hall
  have hr : (NNReal.mk (k.height 0) (k.nonneg 0)) =
      (NNReal.mk (h.height 0) (h.nonneg 0)) := Subtype.ext hroot
  rw [hr] at hall
  exact (List.cons.inj hall).2

lemma scalarFieldIncrements_terminal_layout (h : FieldStep) (hn : 0 < h.depth) :
    scalarFieldIncrements h = (scalarFieldIncrements h).take (h.depth - 1) ++
      [((fieldIncrement h (Fin.last h.depth)).1,
        Real.toNNReal (fieldIncrement h (Fin.last h.depth)).2)] := by
  have he := updated_increments_final h 0
  simp only [add_zero, Function.update_eq_self] at he
  rw [← allIncrements_toNNReal h] at he
  simpa only [add_zero] using scalarIncrements_of_terminal h h hn 0 rfl he

lemma scalarFieldIncrements_update_terminal (h : FieldStep) (hn : 0 < h.depth)
    (t : ℝ) (ht : Function.update h.height (Fin.last h.depth)
      (h.height (Fin.last h.depth) + t) ∈ fieldStrictHeightCone h.depth) :
    scalarFieldIncrements (fieldStepOfStrictHeights h
      (Function.update h.height (Fin.last h.depth) (h.height (Fin.last h.depth) + t)) ht) =
      (scalarFieldIncrements h).take (h.depth - 1) ++
      [((fieldIncrement h (Fin.last h.depth)).1,
        Real.toNNReal ((fieldIncrement h (Fin.last h.depth)).2 + t))] := by
  apply scalarIncrements_of_terminal h _ hn t ?_
    (fieldAllIncrements_update_final h t ht)
  change Function.update h.height (Fin.last h.depth) (h.height (Fin.last h.depth) + t) 0 = h.height 0
  apply Function.update_of_ne
  intro he
  have hv := congrArg Fin.val he
  simp only [Fin.val_zero, Fin.val_last] at hv
  omega

end InvariantIsing

end

end OAI
