import OAI.Probability.InvariantIsing.Fields.FieldZeroIncrement
import OAI.Probability.InvariantIsing.Fields.FieldHeightChart
import Mathlib.Order.Fin.InsertNth

namespace OAI

/-! Splitting one interval of a finite field without changing its height. -/

noncomputable section
open IsingPerceptron Set
open scoped NNReal

namespace InvariantIsing

lemma field_ofFn_insertNth {α : Type*} {n : ℕ} (i : Fin (n + 1))
    (a : α) (f : Fin n → α) :
    List.ofFn (Fin.insertNth i a f) =
      (List.ofFn f).take i.val ++ a :: (List.ofFn f).drop i.val := by
  induction n with
  | zero =>
    have hi : i = 0 := Fin.eq_zero i
    subst i
    simp
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · simp
    · have hf : f = Fin.cons (f 0) (Fin.tail f) := (Fin.cons_self_tail f).symm
      rw [hf, Fin.insertNth_succ_cons]
      simp only [List.ofFn_cons, Fin.val_succ, List.take_succ_cons,
        List.drop_succ_cons, ih, List.cons_append]

/-- Duplicate the old height on both sides of the new cut. -/
def fieldSplitHeight (h : FieldStep) (i : Fin (h.depth + 1))
    (j : Fin (h.depth + 2)) : ℝ :=
  if hj : j.val ≤ i.val then h.height ⟨j.val, by omega⟩
  else h.height ⟨j.val - 1, by omega⟩

lemma fieldSplitHeight_nonneg (h : FieldStep) (i : Fin (h.depth + 1))
    (j : Fin (h.depth + 2)) : 0 ≤ fieldSplitHeight h i j := by
  unfold fieldSplitHeight
  split_ifs <;> exact h.nonneg _

lemma fieldSplitHeight_monotone (h : FieldStep) (i : Fin (h.depth + 1)) :
    Monotone (fieldSplitHeight h i) := by
  intro j k hjk
  unfold fieldSplitHeight
  split_ifs <;> apply h.ordered_height <;> simp only [Fin.mk_le_mk] <;> omega

/-- Inserting a cut strictly inside one existing cell keeps the field path unchanged. -/
def fieldInsertCut (h : FieldStep) (i : Fin (h.depth + 1)) (c : ℝ)
    (hc₀ : h.cut i.castSucc < c) (hc₁ : c < h.cut i.succ) : FieldStep where
  depth := h.depth + 1
  cut := Fin.insertNth i.castSucc.succ c h.cut
  ordered_cut := Fin.strictMono_insertNth h.ordered_cut i c hc₀ hc₁
  first := by
    rw [Fin.insertNth_apply_below (α := fun _ => ℝ) (show (0 : Fin (h.depth + 3)) < i.castSucc.succ by
      change 0 < i.val + 1; omega)]
    exact h.first
  last := by
    rw [Fin.insertNth_apply_above (α := fun _ => ℝ)
      (show i.castSucc.succ < Fin.last (h.depth + 2) by
        change i.val + 1 < h.depth + 2; omega)]
    simpa only [eq_rec_constant, Fin.pred_last] using h.last
  height := fieldSplitHeight h i
  nonneg := fieldSplitHeight_nonneg h i
  ordered_height := fieldSplitHeight_monotone h i

lemma fieldInsertCut_depth (h : FieldStep) (i : Fin (h.depth + 1)) (c : ℝ)
    (hc₀ : h.cut i.castSucc < c) (hc₁ : c < h.cut i.succ) :
    (fieldInsertCut h i c hc₀ hc₁).depth = h.depth + 1 := rfl

lemma fieldInsertCut_last_height (h : FieldStep) (i : Fin (h.depth + 1)) (c : ℝ)
    (hc₀ : h.cut i.castSucc < c) (hc₁ : c < h.cut i.succ) :
    (fieldInsertCut h i c hc₀ hc₁).height (Fin.last (h.depth + 1)) =
      h.height (Fin.last h.depth) := by
  change fieldSplitHeight h i (Fin.last (h.depth + 1)) = _
  simp only [fieldSplitHeight, Fin.val_last]
  rw [dite_eq_right (show ¬h.depth + 1 ≤ i.val by omega)]
  rfl

lemma fieldInsertCut_cut_below (h : FieldStep) (i : Fin (h.depth + 1)) (c : ℝ)
    (hc₀ : h.cut i.castSucc < c) (hc₁ : c < h.cut i.succ)
    (j : Fin (h.depth + 3)) (hj : j.val ≤ i.val) :
    (fieldInsertCut h i c hc₀ hc₁).cut j = h.cut ⟨j.val, by omega⟩ := by
  change Fin.insertNth (α := fun _ => ℝ) i.castSucc.succ c h.cut j = _
  rw [Fin.insertNth_apply_below (α := fun _ => ℝ) (show j < i.castSucc.succ by
    change j.val < i.val + 1; omega)]
  simp only [eq_rec_constant]
  rfl

lemma fieldInsertCut_cut_at (h : FieldStep) (i : Fin (h.depth + 1)) (c : ℝ)
    (hc₀ : h.cut i.castSucc < c) (hc₁ : c < h.cut i.succ) :
    (fieldInsertCut h i c hc₀ hc₁).cut i.castSucc.succ = c := by
  change Fin.insertNth (α := fun _ => ℝ) i.castSucc.succ c h.cut i.castSucc.succ = c
  exact Fin.insertNth_apply_same _ _ _

lemma fieldInsertCut_cut_above (h : FieldStep) (i : Fin (h.depth + 1)) (c : ℝ)
    (hc₀ : h.cut i.castSucc < c) (hc₁ : c < h.cut i.succ)
    (j : Fin (h.depth + 3)) (hj : i.val + 1 < j.val) :
    (fieldInsertCut h i c hc₀ hc₁).cut j = h.cut ⟨j.val - 1, by omega⟩ := by
  change Fin.insertNth (α := fun _ => ℝ) i.castSucc.succ c h.cut j = _
  rw [Fin.insertNth_apply_above (α := fun _ => ℝ) (show i.castSucc.succ < j by exact hj)]
  simp only [eq_rec_constant]
  rfl

lemma fieldInsertCut_height_below (h : FieldStep) (i : Fin (h.depth + 1)) (c : ℝ)
    (hc₀ : h.cut i.castSucc < c) (hc₁ : c < h.cut i.succ)
    (j : Fin (h.depth + 2)) (hj : j.val ≤ i.val) :
    (fieldInsertCut h i c hc₀ hc₁).height j = h.height ⟨j.val, by omega⟩ := by
  exact dite_eq_left hj

lemma fieldInsertCut_height_above (h : FieldStep) (i : Fin (h.depth + 1)) (c : ℝ)
    (hc₀ : h.cut i.castSucc < c) (hc₁ : c < h.cut i.succ)
    (j : Fin (h.depth + 2)) (hj : i.val < j.val) :
    (fieldInsertCut h i c hc₀ hc₁).height j = h.height ⟨j.val - 1, by omega⟩ := by
  exact dite_eq_right (by omega)

end InvariantIsing

end

end OAI
