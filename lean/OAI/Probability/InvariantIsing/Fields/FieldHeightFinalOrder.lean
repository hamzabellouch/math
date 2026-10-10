import OAI.Probability.InvariantIsing.Fields.FieldHeightInteriorOrder

namespace OAI

/-! The final-height version of the actual mixed-coordinate order. -/

noncomputable section
open IsingPerceptron Set
open scoped NNReal

namespace InvariantIsing

def fieldFinalPrefix (h : FieldStep) : List (ℝ × ℝ≥0) :=
  (scalarFieldIncrements h).take (h.depth - 1)

lemma fieldHeight_update_final_mem (h : FieldStep)
    (hstrict : ∀ i, 0 < (fieldIncrement h i).2) (t : ℝ)
    (ht : t ∈ Ioi (-(fieldIncrement h (Fin.last h.depth)).2)) :
    Function.update h.height (Fin.last h.depth) (h.height (Fin.last h.depth) + t) ∈
      fieldStrictHeightCone h.depth := by
  classical
  intro k
  rw [fieldHeightIncrement_update]
  by_cases hk : k = Fin.last h.depth
  · subst k
    simp only [ite_true, fieldHeightIncrement_eq]
    have ht' : -(fieldIncrement h (Fin.last h.depth)).2 < t := ht
    linarith
  · have hn : k.val ≠ (Fin.last h.depth).val + 1 := by
      simp only [Fin.val_last]
      omega
    simpa only [hk, hn, ite_false, add_zero, fieldHeightIncrement_eq] using hstrict k

lemma fieldAllIncrements_update_final_root (h : FieldStep) (hn : 0 < h.depth) (t : ℝ)
    (ht : t ∈ Ioi (-(fieldIncrement h (Fin.last h.depth)).2))
    (hstrict : ∀ i, 0 < (fieldIncrement h i).2) :
    fieldAllIncrements (fieldStepOfStrictHeights h
      (Function.update h.height (Fin.last h.depth) (h.height (Fin.last h.depth) + t))
      (fieldHeight_update_final_mem h hstrict t ht)) =
      (0, NNReal.mk (h.height 0) (h.nonneg 0)) ::
        (fieldFinalPrefix h ++ [((fieldIncrement h (Fin.last h.depth)).1,
          Real.toNNReal ((fieldIncrement h (Fin.last h.depth)).2 + t))]) := by
  rw [fieldAllIncrements_update_final, fieldTerminalIncrements, fieldAllIncrements_root]
  obtain ⟨l, hl⟩ : ∃ l, h.depth = l + 1 := ⟨h.depth - 1, by omega⟩
  simp only [fieldFinalPrefix, hl, Nat.add_sub_cancel, List.take_succ_cons, List.cons_append]

lemma fieldFinalPrefix_length (h : FieldStep) :
    (fieldFinalPrefix h).length = h.depth - 1 := by
  simp only [fieldFinalPrefix, List.length_take, scalarFieldIncrements_length]
  exact Nat.min_eq_left (by omega)

lemma fieldMagnetizationLevel_final_family (h : FieldStep)
    (hstrict : ∀ i, 0 < (fieldIncrement h i).2) (hn : 0 < h.depth) (t : ℝ)
    (ht : t ∈ Ioi (-(fieldIncrement h (Fin.last h.depth)).2))
    (i : Fin (h.depth + 1)) (hi : i.val < h.depth) :
    let G := fieldTerminalFamily (fieldIncrement h (Fin.last h.depth)).2
      (fieldIncrement h (Fin.last h.depth)).1
    fieldMagnetizationLevel (fieldStepOfStrictHeights h
      (Function.update h.height (Fin.last h.depth) (h.height (Fin.last h.depth) + t))
      (fieldHeight_update_final_mem h hstrict t ht)) i =
      fieldScalarOverlaps (fieldFinalPrefix h) (NNReal.mk (h.height 0) (h.nonneg 0))
        (fun y => G.U (t, y)) (fun y => G.X (t, y))
        ⟨i.val, by rw [fieldFinalPrefix_length]; omega⟩ := by
  dsimp only
  let a := (fieldIncrement h (Fin.last h.depth)).2
  let ζ := (fieldIncrement h (Fin.last h.depth)).1
  have hvalue := fieldTerminalFamily_value_eq_operator a ζ t
  have hmean := fieldTerminalFamily_mean_eq_transition a ζ t
  rw [hvalue, hmean]
  exact fieldMagnetizationLevel_root_prefix _ (fieldFinalPrefix h)
    [(ζ, Real.toNNReal (a + t))] (NNReal.mk (h.height 0) (h.nonneg 0))
    (fieldAllIncrements_update_final_root h hn t ht hstrict) i
    ⟨i.val, by rw [fieldFinalPrefix_length]; omega⟩ rfl

theorem fieldHeight_final_earlier_antitone (h : FieldStep)
    (hstrict : ∀ i, 0 < (fieldIncrement h i).2)
    (i : Fin (h.depth + 1)) (hi : i.val < h.depth) {t s : ℝ}
    (ht : t ∈ Ioi (-(fieldIncrement h (Fin.last h.depth)).2))
    (hs : s ∈ Ioi (-(fieldIncrement h (Fin.last h.depth)).2)) (hts : t ≤ s) :
    fieldMagnetizationLevel (fieldStepOfStrictHeights h
      (Function.update h.height (Fin.last h.depth) (h.height (Fin.last h.depth) + s))
      (fieldHeight_update_final_mem h hstrict s hs)) i ≤
    fieldMagnetizationLevel (fieldStepOfStrictHeights h
      (Function.update h.height (Fin.last h.depth) (h.height (Fin.last h.depth) + t))
      (fieldHeight_update_final_mem h hstrict t ht)) i := by
  have hn : 0 < h.depth := by omega
  have hP : ∀ av ∈ fieldFinalPrefix h, 0 < av.1 := by
    intro av hav
    exact scalarFieldIncrements_positive h av (List.mem_of_mem_take hav)
  have hζ0 : 0 ≤ (fieldIncrement h (Fin.last h.depth)).1 := by
    change 0 ≤ h.cut (Fin.last h.depth).castSucc
    rw [← h.first]
    exact h.ordered_cut.monotone (Fin.zero_le _)
  have hζ1 : (fieldIncrement h (Fin.last h.depth)).1 ≤ 1 := by
    change h.cut (Fin.last h.depth).castSucc ≤ 1
    rw [← h.last]
    exact h.ordered_cut.monotone (Fin.le_last _)
  rw [fieldMagnetizationLevel_final_family h hstrict hn s hs i hi,
    fieldMagnetizationLevel_final_family h hstrict hn t ht i hi]
  exact fieldTerminal_earlier_overlaps_antitone _ _ hζ0 hζ1 (fieldFinalPrefix h) hP
    (NNReal.mk (h.height 0) (h.nonneg 0)) ht hs hts _

end InvariantIsing

end

end OAI
