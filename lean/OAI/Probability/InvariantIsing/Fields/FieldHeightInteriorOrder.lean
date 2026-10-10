import OAI.Probability.InvariantIsing.Fields.FieldHeightInteriorLaw

namespace OAI

/-! Actual mixed-height order for nonterminal coordinates. The unchanged
root has exponent zero and is integrated only after the positive prefix. -/

noncomputable section
open IsingPerceptron Set
open scoped NNReal

namespace InvariantIsing

lemma fieldHeight_update_interior_mem (h : FieldStep)
    (hstrict : ∀ i, 0 < (fieldIncrement h i).2) (j : Fin h.depth) (t : ℝ)
    (ht : t ∈ Ioo (-(fieldIncrement h j.castSucc).2) (fieldIncrement h j.succ).2) :
    Function.update h.height j.castSucc (h.height j.castSucc + t) ∈ fieldStrictHeightCone h.depth := by
  classical
  intro k
  rw [fieldHeightIncrement_update]
  by_cases hk : k = j.castSucc
  · subst k
    simp only [ite_true, fieldHeightIncrement_eq]
    linarith [ht.1]
  · by_cases hl : k.val = j.castSucc.val + 1
    · have hkj : k = j.succ := by apply Fin.ext; simpa using hl
      subst k
      simp only [hk, ite_false, Fin.val_succ, Fin.val_castSucc, ite_true,
        fieldHeightIncrement_eq]
      linarith [ht.2]
    · simpa only [hk, hl, ite_false, add_zero, fieldHeightIncrement_eq] using hstrict k

theorem fieldHeight_interior_earlier_antitone (h : FieldStep)
    (hstrict : ∀ i, 0 < (fieldIncrement h i).2)
    (j : Fin h.depth) (hj : 0 < j.val) (i : Fin (h.depth + 1)) (hij : i.val < j.val)
    {t s : ℝ}
    (ht : t ∈ Ioo (-(fieldIncrement h j.castSucc).2) (fieldIncrement h j.succ).2)
    (hs : s ∈ Ioo (-(fieldIncrement h j.castSucc).2) (fieldIncrement h j.succ).2)
    (hts : t ≤ s) :
    fieldMagnetizationLevel (fieldStepOfStrictHeights h
      (Function.update h.height j.castSucc (h.height j.castSucc + s))
      (fieldHeight_update_interior_mem h hstrict j s hs)) i ≤
    fieldMagnetizationLevel (fieldStepOfStrictHeights h
      (Function.update h.height j.castSucc (h.height j.castSucc + t))
      (fieldHeight_update_interior_mem h hstrict j t ht)) i := by
  let P := fieldInteriorPrefix h j
  let S := fieldInteriorTail h j
  let L := fieldFixedAffine S
  let hb := fieldFixedAffine_base S (fieldInteriorTail_strict h j hstrict)
  let hz := fieldFixedAffine_slope S
  have hP : ∀ av ∈ P, 0 < av.1 := by
    intro av hav
    exact scalarFieldIncrements_positive h av (List.mem_of_mem_take hav)
  have hL : ∀ av ∈ L, 0 < av.exponent := by
    intro av hav
    obtain ⟨bv, hv, rfl⟩ := List.mem_map.mp hav
    exact scalarFieldIncrements_positive h bv (List.mem_of_mem_drop hv)
  have hζ : 0 < (fieldIncrement h j.castSucc).1 := by
    change 0 < h.cut j.castSucc.castSucc
    rw [← h.first]
    exact h.ordered_cut (by change 0 < j.val; exact hj)
  have hζη : (fieldIncrement h j.castSucc).1 ≤ (fieldIncrement h j.succ).1 := by
    apply h.ordered_cut.monotone
    change j.val ≤ j.val + 1
    omega
  rw [fieldMagnetizationLevel_interior_family h hstrict j hj s _ i hij,
    fieldMagnetizationLevel_interior_family h hstrict j hj t _ i hij]
  exact fieldAdjacent_earlier_overlaps_antitone
    (fieldIncrement h j.castSucc).2 (fieldIncrement h j.succ).2
    (fieldIncrement h j.castSucc).1 (fieldIncrement h j.succ).1 L hb hz hζ hζη hL P hP
    (NNReal.mk (h.height 0) (h.nonneg 0)) ht hs hts _

end InvariantIsing

end

end OAI
