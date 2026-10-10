import OAI.Probability.InvariantIsing.Fields.FieldHeightLists
import OAI.Probability.InvariantIsing.Fields.FieldRootPrefixLaw
import OAI.Probability.InvariantIsing.Fields.FieldAdjacentScalarLaw

namespace OAI

/-! The actual interior-height magnetization as the root average of the
adjacent Gaussian variation family. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped NNReal

namespace InvariantIsing

def fieldInteriorPrefix (h : FieldStep) (j : Fin h.depth) : List (ℝ × ℝ≥0) :=
  (scalarFieldIncrements h).take (j.val - 1)

def fieldInteriorTail (h : FieldStep) (j : Fin h.depth) : List (ℝ × ℝ≥0) :=
  (scalarFieldIncrements h).drop (j.val + 1)

lemma scalarFieldIncrements_strict (h : FieldStep)
    (hstrict : ∀ i, 0 < (fieldIncrement h i).2) :
    ∀ av ∈ scalarFieldIncrements h, 0 < (av.2 : ℝ) := by
  intro av hav
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hav
  exact hstrict i.succ

lemma fieldInteriorTail_strict (h : FieldStep) (j : Fin h.depth)
    (hstrict : ∀ i, 0 < (fieldIncrement h i).2) :
    ∀ av ∈ fieldInteriorTail h j, 0 < (av.2 : ℝ) := by
  intro av hav
  exact scalarFieldIncrements_strict h hstrict av (List.mem_of_mem_drop hav)

lemma fieldAllIncrements_update_interior_root (h : FieldStep) (j : Fin h.depth)
    (hj : 0 < j.val) (t : ℝ)
    (ht : Function.update h.height j.castSucc (h.height j.castSucc + t) ∈
      fieldStrictHeightCone h.depth) :
    fieldAllIncrements (fieldStepOfStrictHeights h
      (Function.update h.height j.castSucc (h.height j.castSucc + t)) ht) =
      (0, NNReal.mk (h.height 0) (h.nonneg 0)) ::
        (fieldInteriorPrefix h j ++
          ((fieldIncrement h j.castSucc).1, Real.toNNReal ((fieldIncrement h j.castSucc).2 + t)) ::
          ((fieldIncrement h j.succ).1, Real.toNNReal ((fieldIncrement h j.succ).2 - t)) ::
          fieldInteriorTail h j) := by
  rw [fieldAllIncrements_update_interior, fieldAdjacentIncrements, fieldAllIncrements_root]
  obtain ⟨l, hl⟩ : ∃ l, j.val = l + 1 := ⟨j.val - 1, by omega⟩
  simp only [fieldInteriorPrefix, fieldInteriorTail, hl, Nat.add_sub_cancel,
    List.take_succ_cons, List.drop_succ_cons, List.cons_append]

lemma fieldInteriorPrefix_length (h : FieldStep) (j : Fin h.depth) :
    (fieldInteriorPrefix h j).length = j.val - 1 := by
  simp only [fieldInteriorPrefix, List.length_take, scalarFieldIncrements_length]
  exact Nat.min_eq_left (by omega)

theorem fieldMagnetizationLevel_interior_family (h : FieldStep)
    (hstrict : ∀ i, 0 < (fieldIncrement h i).2)
    (j : Fin h.depth) (hj : 0 < j.val) (t : ℝ)
    (ht : Function.update h.height j.castSucc (h.height j.castSucc + t) ∈
      fieldStrictHeightCone h.depth)
    (i : Fin (h.depth + 1)) (hij : i.val < j.val) :
    let S := fieldInteriorTail h j
    let G := fieldAdjacentFamily (fieldIncrement h j.castSucc).2 (fieldIncrement h j.succ).2
      (fieldIncrement h j.castSucc).1 (fieldIncrement h j.succ).1 (fieldFixedAffine S)
      (fieldFixedAffine_base S (fieldInteriorTail_strict h j hstrict)) (fieldFixedAffine_slope S)
    fieldMagnetizationLevel (fieldStepOfStrictHeights h
      (Function.update h.height j.castSucc (h.height j.castSucc + t)) ht) i =
      fieldScalarOverlaps (fieldInteriorPrefix h j) (NNReal.mk (h.height 0) (h.nonneg 0))
        (fun y => G.U (t, y)) (fun y => G.X (t, y))
        ⟨i.val, by rw [fieldInteriorPrefix_length]; omega⟩ := by
  dsimp only
  let P := fieldInteriorPrefix h j
  let S := fieldInteriorTail h j
  let a := (fieldIncrement h j.castSucc).2
  let b := (fieldIncrement h j.succ).2
  let ζ := (fieldIncrement h j.castSucc).1
  let η := (fieldIncrement h j.succ).1
  let L := fieldFixedAffine S
  let hb := fieldFixedAffine_base S (fieldInteriorTail_strict h j hstrict)
  let hs := fieldFixedAffine_slope S
  have hvalue := fieldAdjacentFamily_scalar a b ζ η L hb hs t
  have hmean := fieldAdjacentFamily_scalar_mean a b ζ η L hb hs t
  rw [fieldAdjacentAffineList_increments, fieldFixedAffine_increments] at hvalue hmean
  rw [hvalue, hmean]
  exact fieldMagnetizationLevel_root_prefix _ P
    ((ζ, Real.toNNReal (a + t)) :: (η, Real.toNNReal (b - t)) :: S)
    (NNReal.mk (h.height 0) (h.nonneg 0))
    (fieldAllIncrements_update_interior_root h j hj t ht) i
    ⟨i.val, by dsimp only [P]; rw [fieldInteriorPrefix_length]; omega⟩ rfl

end InvariantIsing

end

end OAI
