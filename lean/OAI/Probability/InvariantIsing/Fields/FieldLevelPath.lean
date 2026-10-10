import OAI.Probability.InvariantIsing.Fields.Field

namespace OAI

/-! The bounded monotone representative on the field partition. Endpoint
values are immaterial to integration; the representative is defined globally. -/

noncomputable section
open MeasureTheory Set

namespace InvariantIsing

/-- Last covariance interval whose lower endpoint has been passed. -/
def fieldLevelIndex (h : FieldStep) (s : ℝ) : Fin (h.depth + 1) :=
  Finset.univ.sup (fun i => if h.cut i.castSucc ≤ s then i else 0)

lemma fieldLevelIndex_monotone (h : FieldStep) : Monotone (fieldLevelIndex h) := by
  intro s t hst
  apply Finset.sup_le
  intro i hi
  by_cases hs : h.cut i.castSucc ≤ s
  · have ht : h.cut i.castSucc ≤ t := hs.trans hst
    have hb := Finset.le_sup (f := fun j : Fin (h.depth + 1) =>
      if h.cut j.castSucc ≤ t then j else 0) hi
    simpa only [fieldLevelIndex, hs, ht, ite_true] using hb
  · simp only [hs, ite_false]
    exact bot_le

lemma fieldLevelIndex_on_cell (h : FieldStep) (i : Fin (h.depth + 1))
    {s : ℝ} (hs : s ∈ Ioo (h.cut i.castSucc) (h.cut i.succ)) :
    fieldLevelIndex h s = i := by
  apply le_antisymm
  · apply Finset.sup_le
    intro j _hj
    by_cases hj : h.cut j.castSucc ≤ s
    · simp only [hj, ite_true]
      by_contra hji
      have hij : i.succ ≤ j.castSucc := by
        change i.val + 1 ≤ j.val
        have : i < j := lt_of_not_ge hji
        exact this
      have hc := h.ordered_cut.monotone hij
      linarith [hs.2]
    · simp only [hj, ite_false]
      exact bot_le
  · have hi := Finset.le_sup (s := Finset.univ)
      (f := fun j : Fin (h.depth + 1) => if h.cut j.castSucc ≤ s then j else 0)
      (Finset.mem_univ i)
    simpa only [fieldLevelIndex, hs.1.le, ite_true] using hi

/-- Monotone unit level values become an admissible overlap path on the
same partition as the actual field. -/
def fieldLevelPath (h : FieldStep) (q : Fin (h.depth + 1) → ℝ)
    (hq : Monotone q) (hunit : ∀ i, q i ∈ Icc (0 : ℝ) 1) : OverlapPath where
  val := fun s => q (fieldLevelIndex h s)
  monotone := hq.comp (fieldLevelIndex_monotone h)
  nonneg := fun _ => (hunit _).1
  le_one := fun _ => (hunit _).2

lemma fieldLevelPath_on_cell (h : FieldStep) (q : Fin (h.depth + 1) → ℝ)
    (hq : Monotone q) (hunit : ∀ i, q i ∈ Icc (0 : ℝ) 1)
    (i : Fin (h.depth + 1)) {s : ℝ}
    (hs : s ∈ Ioo (h.cut i.castSucc) (h.cut i.succ)) :
    fieldLevelPath h q hq hunit s = q i := by
  change q (fieldLevelIndex h s) = q i
  rw [fieldLevelIndex_on_cell h i hs]

end InvariantIsing

end

end OAI
