import OAI.Probability.InvariantIsing.Fields.FieldMagnetization

namespace OAI

/-! Plateau consistency of the actual scalar-field magnetization path. -/

noncomputable section
open Set

namespace InvariantIsing

private lemma finite_level_fiber {n : ℕ} (f q : Fin (n + 1) → ℝ)
    (hf : Monotone f)
    (hq : ∀ k : Fin n, f k.castSucc = f k.succ → q k.castSucc = q k.succ)
    (i j : Fin (n + 1)) (he : f i = f j) : q i = q j := by
  have hord : ∀ j i : Fin (n + 1), i ≤ j → f i = f j → q i = q j := by
    intro j
    induction j using Fin.induction with
    | zero =>
      intro i hi _
      have hi0 : i = 0 := le_antisymm hi (Fin.zero_le i)
      subst i
      rfl
    | succ j ih =>
      intro i hij he
      by_cases hi : i = j.succ
      · rw [hi]
      have hij' : i ≤ j.castSucc := by
        change i.val ≤ j.val
        have hil : i.val ≤ j.val + 1 := hij
        have hne : i.val ≠ j.val + 1 := by
          intro hv
          apply hi
          exact Fin.ext hv
        omega
      have hleft := hf hij'
      have hright := hf (show j.castSucc ≤ j.succ by exact Nat.le_succ j.val)
      have he' : f i = f j.castSucc := by linarith
      have hs : f j.castSucc = f j.succ := by linarith
      exact (ih i hij' he').trans (hq j hs)
  rcases le_total i j with hij | hji
  · exact hord j i hij he
  · exact (hord i j hji he.symm).symm

lemma fieldMagnetizationLevel_eq_of_height_eq (h : FieldStep)
    (i j : Fin (h.depth + 1)) (he : h.height i = h.height j) :
    fieldMagnetizationLevel h i = fieldMagnetizationLevel h j :=
  finite_level_fiber h.height (fieldMagnetizationLevel h) h.ordered_height
    (fieldMagnetizationLevel_tied h) i j he

lemma fieldMagnetizationPath_eq_of_cell_height_eq (h : FieldStep)
    (i j : Fin (h.depth + 1)) {s t : ℝ}
    (hs : s ∈ Ioo (h.cut i.castSucc) (h.cut i.succ))
    (ht : t ∈ Ioo (h.cut j.castSucc) (h.cut j.succ))
    (he : h.height i = h.height j) :
    fieldMagnetizationPath h s = fieldMagnetizationPath h t := by
  rw [fieldMagnetizationPath_on_cell h i hs, fieldMagnetizationPath_on_cell h j ht]
  exact fieldMagnetizationLevel_eq_of_height_eq h i j he

end InvariantIsing

end

end OAI
