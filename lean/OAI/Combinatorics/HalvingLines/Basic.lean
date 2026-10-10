import OAI.Combinatorics.HalvingLines.Model

namespace OAI

namespace PlanarHalving

theorem critical_image_null (f : Point → Point) :
    MeasureTheory.volume (f '' {p | DifferentiableAt ℝ f p ∧
      (fderiv ℝ f p).det = 0}) = 0 := by
  apply MeasureTheory.addHaar_image_eq_zero_of_det_fderivWithin_eq_zero
    MeasureTheory.volume
  · intro p hp
    exact hp.1.hasFDerivAt.hasFDerivWithinAt
  · intro p hp
    exact hp.2

theorem orient_swap (p q r : Point) : orient q p r = -orient p q r := by
  unfold orient
  ring

@[simp] theorem orient_left (p q : Point) : orient p q p = 0 := by
  simp [orient]

@[simp] theorem orient_right (p q : Point) : orient p q q = 0 := by
  unfold orient
  ring

@[simp] theorem switchCount_zero {n : ℕ} (P : Fin n → Point) :
    switchCount P 0 = 0 := by
  simp [switchCount]

@[simp] theorem switchCount_top {n : ℕ} (P : Fin n → Point) :
    switchCount P n = 0 := by
  simp [switchCount]

theorem orient_eq_proj_diff (p q r : Point) (hx : q.1 ≠ p.1) :
    orient p q r = (q.1 - p.1) *
      ((r.2 - slope p q * r.1) - (p.2 - slope p q * p.1)) := by
  unfold orient slope
  field_simp
  ring

lemma orient_zero_iff {n : ℕ} {P : Fin n → Point} (hP : GeneralPosition P)
    {i j : Fin n} (hij : i ≠ j) (l : Fin n) :
    orient (P i) (P j) (P l) = 0 ↔ l = i ∨ l = j := by
  constructor
  · intro hl
    by_contra! hh
    exact hP.2 i j l hij hh.2.symm hh.1.symm hl
  · rintro (rfl | rfl) <;> simp

lemma sideCount_add_reverse {n : ℕ} {P : Fin n → Point} (hP : GeneralPosition P)
    {i j : Fin n} (hij : i ≠ j) : sideCount P i j + sideCount P j i = n - 2 := by
  classical
  let A := Finset.univ.filter (fun l => 0 < orient (P i) (P j) (P l))
  let B := Finset.univ.filter (fun l => 0 < orient (P j) (P i) (P l))
  have hd : Disjoint A B := by
    apply Finset.disjoint_left.mpr
    intro l hlA hlB
    have ha : 0 < orient (P i) (P j) (P l) := (Finset.mem_filter.mp hlA).2
    have hb : 0 < orient (P j) (P i) (P l) := (Finset.mem_filter.mp hlB).2
    rw [orient_swap] at hb
    linarith only [ha, hb]
  have hu : A ∪ B = (Finset.univ.erase i).erase j := by
    ext l
    simp only [A, B, Finset.mem_union, Finset.mem_filter, Finset.mem_univ,
      true_and, Finset.mem_erase]
    rw [orient_swap (P i) (P j) (P l)]
    have hz := orient_zero_iff hP hij l
    constructor
    · intro hl
      have hn : orient (P i) (P j) (P l) ≠ 0 := by
        rcases hl with hl | hl <;> linarith only [hl]
      have hn' : ¬ (l = i ∨ l = j) := fun he => hn (hz.mpr he)
      exact ⟨fun h => hn' (Or.inr h), fun h => hn' (Or.inl h), trivial⟩
    · rintro ⟨hlj, hli, _⟩
      have hn : orient (P i) (P j) (P l) ≠ 0 := by
        intro hh
        rcases hz.mp hh with hh | hh
        · exact hli hh
        · exact hlj hh
      rcases lt_or_gt_of_ne hn with hl | hl
      · right; linarith only [hl]
      · exact Or.inl hl
  change A.card + B.card = n - 2
  rw [← Finset.card_union_of_disjoint hd, hu,
    Finset.card_erase_of_mem (by simp [hij.symm]),
    Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
  omega

lemma belowCount_eq_sideCount_of_x_lt {n : ℕ} (P : Fin n → Point) (i j : Fin n)
    (hx : (P i).1 < (P j).1) : belowCount P i j = sideCount P j i := by
  classical
  unfold belowCount sideCount
  dsimp only
  apply congrArg Finset.card
  apply Finset.filter_congr
  intro l _
  rw [orient_swap, orient_eq_proj_diff _ _ _ hx.ne']
  have hx' : 0 < (P j).1 - (P i).1 := sub_pos.mpr hx
  rw [neg_pos]
  simp only [mul_neg_iff, hx', hx'.not_gt, true_and, false_and,
    or_false, sub_neg]

lemma belowCount_eq_sideCount_of_x_gt {n : ℕ} (P : Fin n → Point) (i j : Fin n)
    (hx : (P j).1 < (P i).1) : belowCount P i j = sideCount P i j := by
  classical
  unfold belowCount sideCount
  dsimp only
  apply congrArg Finset.card
  apply Finset.filter_congr
  intro l _
  rw [orient_eq_proj_diff _ _ _ hx.ne]
  have hx' : (P j).1 - (P i).1 < 0 := sub_neg.mpr hx
  simp only [mul_pos_iff, hx', hx'.not_gt, true_and, false_and,
    false_or, sub_neg]

theorem halvingCount_eq_middle_switchCount {m : ℕ} (hm : 0 < m)
    (P : Fin (2 * m) → Point) (hP : Generic P) :
    halvingCount P = switchCount P m := by
  classical
  unfold halvingCount switchCount
  congr 1
  apply Finset.filter_congr
  intro ij _
  have hm' : m < 2 * m := by omega
  simp only [hm, hm', true_and]
  by_cases hij : ij.1 < ij.2
  · simp only [hij, true_and]
    have hs := sideCount_add_reverse hP.1 hij.ne
    have hdiv : (2 * m - 2) / 2 = m - 1 := by omega
    rw [hdiv]
    rcases lt_or_gt_of_ne (hP.2.1 ij.1 ij.2 hij.ne) with hx | hx
    · rw [belowCount_eq_sideCount_of_x_lt P _ _ hx]
      omega
    · rw [belowCount_eq_sideCount_of_x_gt P _ _ hx]
      omega
  · simp only [hij, false_and]

end PlanarHalving

end OAI
