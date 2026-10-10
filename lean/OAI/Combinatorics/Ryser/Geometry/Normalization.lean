import OAI.Combinatorics.Ryser.Geometry.ProjectiveTransformAffine
import OAI.Combinatorics.Ryser.Geometry.ProjectiveTransformXY
import OAI.Combinatorics.Ryser.Geometry.ProjectiveTransformXZ

namespace OAI

namespace RyserCoveringCounterexample

variable {F : Type*} [Field F]

theorem exists_direction_of_incidence_infinity {p : ProjectivePoint F}
    (h : ProjectiveIncidence p none) : ∃ d, p = Sum.inr d := by
  cases p with
  | inl p => exact h.elim
  | inr d => exact ⟨d, rfl⟩

theorem exists_affine_of_not_incidence_infinity {p : ProjectivePoint F}
    (h : ¬ ProjectiveIncidence p none) : ∃ x, p = Sum.inl x := by
  cases p with
  | inl x => exact ⟨x, rfl⟩
  | inr d => exact (h trivial).elim

theorem exists_slope_of_incidence_infinity_of_ne_vertical {p : ProjectivePoint F}
    (h : ProjectiveIncidence p none) (hne : p ≠ Sum.inr none) :
    ∃ a, p = Sum.inr (some a) := by
  obtain ⟨d, rfl⟩ := exists_direction_of_incidence_infinity h
  cases d with
  | none => exact (hne rfl).elim
  | some a => exact ⟨a, rfl⟩

theorem exists_projectiveTransform_line_to_infinity (l : ProjectiveLine F) :
    ∃ T : ProjectiveTransform F, T.lines l = none := by
  cases l with
  | none => exact ⟨ProjectiveTransform.refl F, rfl⟩
  | some l =>
    rcases l with ⟨d, b⟩
    cases d with
    | none =>
      refine ⟨(translate (-b) 0).trans (swapXZ F), ?_⟩
      simp
    | some a =>
      refine ⟨(((shear (-a)).trans (swapXY F)).trans
        (translate (-b) 0)).trans (swapXZ F), ?_⟩
      simp only [ProjectiveTransform.trans_lines, shear_lines_slope, add_neg_cancel,
        swapXY_lines_slope_zero, translate_lines_vertical, swapXZ_lines_vertical_zero]

theorem exists_projectiveTransform_direction_to_vertical (d : Direction F) :
    ∃ T : ProjectiveTransform F,
      T.points (Sum.inr d) = Sum.inr none ∧
      T.points (Sum.inl (0, 0)) = Sum.inl (0, 0) ∧
      T.lines none = none := by
  cases d with
  | none => exact ⟨ProjectiveTransform.refl F, rfl, rfl, rfl⟩
  | some a =>
    refine ⟨(shear (-a)).trans (swapXY F), ?_, ?_, ?_⟩ <;> simp

theorem exists_projectiveTransform_direction_frame
    (d1 d2 d3 : Direction F) (h12 : d1 ≠ d2) (h13 : d1 ≠ d3)
    (h23 : d2 ≠ d3) :
    ∃ T : ProjectiveTransform F,
      T.points (Sum.inr d1) = Sum.inr (some 0) ∧
      T.points (Sum.inr d2) = Sum.inr none ∧
      T.points (Sum.inr d3) = Sum.inr (some 1) ∧
      T.points (Sum.inl (0, 0)) = Sum.inl (0, 0) := by
  obtain ⟨S, hsecond, horigin, hline⟩ :=
    exists_projectiveTransform_direction_to_vertical d2
  have hinf (d : Direction F) : ProjectiveIncidence (S.points (Sum.inr d)) none := by
    rw [← hline]
    exact (S.incidence (Sum.inr d) none).mpr trivial
  have hfirst : S.points (Sum.inr d1) ≠ Sum.inr none := by
    intro h
    exact h12 (Sum.inr.inj (S.points.injective (h.trans hsecond.symm)))
  have hthird : S.points (Sum.inr d3) ≠ Sum.inr none := by
    intro h
    exact h23 (Sum.inr.inj (S.points.injective (hsecond.trans h.symm)))
  obtain ⟨a, ha⟩ := exists_slope_of_incidence_infinity_of_ne_vertical (hinf d1) hfirst
  obtain ⟨c, hc⟩ := exists_slope_of_incidence_infinity_of_ne_vertical (hinf d3) hthird
  have hac : a ≠ c := by
    intro h
    apply h13
    apply Sum.inr.inj
    apply S.points.injective
    rw [ha, hc, h]
  have hca : c - a ≠ 0 := sub_ne_zero.mpr (Ne.symm hac)
  refine ⟨S.trans ((shear (-a)).trans (scaleY (c - a)⁻¹ (inv_ne_zero hca))),
    ?_, ?_, ?_, ?_⟩
  · simp [ha]
  · simp [hsecond]
  · simp only [ProjectiveTransform.trans_points, hc, shear_points_infinite_slope,
      scaleY_points_infinite_slope, ← sub_eq_add_neg]
    simp [hca]
  · simp [horigin]

theorem exists_projectiveTransform_normalization
    {p1 p2 p3 p4 : ProjectivePoint F} {l : ProjectiveLine F}
    (h12 : p1 ≠ p2) (h13 : p1 ≠ p3) (h23 : p2 ≠ p3)
    (h1 : ProjectiveIncidence p1 l) (h2 : ProjectiveIncidence p2 l)
    (h3 : ProjectiveIncidence p3 l) (h4 : ¬ ProjectiveIncidence p4 l) :
    ∃ T : ProjectiveTransform F,
      T.points p1 = Sum.inr (some 0) ∧
      T.points p2 = Sum.inr none ∧
      T.points p3 = Sum.inr (some 1) ∧
      T.points p4 = Sum.inl (0, 0) := by
  obtain ⟨S, hline⟩ := exists_projectiveTransform_line_to_infinity l
  have hfirst : ProjectiveIncidence (S.points p1) none := by
    rw [← hline]
    exact (S.incidence p1 l).mpr h1
  have hsecond : ProjectiveIncidence (S.points p2) none := by
    rw [← hline]
    exact (S.incidence p2 l).mpr h2
  have hthird : ProjectiveIncidence (S.points p3) none := by
    rw [← hline]
    exact (S.incidence p3 l).mpr h3
  have hfourth : ¬ ProjectiveIncidence (S.points p4) none := by
    rw [← hline]
    exact fun h => h4 ((S.incidence p4 l).mp h)
  obtain ⟨d1, hd1⟩ := exists_direction_of_incidence_infinity hfirst
  obtain ⟨d2, hd2⟩ := exists_direction_of_incidence_infinity hsecond
  obtain ⟨d3, hd3⟩ := exists_direction_of_incidence_infinity hthird
  obtain ⟨x, hx⟩ := exists_affine_of_not_incidence_infinity hfourth
  have hd12 : d1 ≠ d2 := by
    intro h
    apply h12
    apply S.points.injective
    rw [hd1, hd2, h]
  have hd13 : d1 ≠ d3 := by
    intro h
    apply h13
    apply S.points.injective
    rw [hd1, hd3, h]
  have hd23 : d2 ≠ d3 := by
    intro h
    apply h23
    apply S.points.injective
    rw [hd2, hd3, h]
  obtain ⟨U, hu1, hu2, hu3, hu4⟩ :=
    exists_projectiveTransform_direction_frame d1 d2 d3 hd12 hd13 hd23
  refine ⟨(S.trans (translate (-x.1) (-x.2))).trans U, ?_, ?_, ?_, ?_⟩
  · simpa only [ProjectiveTransform.trans_points, hd1, translate_points_infinite] using hu1
  · simpa only [ProjectiveTransform.trans_points, hd2, translate_points_infinite] using hu2
  · simpa only [ProjectiveTransform.trans_points, hd3, translate_points_infinite] using hu3
  · simpa only [ProjectiveTransform.trans_points, hx, translate_points_finite,
      add_neg_cancel] using hu4

theorem exists_projective_normalization
    {p1 p2 p3 p4 : ProjectivePoint F} {l : ProjectiveLine F}
    (h12 : p1 ≠ p2) (h13 : p1 ≠ p3) (h23 : p2 ≠ p3)
    (h1 : ProjectiveIncidence p1 l) (h2 : ProjectiveIncidence p2 l)
    (h3 : ProjectiveIncidence p3 l) (h4 : ¬ ProjectiveIncidence p4 l) :
    ∃ ep : ProjectivePoint F ≃ ProjectivePoint F,
      ∃ el : ProjectiveLine F ≃ ProjectiveLine F,
        (∀ p m, ProjectiveIncidence (ep p) (el m) ↔ ProjectiveIncidence p m) ∧
        ep p1 = Sum.inr (some 0) ∧
        ep p2 = Sum.inr none ∧
        ep p3 = Sum.inr (some 1) ∧
        ep p4 = Sum.inl (0, 0) := by
  obtain ⟨T, hT⟩ := exists_projectiveTransform_normalization h12 h13 h23 h1 h2 h3 h4
  exact ⟨T.points, T.lines, T.incidence, hT⟩

end RyserCoveringCounterexample

end OAI
