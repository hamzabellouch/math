import OAI.Analysis.MassAction.SmallParameter

namespace OAI

universe uIota

/-! Geometry of the reciprocal box used by the affine certificate. -/

namespace Problem326

open Set

/-- The interior of a finite coordinate box is obtained by making every
coordinate inequality strict. -/
theorem mem_interior_coordinate_box_iff
    {ι : Type uIota} [Finite ι] {a b x : ι → ℝ} :
    x ∈ interior (Icc a b) ↔ ∀ i, a i < x i ∧ x i < b i := by
  rw [← pi_univ_Icc, interior_pi_set (Set.toFinite Set.univ)]
  simp only [interior_Icc, mem_pi, mem_univ, mem_Ioo, forall_true_left]

/-- A positive state has every logarithmic exponent strictly between -1
and 1 exactly when it belongs to the interior of the reciprocal box. -/
theorem mem_interior_reciprocal_box_iff
    {ι : Type uIota} [Finite ι] {x : ι → ℝ} {h : ℝ}
    (hh : 0 < h) (hh1 : h < 1) (hx : ∀ i, 0 < x i) :
    x ∈ interior (Icc (fun _ => h) (fun _ => h⁻¹)) ↔
      ∀ i, |Real.log (x i) / Real.log h| < 1 := by
  rw [mem_interior_coordinate_box_iff]
  exact forall_congr' fun i => (abs_log_coordinate_lt_one_iff hh hh1 (hx i)).symm

/-- Closed reciprocal boxes in finitely many real coordinates are compact. -/
theorem isCompact_reciprocal_box {ι : Type uIota} [Finite ι] (h : ℝ) :
    IsCompact (Icc (fun _ : ι => h) (fun _ => h⁻¹)) := by
  rw [← pi_univ_Icc]
  exact isCompact_univ_pi fun _ => isCompact_Icc

/-- Every point in a positive reciprocal box is positive, and its unique
logarithmic exponents lie in the closed unit cube. -/
theorem reciprocal_box_log_coordinates
    {ι : Type uIota} {x : ι → ℝ} {h : ℝ} (hh : 0 < h) (hh1 : h < 1)
    (hx : x ∈ Icc (fun _ => h) (fun _ => h⁻¹)) :
    (∀ i, 0 < x i) ∧
      (∀ i, |Real.log (x i) / Real.log h| ≤ 1) ∧
      (∀ i, h ^ (Real.log (x i) / Real.log h) = x i) := by
  have hpositive : ∀ i, 0 < x i := fun i => hh.trans_le (hx.1 i)
  exact ⟨hpositive,
    fun i => (abs_log_coordinate_le_one_iff hh hh1 (hpositive i)).mpr
      ⟨hx.1 i, hx.2 i⟩,
    fun i => rpow_log_coordinate hh hh1 (hpositive i)⟩

/-- A boundary point of the reciprocal box has a logarithmic coordinate
of absolute value one.  This is the boundary obstruction used to exclude
an active zero-slope label. -/
theorem reciprocal_box_frontier_coordinate
    {ι : Type uIota} [Finite ι] {x : ι → ℝ} {h : ℝ}
    (hh : 0 < h) (hh1 : h < 1)
    (hx : x ∈ frontier (Icc (fun _ => h) (fun _ => h⁻¹))) :
    ∃ i, |Real.log (x i) / Real.log h| = 1 := by
  have hxbox : x ∈ Icc (fun _ => h) (fun _ => h⁻¹) :=
    isClosed_Icc.frontier_subset hx
  obtain ⟨hpositive, hunit, -⟩ := reciprocal_box_log_coordinates hh hh1 hxbox
  have hnot : ¬ ∀ i, |Real.log (x i) / Real.log h| < 1 := by
    intro hall
    exact hx.2 ((mem_interior_reciprocal_box_iff hh hh1 hpositive).mpr hall)
  push Not at hnot
  obtain ⟨i, hi⟩ := hnot
  exact ⟨i, le_antisymm (hunit i) hi⟩

end Problem326

end OAI
