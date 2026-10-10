import OAI.MeasureTheory.Falconer.Angular.AngularFarDepth

namespace OAI

namespace PlanarFalconer
open Set

def angularLengthLeft : Set (Fin 4 → Plane) :=
  {x | 2*dist (x 2) (x 3) < dist (x 0) (x 1)}

def angularLengthRight : Set (Fin 4 → Plane) :=
  {x | 2*dist (x 0) (x 1) < dist (x 2) (x 3)}

def angularLengthComparable : Set (Fin 4 → Plane) :=
  {x | dist (x 0) (x 1) ≤ 2*dist (x 2) (x 3) ∧
    dist (x 2) (x 3) ≤ 2*dist (x 0) (x 1)}

noncomputable def angularLengthShell (b : ℕ) : Set (Fin 4 → Plane) :=
  angularLengthComparable ∩ {x |
    512*(2:ℝ)^(-(b:ℝ)) < max (dist (x 0) (x 1)) (dist (x 2) (x 3)) ∧
    max (dist (x 0) (x 1)) (dist (x 2) (x 3)) ≤ 1024*(2:ℝ)^(-(b:ℝ))}

theorem measurable_angularLengthLeft : MeasurableSet angularLengthLeft := by
  unfold angularLengthLeft
  exact measurableSet_lt (by fun_prop) (by fun_prop)

theorem measurable_angularLengthRight : MeasurableSet angularLengthRight := by
  unfold angularLengthRight
  exact measurableSet_lt (by fun_prop) (by fun_prop)

theorem measurable_angularLengthComparable : MeasurableSet angularLengthComparable := by
  change MeasurableSet ({x : Fin 4 → Plane | dist (x 0) (x 1) ≤ 2*dist (x 2) (x 3)} ∩
    {x | dist (x 2) (x 3) ≤ 2*dist (x 0) (x 1)})
  apply MeasurableSet.inter <;> exact measurableSet_le (by fun_prop) (by fun_prop)

theorem measurable_angularLengthShell (b : ℕ) : MeasurableSet (angularLengthShell b) := by
  apply measurable_angularLengthComparable.inter
  change MeasurableSet ({x : Fin 4 → Plane |
    512*(2:ℝ)^(-(b:ℝ)) < max (dist (x 0) (x 1)) (dist (x 2) (x 3))} ∩
    {x | max (dist (x 0) (x 1)) (dist (x 2) (x 3)) ≤ 1024*(2:ℝ)^(-(b:ℝ))})
  apply MeasurableSet.inter
  · exact measurableSet_lt measurable_const (by fun_prop)
  · exact measurableSet_le (by fun_prop) measurable_const

theorem angular_length_trichotomy (x : Fin 4 → Plane) :
    x ∈ angularLengthLeft ∨ x ∈ angularLengthRight ∨ x ∈ angularLengthComparable := by
  by_cases h1 : x ∈ angularLengthLeft
  · exact Or.inl h1
  by_cases h2 : x ∈ angularLengthRight
  · exact Or.inr (Or.inl h2)
  exact Or.inr (Or.inr ⟨le_of_not_gt h1,le_of_not_gt h2⟩)

theorem angular_length_left_right_disjoint : Disjoint angularLengthLeft angularLengthRight := by
  apply Set.disjoint_left.mpr
  intro x h1 h2
  change 2*dist (x 2) (x 3) < dist (x 0) (x 1) at h1
  change 2*dist (x 0) (x 1) < dist (x 2) (x 3) at h2
  linarith [dist_nonneg (x := x 0) (y := x 1)]

theorem angular_length_left_comparable_disjoint :
    Disjoint angularLengthLeft angularLengthComparable := by
  exact Set.disjoint_left.mpr (fun _ h1 h2 => not_lt_of_ge h2.1 h1)

theorem angular_length_right_comparable_disjoint :
    Disjoint angularLengthRight angularLengthComparable := by
  exact Set.disjoint_left.mpr (fun _ h1 h2 => not_lt_of_ge h2.2 h1)

theorem angularLengthShell_lengths (b : ℕ) {x : Fin 4 → Plane} (hx : x ∈ angularLengthShell b) :
    (256*(2:ℝ)^(-(b:ℝ)) < dist (x 0) (x 1) ∧
      dist (x 0) (x 1) ≤ 1024*(2:ℝ)^(-(b:ℝ))) ∧
    (256*(2:ℝ)^(-(b:ℝ)) < dist (x 2) (x 3) ∧
      dist (x 2) (x 3) ≤ 1024*(2:ℝ)^(-(b:ℝ))) := by
  have hc₁ : max (dist (x 0) (x 1)) (dist (x 2) (x 3)) ≤ 2*dist (x 0) (x 1) :=
    max_le (by linarith [dist_nonneg (x := x 0) (y := x 1)]) hx.1.2
  have hc₂ : max (dist (x 0) (x 1)) (dist (x 2) (x 3)) ≤ 2*dist (x 2) (x 3) :=
    max_le hx.1.1 (by linarith [dist_nonneg (x := x 2) (y := x 3)])
  exact ⟨⟨by linarith [hx.2.1],(le_max_left _ _).trans hx.2.2⟩,
    ⟨by linarith [hx.2.1],(le_max_right _ _).trans hx.2.2⟩⟩

theorem angularLengthShell_disjoint : Pairwise fun b c =>
    Disjoint (angularLengthShell b) (angularLengthShell c) := by
  have horder (b c : ℕ) (hbc : b < c) :
      1024*(2:ℝ)^(-(c:ℝ)) ≤ 512*(2:ℝ)^(-(b:ℝ)) := by
    have he : (10:ℝ)-(c:ℝ) ≤ 9-(b:ℝ) := by
      have hh : (b:ℝ)+1 ≤ (c:ℝ) := by exact_mod_cast hbc
      linarith
    have hh := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2) he
    rw [sub_eq_add_neg,sub_eq_add_neg,Real.rpow_add (by norm_num : (0:ℝ) < 2),
      Real.rpow_add (by norm_num : (0:ℝ) < 2)] at hh
    norm_num at hh
    simpa only [Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2),Real.rpow_natCast] using hh
  intro b c hbc
  apply Set.disjoint_left.mpr
  intro x hb hc
  rcases lt_or_gt_of_ne hbc with h | h
  · exact not_lt_of_ge (hc.2.2.trans (horder b c h)) hb.2.1
  · exact not_lt_of_ge (hb.2.2.trans (horder c b h)) hc.2.1

end PlanarFalconer

end OAI
