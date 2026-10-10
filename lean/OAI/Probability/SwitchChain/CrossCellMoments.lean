import OAI.Probability.SwitchChain.CrossMatrix
import OAI.Probability.SwitchChain.CrossCovariance

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem315.CrossCellMoments

attribute [local instance] Classical.propDecidable

variable {α β : Type*} [sectionFintypeα : Fintype α] [sectionFintypeβ : Fintype β]

abbrev Cell (s : ℕ) (r : α → Fin 3) (c : β → Fin 3) :=
  {z : CrossBlock.Matrix × α × β //
    CrossBlock.total z.1 = s ∧ CrossBlock.row z.1 0 = (r z.2.1).val ∧
      CrossBlock.col z.1 0 = (c z.2.2).val}

instance cellFintype (s : ℕ) (r : α → Fin 3) (c : β → Fin 3) :
    Fintype (Cell s r c) := Fintype.ofFinite _

theorem sum_cell (s : ℕ) (r : α → Fin 3) (c : β → Fin 3)
    (F : α → β → ℝ) :
    (∑ z : Cell s r c, F z.val.2.1 z.val.2.2) =
      ∑ x, ∑ y, (CrossBlock.count s (r x) (c y) : ℝ) * F x y := by
  classical
  rw [← Finset.sum_subtype
    (Finset.univ.filter (fun z : CrossBlock.Matrix × α × β =>
      CrossBlock.total z.1 = s ∧ CrossBlock.row z.1 0 = (r z.2.1).val ∧
        CrossBlock.col z.1 0 = (c z.2.2).val))
    (by intro z; simp)
    (fun z : CrossBlock.Matrix × α × β => F z.2.1 z.2.2)]
  rw [Finset.sum_filter]
  simp only [Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  rw [← Finset.sum_filter]
  simp [CrossBlock.count]

def offCenter (r : α → Fin 3) (x : α) : ℝ := if r x = 1 then 0 else 1

omit [Fintype α] in
theorem offCenter_boolean (r : α → Fin 3) (x : α) :
    offCenter r x = 0 ∨ offCenter r x = 1 := by
  unfold offCenter
  split_ifs <;> simp

theorem sum_cell_two_product (r : α → Fin 3) (c : β → Fin 3)
    (f : α → ℝ) (g : β → ℝ) :
    (∑ z : Cell 2 r c, f z.val.2.1 * g z.val.2.2) =
      CrossCovariance.jointMoment (fun _ : α => 1) (fun _ : β => 1)
        (offCenter r) (offCenter c) f g := by
  rw [sum_cell 2 r c (fun x y => f x * g y)]
  unfold CrossCovariance.jointMoment
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  rw [CrossBlock.count_two_real]
  simp only [offCenter, one_mul, mul_assoc]

theorem card_cell_two (r : α → Fin 3) (c : β → Fin 3) :
    (Fintype.card (Cell 2 r c) : ℝ) =
      CrossCovariance.mass (fun _ : α => 1) (fun _ : β => 1)
        (offCenter r) (offCenter c) := by
  simpa only [CrossCovariance.mass, one_mul, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, mul_one] using
    sum_cell_two_product r c (fun _ => 1) (fun _ => 1)

def average (s : ℕ) (r : α → Fin 3) (c : β → Fin 3)
    (F : α → β → ℝ) : ℝ :=
  (∑ z : Cell s r c, F z.val.2.1 z.val.2.2) / Fintype.card (Cell s r c)

theorem average_product_eq (r : α → Fin 3) (c : β → Fin 3)
    (f : α → ℝ) (g : β → ℝ) :
    average 2 r c (fun x y => f x * g y) =
      CrossCovariance.jointAverage (fun _ : α => 1) (fun _ : β => 1)
        (offCenter r) (offCenter c) f g := by
  unfold average CrossCovariance.jointAverage
  rw [sum_cell_two_product, card_cell_two]

theorem average_offCenter_product (r : α → Fin 3) (c : β → Fin 3) :
    average 2 r c (fun x y => offCenter r x * offCenter c y) = 0 := by
  rw [average_product_eq]
  unfold CrossCovariance.jointAverage
  rw [CrossCovariance.offCenter_jointMoment_zero _ _ _ _
    (offCenter_boolean r) (offCenter_boolean c), zero_div]

theorem sum_first_fiber (s : ℕ) (r : α → Fin 3) (c : β → Fin 3)
    (x : α) (g : β → ℝ) :
    (∑ z : Cell s r c, if z.val.2.1 = x then g z.val.2.2 else 0) =
      ∑ y, (CrossBlock.count s (r x) (c y) : ℝ) * g y := by
  classical
  rw [sum_cell s r c (fun u y => if u = x then g y else 0)]
  simp only [mul_ite, mul_zero]
  simp

def conditionalRight (s : ℕ) (r : α → Fin 3) (c : β → Fin 3)
    (x : α) (g : β → ℝ) : ℝ := by
  classical
  exact (∑ z ∈ (Finset.univ : Finset (Cell s r c)).filter
    (fun z => z.val.2.1 = x), g z.val.2.2) /
      ((Finset.univ : Finset (Cell s r c)).filter
        (fun z => z.val.2.1 = x)).card

theorem conditionalRight_eq_table (s : ℕ) (r : α → Fin 3) (c : β → Fin 3)
    (x : α) (g : β → ℝ) :
    conditionalRight s r c x g =
      (∑ y, (CrossBlock.count s (r x) (c y) : ℝ) * g y) /
        (∑ y, (CrossBlock.count s (r x) (c y) : ℝ)) := by
  classical
  unfold conditionalRight
  rw [Finset.sum_filter, sum_first_fiber]
  congr 1
  have h := sum_first_fiber s r c x (fun _ => 1)
  simpa only [Finset.sum_boole, mul_one] using h

theorem conditionalRight_two (r : α → Fin 3) (c : β → Fin 3)
    (x : α) (g : β → ℝ) :
    conditionalRight 2 r c x g =
      CrossCovariance.rightSliceAverage (fun _ : β => 1)
        (offCenter c) (offCenter r x) g := by
  rw [conditionalRight_eq_table]
  unfold CrossCovariance.rightSliceAverage
  simp only [CrossBlock.count_two_real, offCenter, one_mul]

theorem conditionalRight_two_span (r : α → Fin 3) (c : β → Fin 3)
    (g : β → ℝ) :
    ∃ A B : ℝ, ∀ x, conditionalRight 2 r c x g = A + B * offCenter r x := by
  refine ⟨CrossCovariance.rightSliceAverage (fun _ : β => 1) (offCenter c) 0 g,
    CrossCovariance.rightSliceAverage (fun _ : β => 1) (offCenter c) 1 g -
      CrossCovariance.rightSliceAverage (fun _ : β => 1) (offCenter c) 0 g, ?_⟩
  intro x
  rw [conditionalRight_two]
  exact CrossCovariance.rightSliceAverage_span _ _ _ (offCenter_boolean r) g x

theorem covariance_rank_one (r : α → Fin 3) (c : β → Fin 3)
    (f : α → ℝ) (g : β → ℝ) :
    average 2 r c (fun x y => f x * g y) -
        average 2 r c (fun x _ => f x) * average 2 r c (fun _ y => g y) =
      - ((Fintype.card α : ℝ) * (∑ x, offCenter r x * f x) -
          (∑ x, offCenter r x) * (∑ x, f x)) *
        ((Fintype.card β : ℝ) * (∑ y, offCenter c y * g y) -
          (∑ y, offCenter c y) * (∑ y, g y)) /
        (Fintype.card (Cell 2 r c) : ℝ) ^ 2 := by
  have hleft := average_product_eq r c f (fun _ => 1)
  have hright := average_product_eq r c (fun _ => 1) g
  simp only [mul_one] at hleft
  simp only [one_mul] at hright
  rw [average_product_eq, hleft, hright, card_cell_two]
  simpa only [one_mul, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] using
    CrossCovariance.covariance_rank_one (fun _ : α => 1) (fun _ : β => 1)
      (offCenter r) (offCenter c) f g

theorem sum_second_fiber (s : ℕ) (r : α → Fin 3) (c : β → Fin 3)
    (y : β) (f : α → ℝ) :
    (∑ z : Cell s r c, if z.val.2.2 = y then f z.val.2.1 else 0) =
      ∑ x, (CrossBlock.count s (r x) (c y) : ℝ) * f x := by
  classical
  rw [sum_cell s r c (fun x v => if v = y then f x else 0)]
  simp only [mul_ite, mul_zero]
  simp

def conditionalLeft (s : ℕ) (r : α → Fin 3) (c : β → Fin 3)
    (y : β) (f : α → ℝ) : ℝ := by
  classical
  exact (∑ z ∈ (Finset.univ : Finset (Cell s r c)).filter
    (fun z => z.val.2.2 = y), f z.val.2.1) /
      ((Finset.univ : Finset (Cell s r c)).filter
        (fun z => z.val.2.2 = y)).card

theorem conditionalLeft_eq_table (s : ℕ) (r : α → Fin 3) (c : β → Fin 3)
    (y : β) (f : α → ℝ) :
    conditionalLeft s r c y f =
      (∑ x, (CrossBlock.count s (r x) (c y) : ℝ) * f x) /
        (∑ x, (CrossBlock.count s (r x) (c y) : ℝ)) := by
  classical
  unfold conditionalLeft
  rw [Finset.sum_filter, sum_second_fiber]
  congr 1
  have h := sum_second_fiber s r c y (fun _ => 1)
  simpa only [Finset.sum_boole, mul_one] using h

theorem conditionalLeft_two (r : α → Fin 3) (c : β → Fin 3)
    (y : β) (f : α → ℝ) :
    conditionalLeft 2 r c y f =
      CrossCovariance.rightSliceAverage (fun _ : α => 1)
        (offCenter r) (offCenter c y) f := by
  rw [conditionalLeft_eq_table]
  unfold CrossCovariance.rightSliceAverage
  congr 1
  · apply Finset.sum_congr rfl
    intro x _
    rw [CrossBlock.count_two_real]
    simp only [offCenter, one_mul]
    ring
  · apply Finset.sum_congr rfl
    intro x _
    rw [CrossBlock.count_two_real]
    simp only [offCenter, one_mul]
    ring

theorem conditionalLeft_two_span (r : α → Fin 3) (c : β → Fin 3)
    (f : α → ℝ) :
    ∃ A B : ℝ, ∀ y, conditionalLeft 2 r c y f = A + B * offCenter c y := by
  refine ⟨CrossCovariance.rightSliceAverage (fun _ : α => 1) (offCenter r) 0 f,
    CrossCovariance.rightSliceAverage (fun _ : α => 1) (offCenter r) 1 f -
      CrossCovariance.rightSliceAverage (fun _ : α => 1) (offCenter r) 0 f, ?_⟩
  intro y
  rw [conditionalLeft_two]
  exact CrossCovariance.rightSliceAverage_span _ _ _ (offCenter_boolean c) f y

include sectionFintypeα sectionFintypeβ in
theorem offCenter_disjoint (r : α → Fin 3) (c : β → Fin 3)
    (z : Cell 2 r c) (hr : r z.val.2.1 ≠ 1) : c z.val.2.2 = 1 := by
  have retainedsectionFintypeα := sectionFintypeα
  have retainedsectionFintypeβ := sectionFintypeβ
  apply Fin.ext
  have hrow : CrossBlock.row z.val.1 0 ≠ 1 := by
    intro h
    apply hr
    apply Fin.ext
    exact z.property.2.1.symm.trans h
  exact z.property.2.2.symm.trans
    (CrossBlock.off_center_disjoint z.val.1 z.property.1 hrow)

theorem offCenter_disjoint_symm (r : α → Fin 3) (c : β → Fin 3)
    (z : Cell 2 r c) (hc : c z.val.2.2 ≠ 1) : r z.val.2.1 = 1 := by
  by_contra hr
  exact hc (offCenter_disjoint r c z hr)

theorem exists_center_of_both_offCenter (r : α → Fin 3) (c : β → Fin 3)
    (hrow : ∃ z : Cell 2 r c, r z.val.2.1 ≠ 1)
    (hcol : ∃ z : Cell 2 r c, c z.val.2.2 ≠ 1) :
    ∃ z : Cell 2 r c, r z.val.2.1 = 1 ∧ c z.val.2.2 = 1 := by
  obtain ⟨u, hu⟩ := hrow
  obtain ⟨v, hv⟩ := hcol
  have hr := offCenter_disjoint_symm r c v hv
  have hc := offCenter_disjoint r c u hu
  let M : CrossBlock.Matrix := fun i j => decide (i = j)
  have hM : CrossBlock.total M = 2 ∧ CrossBlock.row M 0 = 1 ∧
      CrossBlock.col M 0 = 1 := by decide
  refine ⟨⟨(M, v.val.2.1, u.val.2.2), hM.1, ?_, ?_⟩, hr, hc⟩
  · simpa only [hr, Fin.val_one] using hM.2.1
  · simpa only [hc, Fin.val_one] using hM.2.2

end Problem315.CrossCellMoments

end

end OAI
