import OAI.LinearAlgebra.MatrixMultiplication.Completion.ProductLaws
import OAI.LinearAlgebra.MatrixMultiplication.Completion.Conditioning
import OAI.LinearAlgebra.MatrixMultiplication.Completion.Labels

namespace OAI

/-! Readable tensor completion and its finite arithmetic realization. -/

noncomputable section

universe uCoord

namespace MatrixMultiplication.CompletionColorLaws

open MatrixMultiplication.Foundation RecursiveCompletion CompletionLabels
open CompletionLaws CompletionProductLaws
open scoped BigOperators
attribute [local instance 10000] Classical.propDecidable Classical.decEq
attribute [local instance 11000] instDecidableEqFin

variable {X Y Z : Type uCoord} [Fintype X] [Fintype Y] [Fintype Z]

abbrev ColorSlice (S : FlaggedTensor X Y Z) (c : Color) :=
  {a : Leaf S // leafColor S a = c}

def colorMix (S : FlaggedTensor X Y Z) (center output : Color)
    (pc : FiniteLaw (ColorSlice S center)) (po : FiniteLaw (ColorSlice S output))
    (α : ℝ) (hα : 0 ≤ α) (hα' : α ≤ 1) : FiniteLaw (Leaf S) where
  mass a := α * (pc.map Subtype.val).mass a + (1 - α) * (po.map Subtype.val).mass a
  nonneg a := add_nonneg (mul_nonneg hα ((pc.map Subtype.val).nonneg a))
    (mul_nonneg (sub_nonneg.mpr hα') ((po.map Subtype.val).nonneg a))
  total := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      (pc.map Subtype.val).total, (po.map Subtype.val).total]
    ring

theorem colorMix_mass (S : FlaggedTensor X Y Z) (center output : Color)
    (pc : FiniteLaw (ColorSlice S center)) (po : FiniteLaw (ColorSlice S output))
    (α : ℝ) (hα : 0 ≤ α) (hα' : α ≤ 1) (a : Leaf S) :
    (colorMix S center output pc po α hα hα').mass a =
      α * (pc.map Subtype.val).mass a + (1 - α) * (po.map Subtype.val).mass a := rfl

theorem colorMix_map_mass {B : Type*} [Fintype B]
    (S : FlaggedTensor X Y Z) (center output : Color)
    (pc : FiniteLaw (ColorSlice S center)) (po : FiniteLaw (ColorSlice S output))
    (α : ℝ) (hα : 0 ≤ α) (hα' : α ≤ 1) (f : Leaf S → B) (b : B) :
    ((colorMix S center output pc po α hα hα').map f).mass b =
      α * ((pc.map Subtype.val).map f).mass b +
        (1 - α) * ((po.map Subtype.val).map f).mass b := by
  rw [FiniteLaw.map_mass]
  simp only [colorMix_mass]
  calc
    _ = ∑ a, (α * (if f a = b then (pc.map Subtype.val).mass a else 0) +
        (1 - α) * (if f a = b then (po.map Subtype.val).mass a else 0)) := by
      apply Finset.sum_congr rfl
      intro a _
      split_ifs <;> simp
    _ = _ := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
        FiniteLaw.map_mass (pc.map Subtype.val) f b,
        FiniteLaw.map_mass (po.map Subtype.val) f b]

theorem colorSlice_map_mass_zero (S : FlaggedTensor X Y Z) (c : Color)
    (p : FiniteLaw (ColorSlice S c)) (a : Leaf S) (ha : leafColor S a ≠ c) :
    (p.map Subtype.val).mass a = 0 := by
  rw [FiniteLaw.map_mass]
  apply Finset.sum_eq_zero
  intro b _
  apply ite_eq_right
  intro hb
  exact ha ((congrArg (leafColor S) hb).symm.trans b.property)

theorem colorMix_mass_zero (S : FlaggedTensor X Y Z) (center output : Color)
    (pc : FiniteLaw (ColorSlice S center)) (po : FiniteLaw (ColorSlice S output))
    (α : ℝ) (hα : 0 ≤ α) (hα' : α ≤ 1) (a : Leaf S)
    (hc : leafColor S a ≠ center) (ho : leafColor S a ≠ output) :
    (colorMix S center output pc po α hα hα').mass a = 0 := by
  rw [colorMix_mass, colorSlice_map_mass_zero S center pc a hc,
    colorSlice_map_mass_zero S output po a ho]
  ring

theorem colorMix_center_mass (S : FlaggedTensor X Y Z) (center output : Color)
    (hne : center ≠ output)
    (pc : FiniteLaw (ColorSlice S center)) (po : FiniteLaw (ColorSlice S output))
    (α : ℝ) (hα : 0 ≤ α) (hα' : α ≤ 1) (a : ColorSlice S center) :
    (colorMix S center output pc po α hα hα').mass a.val = α * pc.mass a := by
  rw [colorMix_mass, pc.map_mass_apply Subtype.val Subtype.val_injective,
    colorSlice_map_mass_zero S output po a.val (by simpa only [a.property] using hne)]
  ring

theorem colorMix_output_mass (S : FlaggedTensor X Y Z) (center output : Color)
    (hne : center ≠ output)
    (pc : FiniteLaw (ColorSlice S center)) (po : FiniteLaw (ColorSlice S output))
    (α : ℝ) (hα : 0 ≤ α) (hα' : α ≤ 1) (a : ColorSlice S output) :
    (colorMix S center output pc po α hα hα').mass a.val = (1 - α) * po.mass a := by
  rw [colorMix_mass, po.map_mass_apply Subtype.val Subtype.val_injective,
    colorSlice_map_mass_zero S center pc a.val (by simpa only [a.property] using hne.symm)]
  ring

theorem exists_mass_pos {A : Type*} [Fintype A] (p : FiniteLaw A) :
    ∃ a, 0 < p.mass a := by
  by_contra h
  have hz : ∀ a, p.mass a = 0 := by
    intro a
    exact le_antisymm (le_of_not_gt (fun ha => h ⟨a, ha⟩)) (p.nonneg a)
  have ht := p.total
  simp only [hz, Finset.sum_const_zero] at ht
  exact zero_ne_one ht

theorem colorMix_output_mass_pos (S : FlaggedTensor X Y Z) (center output : Color)
    (pc : FiniteLaw (ColorSlice S center)) (po : FiniteLaw (ColorSlice S output))
    (α : ℝ) (hα : 0 ≤ α) (hα' : α < 1) (a : ColorSlice S output)
    (ha : 0 < po.mass a) :
    0 < (colorMix S center output pc po α hα hα'.le).mass a.val := by
  rw [colorMix_mass, po.map_mass_apply Subtype.val Subtype.val_injective]
  exact add_pos_of_nonneg_of_pos
    (mul_nonneg hα ((pc.map Subtype.val).nonneg a.val))
    (mul_pos (sub_pos.mpr hα') ha)

abbrev completionEvent (S : FlaggedTensor X Y Z) (center output : Color) (m : ℕ)
    (w : Fin m → Leaf S) : Prop :=
  raisedFlag center output (fun i => leafColor S (w i) = output) ∧
    ∀ i, leafColor S (w i) = center ∨ leafColor S (w i) = output

omit [Fintype X] [Fintype Y] [Fintype Z] in
theorem completionEvent_constant (S : FlaggedTensor X Y Z) (center output : Color)
    (m : ℕ) (hm : 0 < m) (a : ColorSlice S output) :
    completionEvent S center output m (fun _ => a.val) := by
  constructor
  · by_cases h : center = output
    · simp [raisedFlag, h, a.property]
    · simpa only [raisedFlag, ite_eq_right h] using
        (show ∃ _i : Fin m, leafColor S a.val = output from ⟨⟨0, hm⟩, a.property⟩)
  · exact fun _ => Or.inr a.property

def iidColorLaw (S : FlaggedTensor X Y Z) (center output : Color)
    (pc : FiniteLaw (ColorSlice S center)) (po : FiniteLaw (ColorSlice S output))
    (m : ℕ) (α : ℝ) (hα : 0 ≤ α) (hα' : α ≤ 1) :
    FiniteLaw (Fin m → Leaf S) :=
  independentProduct (I := Fin m) (A := fun _ => Leaf S)
    (fun _ : Fin m => colorMix S center output pc po α hα hα')

theorem completionEvent_mass_pos (S : FlaggedTensor X Y Z) (center output : Color)
    (pc : FiniteLaw (ColorSlice S center)) (po : FiniteLaw (ColorSlice S output))
    (m : ℕ) (hm : 0 < m) (α : ℝ) (hα : 0 ≤ α) (hα' : α < 1) :
    0 < eventMass (iidColorLaw S center output pc po m α hα hα'.le)
      (completionEvent S center output m) := by
  obtain ⟨a, ha⟩ := exists_mass_pos po
  let w : {w : Fin m → Leaf S // completionEvent S center output m w} :=
    ⟨fun _ => a.val, completionEvent_constant S center output m hm a⟩
  have hw : 0 < (iidColorLaw S center output pc po m α hα hα'.le).mass w.val := by
    change 0 < ∏ _i : Fin m, (colorMix S center output pc po α hα hα'.le).mass a.val
    exact Finset.prod_pos fun _ _ => colorMix_output_mass_pos S center output pc po α hα hα' a ha
  exact lt_of_lt_of_le hw (Finset.single_le_sum
    (fun v _ => (iidColorLaw S center output pc po m α hα hα'.le).nonneg v.val)
    (Finset.mem_univ w))

def conditionalCompletionLaw (S : FlaggedTensor X Y Z) (center output : Color)
    (pc : FiniteLaw (ColorSlice S center)) (po : FiniteLaw (ColorSlice S output))
    (m : ℕ) (hm : 0 < m) (α : ℝ) (hα : 0 ≤ α) (hα' : α < 1) :
    FiniteLaw (ColorSlice (complete S center m) output) :=
  transport (conditionalLeafEquiv S center output m).symm
    (condition (iidColorLaw S center output pc po m α hα hα'.le)
      (completionEvent S center output m)
      (completionEvent_mass_pos S center output pc po m hm α hα hα'))

theorem conditionalCompletionLaw_mass
    (S : FlaggedTensor X Y Z) (center output : Color)
    (pc : FiniteLaw (ColorSlice S center)) (po : FiniteLaw (ColorSlice S output))
    (m : ℕ) (hm : 0 < m) (α : ℝ) (hα : 0 ≤ α) (hα' : α < 1)
    (a : ColorSlice (complete S center m) output) :
    (conditionalCompletionLaw S center output pc po m hm α hα hα').mass a =
      (iidColorLaw S center output pc po m α hα hα'.le).mass (slot S center m a.val) /
        eventMass (iidColorLaw S center output pc po m α hα hα'.le)
          (completionEvent S center output m) := by
  let e := conditionalLeafEquiv S center output m
  have he : e.symm (e a) = a := e.symm_apply_apply a
  conv_lhs => rw [← he]
  rw [conditionalCompletionLaw, transport_mass, condition_mass]
  rfl

end MatrixMultiplication.CompletionColorLaws

end

end OAI
