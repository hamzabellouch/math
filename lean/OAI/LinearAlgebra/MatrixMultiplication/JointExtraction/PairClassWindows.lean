import OAI.LinearAlgebra.MatrixMultiplication.JointExtraction.TypeCounts

namespace OAI

/-! Joint tensor extraction, compatibility and entropy estimates. -/

noncomputable section

namespace MatrixMultiplication.JointPairClassWindows

open MatrixMultiplication.Foundation

attribute [local instance] Classical.propDecidable

variable {I A C : Type*} [Fintype I] [Fintype A] [Fintype C]
  [DecidableEq I] [DecidableEq A] [DecidableEq C]

abbrev Fiber (k : I → C) (c : C) := {i : I // k i = c}

def fiberWord (z : I → A) (k : I → C) (c : C) : Fiber k c → A :=
  fun i => z i.val

omit [Fintype A] [Fintype C] [DecidableEq I] in
theorem fiber_population (z : I → A) (k : I → C) (f : A → C)
    (hf : ∀ i, f (z i) = k i) (c : C) (a : A) :
    wordPopulation (fiberWord z k c) a =
      if f a = c then wordPopulation z a else 0 := by
  classical
  by_cases ha : f a = c
  · rw [ite_eq_left ha]
    unfold wordPopulation
    apply Fintype.card_congr
    exact
      { toFun := fun i => ⟨i.val.val, i.property⟩
        invFun := fun i => ⟨⟨i.val, by rw [← hf i.val, i.property, ha]⟩, i.property⟩
        left_inv := fun ⟨⟨i, hi⟩, hia⟩ => rfl
        right_inv := fun ⟨i, hia⟩ => rfl }
  · rw [ite_eq_right ha]
    let : IsEmpty {i : Fiber k c // fiberWord z k c i = a} :=
      ⟨fun i => ha (calc
        f a = f (z i.val.val) := congrArg f i.property.symm
        _ = k i.val.val := hf _
        _ = c := i.val.property)⟩
    exact Fintype.card_eq_zero

omit [Fintype C] [DecidableEq I] in
theorem fiber_card (k : I → C) (c : C) :
    Fintype.card (Fiber k c) = wordPopulation k c := rfl

def conditionalCenter (f : A → C) (c : C) (q : A → ℝ) (mass : ℝ) : A → ℝ :=
  fun a => if f a = c then q a / mass else 0

omit [Fintype A] [Fintype C] [DecidableEq I] in
theorem fiber_window (z : I → A) (k : I → C) (f : A → C)
    (hf : ∀ i, f (z i) = k i) (c : C) (q : A → ℝ) (mass η : ℝ)
    (hmass : 0 < mass) (hη : 0 ≤ η)
    (hclass : (Fintype.card (Fiber k c) : ℝ) = (Fintype.card I : ℝ) * mass)
    (hwindow : ∀ a, |(wordPopulation z a : ℝ) / Fintype.card I - q a| ≤ η) :
    ∀ a, |(wordPopulation (fiberWord z k c) a : ℝ) / Fintype.card (Fiber k c) -
      conditionalCenter f c q mass a| ≤ η / mass := by
  intro a
  rw [fiber_population z k f hf c a]
  by_cases ha : f a = c
  · simp only [ha, ite_true, conditionalCenter]
    rw [hclass]
    have hid : (wordPopulation z a : ℝ) / ((Fintype.card I : ℝ) * mass) - q a / mass =
        ((wordPopulation z a : ℝ) / Fintype.card I - q a) / mass := by
      rw [sub_div, div_div]
    rw [hid, abs_div, abs_of_pos hmass]
    exact div_le_div_of_nonneg_right (hwindow a) hmass.le
  · simp only [ha, ite_false, Nat.cast_zero, zero_div, conditionalCenter, sub_zero, abs_zero]
    exact div_nonneg hη hmass.le

omit [Fintype A] [Fintype C] [DecidableEq I] in
theorem fiber_count_window (z : I → A) (k : I → C) (f : A → C)
    (hf : ∀ i, f (z i) = k i) (c : C) (q : A → ℝ) (η : ℝ) (hη : 0 ≤ η)
    (hwindow : ∀ a,
      |(wordPopulation z a : ℝ) - (Fintype.card I : ℝ) * q a| ≤ (Fintype.card I : ℝ) * η) :
    ∀ a, |(wordPopulation (fiberWord z k c) a : ℝ) -
      (Fintype.card I : ℝ) * (if f a = c then q a else 0)| ≤ (Fintype.card I : ℝ) * η := by
  intro a
  rw [fiber_population z k f hf c a]
  by_cases ha : f a = c
  · simpa only [ha, ite_true] using hwindow a
  · simp only [ha, ite_false, Nat.cast_zero, mul_zero, sub_zero, abs_zero]
    exact mul_nonneg (Nat.cast_nonneg _) hη

end MatrixMultiplication.JointPairClassWindows

end

end OAI
