import OAI.LinearAlgebra.MatrixMultiplication.Completion.ColorLaws
import OAI.LinearAlgebra.MatrixMultiplication.Completion.Entropy
import OAI.LinearAlgebra.MatrixMultiplication.Completion.ColorEntropy
import OAI.LinearAlgebra.MatrixMultiplication.Completion.EntropyAlgebra

namespace OAI

/-! Dual matrix multiplication exponents and finite rectangular constructions. -/

noncomputable section

namespace MatrixMultiplication.DualLawEntropy

open MatrixMultiplication.Foundation RecursiveCompletion CompletionLabels CompletionColorLaws
open CompletionProductLaws CompletionLaws
open scoped BigOperators
attribute [local instance 10000] Classical.propDecidable Classical.decEq
attribute [local instance 11000] instDecidableEqFin

universe u
variable {X Y Z : Type u} [Fintype X] [Fintype Y] [Fintype Z]

def allCenter (S : FlaggedTensor X Y Z) (center : Color) (m : ℕ)
    (w : Fin m → Leaf S) : Prop := ∀ i, leafColor S (w i) = center

theorem iid_allowed (S : FlaggedTensor X Y Z) (center output : Color)
    (pc : FiniteLaw (ColorSlice S center)) (po : FiniteLaw (ColorSlice S output))
    (m : ℕ) (a : ℝ) (ha : 0 ≤ a) (ha' : a ≤ 1) (w : Fin m → Leaf S)
    (hw : (iidColorLaw S center output pc po m a ha ha').mass w ≠ 0) (i : Fin m) :
    leafColor S (w i) = center ∨ leafColor S (w i) = output := by
  change (∏ j : Fin m, (colorMix S center output pc po a ha ha').mass (w j)) ≠ 0 at hw
  have hn : (colorMix S center output pc po a ha ha').mass (w i) ≠ 0 :=
    (Finset.prod_ne_zero_iff.mp hw) i (Finset.mem_univ i)
  by_contra h
  exact hn (colorMix_mass_zero S center output pc po a ha ha' (w i)
    (fun h' => h (Or.inl h')) (fun h' => h (Or.inr h')))

omit [Fintype X] [Fintype Y] [Fintype Z] in
theorem not_event_iff_allCenter (S : FlaggedTensor X Y Z) (center output : Color)
    (hne : center ≠ output) (m : ℕ) (w : Fin m → Leaf S)
    (allowed : ∀ i, leafColor S (w i) = center ∨ leafColor S (w i) = output) :
    ¬ completionEvent S center output m w ↔ allCenter S center m w := by
  constructor
  · intro h i
    rcases allowed i with hi | hi
    · exact hi
    · exfalso
      apply h
      refine ⟨?_, allowed⟩
      simpa only [raisedFlag, ite_eq_right hne] using Exists.intro i hi
  · intro h he
    have hx : ∃ i, leafColor S (w i) = output := by
      simpa only [raisedFlag, ite_eq_right hne] using he.1
    obtain ⟨i, hi⟩ := hx
    exact hne ((h i).symm.trans hi)

theorem event_sum_congr {A : Type*} [Fintype A] (P Q : A → Prop) (f : A → ℝ)
    (agree : ∀ a, f a ≠ 0 → (P a ↔ Q a)) :
    (∑ a : {a // P a}, f a.val) = ∑ a : {a // Q a}, f a.val := by
  rw [sum_subtype_indicator P f, sum_subtype_indicator Q f]
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : f a = 0
  · simp [ha]
  · simp only [agree a ha]

theorem removed_event_mass_eq (S : FlaggedTensor X Y Z) (center output : Color)
    (hne : center ≠ output)
    (pc : FiniteLaw (ColorSlice S center)) (po : FiniteLaw (ColorSlice S output))
    (m : ℕ) (a : ℝ) (ha : 0 ≤ a) (ha' : a ≤ 1) :
    eventMass (iidColorLaw S center output pc po m a ha ha')
      (fun w => ¬ completionEvent S center output m w) =
    eventMass (iidColorLaw S center output pc po m a ha ha') (allCenter S center m) := by
  apply event_sum_congr
  intro w hw
  exact not_event_iff_allCenter S center output hne m w
    (iid_allowed S center output pc po m a ha ha' w hw)

theorem removed_event_entropy_eq (S : FlaggedTensor X Y Z) (center output : Color)
    (hne : center ≠ output)
    (pc : FiniteLaw (ColorSlice S center)) (po : FiniteLaw (ColorSlice S output))
    (m : ℕ) (a : ℝ) (ha : 0 ≤ a) (ha' : a ≤ 1) :
    (∑ w : {w // ¬ completionEvent S center output m w},
      entropyTerm ((iidColorLaw S center output pc po m a ha ha').mass w.val)) =
    ∑ w : {w // allCenter S center m w},
      entropyTerm ((iidColorLaw S center output pc po m a ha ha').mass w.val) := by
  apply event_sum_congr (fun w => ¬ completionEvent S center output m w)
    (allCenter S center m)
    (fun w => entropyTerm ((iidColorLaw S center output pc po m a ha ha').mass w))
  intro w hw
  have hm : (iidColorLaw S center output pc po m a ha ha').mass w ≠ 0 := by
    intro hm
    simp [hm] at hw
  exact not_event_iff_allCenter S center output hne m w
    (iid_allowed S center output pc po m a ha ha' w hm)

def centerWordEquiv (S : FlaggedTensor X Y Z) (center : Color) (m : ℕ) :
    {w : Fin m → Leaf S // allCenter S center m w} ≃ (Fin m → ColorSlice S center) where
  toFun w i := ⟨w.val i, w.property i⟩
  invFun w := ⟨fun i => (w i).val, fun i => (w i).property⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem center_word_mass (S : FlaggedTensor X Y Z) (center output : Color)
    (hne : center ≠ output)
    (pc : FiniteLaw (ColorSlice S center)) (po : FiniteLaw (ColorSlice S output))
    (m : ℕ) (a : ℝ) (ha : 0 ≤ a) (ha' : a ≤ 1)
    (w : {w : Fin m → Leaf S // allCenter S center m w}) :
    (iidColorLaw S center output pc po m a ha ha').mass w.val =
      a ^ m * (independentProduct (fun _ : Fin m => pc)).mass (centerWordEquiv S center m w) := by
  change (∏ i, (colorMix S center output pc po a ha ha').mass (w.val i)) =
    a ^ m * ∏ i, pc.mass ⟨w.val i, w.property i⟩
  have hslot (i : Fin m) : (colorMix S center output pc po a ha ha').mass (w.val i) =
      a * pc.mass ⟨w.val i, w.property i⟩ :=
    colorMix_center_mass S center output hne pc po a ha ha' ⟨w.val i, w.property i⟩
  simp_rw [hslot]
  rw [Finset.prod_mul_distrib]
  simp

theorem allCenter_mass (S : FlaggedTensor X Y Z) (center output : Color)
    (hne : center ≠ output)
    (pc : FiniteLaw (ColorSlice S center)) (po : FiniteLaw (ColorSlice S output))
    (m : ℕ) (a : ℝ) (ha : 0 ≤ a) (ha' : a ≤ 1) :
    eventMass (iidColorLaw S center output pc po m a ha ha') (allCenter S center m) = a ^ m := by
  unfold eventMass
  simp_rw [center_word_mass S center output hne pc po m a ha ha']
  rw [← Finset.mul_sum, (centerWordEquiv S center m).sum_comp,
    (independentProduct (fun _ : Fin m => pc)).total, mul_one]

theorem allCenter_entropy (S : FlaggedTensor X Y Z) (center output : Color)
    (hne : center ≠ output)
    (pc : FiniteLaw (ColorSlice S center)) (po : FiniteLaw (ColorSlice S output))
    (m : ℕ) (a : ℝ) (ha : 0 ≤ a) (ha' : a ≤ 1) :
    (∑ w : {w // allCenter S center m w},
      entropyTerm ((iidColorLaw S center output pc po m a ha ha').mass w.val)) =
    entropyTerm (a ^ m) + a ^ m * ((m : ℝ) * finiteEntropy pc.mass) := by
  simp_rw [center_word_mass S center output hne pc po m a ha ha']
  rw [(centerWordEquiv S center m).sum_comp
    (fun w => entropyTerm (a ^ m * (independentProduct (fun _ : Fin m => pc)).mass w))]
  change finiteEntropy (fun w => a ^ m *
    (independentProduct (fun _ : Fin m => pc)).mass w) = _
  rw [entropy_scaled_law, independentProduct_entropy]
  simp

theorem conditionalCompletionLaw_entropy (S : FlaggedTensor X Y Z) (center output : Color)
    (hne : center ≠ output)
    (pc : FiniteLaw (ColorSlice S center)) (po : FiniteLaw (ColorSlice S output))
    (m : ℕ) (hm : 0 < m) (a : ℝ) (ha : 0 ≤ a) (ha' : a < 1) :
    finiteEntropy (conditionalCompletionLaw S center output pc po m hm a ha ha').mass =
      CompletionEntropyAlgebra.conditionalMixEntropy a m
        (finiteEntropy pc.mass) (finiteEntropy po.mass) := by
  rw [conditionalCompletionLaw, transport_entropy]
  have hmass : eventMass (iidColorLaw S center output pc po m a ha ha'.le)
      (fun w => ¬ completionEvent S center output m w) = a ^ m :=
    (removed_event_mass_eq S center output hne pc po m a ha ha'.le).trans
      (allCenter_mass S center output hne pc po m a ha ha'.le)
  have hremoved :
      (∑ w : {w // ¬ completionEvent S center output m w},
        entropyTerm ((iidColorLaw S center output pc po m a ha ha'.le).mass w.val)) =
      entropyTerm (a ^ m) + a ^ m * ((m : ℝ) * finiteEntropy pc.mass) :=
    (removed_event_entropy_eq S center output hne pc po m a ha ha'.le).trans
      (allCenter_entropy S center output hne pc po m a ha ha'.le)
  rw [condition_entropy_of_removed_event _ _ _ (a ^ m)
    ((m : ℝ) * finiteEntropy pc.mass) hmass hremoved]
  rw [iidColorLaw_entropy S center output hne pc po m a ha ha'.le]
  unfold CompletionEntropyAlgebra.conditionalMixEntropy CompletionEntropyAlgebra.binaryEntropy
  congr 1
  ring

end MatrixMultiplication.DualLawEntropy

end

end OAI
