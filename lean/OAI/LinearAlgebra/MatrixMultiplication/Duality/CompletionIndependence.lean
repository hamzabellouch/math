import OAI.LinearAlgebra.MatrixMultiplication.Duality.ProgramIndependence
import OAI.LinearAlgebra.MatrixMultiplication.Duality.InformationConditioning
import OAI.LinearAlgebra.MatrixMultiplication.Duality.InformationTransport
import OAI.LinearAlgebra.MatrixMultiplication.Completion.ProgramPrefixes

namespace OAI

/-! Dual matrix multiplication exponents and finite rectangular constructions. -/

noncomputable section

namespace MatrixMultiplication.DualProgramIndependence

universe u w

open MatrixMultiplication.Foundation RecursiveCompletion CompletionLabels
open CompletionLaws CompletionColorLaws CompletionProductLaws
open DualInformation DualInformationTransport TopologicalFlatten
open scoped BigOperators
attribute [local instance 10000] Classical.propDecidable Classical.decEq
attribute [local instance 11000] instDecidableEqFin

variable {X Y Z : Type u} {Code : Type w} [Fintype X] [Fintype Y] [Fintype Z]
  [Fintype Code] [Inhabited Code] {depth m : ℕ}

def slotCut (depth k : ℕ) (i j : Fin m) : ℕ :=
  if j.val < i.val then depth else if j = i then k else 0

def slotPrior (S : FlaggedTensor X Y Z)
    (p : Program (Leaf S) (Coordinate X Y Z) Color Code depth)
    (i : Fin m) (k : ℕ) (j : Fin m) (a : Leaf S) :
    Color × LabelRecord (fun _ => Code) (slotCut depth k i j) :=
  (leafColor S a, labelRecordOf p.labels (slotCut depth k i j) a)

def slotLabel (S : FlaggedTensor X Y Z)
    (p : Program (Leaf S) (Coordinate X Y Z) Color Code depth)
    (i : Fin m) (k : ℕ) (j : Fin m) (a : Leaf S) : Code :=
  if j = i then p.labels k a else default

omit [Fintype X] [Fintype Y] [Fintype Z] [Fintype Code] [Inhabited Code] in
theorem slotPrior_word_eq_iff (S : FlaggedTensor X Y Z)
    (p : Program (Leaf S) (Coordinate X Y Z) Color Code depth)
    (i : Fin m) (k : ℕ) (a b : Fin m → Leaf S) :
    (fun j => slotPrior S p i k j (a j)) = (fun j => slotPrior S p i k j (b j)) ↔
      (∀ j, leafColor S (a j) = leafColor S (b j)) ∧
        ((∀ j : Fin m, j.val < i.val →
          labelRecordOf p.labels depth (a j) = labelRecordOf p.labels depth (b j)) ∧
          labelRecordOf p.labels k (a i) = labelRecordOf p.labels k (b i)) := by
  constructor
  · intro h
    refine ⟨fun j => congrArg Prod.fst (congrFun h j), ?_, ?_⟩
    · intro j hj
      have hs := congrArg Prod.snd (congrFun h j)
      change labelRecordOf p.labels (slotCut depth k i j) (a j) =
        labelRecordOf p.labels (slotCut depth k i j) (b j) at hs
      rw [labelRecordOf_eq_iff] at hs ⊢
      simpa only [slotCut, ite_eq_left hj] using hs
    · have hs := congrArg Prod.snd (congrFun h i)
      change labelRecordOf p.labels (slotCut depth k i i) (a i) =
        labelRecordOf p.labels (slotCut depth k i i) (b i) at hs
      rw [labelRecordOf_eq_iff] at hs ⊢
      simpa [slotCut] using hs
  · rintro ⟨hc, hp, hi⟩
    funext j
    apply Prod.ext (hc j)
    change labelRecordOf p.labels (slotCut depth k i j) (a j) =
      labelRecordOf p.labels (slotCut depth k i j) (b j)
    rw [labelRecordOf_eq_iff]
    intro n hn
    by_cases hj : j.val < i.val
    · have hn' : n < depth := by simpa only [slotCut, ite_eq_left hj] using hn
      exact label_eq_of_record_eq p.labels (hp j hj) hn'
    · by_cases hji : j = i
      · subst j
        have hn' : n < k := by simpa [slotCut] using hn
        exact label_eq_of_record_eq p.labels hi hn'
      · simp only [slotCut, ite_eq_right hj, ite_eq_right hji] at hn
        exact (Nat.not_lt_zero n hn).elim

omit [Fintype X] [Fintype Y] [Fintype Z] [Fintype Code] in
theorem slotLabel_word_eq_iff (S : FlaggedTensor X Y Z)
    (p : Program (Leaf S) (Coordinate X Y Z) Color Code depth)
    (i : Fin m) (k : ℕ) (a b : Fin m → Leaf S) :
    (fun j => slotLabel S p i k j (a j)) = (fun j => slotLabel S p i k j (b j)) ↔
      p.labels k (a i) = p.labels k (b i) := by
  constructor
  · intro h
    simpa only [slotLabel, ite_eq_left rfl, ite_true] using congrFun h i
  · intro h
    funext j
    by_cases hji : j = i
    · subst j
      simpa only [slotLabel, ite_eq_left rfl, ite_true] using h
    · simp only [slotLabel, ite_eq_right hji]

theorem iidColorLaw_slot_factorization (S : FlaggedTensor X Y Z)
    (p : Program (Leaf S) (Coordinate X Y Z) Color Code depth)
    (center output : Color)
    (pc : FiniteLaw (ColorSlice S center)) (po : FiniteLaw (ColorSlice S output))
    (α : ℝ) (hα : 0 ≤ α) (hα' : α ≤ 1) (hbranch : center ≠ output ∨ α = 0)
    (i : Fin m) (k : ℕ)
    (hc : ConditionalMassFactorization pc (fun a => labelRecordOf p.labels k a.val)
      (fun a => p.labels k a.val) (fun a => a.val.val.1))
    (ho : ConditionalMassFactorization po (fun a => labelRecordOf p.labels k a.val)
      (fun a => p.labels k a.val) (fun a => a.val.val.1)) :
    ConditionalMassFactorization (iidColorLaw S center output pc po m α hα hα')
      (fun a j => slotPrior S p i k j (a j))
      (fun a j => slotLabel S p i k j (a j)) (fun a j => (a j).val.1) := by
  apply independentProduct_factorization
    (fun _ : Fin m => colorMix S center output pc po α hα hα')
    (slotPrior S p i k) (slotLabel S p i k) (fun _ a => a.val.1)
  intro j
  by_cases hji : j = i
  · subst j
    apply mass_factorization_of_same_partitions (colorMix S center output pc po α hα hα')
      (fun a => (leafColor S a, labelRecordOf p.labels k a)) (p.labels k) (fun a => a.val.1)
    · intro a b
      simp only [slotPrior, Prod.mk.injEq, labelRecordOf_eq_iff]
      simp [slotCut]
    · intro a b
      simp [slotLabel]
    · intro a b
      rfl
    · exact colorMix_recorded_factorization S center output pc po α hα hα' hbranch
        (labelRecordOf p.labels k) (p.labels k) (fun a => a.val.1) hc ho
  · have hl : slotLabel S p i k j = (fun _ => (default : Code)) := by
      funext a
      simp [slotLabel, hji]
    rw [hl]
    exact factorization_constant_label (colorMix S center output pc po α hα hα')
      (slotPrior S p i k j) (default : Code) (fun a => a.val.1)

def slotCompletionEvent (center output : Color) (i : Fin m) (k : ℕ)
    (r : ∀ j : Fin m, Color × LabelRecord (fun _ => Code) (slotCut depth k i j)) : Prop :=
  raisedFlag center output (fun j => (r j).1 = output) ∧
    ∀ j, (r j).1 = center ∨ (r j).1 = output

theorem condition_slot_factorization (S : FlaggedTensor X Y Z)
    (p : Program (Leaf S) (Coordinate X Y Z) Color Code depth)
    (center output : Color)
    (pc : FiniteLaw (ColorSlice S center)) (po : FiniteLaw (ColorSlice S output))
    (α : ℝ) (hα : 0 ≤ α) (hα' : α < 1) (hbranch : center ≠ output ∨ α = 0)
    (hm : 0 < m) (i : Fin m) (k : ℕ)
    (hc : ConditionalMassFactorization pc (fun a => labelRecordOf p.labels k a.val)
      (fun a => p.labels k a.val) (fun a => a.val.val.1))
    (ho : ConditionalMassFactorization po (fun a => labelRecordOf p.labels k a.val)
      (fun a => p.labels k a.val) (fun a => a.val.val.1)) :
    ConditionalMassFactorization
      (condition (iidColorLaw S center output pc po m α hα hα'.le)
        (completionEvent S center output m)
        (completionEvent_mass_pos S center output pc po m hm α hα hα'))
      (fun a j => slotPrior S p i k j (a.val j))
      (fun a j => slotLabel S p i k j (a.val j)) (fun a j => (a.val j).val.1) := by
  exact conditionalMassFactorization_condition
    (iidColorLaw S center output pc po m α hα hα'.le)
    (fun a j => slotPrior S p i k j (a j))
    (fun a j => slotLabel S p i k j (a j)) (fun a j => (a j).val.1)
    (slotCompletionEvent center output i k)
    (completionEvent_mass_pos S center output pc po m hm α hα hα')
    (iidColorLaw_slot_factorization S p center output pc po α hα hα'.le hbranch i k hc ho)

theorem conditionalCompletionLaw_inherited_factorization (S : FlaggedTensor X Y Z)
    (p : Program (Leaf S) (Coordinate X Y Z) Color Code depth)
    (context_eq : ∀ a, p.context a = leafColor S a)
    (view_eq : ∀ side a, p.view side a = coordinate a.val side)
    (center output : Color)
    (pc : FiniteLaw (ColorSlice S center)) (po : FiniteLaw (ColorSlice S output))
    (α : ℝ) (hα : 0 ≤ α) (hα' : α < 1) (hbranch : center ≠ output ∨ α = 0)
    (hm : 0 < m) (i : Fin m) (k : ℕ) (hk : k < depth)
    (hc : ConditionalMassFactorization pc (fun a => labelRecordOf p.labels k a.val)
      (fun a => p.labels k a.val) (fun a => a.val.val.1))
    (ho : ConditionalMassFactorization po (fun a => labelRecordOf p.labels k a.val)
      (fun a => p.labels k a.val) (fun a => a.val.val.1)) :
    ConditionalMassFactorization
      (conditionalCompletionLaw S center output pc po m hm α hα hα')
      (fun a => labelRecordOf
        (completionLocalProgram S center m p context_eq view_eq).labels
        (3 + (i.val * depth + k)) a.val)
      (fun a => (completionLocalProgram S center m p context_eq view_eq).labels
        (3 + (i.val * depth + k)) a.val)
      (fun a => a.val.val.1) := by
  let e := conditionalLeafEquiv S center output m
  let q := condition (iidColorLaw S center output pc po m α hα hα'.le)
    (completionEvent S center output m)
    (completionEvent_mass_pos S center output pc po m hm α hα hα')
  have hslot (a : {w : Fin m → Leaf S // completionEvent S center output m w}) :
      slot S center m (e.symm a).val = a.val :=
    congrArg Subtype.val (e.apply_symm_apply a)
  change ConditionalMassFactorization (q.map e.symm) _ _ _
  rw [mass_factorization_map_iff]
  apply mass_factorization_of_same_partitions q
    (fun a j => slotPrior S p i k j (a.val j))
    (fun a j => slotLabel S p i k j (a.val j)) (fun a j => (a.val j).val.1)
  · intro a b
    rw [slotPrior_word_eq_iff, completionProgram_record_eq_iff _ _ _ _ _ _ i k hk.le]
    simp only [(e.symm a).property, (e.symm b).property, true_and, pattern,
      hslot, funext_iff]
  · intro a b
    rw [slotLabel_word_eq_iff,
      completionLocalProgram_label_slot _ _ _ _ _ _ i k hk,
      completionLocalProgram_label_slot _ _ _ _ _ _ i k hk, hslot, hslot]
    simp only [encodeOld, Option.some.injEq, Sum.inr.injEq]
  · intro a b
    rfl
  · exact condition_slot_factorization S p center output pc po α hα hα' hbranch hm i k hc ho

end MatrixMultiplication.DualProgramIndependence

end

end OAI
