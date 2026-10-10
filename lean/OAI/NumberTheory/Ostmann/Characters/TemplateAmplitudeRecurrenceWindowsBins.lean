import OAI.NumberTheory.Ostmann.Characters.SourceTemplateLeafMask
import OAI.NumberTheory.Ostmann.Characters.TemplateAmplitudeRecurrenceSupportPropagationBasic
import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedLeafProfiles
import OAI.NumberTheory.Ostmann.Characters.TemplateWords

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters.Template
open HigherBiasSource.SourceTemplate
attribute [local instance] Classical.propDecidable

theorem canonical_weightSupport_words (k : ℕ) (leafMask : ℤ → State k 0 → Prop)
    (P : ℤ → Prop) (hP : ∀s x,leafMask s x → P (x (.word,true)))
    (X Δ W : ℝ) (j : ℕ) (s : ℤ) (x : State k j) (t : HistoryReconstruction.Tree j)
    (h : WeightSupport k (canonicalHistoryMask k leafMask) X Δ W j s x t) :
    ∀i : WordSlot k j,P (x i.val) := by
  induction j generalizing s with
  | zero =>
    intro i
    rw [initial_word_unique k i]
    exact hP s x h.1
  | succ j ih =>
    let R := reconstructedPivot k j x s t.1.1 t.1.2
    have hl := ih t.1.1 (childState k j true x R) t.2.1 h.2.1
    have hr := ih t.1.2 (childState k j false x R) t.2.2 h.2.2
    intro i
    obtain ⟨u,b,hi⟩ : ∃u b,(wordEquiv (schedule k j) j).symm (u,b)=i :=
      ⟨_,_,(wordEquiv (schedule k j) j).symm_apply_apply i⟩
    subst i
    have hc (b : Bool) : childState k j b x R u.val =
        x ((wordEquiv (schedule k j) j).symm (u,b)).val :=
      childState_copied k j b x R ⟨u.val,word_copied _ _ _ u.property.1 u.property.2⟩
    cases b
    · exact (hc false) ▸ hr u
    · exact (hc true) ▸ hl u

theorem retainedHistoryWeight_active_words {k : ℕ}
    {B V : (j:ℕ) → State k (j+1) → ℤ}
    {extra : (j:ℕ) → ℤ → State k j → HistoryReconstruction.Tree j → Prop}
    {leafMask : ℤ → State k 0 → Prop} {X Δ W : ℝ} {j : ℕ} {s : ℤ}
    {x : State k j} {t : HistoryReconstruction.Tree j}
    (P : ℤ → Prop) (hP : ∀s x,leafMask s x → P (x (.word,true)))
    (h : retainedHistoryWeight k B V extra (canonicalHistoryMask k leafMask)
      X Δ W j s x t ≠ 0) : ∀i : WordSlot k j,P (x i.val) := by
  have hs := retainedHistoryWeight_support h
  have hw : weight k (canonicalHistoryMask k leafMask) X Δ W j s x t ≠ 0 := by
    simpa only [retainedHistoryWeight,ite_eq_left hs] using h
  exact canonical_weightSupport_words k leafMask P hP X Δ W j s x t
    (weightSupport_of_weight_ne_zero k _ X Δ W j s x t hw)

theorem retainedHistoryWeight_source_word_bin {k : ℕ}
    {B V : (j:ℕ) → State k (j+1) → ℤ}
    {extra : (j:ℕ) → ℤ → State k j → HistoryReconstruction.Tree j → Prop}
    {J : ℤ} {X Δ W : ℝ} {j : ℕ} {s : ℤ} {x : State k j} {t : HistoryReconstruction.Tree j}
    (h : retainedHistoryWeight k B V extra
      (canonicalHistoryMask k (sourceRangeLeafMask k J X Δ W)) X Δ W j s x t ≠ 0)
    (i : WordSlot k j) : ⌊Real.log (x i.val:ℝ)⌋=J :=
  retainedHistoryWeight_active_words (fun n=>⌊Real.log (n:ℝ)⌋=J)
    (fun _ _ h=>h.1.1) h i

theorem retainedHistoryWeight_source_word_log {k : ℕ}
    {B V : (j:ℕ) → State k (j+1) → ℤ}
    {extra : (j:ℕ) → ℤ → State k j → HistoryReconstruction.Tree j → Prop}
    {J : ℤ} {X Δ W : ℝ} {j : ℕ} {s : ℤ} {x : State k j} {t : HistoryReconstruction.Tree j}
    (h : retainedHistoryWeight k B V extra
      (canonicalHistoryMask k (sourceRangeLeafMask k J X Δ W)) X Δ W j s x t ≠ 0)
    (i : WordSlot k j) : (J:ℝ) ≤ Real.log (x i.val:ℝ) ∧ Real.log (x i.val:ℝ) < (J:ℝ)+1 :=
  Int.floor_eq_iff.mp (retainedHistoryWeight_source_word_bin h i)

theorem retainedHistoryWeight_source_copied_word_bin {k j : ℕ}
    {B V : (l:ℕ) → State k (l+1) → ℤ}
    {extra : (l:ℕ) → ℤ → State k l → HistoryReconstruction.Tree l → Prop}
    {J P s : ℤ} {X Δ W : ℝ} {hC : CopiedState k j} {y : OutsideState k j}
    {t : HistoryReconstruction.Tree j}
    (h : retainedHistoryWeight k B V extra
      (canonicalHistoryMask k (sourceRangeLeafMask k J X Δ W)) X Δ W j s
        (sourceState k j P hC y) t ≠ 0) (i : WordSlot k j) :
    ⌊Real.log (hC ⟨i.val,word_copied _ _ _ i.property.1 i.property.2⟩:ℝ)⌋=J := by
  have hh := retainedHistoryWeight_source_word_bin h i
  have he := sourceState_copied_value P hC y
    ⟨i.val,word_copied _ _ _ i.property.1 i.property.2⟩
  rwa [he] at hh

end Ostmann.Characters.Template

end

end OAI
