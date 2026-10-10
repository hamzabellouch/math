import OAI.Probability.InvariantIsing.Fields.FieldRefinePaths
import Mathlib.Data.List.Sort

namespace OAI

/-! Finite common refinements, built only by duplicating constant-height cells. -/

noncomputable section
open MeasureTheory IsingPerceptron Set
open scoped NNReal

namespace InvariantIsing

def fieldCutSet (h : FieldStep) : Finset ℝ := by
  classical
  exact Finset.univ.image h.cut

@[simp] lemma mem_fieldCutSet (h : FieldStep) (s : ℝ) :
    s ∈ fieldCutSet h ↔ ∃ i, h.cut i = s := by
  classical
  simp [fieldCutSet]

lemma fieldCutSet_bounds (h : FieldStep) {s : ℝ} (hs : s ∈ fieldCutSet h) :
    s ∈ Icc (0 : ℝ) 1 := by
  obtain ⟨i, rfl⟩ := (mem_fieldCutSet h s).mp hs
  constructor
  · rw [← h.first]; exact h.ordered_cut.monotone (Fin.zero_le i)
  · rw [← h.last]; exact h.ordered_cut.monotone (Fin.le_last i)

lemma fieldCutSet_insertCut (h : FieldStep) (i : Fin (h.depth + 1)) (c : ℝ)
    (hc₀ : h.cut i.castSucc < c) (hc₁ : c < h.cut i.succ) :
    fieldCutSet (fieldInsertCut h i c hc₀ hc₁) = insert c (fieldCutSet h) := by
  classical
  have he := Fin.range_insertNth i.castSucc.succ c h.cut
  ext s
  simp only [mem_fieldCutSet, Finset.mem_insert]
  change (∃ j, Fin.insertNth (α := fun _ => ℝ) i.castSucc.succ c h.cut j = s) ↔
    s = c ∨ ∃ j, h.cut j = s
  simpa only [Set.insert, Set.mem_ofPred_eq, Set.mem_range] using Set.ext_iff.mp he s

inductive FieldRefines : FieldStep → FieldStep → Prop
  | refl (h : FieldStep) : FieldRefines h h
  | insert {h k : FieldStep} (hk : FieldRefines h k) (i : Fin (k.depth + 1))
      (c : ℝ) (hc₀ : k.cut i.castSucc < c) (hc₁ : c < k.cut i.succ) :
      FieldRefines h (fieldInsertCut k i c hc₀ hc₁)

lemma FieldRefines.trans {h k l : FieldStep} (hhk : FieldRefines h k)
    (hkl : FieldRefines k l) : FieldRefines h l := by
  induction hkl with
  | refl => exact hhk
  | insert hkl i c hc₀ hc₁ ih => exact FieldRefines.insert ih i c hc₀ hc₁

lemma FieldRefines.value {h k : FieldStep} (hk : FieldRefines h k) (z : ℝ) :
    fieldValue k z = fieldValue h z := by
  induction hk with
  | refl => rfl
  | insert hk i c hc₀ hc₁ ih => exact (fieldValue_insertCut _ i c hc₀ hc₁ z).trans ih

lemma FieldRefines.field_ae {h k : FieldStep} (hk : FieldRefines h k) :
    fieldFunction k =ᵐ[pathMeasure] fieldFunction h := by
  induction hk with
  | refl => exact Filter.EventuallyEq.rfl
  | insert hk i c hc₀ hc₁ ih => exact (fieldFunction_insertCut_ae _ i c hc₀ hc₁).trans ih

lemma FieldRefines.magnetization_ae {h k : FieldStep} (hk : FieldRefines h k) :
    (fieldMagnetizationPath k).val =ᵐ[pathMeasure] (fieldMagnetizationPath h).val := by
  induction hk with
  | refl => exact Filter.EventuallyEq.rfl
  | insert hk i c hc₀ hc₁ ih =>
    exact (fieldMagnetizationPath_insertCut_ae _ i c hc₀ hc₁).trans ih

lemma FieldRefines.pairing {h k : FieldStep} (hk : FieldRefines h k) (p : OverlapPath) :
    fieldPairing p k = fieldPairing p h := by
  apply integral_congr_ae
  filter_upwards [hk.field_ae] with s hs
  rw [hs]

lemma field_exists_refinement (h : FieldStep) (S : Finset ℝ)
    (hS : ∀ s ∈ S, s ∈ Icc (0 : ℝ) 1) :
    ∃ k, FieldRefines h k ∧ fieldCutSet k = fieldCutSet h ∪ S := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨h, FieldRefines.refl h, by simp⟩
  | @insert c S hc ih =>
    obtain ⟨k, hk, hcuts⟩ := ih (fun s hs => hS s (Finset.mem_insert_of_mem hs))
    by_cases hck : c ∈ fieldCutSet k
    · refine ⟨k, hk, ?_⟩
      rw [hcuts] at hck ⊢
      ext s
      simp only [Finset.mem_union, Finset.mem_insert]
      constructor
      · intro hs; rcases hs with hs | hs
        · exact Or.inl hs
        · exact Or.inr (Or.inr hs)
      · intro hs; rcases hs with hs | rfl | hs
        · exact Or.inl hs
        · simpa only [Finset.mem_union] using hck
        · exact Or.inr hs
    · have hcb := hS c (Finset.mem_insert_self c S)
      have hc0 : 0 < c := by
        have hne : c ≠ 0 := by
          intro he; apply hck
          apply (mem_fieldCutSet k c).mpr
          exact ⟨0, k.first.trans he.symm⟩
        exact lt_of_le_of_ne hcb.1 (Ne.symm hne)
      have hc1 : c < 1 := by
        have hne : c ≠ 1 := by
          intro he; apply hck
          apply (mem_fieldCutSet k c).mpr
          exact ⟨Fin.last (k.depth + 1), k.last.trans he.symm⟩
        exact lt_of_le_of_ne hcb.2 hne
      obtain ⟨i, hi₀, hi₁⟩ := finite_partition_cell k.cut
        (by simpa only [k.first] using hc0.le) (by simpa only [k.last] using hc1)
      have hi : k.cut i.castSucc < c := lt_of_le_of_ne hi₀ (by
        intro he; exact hck ((mem_fieldCutSet k c).mpr ⟨i.castSucc, he⟩))
      refine ⟨fieldInsertCut k i c hi hi₁, FieldRefines.insert hk i c hi hi₁, ?_⟩
      rw [fieldCutSet_insertCut, hcuts]
      ext s
      simp only [Finset.mem_insert, Finset.mem_union]
      tauto

lemma field_cutList_eq_of_set_eq {h k : FieldStep} (he : fieldCutSet h = fieldCutSet k) :
    List.ofFn h.cut = List.ofFn k.cut := by
  have hh : (List.ofFn h.cut).SortedLT :=
    List.sortedLT_iff_pairwise.mpr (List.pairwise_ofFn.mpr h.ordered_cut)
  have hk : (List.ofFn k.cut).SortedLT :=
    List.sortedLT_iff_pairwise.mpr (List.pairwise_ofFn.mpr k.ordered_cut)
  apply hh.eq_of_mem_iff hk
  intro s
  have hs := Finset.ext_iff.mp he s
  simpa only [mem_fieldCutSet, List.mem_ofFn] using hs

lemma field_common_refinement (h k : FieldStep) :
    ∃ h' k', FieldRefines h h' ∧ FieldRefines k k' ∧
      List.ofFn h'.cut = List.ofFn k'.cut := by
  obtain ⟨h', hh', hhcut⟩ := field_exists_refinement h (fieldCutSet k)
    (fun _ hs => fieldCutSet_bounds k hs)
  obtain ⟨k', hk', hkcut⟩ := field_exists_refinement k (fieldCutSet h)
    (fun _ hs => fieldCutSet_bounds h hs)
  refine ⟨h', k', hh', hk', field_cutList_eq_of_set_eq ?_⟩
  rw [hhcut, hkcut, Finset.union_comm]

end InvariantIsing

end

end OAI
