import OAI.NumberTheory.DukePrimeDegree.Dynamics.EuclideanVelocityProjection
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.EquivFin

namespace OAI

/-!
# Finite frame selection by Gram determinants

The projected coordinate vectors form a finite measurable spanning family.
Maximal nonzero Gram minors select a basis from that family. All tests used
in the selection are measurable real determinants, so this does not assume
a measurable tangent-frame theorem.
-/

noncomputable section
open MeasureTheory Set Matrix
open scoped BigOperators InnerProductSpace

namespace DukePrimeDegree

section GramFrames

variable {I E : Type*} [Fintype I] [DecidableEq I]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def finiteGramDet (v : I → E) (S : Finset I) : ℝ :=
  (Matrix.gram ℝ (fun i : S => v i)).det

def IsMaximalGramFrame (v : I → E) (S : Finset I) : Prop :=
  finiteGramDet v S ≠ 0 ∧
    ∀ T : Finset I, S.card < T.card → finiteGramDet v T = 0

theorem exists_maximalGramFrame (v : I → E) : ∃ S, IsMaximalGramFrame v S := by
  classical
  let F := Finset.univ.filter (fun S : Finset I => finiteGramDet v S ≠ 0)
  have hF : F.Nonempty := by
    refine ⟨∅, ?_⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    let : IsEmpty (↑(∅ : Finset I)) := ⟨fun i => Finset.notMem_empty i.val i.property⟩
    simp only [finiteGramDet, Matrix.det_isEmpty, ne_eq, one_ne_zero, not_false_eq_true]
  obtain ⟨S, hS, hmax⟩ := F.exists_max_image Finset.card hF
  refine ⟨S, (Finset.mem_filter.mp hS).2, ?_⟩
  intro T hST
  by_contra hT
  have hTF : T ∈ F := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hT⟩
  exact (not_lt_of_ge (hmax T hTF)) hST

omit [Fintype I] in
theorem IsMaximalGramFrame.linearIndependent {v : I → E} {S : Finset I}
    (hS : IsMaximalGramFrame v S) : LinearIndependent ℝ (fun i : S => v i) :=
  Matrix.linearIndependent_of_det_gram_ne_zero hS.1

omit [Fintype I] in
theorem IsMaximalGramFrame.span_eq {v : I → E} {S : Finset I}
    (hS : IsMaximalGramFrame v S) :
    Submodule.span ℝ (v '' (S : Set I)) = Submodule.span ℝ (Set.range v) := by
  apply le_antisymm
  · exact Submodule.span_mono (Set.image_subset_range _ _)
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    by_contra hi
    have hiS : i ∉ S := by
      intro hiS
      exact hi (Submodule.subset_span ⟨i, hiS, rfl⟩)
    have hli : LinearIndepOn ℝ v (S : Set I) := hS.linearIndependent
    have hins : LinearIndepOn ℝ v (insert i (S : Set I)) :=
      (linearIndepOn_insert hiS).mpr ⟨hli, hi⟩
    have hdet : finiteGramDet v (insert i S) ≠ 0 := by
      apply Matrix.det_gram_ne_zero_iff_linearIndependent.mpr
      let e : ↥(insert i S) → ↑(insert i (S : Set I)) := fun x =>
        ⟨x.val, by
          rcases Finset.mem_insert.mp x.property with h | h
          · exact Or.inl h
          · exact Or.inr h⟩
      have hlin : LinearIndependent ℝ (fun x : ↑(insert i (S : Set I)) => v x) := hins
      apply hlin.comp e
      intro x y h
      apply Subtype.ext
      exact congrArg (fun z : ↑(insert i (S : Set I)) => z.val) h
    have hcard : S.card < (insert i S).card := by
      rw [Finset.card_insert_of_notMem hiS]
      exact Nat.lt_succ_self _
    exact hdet (hS.2 _ hcard)

private def frameEnumeration (I : Type*) [Fintype I] [DecidableEq I]
    (k : ℕ) : Finset I :=
  if hk : k < Fintype.card (Finset I) then
    (Fintype.equivFin (Finset I)).symm ⟨k, hk⟩ else ∅

private theorem frameEnumeration_surjective (S : Finset I) :
    ∃ k, frameEnumeration I k = S := by
  let k := Fintype.equivFin (Finset I) S
  refine ⟨k.val, ?_⟩
  simp only [frameEnumeration, k.isLt, dite_true]
  exact (Fintype.equivFin (Finset I)).symm_apply_apply S

private theorem exists_maximalGramFrameIndex (v : I → E) :
    ∃ k, IsMaximalGramFrame v (frameEnumeration I k) := by
  obtain ⟨S, hS⟩ := exists_maximalGramFrame v
  obtain ⟨k, hk⟩ := frameEnumeration_surjective S
  exact ⟨k, hk.symm ▸ hS⟩

def maximalGramFrameIndex (v : I → E) : ℕ := by
  classical
  exact Nat.find (exists_maximalGramFrameIndex v)

def maximalGramFrame (v : I → E) : Finset I :=
  frameEnumeration I (maximalGramFrameIndex v)

theorem maximalGramFrame_spec (v : I → E) :
    IsMaximalGramFrame v (maximalGramFrame v) := by
  classical
  exact Nat.find_spec (exists_maximalGramFrameIndex v)

def finiteFrameVector (v : I → E) (S : Finset I) (j : ℕ) : E :=
  if hj : j < S.card then v ((S.equivFin.symm ⟨j, hj⟩).val) else 0

def selectedFrameVector (v : I → E) (j : ℕ) : E :=
  finiteFrameVector v (maximalGramFrame v) j

theorem selectedFrameVector_linearIndependent (v : I → E) :
    LinearIndependent ℝ (fun j : Fin (maximalGramFrame v).card =>
      selectedFrameVector v j) := by
  have hli := (maximalGramFrame_spec v).linearIndependent
  have heq : (fun j : Fin (maximalGramFrame v).card => selectedFrameVector v j) =
      (fun i : maximalGramFrame v => v i) ∘ (maximalGramFrame v).equivFin.symm := by
    funext j
    simp only [selectedFrameVector, finiteFrameVector, j.isLt, dite_true, Function.comp_def]
  rw [heq]
  exact hli.comp _ (maximalGramFrame v).equivFin.symm.injective

theorem selectedFrameVector_span (v : I → E) :
    Submodule.span ℝ (Set.range (fun j : Fin (maximalGramFrame v).card =>
      selectedFrameVector v j)) = Submodule.span ℝ (Set.range v) := by
  have hrange : Set.range (fun j : Fin (maximalGramFrame v).card =>
      selectedFrameVector v j) = v '' (maximalGramFrame v : Set I) := by
    ext x
    constructor
    · rintro ⟨j, rfl⟩
      simp only [selectedFrameVector, finiteFrameVector, j.isLt, dite_true]
      exact ⟨_, ((maximalGramFrame v).equivFin.symm j).property, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      refine ⟨(maximalGramFrame v).equivFin ⟨i, hi⟩, ?_⟩
      simp only [selectedFrameVector, finiteFrameVector,
        ((maximalGramFrame v).equivFin ⟨i, hi⟩).isLt, dite_true]
      change v (((maximalGramFrame v).equivFin.symm
        ((maximalGramFrame v).equivFin ⟨i, hi⟩)).val) = v i
      rw [Equiv.symm_apply_apply]
  rw [hrange]
  exact (maximalGramFrame_spec v).span_eq

theorem maximalGramFrame_card (v : I → E) :
    (maximalGramFrame v).card = Module.finrank ℝ (Submodule.span ℝ (Set.range v)) := by
  have h := finrank_span_eq_card (selectedFrameVector_linearIndependent v)
  rw [selectedFrameVector_span, Fintype.card_fin] at h
  exact h.symm

theorem maximalGramFrame_card_of_span_transport (v w : I → E)
    (A : E ≃ₗ[ℝ] E)
    (hspan : Submodule.span ℝ (Set.range w) =
      (Submodule.span ℝ (Set.range v)).map A.toLinearMap) :
    (maximalGramFrame w).card = (maximalGramFrame v).card := by
  rw [maximalGramFrame_card, maximalGramFrame_card, hspan, A.finrank_map_eq]

end GramFrames

section Measurability

variable {Z I E : Type*} [MeasurableSpace Z] [Fintype I] [DecidableEq I]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

theorem measurable_finiteGramDet (v : Z → I → E)
    (hv : ∀ i, Measurable (fun z => v z i)) (S : Finset I) :
    Measurable (fun z => finiteGramDet (v z) S) := by
  have hm : Measurable (fun z => Matrix.gram ℝ (fun i : S => v z i)) := by
    apply measurable_pi_iff.mpr
    intro i
    apply measurable_pi_iff.mpr
    intro j
    exact (hv i).inner (hv j)
  exact continuous_id.matrix_det.measurable.comp hm

theorem measurableSet_isMaximalGramFrame (v : Z → I → E)
    (hv : ∀ i, Measurable (fun z => v z i)) (S : Finset I) :
    MeasurableSet {z | IsMaximalGramFrame (v z) S} := by
  apply MeasurableSet.inter
  · exact (measurableSet_eq_fun (measurable_finiteGramDet v hv S) measurable_const).compl
  · change MeasurableSet {z | ∀ T : Finset I, S.card < T.card → finiteGramDet (v z) T = 0}
    rw [Set.ofPred_forall]
    apply MeasurableSet.iInter
    intro T
    by_cases hST : S.card < T.card
    · simpa only [hST, true_implies] using
        measurableSet_eq_fun (measurable_finiteGramDet v hv T) measurable_const
    · simp only [hST, false_implies, Set.ofPred_true]
      exact MeasurableSet.univ

theorem measurable_maximalGramFrameIndex (v : Z → I → E)
    (hv : ∀ i, Measurable (fun z => v z i)) :
    Measurable (fun z => maximalGramFrameIndex (v z)) := by
  classical
  exact measurable_find (fun z => exists_maximalGramFrameIndex (v z))
    (fun k => measurableSet_isMaximalGramFrame v hv (frameEnumeration I k))

theorem measurableSet_maximalGramFrame_eq (v : Z → I → E)
    (hv : ∀ i, Measurable (fun z => v z i)) (S : Finset I) :
    MeasurableSet {z | maximalGramFrame (v z) = S} := by
  have hpre : MeasurableSet {k : ℕ | frameEnumeration I k = S} :=
    (Set.to_countable _).measurableSet
  exact (measurable_maximalGramFrameIndex v hv) hpre

theorem measurable_selectedFrameVector (v : Z → I → E)
    (hv : ∀ i, Measurable (fun z => v z i)) (j : ℕ) :
    Measurable (fun z => selectedFrameVector (v z) j) := by
  classical
  have hm (k : ℕ) : Measurable (fun z =>
      finiteFrameVector (v z) (frameEnumeration I k) j) := by
    by_cases hj : j < (frameEnumeration I k).card
    · simpa only [finiteFrameVector, hj, dite_true] using
        hv (((frameEnumeration I k).equivFin.symm ⟨j, hj⟩).val)
    · simpa only [finiteFrameVector, hj, dite_false] using
        (measurable_const : Measurable (fun _ : Z => (0 : E)))
  exact Measurable.find hm
    (fun k => measurableSet_isMaximalGramFrame v hv (frameEnumeration I k))
    (fun z => exists_maximalGramFrameIndex (v z))

theorem measurable_selectedFrameCard (v : Z → I → E)
    (hv : ∀ i, Measurable (fun z => v z i)) :
    Measurable (fun z => (maximalGramFrame (v z)).card) := by
  exact (measurable_from_nat : Measurable (fun k => (frameEnumeration I k).card)).comp
    (measurable_maximalGramFrameIndex v hv)

end Measurability

end DukePrimeDegree

end

end OAI
