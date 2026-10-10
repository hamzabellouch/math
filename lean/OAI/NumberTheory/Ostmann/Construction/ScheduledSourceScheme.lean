import OAI.NumberTheory.Ostmann.Construction.AtomAncestorSources
import OAI.NumberTheory.Ostmann.Characters.TreeAncestorScheme
import OAI.NumberTheory.Ostmann.Arithmetic.SingleFrequencyModulus
import OAI.NumberTheory.Ostmann.Arithmetic.SampledHistoryEnergy

namespace OAI

namespace Ostmann
open scoped BigOperators Classical

theorem ancestorNodeIndex_injective (n : ℕ) (j : Fin (2 ^ n - 1)) :
    Function.Injective (ancestorNodeIndex n j) := by
  intro a b h
  have he := congrArg (fun i => (preorderNodePath n i).length) h
  rw [ancestorNodeIndex_path, ancestorNodeIndex_path, List.length_take, List.length_take,
    min_eq_left a.isLt.le, min_eq_left b.isLt.le] at he
  exact Fin.ext he

section
variable {I B : Type*} [Fintype I]
variable (role : I → CopyScheduleRole) (S : Finset ℤ) (n : ℕ) (t : FrequencyTree S n)
variable (left right : (j : Fin (2 ^ n - 1)) →
  CopyScheduleH role (n - ((preorderNodePath n j).length + 1)) →
    B ⊕ Fin (preorderNodePath n j).length)
variable (C : B → ℤ)

/-- Every ancestor is a genuine proper prefix of this node. The source
products are constructed from H slots, rather than assumed coefficients. -/
noncomputable def scheduledSourceScheme : PivotDependencyScheme (2 ^ n - 1) where
  frequencies j := singleTreeNodeFrequencies S n t j.val
  depth j := (preorderNodePath n j).length
  fixedLeft j := atomFixedProduct (left j) C
  fixedRight j := atomFixedProduct (right j) C
  ancestorsLeft j := (atomAncestorSet (left j)).image (ancestorNodeIndex n j)
  ancestorsRight j := (atomAncestorSet (right j)).image (ancestorNodeIndex n j)
  earlierLeft j i hi := by
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hi
    exact ancestorNodeIndex_earlier n j a
  earlierRight j i hi := by
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hi
    exact ancestorNodeIndex_earlier n j a

theorem scheduledSourceScheme_left
    (hinj : ∀ j, Function.Injective (left j))
    (p : Fin (2 ^ n - 1) → ℤ) (j : Fin (2 ^ n - 1)) :
    (scheduledSourceScheme role S n t left right C).leftCoefficient p j =
      ∏ h : CopyScheduleH role (n - ((preorderNodePath n j).length + 1)),
        Sum.elim C (fun a => p (ancestorNodeIndex n j a)) (left j h) := by
  change atomFixedProduct (left j) C *
    (∏ i ∈ (atomAncestorSet (left j)).image (ancestorNodeIndex n j), p i) = _
  rw [Finset.prod_image (ancestorNodeIndex_injective n j).injOn]
  exact (atomSource_product (left j) (hinj j) C (fun a => p (ancestorNodeIndex n j a))).symm

theorem scheduledSourceScheme_right
    (hinj : ∀ j, Function.Injective (right j))
    (p : Fin (2 ^ n - 1) → ℤ) (j : Fin (2 ^ n - 1)) :
    (scheduledSourceScheme role S n t left right C).rightCoefficient p j =
      ∏ h : CopyScheduleH role (n - ((preorderNodePath n j).length + 1)),
        Sum.elim C (fun a => p (ancestorNodeIndex n j a)) (right j h) := by
  change atomFixedProduct (right j) C *
    (∏ i ∈ (atomAncestorSet (right j)).image (ancestorNodeIndex n j), p i) = _
  rw [Finset.prod_image (ancestorNodeIndex_injective n j).injOn]
  exact (atomSource_product (right j) (hinj j) C (fun a => p (ancestorNodeIndex n j a))).symm

theorem scheduledSourceScheme_depth (j : Fin (2 ^ n - 1)) :
    (scheduledSourceScheme role S n t left right C).depth j ≤ n :=
  (preorderNodePath_length n j).le

theorem scheduledSourceScheme_root_ne_zero (hS : ∀ s ∈ S, s ≠ 0)
    (j : Fin (2 ^ n - 1)) :
    ((scheduledSourceScheme role S n t left right C).frequencies j).root ≠ 0 :=
  hS _ (singleTreeNodeFrequencies_root_mem S n t j.val j.isLt)

theorem scheduledSourceScheme_frequency_dvd (j : Fin (2 ^ n - 1)) :
    ((scheduledSourceScheme role S n t left right C).frequencies j).root.natAbs ∣
      historyFrequencyProduct S n t := by
  apply history_node_dvd_frequencyProduct S n t
  change singleTreeNodeFrequencies S n t j.val ∈ singleFrequencySplitList S n t
  rw [singleTreeNodeFrequencies, List.getD_eq_getElem _ _ (by
    simpa only [singleFrequencySplitList_length] using j.isLt)]
  exact List.getElem_mem _

/-- Literal integer node relations and coefficient units give the sampled
history used by the existing residue-support estimate. -/
theorem scheduledSourceScheme_valid
    (hinjL : ∀ j, Function.Injective (left j))
    (hinjR : ∀ j, Function.Injective (right j))
    (Q : ℕ) (a : SampledPivotHistory n Q)
    (hnode : ∀ j : Fin (2 ^ n - 1),
      let f := singleTreeNodeFrequencies S n t j.val
      let L := ∏ h, Sum.elim C (fun b => a.pivots (ancestorNodeIndex n j b)) (left j h)
      let R := ∏ h, Sum.elim C (fun b => a.pivots (ancestorNodeIndex n j b)) (right j h)
      f.left * L * a.rightProduct j - f.right * R * a.leftProduct j = f.root * a.pivots j ∧
        IsCoprime L f.root ∧ IsCoprime R f.root) :
    a.valid (scheduledSourceScheme role S n t left right C) := by
  constructor
  · intro j
    rw [scheduledSourceScheme_left role S n t left right C hinjL,
      scheduledSourceScheme_right role S n t left right C hinjR]
    exact (hnode j).1
  · intro j
    rw [scheduledSourceScheme_left role S n t left right C hinjL,
      scheduledSourceScheme_right role S n t left right C hinjR]
    exact (hnode j).2

end
end Ostmann

end OAI
