import OAI.Combinatorics.BalancedRyser.Local.AlignedGlobalProduct
import OAI.Combinatorics.BalancedRyser.Local.AlignedProjectedExposure

namespace OAI

namespace Balanced.AlignedListProbability
open TupleAlignment PartialAlignment
noncomputable section
open scoped Classical
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem generatedPositions_reconstruct (d : Fin 4 → Direction F)
    (hd : ∀ i, d i ≠ d (i+1)) (σ : Fin 4 → Bool)
    (g : Direction F) (hg : ∀ i, d i ≠ g) (c : F)
    (J : Finset (Fin 4)) (hJ : J.card ≤ 1)
    (a o : Fin 4 → Bool → F) (hold : ∀ j ∈ J, o j = a j)
    (halign : ∀ j, OnLine (tuplePositionEquiv d hd σ o j) (g,c))
    (x : {j : Fin 4 // j ∈ freePositions J} → F)
    (hx : ∀ j, linePointEquiv g c
      ⟨tuplePositionEquiv d hd σ o j.1, halign j.1⟩ = x j) :
    generatedPositions d hd σ g hg c J hJ a x = tuplePositionEquiv d hd σ o := by
  let v : AlignedPartialOffsets d hd σ g c J a := ⟨⟨o,hold⟩,halign⟩
  let e := alignedFreeCoordinatesEquiv d hd σ g hg c J hJ a
  have he : e v = x := funext hx
  have hi : e.symm x = v := by rw [← he]; exact e.symm_apply_apply v
  change tuplePositionEquiv d hd σ (e.symm x).1.1 = _
  rw [hi]

end
end Balanced.AlignedListProbability

namespace Balanced.Local.AlignedGlobal
open RootChildPartition AlignedListProbability TupleAlignment PartialAlignment TokenExposure
noncomputable section
open scoped Classical
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {b κ : ℕ}

def currentOldIndices (P : EqualityPattern b κ) (R : Finset (Fin b))
    (i : Fin b) : Finset (Fin 4) :=
  if i ∈ R then ∅ else rootGeneratorIndices P R i

theorem currentOldIndices_card_le_one (P : EqualityPattern b κ)
    (R : Finset (Fin b))
    (hchild : ∀ i, i ∉ R → (P.classSet i ∩ R.biUnion P.classSet).card = 1)
    (i : Fin b) : (currentOldIndices P R i).card ≤ 1 := by
  by_cases hi : i ∈ R
  · simp [currentOldIndices, hi]
  · rw [currentOldIndices, ite_eq_right hi, card_rootGeneratorIndices, hchild i hi]

def currentFreeIndex (P : EqualityPattern b κ) (R : Finset (Fin b)) (i : Fin b)
    (j : {j : Fin 4 // j ∈ freePositions (currentOldIndices P R i)}) :
    FreeIndex P R := by
  refine ⟨(i,j.1), ?_⟩
  by_cases hi : i ∈ R
  · simp [mem_dependentOccurrences, hi]
  · have hj := j.2
    simp only [freePositions, Finset.mem_filter, Finset.mem_univ, true_and,
      currentOldIndices, ite_eq_right hi, rootGeneratorIndices] at hj
    simp only [mem_dependentOccurrences, hi, not_false_eq_true, true_and, not_or]
    exact hj

theorem generated_current_tuple (P : EqualityPattern b κ) (hκ : κ ≤ 2)
    (R : Finset (Fin b)) (hD : (dependentOccurrences P R).card = 2*κ)
    (bits : Bits b) (p : Point F) (e : DirectionToken b κ ↪ Direction F)
    (i : Fin b) (hJ : (currentOldIndices P R i).card ≤ 1)
    (z : (FreeIndex P R → F) × AlignedUnused.UnusedArray P (tokenInjectionEquiv F b κ e).1)
    (a : Fin 4 → Bool → F)
    (ha : ∀ j ∈ currentOldIndices P R i,
      ((coordinateEquiv P hκ R hD (tokenInjectionEquiv F b κ e).1
        (allTokensDistinct_eligible P _ (tokenInjectionEquiv F b κ e).2) bits p).symm z).1
          (e (Sum.inr (P.classOf i j))) = a j) :
    generatedPositions (tupleDirections P e i) (tupleDirections_adjacent P e i)
      (bits i) (e (Sum.inl i)) (tupleDirections_ne_target P e i)
      (lineEval (e (Sum.inl i)) p) (currentOldIndices P R i) hJ a
      (fun j => z.1 (currentFreeIndex P R i j)) =
      fun j => prescribedPoint P (tokenInjectionEquiv F b κ e).1 bits
        ((coordinateEquiv P hκ R hD (tokenInjectionEquiv F b κ e).1
          (allTokensDistinct_eligible P _ (tokenInjectionEquiv F b κ e).2) bits p).symm z).1
        (i,j) := by
  let A := (tokenInjectionEquiv F b κ e).1
  let hA := allTokensDistinct_eligible P A (tokenInjectionEquiv F b κ e).2
  let E := coordinateEquiv P hκ R hD A hA bits p
  let M := E.symm z
  have hm : ∀ j, OnLine (tuplePositionEquiv (tupleDirections P e i)
      (tupleDirections_adjacent P e i) (bits i)
      (fun k => M.1 (e (Sum.inr (P.classOf i k)))) j)
      (e (Sum.inl i), lineEval (e (Sum.inl i)) p) := fun j => M.2 (i,j)
  apply generatedPositions_reconstruct _ _ _ _ _ _ _ _ a
    (fun k => M.1 (e (Sum.inr (P.classOf i k)))) ha hm
  intro j
  have h := congrFun (congrArg Prod.fst (E.apply_symm_apply z)) (currentFreeIndex P R i j)
  exact h

theorem currentFreeIndex_injective (P : EqualityPattern b κ)
    (R : Finset (Fin b)) (i : Fin b) :
    Function.Injective (currentFreeIndex P R i) := by
  intro j k h
  apply Subtype.ext
  exact congrArg (fun t : FreeIndex P R => t.1.2) h

theorem pointOutput_eq_global {Z : Type*}
    (P : EqualityPattern b κ) (hκ : κ ≤ 2)
    (R : Finset (Fin b)) (hD : (dependentOccurrences P R).card = 2*κ)
    (bits : Bits b) (p : Point F) (e : DirectionToken b κ ↪ Direction F)
    (i : Fin b) (hJ : (currentOldIndices P R i).card ≤ 1)
    (z : (FreeIndex P R → F) × AlignedUnused.UnusedArray P (tokenInjectionEquiv F b κ e).1)
    (a : Z → Fin 4 → Bool → F)
    (x : Z → {j : Fin 4 // j ∈ freePositions (currentOldIndices P R i)} → F)
    (w : Z)
    (ha : ∀ j ∈ currentOldIndices P R i,
      ((coordinateEquiv P hκ R hD (tokenInjectionEquiv F b κ e).1
        (allTokensDistinct_eligible P _ (tokenInjectionEquiv F b κ e).2) bits p).symm z).1
          (e (Sum.inr (P.classOf i j))) = a w j)
    (hx : x w = fun j => z.1 (currentFreeIndex P R i j)) (j : Fin 4) :
    pointOutput P bits p i (currentOldIndices P R i) hJ a x e w j =
      prescribedPoint P (tokenInjectionEquiv F b κ e).1 bits
        ((coordinateEquiv P hκ R hD (tokenInjectionEquiv F b κ e).1
          (allTokensDistinct_eligible P _ (tokenInjectionEquiv F b κ e).2) bits p).symm z).1
        (i,j) := by
  unfold pointOutput
  rw [hx]
  exact congrFun (generated_current_tuple P hκ R hD bits p e i hJ z (a w) ha) j

end
end Balanced.Local.AlignedGlobal

end OAI
