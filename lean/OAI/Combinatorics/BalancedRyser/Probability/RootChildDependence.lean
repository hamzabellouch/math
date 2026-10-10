import OAI.Combinatorics.BalancedRyser.Probability.RootChildCount

namespace OAI

namespace Balanced.RootChildPartition

open scoped BigOperators

def touchedPositions (J : Finset (Fin 4)) : Finset (Fin 4) :=
  Finset.univ.filter fun i => i ∈ J ∨ i + 1 ∈ J

theorem card_touchedPositions_of_card_le_one (J : Finset (Fin 4)) (hJ : J.card ≤ 1) :
    (touchedPositions J).card = 2 * J.card := by
  have h : ∀ K : Finset (Fin 4), K.card ≤ 1 →
      (touchedPositions K).card = 2 * K.card := by decide
  exact h J hJ

def rootGeneratorIndices {b κ : ℕ} (P : Local.EqualityPattern b κ)
    (R : Finset (Fin b)) (i : Fin b) : Finset (Fin 4) :=
  Finset.univ.filter fun j => P.classOf i j ∈ R.biUnion P.classSet

theorem card_rootGeneratorIndices {b κ : ℕ} (P : Local.EqualityPattern b κ)
    (R : Finset (Fin b)) (i : Fin b) :
    (rootGeneratorIndices P R i).card = (P.classSet i ∩ R.biUnion P.classSet).card := by
  have he : (rootGeneratorIndices P R i).image (P.classOf i) =
      P.classSet i ∩ R.biUnion P.classSet := by
    ext a
    simp only [rootGeneratorIndices, Local.EqualityPattern.classSet,
      Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_inter]
    constructor
    · rintro ⟨j, hj, rfl⟩
      exact ⟨⟨j, rfl⟩, hj⟩
    · rintro ⟨⟨j, rfl⟩, hj⟩
      exact ⟨j, hj, rfl⟩
  rw [← he, Finset.card_image_of_injective _ (P.withinTuple i)]

def dependentOccurrences {b κ : ℕ} (P : Local.EqualityPattern b κ)
    (R : Finset (Fin b)) : Finset (Fin b × Fin 4) :=
  (Finset.univ \ R).biUnion fun i =>
    (touchedPositions (rootGeneratorIndices P R i)).image fun j => (i, j)

@[simp] theorem mem_dependentOccurrences {b κ : ℕ} (P : Local.EqualityPattern b κ)
    (R : Finset (Fin b)) (ij : Fin b × Fin 4) :
    ij ∈ dependentOccurrences P R ↔ ij.1 ∉ R ∧
      (P.classOf ij.1 ij.2 ∈ R.biUnion P.classSet ∨
        P.classOf ij.1 (ij.2 + 1) ∈ R.biUnion P.classSet) := by
  rcases ij with ⟨i, j⟩
  simp [dependentOccurrences, touchedPositions, rootGeneratorIndices]

theorem card_dependentOccurrences {b κ : ℕ} (P : Local.EqualityPattern b κ)
    (R : Finset (Fin b))
    (hchild : ∀ i, i ∉ R → (P.classSet i ∩ R.biUnion P.classSet).card = 1) :
    (dependentOccurrences P R).card = 2 * (Finset.univ \ R).card := by
  unfold dependentOccurrences
  rw [Finset.card_biUnion]
  · calc
      (∑ i ∈ Finset.univ \ R,
          ((touchedPositions (rootGeneratorIndices P R i)).image fun j => (i, j)).card) =
          ∑ _i ∈ Finset.univ \ R, 2 := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.card_image_of_injective _ (fun _ _ h => (Prod.mk.inj h).2)]
        have hc : (rootGeneratorIndices P R i).card = 1 := by
          rw [card_rootGeneratorIndices, hchild i (Finset.mem_sdiff.mp hi).2]
        rw [card_touchedPositions_of_card_le_one _ hc.le, hc]
      _ = _ := by simp [Nat.mul_comm]
  · intro i hi j hj hij
    apply Finset.disjoint_left.mpr
    intro a hai haj
    obtain ⟨x, hx, hxa⟩ := Finset.mem_image.mp hai
    obtain ⟨y, hy, hya⟩ := Finset.mem_image.mp haj
    exact hij (congrArg Prod.fst (hxa.trans hya.symm))

theorem exists_roots_with_exact_dependent_budget {b κ : ℕ}
    (P : Local.EqualityPattern b κ) (hb : 3 ≤ b) (hκ : κ ≤ 2) :
    ∃ R : Finset (Fin b), DisjointRoots P.classSet R ∧
      (Finset.univ \ R).card = κ ∧
      (dependentOccurrences P R).card = 2 * κ ∧
      ∀ i, i ∉ R →
        (P.classSet i ∩ R.biUnion P.classSet).card = 1 ∧
        P.classSet i ∩ (Finset.univ.erase i).biUnion P.classSet ⊆
          R.biUnion P.classSet := by
  obtain ⟨R, hr, hc, hchildren⟩ := exists_pattern_roots_exact_of_three_le P hb hκ
  refine ⟨R, hr, hc, ?_, hchildren⟩
  rw [card_dependentOccurrences P R (fun i hi => (hchildren i hi).1), hc]

end Balanced.RootChildPartition

end OAI
