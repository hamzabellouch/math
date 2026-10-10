import OAI.Probability.SpanningForest.Definitions

namespace OAI

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Problem336.USTInclusionCount

def edgePairs (A : Finset EdgeCode) : Finset (ℕ × ℕ) :=
  A.map (Function.Embedding.subtype (fun p : ℕ × ℕ => p.1 < p.2))

@[simp] theorem edgePairs_card (A : Finset EdgeCode) : (edgePairs A).card = A.card :=
  Finset.card_map _

@[simp] theorem edgePairs_subset_iff (A : Finset EdgeCode) (T : Finset (ℕ × ℕ)) :
    edgePairs A ⊆ T ↔ ∀ e ∈ A, e.val ∈ T := by
  simp [edgePairs, Finset.subset_iff]

theorem ustCylinder_positive_toReal (K : FiniteSubgraphCode) (A : Finset EdgeCode) :
    (ustCylinder K A ∅).toReal =
      (((spanningTrees K).filter (fun T => edgePairs A ⊆ T)).card : ℝ) /
        ((spanningTrees K).card : ℝ) := by
  classical
  simp [ustCylinder, edgePairs_subset_iff, ENNReal.toReal_div]

theorem ustCylinder_positive_eq (K : FiniteSubgraphCode) (A : Finset EdgeCode) :
    ustCylinder K A ∅ =
      (((spanningTrees K).filter (fun T => edgePairs A ⊆ T)).card : ℝ≥0∞) /
        ((spanningTrees K).card : ℝ≥0∞) := by
  classical
  simp [ustCylinder, edgePairs_subset_iff]

def supportedPairs (K : FiniteSubgraphCode) (A : Finset EdgeCode) : Finset K.2 :=
  (edgePairs A).subtype (fun p => p ∈ K.2)

theorem supportedPairs_map (K : FiniteSubgraphCode) (A : Finset EdgeCode)
    (hA : ∀ e ∈ A, e.val ∈ K.2) :
    (supportedPairs K A).map (Function.Embedding.subtype (fun p => p ∈ K.2)) =
      edgePairs A :=
  Finset.subtype_map_of_mem (fun _ hp => (edgePairs_subset_iff A K.2).mpr hA hp)

def requiredEdgeEquiv (K : FiniteSubgraphCode) (A : Finset EdgeCode)
    (hA : ∀ e ∈ A, e.val ∈ K.2) : A ≃ supportedPairs K A :=
  Equiv.ofBijective
    (fun e => ⟨⟨e.val.val, hA e.val e.property⟩,
      Finset.mem_subtype.mpr (Finset.mem_map.mpr ⟨e.val, e.property, rfl⟩)⟩)
    ⟨by
      intro a b hab
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun p : supportedPairs K A => p.val.val) hab,
     by
      intro p
      obtain ⟨e, he, hep⟩ := Finset.mem_map.mp (Finset.mem_subtype.mp p.property)
      refine ⟨⟨e, he⟩, ?_⟩
      apply Subtype.ext
      exact Subtype.ext hep⟩

@[simp] theorem requiredEdgeEquiv_val (K : FiniteSubgraphCode) (A : Finset EdgeCode)
    (hA : ∀ e ∈ A, e.val ∈ K.2) (e : A) :
    (requiredEdgeEquiv K A hA e).val.val = e.val.val := rfl

theorem supportedPairs_card (K : FiniteSubgraphCode) (A : Finset EdgeCode)
    (hA : ∀ e ∈ A, e.val ∈ K.2) : (supportedPairs K A).card = A.card := by
  simpa only [Fintype.card_coe] using (Fintype.card_congr (requiredEdgeEquiv K A hA)).symm

theorem supportedPairs_inclusion_iff (K : FiniteSubgraphCode) (A : Finset EdgeCode)
    (hA : ∀ e ∈ A, e.val ∈ K.2) (T : Finset (ℕ × ℕ)) :
    (∀ e ∈ supportedPairs K A, e.val ∈ T) ↔ edgePairs A ⊆ T := by
  rw [← supportedPairs_map K A hA]
  simp [Finset.subset_iff]

theorem det_required_reindex {R : Type*} [CommRing R]
    (K : FiniteSubgraphCode) (A : Finset EdgeCode)
    (hA : ∀ e ∈ A, e.val ∈ K.2) (M : Matrix K.2 K.2 R) :
    Matrix.det (fun e f : A =>
      M ⟨e.val.val, hA e.val e.property⟩ ⟨f.val.val, hA f.val f.property⟩) =
      Matrix.det (M.submatrix
        (Subtype.val : supportedPairs K A → K.2)
        (Subtype.val : supportedPairs K A → K.2)) := by
  exact Matrix.det_submatrix_equiv_self (requiredEdgeEquiv K A hA)
    (M.submatrix Subtype.val Subtype.val)

end Problem336.USTInclusionCount

end

end OAI
