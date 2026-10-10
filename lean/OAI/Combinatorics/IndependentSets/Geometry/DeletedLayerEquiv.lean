import Mathlib
import OAI.Combinatorics.IndependentSets.Reduction.Small
import OAI.Combinatorics.IndependentSets.Reduction.SubchainView
import OAI.Combinatorics.IndependentSets.Reduction.ArbitraryRealJunta

namespace OAI

namespace LargeIndependentSets
open MeasureTheory ProductAveraging PhaseTest
open scoped BigOperators Classical NNReal

def deletedLayerEquiv {n : ℕ} {B : Finset (Fin (n+1))} (i : B) :
    {j : B // j ≠ i} ≃ (B.erase i.val) where
  toFun j := ⟨j.val.val, Finset.mem_erase.mpr ⟨fun h => j.property (Subtype.ext h), j.val.property⟩⟩
  invFun j := ⟨⟨j.val, (Finset.mem_erase.mp j.property).2⟩,
    fun h => (Finset.mem_erase.mp j.property).1 (congrArg Subtype.val h)⟩
  left_inv j := by cases j; rfl
  right_inv j := by cases j; rfl

def deletedCoordEquiv {L R : Type} {n : ℕ} {B : Finset (Fin (n+1))} (i : B) :
    (Sigma fun j : {j : B // j ≠ i} => MixedTuple L R n j.val.val.val) ≃
      SubchainCoord L R n (B.erase i.val) where
  toFun d := ⟨deletedLayerEquiv i d.1, d.2⟩
  invFun d := ⟨(deletedLayerEquiv i).symm d.1, d.2⟩
  left_inv d := by cases d; rfl
  right_inv d := by cases d; rfl

lemma deletion_nonempty {n : ℕ} {B : Finset (Fin (n+1))} (hB : 2 ≤ B.card) (i : B) :
    (B.erase i.val).Nonempty := by
  apply Finset.card_pos.mp
  rw [Finset.card_erase_of_mem i.property]
  omega

lemma deletion_small {n s : ℕ} {B : Finset (Fin (n+1))} (hB : 2 ≤ B.card) (hBs : B.card ≤ s)
    (i : B) : Small s (B.erase i.val) :=
  ⟨deletion_nonempty hB i, (Finset.card_le_card (Finset.erase_subset _ _)).trans hBs⟩

lemma junta_error_reindex {α β : Type} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] (e : α ≃ β) (S : Finset β)
    (f : (β → ℝ) → ℝ) (hf : Measurable f) :
    (∫ θ, (f (reindex e θ) -
      average rotationLaw (S.image e.symm) (f ∘ reindex e) θ)^2
      ∂Measure.pi (fun _ : α => rotationLaw)) =
    ∫ θ, (f θ - average rotationLaw S f θ)^2
      ∂Measure.pi (fun _ : β => rotationLaw) := by
  have hS : (S.image e.symm).image e = S := by simp [Finset.image_image]
  simp_rw [average_reindex rotationLaw e _ hf, hS]
  exact integral_preserving (reindex_preserving rotationLaw e)
    ((hf.sub (average_measurable rotationLaw S hf)).pow_const 2).aestronglyMeasurable

end LargeIndependentSets

end OAI
