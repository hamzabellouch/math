import Mathlib
import OAI.Analysis.CoulombIonization.Variational.CutCoreNumber
import OAI.Analysis.CoulombIonization.Variational.BlockSwap

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter
open scoped BigOperators

namespace CoulombAtom

lemma reindexForm_twice {L M N : ℕ} (e : Fin L ≃ Fin M) (f : Fin M ≃ Fin N)
    (ψ : FormVector N) : reindexForm e (reindexForm f ψ) = reindexForm (e.trans f) ψ := rfl

def outFirstLabels (N M : ℕ) : Fin (M+N) → Fin 2 :=
  joinLists (fun _ : Fin M => 1) (fun _ : Fin N => 0)

lemma coreCutLabels_blockSwap (N M : ℕ) :
    coreCutLabels N M ∘ blockSwap N M = outFirstLabels N M := by
  funext i
  obtain ⟨j,rfl⟩ := finSumFinEquiv.surjective i
  rcases j with j | j <;>
    simp only [Function.comp_apply,blockSwap_left,blockSwap_right,coreCutLabels,
      outFirstLabels,joinLists_left,joinLists_right]

lemma outFirstLabels_invariant {N M : ℕ} (π : Equiv.Perm (Fin M)) :
    outFirstLabels N M ∘ corePerm N π = outFirstLabels N M := by
  change joinLists (fun _ : Fin M => (1 : Fin 2)) (fun _ : Fin N => 0) ∘ corePerm N π = _
  rw [joinLists_corePerm]
  rfl

lemma swapBlocks_ordered_value {L : ℕ} (p : Fin 2 → SmoothMultiplier spaceDirections)
    (hp : ∀ x, ∑ a : Fin 2, (p a).value x^2 = 1) (ψ : FormVector L)
    (c : Fin L → Fin 2) (s) (x) :
    (swapBlocks (orderedCutForm p hp ψ c)).value s x =
      (multiplyForm (spatialProduct p hp (outFirstLabels (cutCoreNumber c) (cutOutNumber c)))
        (reindexForm ((blockSwap (cutCoreNumber c) (cutOutNumber c)).trans (cutOrder c)) ψ)).value s x := by
  change (spatialProductValue p c ((x ∘ (blockSwap _ _).symm) ∘ (cutOrder c).symm) : ℂ) * _ = _
  rw [spatialProductValue_reindex,spatialProductValue_reindex,cutOrder_labels,coreCutLabels_blockSwap]
  rfl

lemma orderedCutForm_out_antisymmetric {L : ℕ} (p : Fin 2 → SmoothMultiplier spaceDirections)
    (hp : ∀ x, ∑ a : Fin 2, (p a).value x^2 = 1)
    {ψ : FormVector L} (hψ : SobolevFermion ψ) (c : Fin L → Fin 2) :
    CoreAntisymmetric (swapBlocks (orderedCutForm p hp ψ c)) := by
  have ha := (hψ.reindex ((blockSwap _ _).trans (cutOrder c))).coreAntisymmetric.multiply
    (spatialProduct p hp (outFirstLabels (cutCoreNumber c) (cutOutNumber c)))
    (fun π x => spatialProduct_invariant p _ (corePerm _ π) (outFirstLabels_invariant π) x)
  intro π s
  simpa only [swapBlocks_ordered_value] using ha π s

end CoulombAtom

end

end OAI
