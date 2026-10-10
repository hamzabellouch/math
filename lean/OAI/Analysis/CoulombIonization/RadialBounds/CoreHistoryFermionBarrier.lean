import Mathlib
import OAI.Analysis.CoulombIonization.Localization.CoreHistoryCoordinatesBarrier

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter
open scoped BigOperators

namespace CoulombAtom

lemma leftList_corePerm {α : Type*} {N M : ℕ} (x : Fin (N+M) → α)
    (π : Equiv.Perm (Fin N)) : leftList (x ∘ corePerm M π) = leftList x ∘ π := by
  funext i
  simp [leftList,corePerm]

lemma leftList_liftCoreOrder {α : Type*} {K N M : ℕ} (e : Fin K ≃ Fin N)
    (x : Fin (K+M) → α) :
    leftList (x ∘ (liftCoreOrder M e).symm) = leftList x ∘ e.symm := by
  funext i
  simp only [leftList,Function.comp_apply,liftCoreOrder_symm,liftCoreOrder_left]

lemma repeatedCutForm_value {N M : ℕ} (p : Fin 2 → SmoothMultiplier spaceDirections)
    (hp : ∀ x, ∑ a, (p a).value x^2 = 1) (ψ : FormVector (N+M)) (c : Fin N → Fin 2)
    (s : Spins ((cutCoreNumber c+cutOutNumber c)+M)) (x) :
    (repeatedCutForm p hp ψ c).value s x =
      (spatialProductValue p (coreCutLabels (cutCoreNumber c) (cutOutNumber c)) (leftList x) : ℂ)*
        (reindexForm (liftCoreOrder M (cutOrder c)) ψ).value s x := by
  change (spatialProductValue p c (coreLeftLinear N M (x ∘ (liftCoreOrder M (cutOrder c)).symm)) : ℂ)*_ = _
  rw [coreLeftLinear_apply,leftList_liftCoreOrder,spatialProductValue_reindex,cutOrder_labels]
  rfl

lemma nextCoreObservation_value {N M : ℕ} (p : Fin 2 → SmoothMultiplier spaceDirections)
    (hp : ∀ x, ∑ a, (p a).value x^2 = 1) (ψ : FormVector (N+M)) (c : Fin N → Fin 2)
    (s : Spins (cutCoreNumber c+(cutOutNumber c+M))) (x) :
    (nextCoreObservation p hp ψ c).value s x =
      (spatialProductValue p (coreCutLabels (cutCoreNumber c) (cutOutNumber c))
        (leftList (x ∘ (coreObservationAssoc _ _ _).symm)) : ℂ)*
      (reindexForm (coreObservationAssoc _ _ _)
        (reindexForm (liftCoreOrder M (cutOrder c)) ψ)).value s x := by
  exact repeatedCutForm_value p hp ψ c _ _

theorem nextCoreObservation_antisymmetric {N M : ℕ} {ψ : FormVector (N+M)}
    (ha : CoreAntisymmetric ψ) (p : Fin 2 → SmoothMultiplier spaceDirections)
    (hp : ∀ x, ∑ a, (p a).value x^2 = 1) (c : Fin N → Fin 2) :
    CoreAntisymmetric (nextCoreObservation p hp ψ c) := by
  have hh := (ha.reindex_lift (cutOrder c)).observation_order
    (N := cutCoreNumber c) (K := cutOutNumber c)
  intro π s
  filter_upwards [hh π s] with x hx
  rw [nextCoreObservation_value,nextCoreObservation_value,
    coreObservationAssoc_perm_comp,leftList_corePerm,
    spatialProduct_invariant p _ (corePerm _ π) (coreCutLabels_invariant π),hx]
  ring

end CoulombAtom

end

end OAI
