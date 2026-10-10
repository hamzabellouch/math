import Mathlib
import OAI.Analysis.CoulombIonization.RadialBounds.CoreMultiplierLiftBarrier

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter
open scoped BigOperators

namespace CoulombAtom

def coreObservationAssoc (N K M : ℕ) : Fin (N+(K+M)) ≃ Fin ((N+K)+M) :=
  finSumFinEquiv.symm.trans
    ((Equiv.sumCongr (Equiv.refl (Fin N)) finSumFinEquiv.symm).trans
      ((Equiv.sumAssoc (Fin N) (Fin K) (Fin M)).symm.trans
        ((Equiv.sumCongr finSumFinEquiv (Equiv.refl (Fin M))).trans finSumFinEquiv)))

lemma coreObservationAssoc_core {N K M : ℕ} (i : Fin N) :
    coreObservationAssoc N K M (finSumFinEquiv (Sum.inl i)) =
      finSumFinEquiv (Sum.inl (finSumFinEquiv (Sum.inl i))) := by
  simp [coreObservationAssoc]

lemma coreObservationAssoc_middle {N K M : ℕ} (i : Fin K) :
    coreObservationAssoc N K M (finSumFinEquiv (Sum.inr (finSumFinEquiv (Sum.inl i)))) =
      finSumFinEquiv (Sum.inl (finSumFinEquiv (Sum.inr i))) := by
  simp [coreObservationAssoc]

lemma coreObservationAssoc_out {N K M : ℕ} (i : Fin M) :
    coreObservationAssoc N K M (finSumFinEquiv (Sum.inr (finSumFinEquiv (Sum.inr i)))) =
      finSumFinEquiv (Sum.inr i) := by
  simp [coreObservationAssoc]

lemma joinLists_observation_order {α : Type*} {N K M : ℕ}
    (x : Fin N → α) (y : Fin K → α) (z : Fin M → α) :
    joinLists x (joinLists y z) ∘ (coreObservationAssoc N K M).symm =
      joinLists (joinLists x y) z := by
  apply (Equiv.comp_symm_eq (coreObservationAssoc N K M) _ _).mpr
  funext i
  obtain ⟨j,rfl⟩ := finSumFinEquiv.surjective i
  cases j with
  | inl j => simp only [Function.comp_apply,coreObservationAssoc_core,joinLists_left]
  | inr j =>
    obtain ⟨k,rfl⟩ := finSumFinEquiv.surjective j
    cases k <;> simp only [Function.comp_apply,coreObservationAssoc_middle,
      coreObservationAssoc_out,joinLists_left,joinLists_right]

lemma coreSlice_observation_order {N K M : ℕ} (ψ : FormVector ((N+K)+M))
    (s : Spins K) (t : Spins M) (u : Configuration K) (v : Configuration M) :
    coreSlice (reindexForm (coreObservationAssoc N K M) ψ) (joinLists s t) (joinLists u v) =
      coreSlice (coreSlice ψ t v) s u := by
  apply congrArg₂ FormVector.mk
  · funext q x
    change ψ.value _ _ = ψ.value _ _
    rw [joinLists_observation_order,joinLists_observation_order]
  · funext q i a x
    change ψ.gradient _ _ _ _ = ψ.gradient _ _ _ _
    rw [joinLists_observation_order,joinLists_observation_order,coreObservationAssoc_core]

lemma coreObservationAssoc_perm_comp {α : Type*} {N K M : ℕ}
    (π : Equiv.Perm (Fin N)) (f : Fin (N+(K+M)) → α) :
    (f ∘ corePerm (K+M) π) ∘ (coreObservationAssoc N K M).symm =
      (f ∘ (coreObservationAssoc N K M).symm) ∘ corePerm M (corePerm K π) := by
  funext i
  obtain ⟨j,rfl⟩ := finSumFinEquiv.surjective i
  cases j with
  | inl j =>
    obtain ⟨k,rfl⟩ := finSumFinEquiv.surjective j
    cases k <;> simp [Function.comp_apply,corePerm,coreObservationAssoc,Equiv.permCongr_apply]
  | inr j => simp [Function.comp_apply,corePerm,coreObservationAssoc,Equiv.permCongr_apply]

lemma CoreAntisymmetric.observation_order {N K M : ℕ} {ψ : FormVector ((N+K)+M)}
    (ha : CoreAntisymmetric ψ) :
    CoreAntisymmetric (reindexForm (coreObservationAssoc N K M) ψ) := by
  intro π s
  have hh := (configurationReindex_preserving (coreObservationAssoc N K M)).quasiMeasurePreserving.ae
    (ha (corePerm K π) (s ∘ (coreObservationAssoc N K M).symm))
  filter_upwards [hh] with x hx
  change ψ.value ((s ∘ corePerm (K+M) π) ∘ (coreObservationAssoc N K M).symm)
    ((x ∘ corePerm (K+M) π) ∘ (coreObservationAssoc N K M).symm) = _
  rw [coreObservationAssoc_perm_comp,coreObservationAssoc_perm_comp]
  simpa only [configurationReindex_apply,corePerm_sign,reindexForm] using hx

def nextCoreObservation {N M : ℕ} (p : Fin 2 → SmoothMultiplier spaceDirections)
    (hp : ∀ x, ∑ a, (p a).value x^2 = 1) (ψ : FormVector (N+M)) (c : Fin N → Fin 2) :
    FormVector (cutCoreNumber c+(cutOutNumber c+M)) :=
  reindexForm (coreObservationAssoc _ _ _) (repeatedCutForm p hp ψ c)

lemma nextCoreObservation_sobolev {N M : ℕ} {ψ : FormVector (N+M)} (hψ : SobolevVector ψ)
    (p : Fin 2 → SmoothMultiplier spaceDirections)
    (hp : ∀ x, ∑ a, (p a).value x^2 = 1) (c : Fin N → Fin 2) :
    SobolevVector (nextCoreObservation p hp ψ c) :=
  (repeatedCutForm_sobolev hψ p hp c).reindex _

lemma nextCoreObservation_slice {N M : ℕ} (ψ : FormVector (N+M))
    (p : Fin 2 → SmoothMultiplier spaceDirections)
    (hp : ∀ x, ∑ a, (p a).value x^2 = 1) (c : Fin N → Fin 2)
    (s : Spins (cutOutNumber c)) (t : Spins M)
    (u : Configuration (cutOutNumber c)) (v : Configuration M) :
    coreSlice (nextCoreObservation p hp ψ c) (joinLists s t) (joinLists u v) =
      coreSlice (orderedCutForm p hp (coreSlice ψ t v) c) s u := by
  unfold nextCoreObservation
  rw [coreSlice_observation_order,repeatedCutForm_slice]

end CoulombAtom

end

end OAI
