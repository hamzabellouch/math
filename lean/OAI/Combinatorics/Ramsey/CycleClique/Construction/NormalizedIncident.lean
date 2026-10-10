import OAI.Combinatorics.Ramsey.CycleClique.Construction.RawOrientations
import OAI.Combinatorics.Ramsey.CycleClique.Construction.RawPermutation
import OAI.Combinatorics.Ramsey.CycleClique.Construction.RawCliqueCompletion

namespace OAI

/-! Count the incident clique vertices after isolated chain pieces are removed. -/

namespace CycleClique.Construction
open scoped Classical

variable {V : Type*} {G : SimpleGraph V} {Q : Finset V}

noncomputable def activeCliqueCount (Q : Finset V) (l : List V) : ℕ :=
  if 3 ≤ l.length then chainCliqueCount Q l else 0

@[simp] theorem activeCliqueCount_nil : activeCliqueCount Q ([] : List V) = 0 := by
  simp [activeCliqueCount]

@[simp] theorem activeCliqueCount_singleton (x : V) : activeCliqueCount Q [x] = 0 := by
  simp [activeCliqueCount]

@[simp] theorem activeCliqueCount_reverse (l : List V) :
    activeCliqueCount Q l.reverse = activeCliqueCount Q l := by
  simp [activeCliqueCount]

theorem activeCliqueCount_add_singleton {l : List V} (hne : l ≠ [])
    (hends : (∀ v ∈ l.head?, v ∈ Q) ∧ (∀ v ∈ l.getLast?, v ∈ Q))
    (hsteps : l.IsChain (fun x y => ¬ (x ∈ Q ∧ y ∈ Q))) :
    activeCliqueCount Q l + (if l.length = 1 then 1 else 0) = chainCliqueCount Q l := by
  classical
  by_cases hlen : 3 ≤ l.length
  · have hn : l.length ≠ 1 := by omega
    simp [activeCliqueCount, hlen, hn]
  · have hc := short_chainCliqueCount hne hends hsteps (by omega)
    have hall := short_chain_in_clique hends hsteps (by omega)
    have hlength : l.length = 1 := by
      cases l with
      | nil => exact False.elim (hne rfl)
      | cons x xs =>
        cases xs with
        | nil => rfl
        | cons y xs =>
          exact False.elim ((List.isChain_cons_cons.mp hsteps).1
            ⟨hall x (by simp), hall y (by simp)⟩)
    simp [activeCliqueCount, hlength, hc]

namespace RawPathSystem

theorem normalize_incident (S : RawPathSystem G Q) :
    S.normalize.incident = (S.chains.map (activeCliqueCount Q)).sum := by
  rw [ExpandedPathSystem.incident_eq_chainCliqueCount, chainCliqueCount_flatten]
  change ((S.chains.filter (fun l => decide (3 ≤ l.length))).map (chainCliqueCount Q)).sum = _
  induction S.chains with
  | nil => rfl
  | cons l C ih =>
    by_cases hl : 3 ≤ l.length
    · simpa [List.filter_cons, hl, activeCliqueCount] using
        congrArg (fun n => chainCliqueCount Q l + n) ih
    · simpa [List.filter_cons, hl, activeCliqueCount] using ih

@[simp] theorem orientChains_normalize_incident (S : RawPathSystem G Q) (p : List V → Bool) :
    (S.orientChains p).normalize.incident = S.normalize.incident := by
  rw [normalize_incident, normalize_incident]
  change ((S.chains.map (orientedChain p)).map (activeCliqueCount Q)).sum = _
  rw [List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro l hl
  change activeCliqueCount Q (orientedChain p l) = activeCliqueCount Q l
  unfold orientedChain
  split_ifs <;> simp only [activeCliqueCount_reverse]

@[simp] theorem reorder_normalize_incident (S : RawPathSystem G Q)
    (K : List (List V)) (hp : K.Perm S.chains) :
    (S.reorder K hp).normalize.incident = S.normalize.incident := by
  rw [normalize_incident, normalize_incident]
  exact (hp.map (activeCliqueCount Q)).sum_eq

@[simp] theorem completeClique_normalize_incident (S : RawPathSystem G Q) :
    S.completeClique.normalize.incident = S.normalize.incident := by
  rw [normalize_incident, normalize_incident]
  change ((S.chains ++ (Q \ S.vertices).toList.map (fun v => [v])).map (activeCliqueCount Q)).sum = _
  simp [List.map_map, Function.comp_def]

end RawPathSystem

namespace ExpandedPathSystem

@[simp] theorem toRaw_normalize_incident (S : ExpandedPathSystem G Q) :
    S.toRaw.normalize.incident = S.incident := by
  rw [RawPathSystem.normalize_incident, incident_eq_chainCliqueCount, chainCliqueCount_flatten]
  change (S.chains.map (activeCliqueCount Q)).sum = _
  apply congrArg List.sum
  apply List.map_congr_left
  intro l hl
  simp only [activeCliqueCount, S.nontrivial l hl, ↓reduceIte]

end ExpandedPathSystem

end CycleClique.Construction

end OAI
