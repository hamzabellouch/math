import OAI.Combinatorics.Ramsey.CycleClique.Construction.RawCliqueCompletion

namespace OAI

/-! Representatives: each chain start, and the first vertex following
every nonterminal clique vertex in the oriented expanded chain. -/

namespace CycleClique.Construction
open scoped Classical

variable {V : Type*} {Q : Finset V}

noncomputable def representativesFrom (Q : Finset V) (prev : V) : List V → List V
  | [] => []
  | x :: xs => (if prev ∈ Q then [x] else []) ++ representativesFrom Q x xs

noncomputable def chainRepresentatives (Q : Finset V) : List V → List V
  | [] => []
  | x :: xs => x :: representativesFrom Q x xs

theorem representativesFrom_sublist (prev : V) (xs : List V) :
    (representativesFrom Q prev xs).Sublist xs := by
  induction xs generalizing prev with
  | nil => exact .refl _
  | cons x xs ih =>
    simp only [representativesFrom]
    split_ifs
    · simpa using (ih x).cons_cons x
    · simpa using (ih x).cons x

theorem chainRepresentatives_sublist (l : List V) : (chainRepresentatives Q l).Sublist l := by
  cases l with
  | nil => exact .refl _
  | cons x xs => exact (representativesFrom_sublist x xs).cons_cons x

@[simp] theorem chainCliqueCount_cons (x : V) (xs : List V) :
    chainCliqueCount Q (x :: xs) = (if x ∈ Q then 1 else 0) + chainCliqueCount Q xs := by
  simp [chainCliqueCount, List.filter_cons]
  split_ifs <;> simp [Nat.add_comm]

theorem representativesFrom_length (prev : V) (xs : List V)
    (hlast : ∀ v ∈ (prev :: xs).getLast?, v ∈ Q) :
    (representativesFrom Q prev xs).length + 1 = chainCliqueCount Q (prev :: xs) := by
  induction xs generalizing prev with
  | nil =>
    have hp : prev ∈ Q := hlast prev (by simp)
    simp [representativesFrom, chainCliqueCount, hp]
  | cons x xs ih =>
    have hi := ih x (by simpa using hlast)
    rw [representativesFrom, List.length_append, chainCliqueCount_cons]
    have hlen : (if prev ∈ Q then [x] else []).length = (if prev ∈ Q then 1 else 0) := by
      split_ifs <;> rfl
    rw [hlen]
    omega

theorem chainRepresentatives_length (l : List V)
    (hlast : ∀ v ∈ l.getLast?, v ∈ Q) :
    (chainRepresentatives Q l).length = chainCliqueCount Q l := by
  cases l with
  | nil => rfl
  | cons x xs =>
    simpa only [chainRepresentatives, List.length_cons] using representativesFrom_length x xs hlast

namespace RawPathSystem

variable {G : SimpleGraph V}

noncomputable def representatives (S : RawPathSystem G Q) : List V :=
  (S.chains.map (chainRepresentatives Q)).flatten

theorem representatives_sublist (S : RawPathSystem G Q) :
    S.representatives.Sublist S.chains.flatten := by
  have h : ∀ C : List (List V),
      (C.map (chainRepresentatives Q)).flatten.Sublist C.flatten := by
    intro C
    induction C with
    | nil => exact .refl _
    | cons l C ih =>
      exact (chainRepresentatives_sublist l).append ih
  exact h S.chains

theorem representatives_nodup (S : RawPathSystem G Q) : S.representatives.Nodup :=
  S.flatten_nodup.sublist S.representatives_sublist

theorem representatives_length (S : RawPathSystem G Q) :
    S.representatives.length = chainCliqueCount Q S.chains.flatten := by
  rw [chainCliqueCount_flatten]
  unfold representatives
  rw [List.length_flatten, List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro l hl
  exact chainRepresentatives_length l (S.endpoints l hl).2

theorem completeClique_representatives_length (S : RawPathSystem G Q) :
    S.completeClique.representatives.length = Q.card := by
  rw [representatives_length]
  have hnd := S.completeClique.flatten_nodup.filter (fun v => decide (v ∈ Q))
  have hset : (S.completeClique.chains.flatten.filter (fun v => decide (v ∈ Q))).toFinset = Q := by
    ext v
    simp only [List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
    constructor
    · exact And.right
    · intro hv
      constructor
      · have hm : v ∈ S.completeClique.vertices := by
          rw [completeClique_vertices]
          exact Finset.mem_union_right _ hv
        exact List.mem_toFinset.mp hm
      · exact hv
  unfold chainCliqueCount
  rw [← List.toFinset_card_of_nodup hnd, hset]

end RawPathSystem

end CycleClique.Construction

end OAI
