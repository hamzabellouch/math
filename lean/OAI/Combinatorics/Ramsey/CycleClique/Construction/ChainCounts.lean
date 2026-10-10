import OAI.Combinatorics.Ramsey.CycleClique.Construction.NormalizeChains

namespace OAI

/-! Count assigned paths before and after deleting singleton chain pieces. -/

namespace CycleClique.Construction
variable {V : Type*} {G : SimpleGraph V} {Q : Finset V}

noncomputable def chainCliqueCount (Q : Finset V) (l : List V) : ℕ := by
  classical
  exact (l.filter (fun v => decide (v ∈ Q))).length

noncomputable def rawAssignedCount (Q : Finset V) (C : List (List V)) : ℕ :=
  (C.map (fun l => chainCliqueCount Q l - 1)).sum

@[simp] theorem chainCliqueCount_append (A B : List V) :
    chainCliqueCount Q (A ++ B) = chainCliqueCount Q A + chainCliqueCount Q B := by
  classical
  simp [chainCliqueCount, List.filter_append]

@[simp] theorem chainCliqueCount_reverse (A : List V) :
    chainCliqueCount Q A.reverse = chainCliqueCount Q A := by
  classical
  simp [chainCliqueCount, List.filter_reverse]

theorem chainCliqueCount_eq_zero {J : List V} (hJ : ∀ z ∈ J, z ∉ Q) :
    chainCliqueCount Q J = 0 := by
  classical
  simp only [chainCliqueCount, List.length_eq_zero_iff, List.filter_eq_nil_iff]
  intro z hz
  simpa using hJ z hz

@[simp] theorem rawAssignedCount_append (A B : List (List V)) :
    rawAssignedCount Q (A ++ B) = rawAssignedCount Q A + rawAssignedCount Q B := by
  simp [rawAssignedCount]

theorem chainCliqueCount_pos {l : List V} (hne : l ≠ [])
    (hhead : ∀ v ∈ l.head?, v ∈ Q) : 1 ≤ chainCliqueCount Q l := by
  classical
  have hm : l.head hne ∈ l.filter (fun v => decide (v ∈ Q)) := by
    apply List.mem_filter.mpr
    exact ⟨List.head_mem hne, by simpa using hhead _ (List.head?_eq_some_head hne)⟩
  exact List.length_pos_iff.mpr (List.ne_nil_of_mem hm)

theorem chainCliqueCount_pos_last {l : List V} (hne : l ≠ [])
    (hlast : ∀ v ∈ l.getLast?, v ∈ Q) : 1 ≤ chainCliqueCount Q l := by
  rw [← chainCliqueCount_reverse]
  exact chainCliqueCount_pos (by simpa using hne) (by simpa using hlast)

theorem chainCliqueCount_flatten (C : List (List V)) :
    chainCliqueCount Q C.flatten = (C.map (chainCliqueCount Q)).sum := by
  classical
  simp only [chainCliqueCount, List.filter_flatten, List.length_flatten, List.map_map,
    Function.comp_def]
  rfl

theorem rawAssignedCount_add_length (C : List (List V))
    (hpos : ∀ l ∈ C, 1 ≤ chainCliqueCount Q l) :
    rawAssignedCount Q C + C.length = chainCliqueCount Q C.flatten := by
  rw [chainCliqueCount_flatten]
  induction C with
  | nil => simp [rawAssignedCount]
  | cons l C ih =>
    have hl := hpos l (by simp)
    have hi := ih (fun l hl => hpos l (by simp [hl]))
    simp only [rawAssignedCount, List.map_cons, List.sum_cons, List.length_cons] at hi ⊢
    omega

theorem ExpandedPathSystem.incident_eq_chainCliqueCount (S : ExpandedPathSystem G Q) :
    S.incident = chainCliqueCount Q S.chains.flatten := by
  classical
  have heq : S.vertices ∩ Q =
      (S.chains.flatten.filter (fun v => decide (v ∈ Q))).toFinset := by
    ext v
    simp [ExpandedPathSystem.vertices]
    aesop
  unfold incident
  rw [heq, List.toFinset_card_of_nodup (S.flatten_nodup.filter _)]
  rfl

theorem ExpandedPathSystem.assignedCount_eq_raw (S : ExpandedPathSystem G Q) :
    S.assignedCount = rawAssignedCount Q S.chains := by
  have hpos : ∀ l ∈ S.chains, 1 ≤ chainCliqueCount Q l := by
    intro l hl
    apply chainCliqueCount_pos
    · intro heq
      have hh := S.nontrivial l hl
      simp [heq] at hh
    · exact (S.endpoints l hl).1
  have h := rawAssignedCount_add_length S.chains hpos
  rw [← S.incident_eq_chainCliqueCount] at h
  unfold assignedCount
  omega

theorem short_chainCliqueCount {l : List V} (hne : l ≠ [])
    (hends : (∀ v ∈ l.head?, v ∈ Q) ∧ (∀ v ∈ l.getLast?, v ∈ Q))
    (hsteps : l.IsChain (fun x y => ¬ (x ∈ Q ∧ y ∈ Q)))
    (hlen : l.length < 3) : chainCliqueCount Q l = 1 := by
  classical
  cases l with
  | nil => exact False.elim (hne rfl)
  | cons x l =>
    cases l with
    | nil =>
      have hx := hends.1 x (by simp)
      simp [chainCliqueCount, hx]
    | cons y l =>
      have hy := short_chain_in_clique hends hsteps hlen
      have hxQ := hy x (by simp)
      have hyQ := hy y (by simp)
      exact False.elim ((List.isChain_cons_cons.mp hsteps).1 ⟨hxQ, hyQ⟩)

theorem short_chainCliqueCount_le {l : List V}
    (hends : (∀ v ∈ l.head?, v ∈ Q) ∧ (∀ v ∈ l.getLast?, v ∈ Q))
    (hsteps : l.IsChain (fun x y => ¬ (x ∈ Q ∧ y ∈ Q)))
    (hlen : l.length < 3) : chainCliqueCount Q l ≤ 1 := by
  by_cases he : l = []
  · subst l
    simp [chainCliqueCount]
  · rw [short_chainCliqueCount he hends hsteps hlen]

theorem normalizeChains_assignedCount (C : List (List V))
    (hpaths : ∀ l ∈ C, l.Nodup ∧ l.IsChain G.Adj)
    (hdis : C.Pairwise List.Disjoint)
    (hends : ∀ l ∈ C, (∀ v ∈ l.head?, v ∈ Q) ∧ (∀ v ∈ l.getLast?, v ∈ Q))
    (hsteps : ∀ l ∈ C, l.IsChain (fun x y => ¬ (x ∈ Q ∧ y ∈ Q))) :
    (normalizeChains C hpaths hdis hends hsteps).assignedCount = rawAssignedCount Q C := by
  classical
  rw [ExpandedPathSystem.assignedCount_eq_raw]
  change rawAssignedCount Q (C.filter (fun l => decide (3 ≤ l.length))) = _
  induction C with
  | nil => simp [rawAssignedCount]
  | cons l C ih =>
    have ht := ih (fun l hl => hpaths l (by simp [hl]))
      (List.pairwise_cons.mp hdis).2
      (fun l hl => hends l (by simp [hl]))
      (fun l hl => hsteps l (by simp [hl]))
    by_cases hl : 3 ≤ l.length
    · simpa [List.filter_cons, hl, rawAssignedCount] using
        congrArg (fun n => chainCliqueCount Q l - 1 + n) ht
    · have hc := short_chainCliqueCount_le
        (hends l (by simp)) (hsteps l (by simp)) (by omega)
      have hz : chainCliqueCount Q l - 1 = 0 := by omega
      simpa [List.filter_cons, hl, rawAssignedCount, hz] using ht

end CycleClique.Construction

end OAI
