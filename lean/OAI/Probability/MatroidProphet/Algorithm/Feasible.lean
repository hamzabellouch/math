import OAI.Probability.MatroidProphet.Algorithm.Rule

namespace OAI

namespace MatroidProphet
open Set Finset

lemma guardedPath_group_mono {α : Type*} [Fintype α]
    (M : Matroid α) (hE : M.E = Set.univ) (κ : ℕ) (D C : ℕ → Set α) (k : ℤ) :
    Monotone (fun h => guardedPath M hE κ D C h k) := by
  apply monotone_nat_of_le_succ
  intro h
  exact (guarded_subset_nominal M hE κ D C h k).trans
    (nominal_subset_guarded M hE κ D C h k)

lemma assigned_some_of_eligible {n : ℕ} {K : Type*}
    (assign : Fin n → K → Option ℤ) (v : Fin n → K) (e : Fin n)
    (he : e ∈ assignedEligible assign v) :
    assign e (v e) = some (assignedLayer assign v e) := by
  classical
  cases h : assign e (v e) <;> simp_all [assignedEligible, assignedLayer]

namespace MainAlgorithm
variable {n : ℕ}

lemma assign_spec (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (d : MainMasks n) (seen : Fin n → Option ℤ) (e : Fin n) (w : Option ℤ) (b : ℤ) :
    assign M hE d seen e w = some b ↔
      ∃ i, w = some i ∧ eligible M hE d seen e i ∧ birth M hE d seen e i = b := by
  classical
  cases w with
  | none => simp [assign]
  | some i =>
    by_cases h : eligible M hE d seen e i <;> simp [assign, h]

lemma eligible_mem_final (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (d : MainMasks n) (seen : Fin n → Option ℤ) (e : Fin n) (i : ℤ)
    (he : eligible M hE d seen e i) :
    e ∈ finalPath M hE d seen (birth M hE d seen e i) := by
  have hi : i ∈ groups M d seen := he.2.2.1
  have hidx : (groups M d seen).idxOf i < (groups M d seen).length :=
    List.idxOf_lt_length_of_mem hi
  have hm := nominalBirth_mem M hE (2^100) (groupMask M d seen d.D)
    (groupMask M d seen d.C) ((groups M d seen).idxOf i) e
  have hs := nominal_subset_guarded M hE (2^100) (groupMask M d seen d.D)
    (groupMask M d seen d.C) ((groups M d seen).idxOf i) (birth M hE d seen e i) hm
  exact guardedPath_group_mono M hE (2^100) (groupMask M d seen d.D)
    (groupMask M d seen d.C) _ (Nat.succ_le_of_lt hidx) hs

lemma assigned_lower_in_base (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (d : MainMasks n) (seen v : Fin n → Option ℤ)
    (e : Fin n) (he : e ∈ assignedEligible (assign M hE d seen) v)
    (f : Fin n) (hf : f ∈ assignedEligible (assign M hE d seen) v)
    (hlt : assignedLayer (assign M hE d seen) v e < assignedLayer (assign M hE d seen) v f) :
    e ∈ finalPath M hE d seen (assignedLayer (assign M hE d seen) v f - 2) := by
  obtain ⟨i, _, hei, hbi⟩ := (assign_spec M hE d seen e _ _).mp
    (assigned_some_of_eligible (assign M hE d seen) v e he)
  obtain ⟨j, _, hfj, hbj⟩ := (assign_spec M hE d seen f _ _).mp
    (assigned_some_of_eligible (assign M hE d seen) v f hf)
  have heiParity := hei.2.2.2.2.2.1
  have hfjParity := hfj.2.2.2.2.2.1
  rw [hbi] at heiParity
  rw [hbj] at hfjParity
  have hgap : assignedLayer (assign M hE d seen) v e ≤
      assignedLayer (assign M hE d seen) v f - 2 := by omega
  have hm := eligible_mem_final M hE d seen e i hei
  rw [hbi] at hm
  exact guardedPath_mono M hE (2^100) (groupMask M d seen d.D)
    (groupMask M d seen d.C) (groups M d seen).length hgap hm

theorem core_feasible (M : Matroid (Fin n)) (hE : M.E = Set.univ) :
    Feasible M (core M hE) := by
  apply layerOnlineRule_feasible M hE (roundedLevel weightBase) (measurable_roundedLevel weightBase)
  intro r seen v e he f hf hlt
  exact assigned_lower_in_base M hE (mainMasks r) seen v e he f hf hlt

theorem hidden_feasible (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (w : Weights n) (hw : ∀ e, 0 ≤ w e) (r : Seed (mainSeedBits n))
    (π : ArrivalOrder n) (t : ℕ) :
    M.Indep (hiddenAcceptedThrough (hidden M hE) r w π t : Set (Fin n)) := by
  have hobs : ∀ e, 0 ≤ observed (hidden M hE) r w e := by
    intro e
    unfold observed
    split_ifs
    · exact hw e
    · exact le_rfl
  exact (core_feasible M hE r (observed (hidden M hE) r w) w π t hobs hw).subset
    (by intro e he; exact (Finset.mem_sdiff.mp he).1)

end MainAlgorithm
end MatroidProphet

end OAI
