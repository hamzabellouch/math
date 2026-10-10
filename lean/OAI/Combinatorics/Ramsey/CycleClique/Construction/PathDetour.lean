import OAI.Combinatorics.Ramsey.CycleClique.Construction.ListSurgery
import OAI.Combinatorics.Ramsey.CycleClique.Construction.OptimalPathSystem
import OAI.Combinatorics.Ramsey.CycleClique.Construction.OutsidePathRules

namespace OAI

/-! Insert an outside detour into any step of an expanded chain.
All old vertices and assigned-path endpoints are retained. -/

namespace CycleClique.Construction.ExpandedPathSystem

variable {V : Type*} {G : SimpleGraph V} {Q : Finset V}

theorem exists_edge_detour (S : ExpandedPathSystem G Q)
    {P R : List (List V)} {A B J : List V} {x y : V}
    (hsys : S.chains = P ++ (A ++ x :: y :: B) :: R)
    (hJQ : ∀ z ∈ J, z ∉ Q)
    (hJ : J.Nodup) (hdis : J.Disjoint S.chains.flatten)
    (hpath : (x :: (J ++ [y])).IsChain G.Adj) :
    ∃ T : ExpandedPathSystem G Q,
      T.amount = S.amount + J.length ∧ T.incident = S.incident ∧
        T.assignedCount = S.assignedCount := by
  classical
  let old := A ++ x :: y :: B
  let new := A ++ x :: (J ++ y :: B)
  let C := P ++ new :: R
  have holdmem : old ∈ S.chains := by simp [hsys, old]
  have hflatold : S.chains.flatten =
      (P.flatten ++ A ++ [x]) ++ ((y :: B) ++ R.flatten) := by
    simp [hsys, List.append_assoc]
  have hflatnew : C.flatten =
      (P.flatten ++ A ++ [x]) ++ J ++ ((y :: B) ++ R.flatten) := by
    simp [C, new, List.append_assoc]
  have hflat : C.flatten.Nodup := by
    rw [hflatnew]
    apply nodup_insert_list
    · rw [← hflatold]
      exact S.flatten_nodup
    · exact hJ
    · rwa [← hflatold]
  have hnewpath : new.IsChain G.Adj := chain_insert_between
    (S.paths old holdmem).2 hpath
  have hxy : ¬ (x ∈ Q ∧ y ∈ Q) := by
    have h := List.isChain_append_cons_cons.mp (S.no_clique_steps old holdmem)
    exact h.2.1
  have hmid := chain_outside_interior hxy hJQ
  have hnewnoclique : new.IsChain (fun a b => ¬ (a ∈ Q ∧ b ∈ Q)) :=
    chain_insert_between (S.no_clique_steps old holdmem) hmid
  have hmemOld : ∀ l, l ∈ P ∨ l ∈ R → l ∈ S.chains := by
    intro l hl
    simp only [hsys, List.mem_append, List.mem_cons]
    tauto
  let T : ExpandedPathSystem G Q := {
    chains := C
    nontrivial := by
      intro l hl
      rcases List.mem_append.mp hl with hl | hl
      · exact S.nontrivial l (hmemOld l (Or.inl hl))
      · rcases List.mem_cons.mp hl with rfl | hl
        · have hlen := S.nontrivial old holdmem
          simp only [old, List.length_append, List.length_cons] at hlen
          simp only [new, List.length_append, List.length_cons]
          omega
        · exact S.nontrivial l (hmemOld l (Or.inr hl))
    paths := by
      intro l hl
      refine ⟨(List.nodup_flatten.mp hflat).1 l hl, ?_⟩
      rcases List.mem_append.mp hl with hl | hl
      · exact (S.paths l (hmemOld l (Or.inl hl))).2
      · rcases List.mem_cons.mp hl with rfl | hl
        · exact hnewpath
        · exact (S.paths l (hmemOld l (Or.inr hl))).2
    disjoint := (List.nodup_flatten.mp hflat).2
    endpoints := by
      intro l hl
      rcases List.mem_append.mp hl with hl | hl
      · exact S.endpoints l (hmemOld l (Or.inl hl))
      · rcases List.mem_cons.mp hl with rfl | hl
        · have hh : new.head? = old.head? := head_insert_between A B J x y
          have ht : new.getLast? = old.getLast? := last_insert_between A B J x y
          rw [hh, ht]
          exact S.endpoints old holdmem
        · exact S.endpoints l (hmemOld l (Or.inr hl))
    no_clique_steps := by
      intro l hl
      rcases List.mem_append.mp hl with hl | hl
      · exact S.no_clique_steps l (hmemOld l (Or.inl hl))
      · rcases List.mem_cons.mp hl with rfl | hl
        · exact hnewnoclique
        · exact S.no_clique_steps l (hmemOld l (Or.inr hl)) }
  have hverts : T.vertices = S.vertices ∪ J.toFinset := by
    ext v
    simp only [vertices, T, List.mem_toFinset, Finset.mem_union, hflatold, hflatnew,
      List.mem_append, List.mem_cons]
    tauto
  have hJdiff : J.toFinset \ Q = J.toFinset := by
    apply Finset.sdiff_eq_self_iff_disjoint.mpr
    apply Finset.disjoint_left.mpr
    intro v hv hvQ
    exact hJQ v (List.mem_toFinset.mp hv) hvQ
  have hJinter : J.toFinset ∩ Q = ∅ := by
    apply Finset.disjoint_iff_inter_eq_empty.mp
    exact Finset.sdiff_eq_self_iff_disjoint.mp hJdiff
  have hdisfin : Disjoint (S.vertices \ Q) J.toFinset := by
    apply Finset.disjoint_left.mpr
    intro v hv hvJ
    exact List.disjoint_left.mp hdis (List.mem_toFinset.mp hvJ)
      (List.mem_toFinset.mp (Finset.mem_sdiff.mp hv).1)
  have hamount : T.amount = S.amount + J.length := by
    change (T.vertices \ Q).card = (S.vertices \ Q).card + J.length
    rw [hverts, Finset.union_sdiff_distrib, hJdiff,
      Finset.card_union_of_disjoint hdisfin, List.toFinset_card_of_nodup hJ]
  have hincident : T.incident = S.incident := by
    simp only [incident, hverts, Finset.union_inter_distrib_right, hJinter, Finset.union_empty]
  have hcount : T.chains.length = S.chains.length := by
    simp [T, C, hsys]
  refine ⟨T, hamount, hincident, ?_⟩
  simp only [assignedCount, hincident, hcount]

/-- An outside detour that stays in the exact closing interval is
excluded by the established optimality criterion. -/
theorem IsOptimal.no_edge_detour {S : ExpandedPathSystem G Q} {k : ℕ}
    (hopt : S.IsOptimal k) (hk : 3 ≤ k) (hQk : Q.card ≤ k)
    (hQ : G.IsClique (Q : Set V)) (hcycle : ¬ HasCycle G (k + 1))
    {P R : List (List V)} {A B J : List V} {x y : V}
    (hsys : S.chains = P ++ (A ++ x :: y :: B) :: R)
    (hJQ : ∀ z ∈ J, z ∉ Q)
    (hJ : J.Nodup) (hdis : J.Disjoint S.chains.flatten)
    (hpath : (x :: (J ++ [y])).IsChain G.Adj) (hpos : J ≠ [])
    (hupper : S.amount + J.length + S.incident ≤ k + 1) : False := by
  obtain ⟨T, hamount, hincident, hcount⟩ :=
    S.exists_edge_detour hsys hJQ hJ hdis hpath
  apply hopt.criterion hk hQk hQ hcycle T
  · simp only [hcount, le_refl, ↓reduceIte, hamount]
    have : 0 < J.length := List.length_pos_iff.mpr hpos
    omega
  · simpa only [hamount, hincident] using hupper

theorem IsOptimal.forbidden_edge_detour {S : ExpandedPathSystem G Q} {k d : ℕ}
    (hopt : S.IsOptimal k) (hk : 3 ≤ k) (hQk : Q.card ≤ k)
    (hQ : G.IsClique (Q : Set V)) (hcycle : ¬ HasCycle G (k + 1))
    {P R : List (List V)} {A B : List V} {x y : V}
    (hsys : S.chains = P ++ (A ++ x :: y :: B) :: R)
    (hd : 1 ≤ d)
    (hupper : S.amount + d + S.incident ≤ k + 1) :
    ¬ OutsidePath G ((Q : Set V) ∪ (S.vertices : Set V)) x y d := by
  classical
  intro h
  obtain ⟨J, hJ, hJlen, hJout, hpath⟩ := h.interior
  have hJQ : ∀ z ∈ J, z ∉ Q := fun z hz hzQ => hJout z hz (Or.inl hzQ)
  have hdis : J.Disjoint S.chains.flatten := by
    apply List.disjoint_left.mpr
    intro z hz hzold
    exact hJout z hz (Or.inr (List.mem_toFinset.mpr hzold))
  apply hopt.no_edge_detour hk hQk hQ hcycle hsys hJQ hJ hdis hpath
  · intro he
    simp only [he, List.length_nil] at hJlen
    omega
  · simpa only [hJlen] using hupper

theorem IsOptimal.forbidden_one_vertex_edge_detour {S : ExpandedPathSystem G Q} {k : ℕ}
    (hopt : S.IsOptimal k) (hk : 3 ≤ k) (hQk : Q.card ≤ k)
    (hQ : G.IsClique (Q : Set V)) (hcycle : ¬ HasCycle G (k + 1))
    {P R : List (List V)} {A B : List V} {x y : V}
    (hsys : S.chains = P ++ (A ++ x :: y :: B) :: R) :
    ¬ OutsidePath G ((Q : Set V) ∪ (S.vertices : Set V)) x y 1 := by
  apply hopt.forbidden_edge_detour hk hQk hQ hcycle hsys (by omega)
  have hb := hopt.budget
  have hi := S.incident_le
  omega

end CycleClique.Construction.ExpandedPathSystem

end OAI
