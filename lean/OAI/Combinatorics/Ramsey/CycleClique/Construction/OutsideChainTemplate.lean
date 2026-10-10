import OAI.Combinatorics.Ramsey.CycleClique.Construction.AssignedDeletion
import OAI.Combinatorics.Ramsey.CycleClique.Construction.OutsidePathRules
import OAI.Combinatorics.Ramsey.CycleClique.Construction.RawEmbedding

namespace OAI

/-! Expand one certified outside connector inside an explicit chain
template. All old vertices are checked as a finite disjoint path collection. -/

namespace CycleClique.Construction.RawPathSystem

open scoped Classical

variable {V : Type*} {G : SimpleGraph V} {Q : Finset V}

theorem expand_outside_template (S : RawPathSystem G Q) {A B J : List V} {x y : V}
    (hold : (S.chains.flatten ++ (A ++ x :: y :: B)).Nodup)
    (hleft : (A ++ [x]).IsChain G.Adj) (hright : (y :: B).IsChain G.Adj)
    (hstart : ∀ v ∈ (A ++ [x]).head?, v ∈ Q)
    (hfinish : ∀ v ∈ (y :: B).getLast?, v ∈ Q)
    (hleftSteps : (A ++ [x]).IsChain (fun a b => ¬ (a ∈ Q ∧ b ∈ Q)))
    (hrightSteps : (y :: B).IsChain (fun a b => ¬ (a ∈ Q ∧ b ∈ Q)))
    (hJ : J.Nodup) (hJne : J ≠ []) (hJQ : ∀ v ∈ J, v ∉ Q)
    (hdis : J.Disjoint (S.chains.flatten ++ (A ++ x :: y :: B)))
    (hpath : (x :: (J ++ [y])).IsChain G.Adj) :
    ∃ T : RawPathSystem G Q,
      T.chains = S.chains ++ [A ++ x :: (J ++ y :: B)] ∧
      T.amount = chainOutsideCount Q (S.chains.flatten ++ (A ++ x :: y :: B)) + J.length ∧
      T.assignedCount = S.assignedCount + (chainCliqueCount Q (A ++ x :: y :: B) - 1) ∧
      T.normalize.incident ≤ chainCliqueCount Q (S.chains.flatten ++ (A ++ x :: y :: B)) := by
  classical
  let l := A ++ x :: (J ++ y :: B)
  let C := S.chains ++ [l]
  have hp : C.flatten.Perm ((S.chains.flatten ++ (A ++ x :: y :: B)) ++ J) := by
    apply List.perm_iff_count.mpr
    intro v
    simp only [C, l, List.flatten_append, List.flatten_cons, List.flatten_nil,
      List.append_nil, List.count_append, List.count_cons]
    omega
  have hflat : C.flatten.Nodup := hp.nodup_iff.mpr (hold.append hJ hdis.symm)
  have hleftRev : (x :: A.reverse).IsChain G.Adj := by
    simpa using List.isChain_reverse.mpr (hleft.imp (fun _ _ h => h.symm))
  have hleftRevSteps : (x :: A.reverse).IsChain (fun a b => ¬ (a ∈ Q ∧ b ∈ Q)) := by
    simpa using List.isChain_reverse.mpr (hleftSteps.imp (fun _ _ h (h' : _ ∧ _) => h h'.symm))
  have hlpath : l.IsChain G.Adj := by
    simpa only [l, List.reverse_reverse] using
      reverse_join_chain (fun _ _ h => h.symm) hleftRev hright hpath
  have hlsteps : l.IsChain (fun a b => ¬ (a ∈ Q ∧ b ∈ Q)) := by
    simpa only [l, List.reverse_reverse] using
      reverse_join_chain (fun _ _ h (h' : _ ∧ _) => h h'.symm) hleftRevSteps hrightSteps
        (chain_outside_interior_of_ne_nil hJne hJQ)
  have hlhead : l.head? = (A ++ [x]).head? := by
    cases A <;> rfl
  have hlrepl : l = (A ++ [x]) ++ J ++ (y :: B) := by simp [l, List.append_assoc]
  have hllast : l.getLast? = (y :: B).getLast? := by
    rw [hlrepl, List.getLast?_append,
      List.getLast?_eq_some_getLast (show y :: B ≠ [] by simp)]
    rfl
  let T : RawPathSystem G Q := {
    chains := C
    paths := by
      intro r hr
      refine ⟨(List.nodup_flatten.mp hflat).1 r hr, ?_⟩
      rcases List.mem_append.mp hr with hr | hr
      · exact (S.paths r hr).2
      · have he : r = l := by simpa using hr
        exact he.symm ▸ hlpath
    disjoint := (List.nodup_flatten.mp hflat).2
    endpoints := by
      intro r hr
      rcases List.mem_append.mp hr with hr | hr
      · exact S.endpoints r hr
      · have he : r = l := by simpa using hr
        subst r
        simpa only [hlhead, hllast] using And.intro hstart hfinish
    no_clique_steps := by
      intro r hr
      rcases List.mem_append.mp hr with hr | hr
      · exact S.no_clique_steps r hr
      · have he : r = l := by simpa using hr
        exact he.symm ▸ hlsteps }
  refine ⟨T, rfl, ?_, ?_, ?_⟩
  · rw [T.amount_eq_outside_count]
    have hh := (hp.filter (fun v => decide (v ∉ Q))).length_eq
    have hfilter : J.filter (fun v => decide (v ∉ Q)) = J := by
      apply List.filter_eq_self.mpr
      intro v hv
      simpa using hJQ v hv
    simpa only [chainOutsideCount, List.filter_append, List.length_append, hfilter] using hh
  · change rawAssignedCount Q C = S.assignedCount + _
    have hlcount : chainCliqueCount Q l = chainCliqueCount Q (A ++ x :: y :: B) := by
      have hz := chainCliqueCount_eq_zero hJQ
      rw [hlrepl]
      simp only [chainCliqueCount_append, hz, Nat.add_zero]
      simp [chainCliqueCount_cons, Nat.add_assoc, show chainCliqueCount Q [] = 0 from rfl]
    simp only [C, rawAssignedCount, List.map_append, List.sum_append, List.map_cons,
      List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero, hlcount]
    rfl
  · apply T.normalize_incident_le.trans
    have hh := (hp.filter (fun v => decide (v ∈ Q))).length_eq
    have hz := chainCliqueCount_eq_zero hJQ
    have he : chainCliqueCount Q T.chains.flatten =
        chainCliqueCount Q (S.chains.flatten ++ (A ++ x :: y :: B)) := by
      simpa only [chainCliqueCount, List.filter_append, List.length_append,
        show (J.filter (fun v => decide (v ∈ Q))).length = 0 from hz, Nat.add_zero] using hh
    exact he.le

end CycleClique.Construction.RawPathSystem

end OAI
