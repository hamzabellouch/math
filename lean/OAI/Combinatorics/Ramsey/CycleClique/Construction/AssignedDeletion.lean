import OAI.Combinatorics.Ramsey.CycleClique.Construction.RawPathSystem
import OAI.Combinatorics.Ramsey.CycleClique.Construction.RepresentativeOutside

namespace OAI

/-! Deleting a single assigned path splits its chain at the two clique
endpoints. All remaining assigned paths and their interiors are retained. -/

namespace CycleClique.Construction.RawPathSystem

open scoped Classical

variable {V : Type*} {G : SimpleGraph V} {Q : Finset V}

theorem amount_eq_outside_count (S : RawPathSystem G Q) :
    S.amount = chainOutsideCount Q S.chains.flatten := by
  classical
  have heq : S.vertices \ Q =
      (S.chains.flatten.filter (fun v => decide (v ∉ Q))).toFinset := by
    ext v
    simp [vertices]
    aesop
  unfold amount chainOutsideCount
  rw [heq, List.toFinset_card_of_nodup (S.flatten_nodup.filter _)]

theorem delete_assigned_path (S : RawPathSystem G Q)
    {P R : List (List V)} {A J B : List V} {x y : V}
    (hsys : S.chains = P ++ (A ++ x :: (J ++ y :: B)) :: R)
    (hx : x ∈ Q) (hy : y ∈ Q) (hJ : ∀ z ∈ J, z ∉ Q) :
    ∃ T : RawPathSystem G Q,
      T.chains = P ++ (A ++ [x]) :: (y :: B) :: R ∧
      T.amount + J.length = S.amount ∧
      T.assignedCount + 1 = S.assignedCount ∧
      T.vertices ⊆ S.vertices := by
  classical
  let K := P ++ (A ++ [x]) :: (y :: B) :: R
  have hold : A ++ x :: (J ++ y :: B) ∈ S.chains := by simp [hsys]
  have hp : (K.flatten ++ J).Perm S.chains.flatten := by
    apply List.perm_iff_count.mpr
    intro v
    simp only [K, hsys, List.flatten_append, List.flatten_cons,
      List.count_append, List.count_cons]
    simp only [List.count_nil]
    omega
  have hflat : K.flatten.Nodup := (List.nodup_append.mp
    (hp.nodup_iff.mpr S.flatten_nodup)).1
  have hpreFull : (A ++ [x]).IsChain G.Adj := by
    have hh := (S.paths _ hold).2
    exact
      (List.isChain_append.mp (show ((A ++ [x]) ++ (J ++ y :: B)).IsChain G.Adj by
        simpa [List.append_assoc] using hh)).1
  have hsufPath : (y :: B).IsChain G.Adj := by
    exact (List.isChain_append.mp
      (List.isChain_cons.mp (List.isChain_append.mp (S.paths _ hold).2).2.1).2).2.1
  have hpreSteps : (A ++ [x]).IsChain (fun a b => ¬ (a ∈ Q ∧ b ∈ Q)) := by
    exact (List.isChain_append.mp (show ((A ++ [x]) ++ (J ++ y :: B)).IsChain
      (fun a b => ¬ (a ∈ Q ∧ b ∈ Q)) by
        simpa [List.append_assoc] using S.no_clique_steps _ hold)).1
  have hsufSteps : (y :: B).IsChain (fun a b => ¬ (a ∈ Q ∧ b ∈ Q)) := by
    exact (List.isChain_append.mp
      (List.isChain_cons.mp (List.isChain_append.mp (S.no_clique_steps _ hold)).2.1).2).2.1
  let T : RawPathSystem G Q := {
    chains := K
    paths := by
      intro l hl
      refine ⟨(List.nodup_flatten.mp hflat).1 l hl, ?_⟩
      simp only [K, List.mem_append, List.mem_cons] at hl
      rcases hl with hl | rfl | rfl | hl
      · exact (S.paths l (by simp [hsys, hl])).2
      · exact hpreFull
      · exact hsufPath
      · exact (S.paths l (by simp [hsys, hl])).2
    disjoint := (List.nodup_flatten.mp hflat).2
    endpoints := by
      intro l hl
      simp only [K, List.mem_append, List.mem_cons] at hl
      rcases hl with hl | rfl | rfl | hl
      · exact S.endpoints l (by simp [hsys, hl])
      · refine ⟨?_, by simpa using hx⟩
        intro v hv
        cases A with
        | nil =>
          have heq : x = v := by simpa using hv
          simpa only [heq] using hx
        | cons a A =>
          exact (S.endpoints _ hold).1 v (by simpa using hv)
      · refine ⟨by simpa using hy, ?_⟩
        intro v hv
        apply (S.endpoints _ hold).2 v
        have hh := List.getLast?_eq_some_getLast (show y :: B ≠ [] by simp)
        rw [List.getLast?_append, List.getLast?_cons_of_ne_nil (by simp),
          List.getLast?_append, hh]
        simpa only [hh, Option.or] using hv
      · exact S.endpoints l (by simp [hsys, hl])
    no_clique_steps := by
      intro l hl
      simp only [K, List.mem_append, List.mem_cons] at hl
      rcases hl with hl | rfl | rfl | hl
      · exact S.no_clique_steps l (by simp [hsys, hl])
      · exact hpreSteps
      · exact hsufSteps
      · exact S.no_clique_steps l (by simp [hsys, hl]) }
  refine ⟨T, rfl, ?_, ?_, ?_⟩
  · rw [T.amount_eq_outside_count, S.amount_eq_outside_count]
    have hh := hp.filter (fun v => decide (v ∉ Q))
    have hfilter : J.filter (fun v => decide (v ∉ Q)) = J := by
      apply List.filter_eq_self.mpr
      intro v hv
      simpa using hJ v hv
    simpa only [chainOutsideCount, List.filter_append, List.length_append, hfilter] using
      hh.length_eq
  · have hxcount : chainCliqueCount Q [x] = 1 := by simp [chainCliqueCount, hx]
    have hycount : 1 ≤ chainCliqueCount Q (y :: B) :=
      chainCliqueCount_pos (by simp) (by simpa using hy)
    have hzero := chainCliqueCount_eq_zero hJ
    change rawAssignedCount Q K + 1 = rawAssignedCount Q S.chains
    simp only [K, hsys, rawAssignedCount, List.map_append, List.map_cons,
      List.sum_append, List.sum_cons, chainCliqueCount_append, hxcount]
    have heq : chainCliqueCount Q (x :: (J ++ y :: B)) =
        1 + chainCliqueCount Q (y :: B) := by
      change chainCliqueCount Q ([x] ++ (J ++ y :: B)) = _
      rw [chainCliqueCount_append, chainCliqueCount_append, hxcount, hzero, Nat.zero_add]
    rw [heq]
    omega
  · intro v hv
    change v ∈ K.flatten.toFinset at hv
    apply List.mem_toFinset.mpr
    exact hp.mem_iff.mp (List.mem_append_left _ (List.mem_toFinset.mp hv))

end CycleClique.Construction.RawPathSystem

end OAI
