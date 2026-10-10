import OAI.Combinatorics.Ramsey.CycleClique.Construction.RawRestrict
import OAI.Combinatorics.Ramsey.CycleClique.Construction.OutsideChainTemplate
import OAI.Combinatorics.Ramsey.CycleClique.Construction.TerminalIncrementProfiles

namespace OAI

/-! No short outside path can join the two internal vertices of an old
amount-two path: its detour would absorb that old assigned path. -/

namespace CycleClique.Construction.ExpandedPathSystem

open scoped Classical

variable {V : Type*} {G : SimpleGraph V} {Q : Finset V} {S : ExpandedPathSystem G Q}

theorem IsOptimal.forbidden_amount_two_detour {k d : ℕ}
    (hopt : S.IsOptimal k) (ht : 9 ≤ Q.card) (hQk : Q.card ≤ k)
    (hkQ : k ≤ 2 * Q.card + 1) (hQ : G.IsClique (Q : Set V))
    (hcycle : ¬ HasCycle G (k + 1)) (hd : 1 ≤ d) (hd' : d ≤ 6)
    {P R : List (List V)} {A B : List V} {q r u v : V}
    (hsys : S.chains = P ++ (A ++ q :: u :: v :: r :: B) :: R)
    (hq : q ∈ Q) (hr : r ∈ Q) (hu : u ∉ Q) (hv : v ∉ Q) :
    ¬ OutsidePath G ((Q : Set V) ∪ (S.vertices : Set V)) u v d := by
  classical
  intro houtside
  obtain ⟨J, hJ, hJlen, hJout, hpath⟩ := houtside.interior
  have hJQ : ∀ z ∈ J, z ∉ Q := fun z hz hzQ => hJout z hz (Or.inl hzQ)
  have hJne : J ≠ [] := by intro he; simp only [he, List.length_nil] at hJlen; omega
  let old := A ++ q :: u :: v :: r :: B
  have holdmem : old ∈ S.chains := by simp [old, hsys]
  have hrest : (P ++ R).Sublist S.toRaw.chains := by
    change (P ++ R).Sublist S.chains
    rw [hsys]
    exact (List.Sublist.refl P).append ((List.Sublist.refl R).cons _)
  let U := S.toRaw.restrictChains (P ++ R) hrest
  have hperm : (U.chains.flatten ++ ((A ++ [q]) ++ u :: v :: r :: B)).Perm S.chains.flatten := by
    apply List.perm_iff_count.mpr
    intro z
    simp only [U, RawPathSystem.restrictChains, hsys, List.flatten_append, List.flatten_cons,
      List.count_append, List.count_cons, List.count_nil]
    omega
  have hflat : (U.chains.flatten ++ ((A ++ [q]) ++ u :: v :: r :: B)).Nodup :=
    hperm.nodup_iff.mpr S.flatten_nodup
  have hdis : J.Disjoint (U.chains.flatten ++ ((A ++ [q]) ++ u :: v :: r :: B)) := by
    apply List.disjoint_left.mpr
    intro z hz hzold
    exact hJout z hz (Or.inr (List.mem_toFinset.mpr (hperm.mem_iff.mp hzold)))
  have holdsplit : old = ((A ++ [q]) ++ [u]) ++ (v :: r :: B) := by
    simp [old, List.append_assoc]
  have hleft : ((A ++ [q]) ++ [u]).IsChain G.Adj := by
    exact (List.isChain_append.mp (holdsplit ▸ (S.paths old holdmem).2)).1
  have hright : (v :: r :: B).IsChain G.Adj := by
    exact (List.isChain_append.mp (holdsplit ▸ (S.paths old holdmem).2)).2.1
  have hleftSteps : ((A ++ [q]) ++ [u]).IsChain (fun a b => ¬ (a ∈ Q ∧ b ∈ Q)) := by
    exact (List.isChain_append.mp (holdsplit ▸ S.no_clique_steps old holdmem)).1
  have hrightSteps : (v :: r :: B).IsChain (fun a b => ¬ (a ∈ Q ∧ b ∈ Q)) := by
    exact (List.isChain_append.mp (holdsplit ▸ S.no_clique_steps old holdmem)).2.1
  have hstart : ∀ z ∈ ((A ++ [q]) ++ [u]).head?, z ∈ Q := by
    intro z hz
    apply (S.endpoints old holdmem).1 z
    rw [holdsplit]
    exact List.mem_head?_append_of_mem_head? hz
  have hfinish : ∀ z ∈ (v :: r :: B).getLast?, z ∈ Q := by
    intro z hz
    apply (S.endpoints old holdmem).2 z
    rw [holdsplit, List.getLast?_append,
      List.getLast?_eq_some_getLast (show v :: r :: B ≠ [] by simp)]
    simpa only [List.getLast?_eq_some_getLast (show v :: r :: B ≠ [] by simp), Option.or] using hz
  obtain ⟨T, hT, hTa, _, _⟩ := U.expand_outside_template hflat hleft hright hstart hfinish
    hleftSteps hrightSteps hJ hJne hJQ hdis hpath
  have hamount : T.amount = S.amount + d := by
    have hs := (hperm.filter (fun z => decide (z ∉ Q))).length_eq
    change chainOutsideCount Q (U.chains.flatten ++ ((A ++ [q]) ++ u :: v :: r :: B)) =
      chainOutsideCount Q S.chains.flatten at hs
    have hSoutside : chainOutsideCount Q S.chains.flatten = S.amount := by
      exact S.toRaw.amount_eq_outside_count.symm
    rw [hSoutside] at hs
    omega
  have hpreEnds : (∀ z ∈ (A ++ [q]).head?, z ∈ Q) ∧
      (∀ z ∈ (A ++ [q]).getLast?, z ∈ Q) := by
    refine ⟨?_, by simpa using hq⟩
    intro z hz
    apply (S.endpoints old holdmem).1 z
    simpa [old, List.append_assoc] using List.mem_head?_append_of_mem_head?
      (t := u :: v :: r :: B) hz
  have hpreSteps : (A ++ [q]).IsChain (fun a b => ¬ (a ∈ Q ∧ b ∈ Q)) :=
    (List.isChain_append.mp hleftSteps).1
  have hsufEnds : (∀ z ∈ (r :: B).head?, z ∈ Q) ∧
      (∀ z ∈ (r :: B).getLast?, z ∈ Q) := by
    refine ⟨by simpa using hr, ?_⟩
    intro z hz
    apply hfinish z
    cases B with
    | nil => simpa using hz
    | cons b B => simpa using hz
  have hsufSteps : (r :: B).IsChain (fun a b => ¬ (a ∈ Q ∧ b ∈ Q)) :=
    (List.isChain_cons.mp hrightSteps).2
  obtain ⟨wa, hwa⟩ := exists_assignedAmounts hpreEnds hpreSteps
  obtain ⟨wb, hwb⟩ := exists_assignedAmounts hsufEnds hsufSteps
  have hOldProfile : AssignedAmounts Q old (wa ++ 2 :: wb) := by
    have hh := hwa.append_segment (by simp) (J := [u, v]) (by simp [hu, hv]) (by simp) hwb
    simpa [old, List.append_assoc] using hh
  have hNewProfile : AssignedAmounts Q ((A ++ [q]) ++ u :: (J ++ v :: r :: B))
      (wa ++ (d + 2) :: wb) := by
    have hOutside : ∀ z ∈ u :: (J ++ [v]), z ∉ Q := by
      intro z hz
      simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hz
      rcases hz with rfl | hz | rfl
      · exact hu
      · exact hJQ z hz
      · exact hv
    have hh := hwa.append_segment (by simp) hOutside (by simp) hwb
    simpa [List.append_assoc, hJlen, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hh
  obtain ⟨wp, hp⟩ := S.toRaw.exists_subchain_profile P (by intro l hl; change l ∈ S.chains; simp [hsys, hl])
  obtain ⟨wr, hr'⟩ := S.toRaw.exists_subchain_profile R (by intro l hl; change l ∈ S.chains; simp [hsys, hl])
  let original := wp ++ (wa ++ 2 :: wb) ++ wr
  let kept := wp ++ wa ++ wb ++ wr
  let output := (wp ++ wr) ++ (wa ++ (d + 2) :: wb)
  have ho : SystemAssignedAmounts Q S.toRaw.chains original := by
    rw [show S.toRaw.chains = P ++ old :: R by
      change S.chains = P ++ old :: R
      simpa [old] using hsys]
    simpa only [original, List.append_assoc] using hp.append (.cons hOldProfile hr')
  have ht' : SystemAssignedAmounts Q T.chains output := by
    rw [hT]
    change SystemAssignedAmounts Q ((P ++ R) ++ [_]) output
    simpa [output] using (hp.append hr').append (.cons hNewProfile .nil)
  have horig : original.Perm (kept ++ [2]) := by
    apply List.perm_iff_count.mpr
    intro z
    simp only [original, kept, List.count_append, List.count_cons, List.count_nil]
    omega
  have hout : output.Perm ((d + 2) :: kept) := by
    apply List.perm_iff_count.mpr
    intro z
    simp only [output, kept, List.count_append, List.count_cons]
    omega
  obtain ⟨_, _, _, ha, _⟩ := hopt.terminal_increment_profiles ht hQk hkQ hQ hcycle hd hd'
    S.toRaw T (by simp) (by simp) ho ht' horig hout hamount
  omega

end CycleClique.Construction.ExpandedPathSystem

end OAI
