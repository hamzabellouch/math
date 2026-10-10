import OAI.Combinatorics.Ramsey.CycleClique.Construction.RepresentativeCuts
import OAI.Combinatorics.Ramsey.CycleClique.Construction.RawPermutation
import OAI.Combinatorics.Ramsey.CycleClique.Construction.ReplacementOptimality

namespace OAI

/-! Manuscript grow:one for every pair of representatives of an oriented
raw system with the optimal amount. -/

namespace CycleClique.Construction.ExpandedPathSystem

open scoped Classical

variable {V : Type*} {G : SimpleGraph V} {Q : Finset V} {S : ExpandedPathSystem G Q}

theorem IsOptimal.representatives_one_exclusion {k : ℕ} (hopt : S.IsOptimal k)
    (hk : 3 ≤ k) (hQk : Q.card ≤ k) (hQ : G.IsClique (Q : Set V))
    (hcycle : ¬ HasCycle G (k + 1)) (U : RawPathSystem G Q)
    (hUamount : U.amount = S.amount)
    (hUvertices : ∀ v ∈ U.vertices, v ∈ Q ∨ v ∈ S.vertices)
    {x y : V} (hx : x ∈ U.representatives) (hy : y ∈ U.representatives) (hne : x ≠ y) :
    ¬ OutsidePath G ((Q : Set V) ∪ (S.vertices : Set V)) x y 1 := by
  obtain ⟨l, hl, hx⟩ := List.mem_flatten.mp hx
  obtain ⟨l', hl', heql⟩ := List.mem_map.mp hl
  subst l
  obtain ⟨m, hm, hy⟩ := List.mem_flatten.mp hy
  obtain ⟨m', hm', heqm⟩ := List.mem_map.mp hm
  subst m
  have hxc := chainRepresentatives_mem_cut hx
  have hyc := chainRepresentatives_mem_cut hy
  by_cases hlm : l' = m'
  · subst m'
    obtain ⟨P, R, hchains⟩ := List.append_of_mem hl'
    rcases repCuts_ordered (U.paths l' hl').1 hne hxc hyc with
      ⟨A, B, D, he, hA, hB⟩ | ⟨A, B, D, he, hA, hB⟩
    · exact hopt.forbidden_same_chain_one hk hQk hQ hcycle U hUamount hUvertices
        (by simpa [he] using hchains) hA hB
    · intro hout
      exact hopt.forbidden_same_chain_one hk hQk hQ hcycle U hUamount hUvertices
        (by simpa [he] using hchains) hA hB hout.reverse
  · obtain ⟨R, hp⟩ := U.bring_two_front hl' hm' hlm
    let U' := U.reorder (l' :: m' :: R) hp
    have hamount : U'.amount = S.amount := by simpa [U'] using hUamount
    have hvertices : ∀ v ∈ U'.vertices, v ∈ Q ∨ v ∈ S.vertices := by
      intro v hv
      apply hUvertices v
      simpa [U'] using hv
    obtain ⟨A, B, he₁, hA⟩ := hxc
    obtain ⟨C, D, he₂, hC⟩ := hyc
    apply hopt.forbidden_different_chain_one hk hQk hQ hcycle U' hamount hvertices
      (P := []) (M := []) (R := R) (A := A) (B := B) (C := C) (D := D)
    · simp [U', RawPathSystem.reorder, he₁, he₂]
    · exact hA
    · exact hC

theorem IsOptimal.completed_representatives_one_exclusion {k : ℕ} (hopt : S.IsOptimal k)
    (hk : 3 ≤ k) (hQk : Q.card ≤ k) (hQ : G.IsClique (Q : Set V))
    (hcycle : ¬ HasCycle G (k + 1)) {x y : V}
    (hx : x ∈ S.toRaw.completeClique.representatives)
    (hy : y ∈ S.toRaw.completeClique.representatives) (hne : x ≠ y) :
    ¬ OutsidePath G ((Q : Set V) ∪ (S.vertices : Set V)) x y 1 := by
  apply hopt.representatives_one_exclusion hk hQk hQ hcycle S.toRaw.completeClique
    (by simp) ?_ hx hy hne
  intro v hv
  rw [RawPathSystem.completeClique_vertices] at hv
  exact (Finset.mem_union.mp hv).symm

end CycleClique.Construction.ExpandedPathSystem

end OAI
