import OAI.Combinatorics.Ramsey.CycleClique.Construction.RawCanonical
import OAI.Combinatorics.Ramsey.CycleClique.Construction.OptimalPathSystem

namespace OAI

/-! Every optimal system is realized by a nonempty-chain raw system in
exactly the canonical domain consumed by the finite certificates. -/

namespace CycleClique.Construction
variable {V : Type*} {G : SimpleGraph V} {Q : Finset V}

namespace RawPathSystem

theorem canonical_profile_nonempty (S : RawPathSystem G Q) {P : List (List ℕ)}
    (hp : List.Forall₂ (AssignedAmounts Q) S.chains P)
    (hne : ∀ l ∈ S.chains, l ≠ []) :
    ∃ T : RawPathSystem G Q,
      T.vertices = S.vertices ∧ T.amount = S.amount ∧ T.assignedCount = S.assignedCount ∧
      List.Forall₂ (AssignedAmounts Q) T.chains (canonicalAmounts P) ∧
      ∀ l ∈ T.chains, l ≠ [] := by
  obtain ⟨D, hD, hprof⟩ := orient_chain_profiles hp
  have hDne : ∀ l ∈ D, l ≠ [] := by
    intro l hl
    obtain ⟨r, hr, hrl⟩ := chainOrientations_source hD l hl
    rcases hrl with he | he
    · subst l
      exact hne r hr
    · rw [he]
      exact List.reverse_ne_nil_iff.mpr (hne r hr)
  let U := S.reorient D hD
  obtain ⟨C, hC, hperm⟩ := List.perm_comp_forall₂ (canonicalAmounts_perm P) hprof.flip
  let T := U.reorder C hperm
  refine ⟨T, ?_, ?_, ?_, hC.flip, ?_⟩
  · exact (U.reorder_vertices C hperm).trans (S.reorient_vertices D hD)
  · exact (U.reorder_amount C hperm).trans (S.reorient_amount D hD)
  · exact (U.reorder_assignedCount C hperm).trans (S.reorient_assignedCount D hD)
  · intro l hl
    exact hDne l (hperm.mem_iff.mp hl)

end RawPathSystem

namespace ExpandedPathSystem

open scoped Classical

variable {S : ExpandedPathSystem G Q}

theorem completeClique_chains_nonempty (S : ExpandedPathSystem G Q) :
    ∀ l ∈ S.toRaw.completeClique.chains, l ≠ [] := by
  intro l hl
  change l ∈ S.chains ++ (Q \ S.toRaw.vertices).toList.map (fun v => [v]) at hl
  rcases List.mem_append.mp hl with hl | hl
  · have hn := S.nontrivial l hl
    intro he
    simp only [he, List.length_nil] at hn
    omega
  · obtain ⟨v, _, rfl⟩ := List.mem_map.mp hl
    simp

theorem IsOptimal.exists_canonical_raw {k : ℕ} (hopt : S.IsOptimal k) :
    ∃ (P : List (List ℕ)) (U : RawPathSystem G Q),
      P ∈ pathPatterns Q.card (k - Q.card) ∧
      U.vertices = Q ∪ S.vertices ∧ U.amount = S.amount ∧
      U.assignedCount = S.assignedCount ∧
      List.Forall₂ (AssignedAmounts Q) U.chains P ∧
      ∀ l ∈ U.chains, l ≠ [] := by
  obtain ⟨P, hp, hmem⟩ := S.exists_canonical_profile hopt.budget
  obtain ⟨U, hUv, hUa, hUe, hprof, hne⟩ :=
    S.toRaw.completeClique.canonical_profile_nonempty hp S.completeClique_chains_nonempty
  refine ⟨canonicalAmounts P, U, hmem, ?_, ?_, ?_, hprof, hne⟩
  · rw [hUv, RawPathSystem.completeClique_vertices]
    exact Finset.union_comm _ _
  · simpa using hUa
  · simpa using hUe

end ExpandedPathSystem

end CycleClique.Construction

end OAI
