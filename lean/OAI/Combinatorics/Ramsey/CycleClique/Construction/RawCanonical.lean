import OAI.Combinatorics.Ramsey.CycleClique.Construction.CanonicalProfiles
import OAI.Combinatorics.Ramsey.CycleClique.Construction.AssignedProfileOperations
import OAI.Combinatorics.Ramsey.CycleClique.Construction.RawPermutation
import Mathlib.Data.List.Perm.Basic

namespace OAI

/-! Realize numerical canonical profiles by independently orienting and
reordering the actual chains, preserving the full raw vertex set. -/

namespace CycleClique.Construction
variable {V : Type*} {Q : Finset V}

def ChainOrientation (l r : List V) : Prop := r = l ∨ r = l.reverse

theorem chainOrientations_flatten {C D : List (List V)}
    (h : List.Forall₂ ChainOrientation C D) : D.flatten.Perm C.flatten := by
  induction h with
  | nil => exact .refl _
  | @cons l r C D hr ht ih =>
    rcases hr with he | he
    · subst r; exact (List.Perm.refl l).append ih
    · subst r; exact (List.reverse_perm l).append ih

theorem chainOrientations_source {C D : List (List V)}
    (h : List.Forall₂ ChainOrientation C D) :
    ∀ r ∈ D, ∃ l ∈ C, ChainOrientation l r := by
  induction h with
  | nil => simp
  | @cons l r C D hr ht ih =>
    intro s hs
    rcases List.mem_cons.mp hs with rfl | hs
    · exact ⟨l, by simp, hr⟩
    · obtain ⟨l', hl', hh⟩ := ih s hs
      exact ⟨l', by simp [hl'], hh⟩

theorem orient_chain_profiles {C : List (List V)} {P : List (List ℕ)}
    (hp : List.Forall₂ (AssignedAmounts Q) C P) :
    ∃ D, List.Forall₂ ChainOrientation C D ∧
      List.Forall₂ (AssignedAmounts Q) D (P.map orientAmounts) := by
  induction hp with
  | nil => exact ⟨[], .nil, .nil⟩
  | @cons l w C P hw ht ih =>
    obtain ⟨D, hD, hprof⟩ := ih
    by_cases h : w ≤ w.reverse
    · exact ⟨l :: D, .cons (Or.inl rfl) hD,
        by simpa only [List.map_cons, orientAmounts, h, ↓reduceIte] using
          List.Forall₂.cons hw hprof⟩
    · exact ⟨l.reverse :: D, .cons (Or.inr rfl) hD,
        by simpa only [List.map_cons, orientAmounts, h, ↓reduceIte] using
          List.Forall₂.cons hw.reverse hprof⟩

namespace RawPathSystem

variable {G : SimpleGraph V}

def reorient (S : RawPathSystem G Q) (D : List (List V))
    (h : List.Forall₂ ChainOrientation S.chains D) : RawPathSystem G Q where
  chains := D
  paths := by
    intro r hr
    obtain ⟨l, hl, he⟩ := chainOrientations_source h r hr
    rcases he with he | he
    · subst r; exact S.paths l hl
    · subst r; exact ⟨List.nodup_reverse.mpr (S.paths l hl).1,
        List.isChain_reverse.mpr ((S.paths l hl).2.imp (fun _ _ hh => hh.symm))⟩
  disjoint := (List.nodup_flatten.mp
    ((chainOrientations_flatten h).nodup_iff.mpr S.flatten_nodup)).2
  endpoints := by
    intro r hr
    obtain ⟨l, hl, he⟩ := chainOrientations_source h r hr
    rcases he with he | he
    · subst r; exact S.endpoints l hl
    · subst r; simpa only [List.head?_reverse, List.getLast?_reverse] using
        And.intro (S.endpoints l hl).2 (S.endpoints l hl).1
  no_clique_steps := by
    intro r hr
    obtain ⟨l, hl, he⟩ := chainOrientations_source h r hr
    rcases he with he | he
    · subst r; exact S.no_clique_steps l hl
    · subst r; exact List.isChain_reverse.mpr
        ((S.no_clique_steps l hl).imp (fun _ _ hh hh' => hh hh'.symm))

@[simp] theorem reorient_vertices (S : RawPathSystem G Q) (D : List (List V))
    (h : List.Forall₂ ChainOrientation S.chains D) : (S.reorient D h).vertices = S.vertices := by
  ext v
  simp only [vertices, reorient, List.mem_toFinset]
  exact (chainOrientations_flatten h).mem_iff

@[simp] theorem reorient_amount (S : RawPathSystem G Q) (D : List (List V))
    (h : List.Forall₂ ChainOrientation S.chains D) : (S.reorient D h).amount = S.amount := by
  unfold amount
  rw [reorient_vertices]

@[simp] theorem reorient_assignedCount (S : RawPathSystem G Q) (D : List (List V))
    (h : List.Forall₂ ChainOrientation S.chains D) :
    (S.reorient D h).assignedCount = S.assignedCount := by
  change rawAssignedCount Q D = rawAssignedCount Q S.chains
  generalize heq : S.chains = C at h ⊢
  clear heq
  induction h with
  | nil => rfl
  | @cons l r C D hr ht ih =>
    rcases hr with he | he <;> subst r <;>
      simp only [rawAssignedCount, List.map_cons, List.sum_cons,
        chainCliqueCount_reverse] at ih ⊢ <;> omega

theorem canonical_profile (S : RawPathSystem G Q) {P : List (List ℕ)}
    (hp : List.Forall₂ (AssignedAmounts Q) S.chains P) :
    ∃ T : RawPathSystem G Q,
      T.vertices = S.vertices ∧ T.amount = S.amount ∧ T.assignedCount = S.assignedCount ∧
      List.Forall₂ (AssignedAmounts Q) T.chains (canonicalAmounts P) := by
  obtain ⟨D, hD, hprof⟩ := orient_chain_profiles hp
  let U := S.reorient D hD
  obtain ⟨C, hC, hperm⟩ := List.perm_comp_forall₂ (canonicalAmounts_perm P) hprof.flip
  let T := U.reorder C hperm
  refine ⟨T, ?_, ?_, ?_, hC.flip⟩
  · exact (U.reorder_vertices C hperm).trans (S.reorient_vertices D hD)
  · exact (U.reorder_amount C hperm).trans (S.reorient_amount D hD)
  · exact (U.reorder_assignedCount C hperm).trans (S.reorient_assignedCount D hD)

end RawPathSystem

end CycleClique.Construction

end OAI
