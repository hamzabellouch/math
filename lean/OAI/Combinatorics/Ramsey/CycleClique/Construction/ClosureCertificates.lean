import OAI.Combinatorics.Ramsey.CycleClique.Construction.FiniteAttachments

namespace OAI

/-! Soundness of the checker's hypothetical zero/one attachment rules.
Each local contradiction is witnessed by explicit required paths and a
checked bad state; inherited constraints refer only to earlier states. -/

namespace CycleClique.Construction
structure EdgeAttachmentData (n : ℕ) where
  i : Fin n
  j : Fin n
  required : List (RequiredPathData (Fin n))
  bad : BadData n
  deriving DecidableEq

structure FreshAttachmentData (n : ℕ) where
  i : Fin n
  j : Fin n
  required : List (RequiredPathData (Fin (n + 1)))
  bad : BadData (n + 1)
  deriving DecidableEq

variable {n : ℕ}

def EdgeAttachmentData.Check (H : SimpleGraph (Fin n)) (M : ForbiddenMatrix n)
    (k t : ℕ) (c : EdgeAttachmentData n) : Prop :=
  (∀ p ∈ c.required, p.Check (addedEdgeGraph H c.i c.j) k) ∧
    c.bad.Check (addedEdgeGraph H c.i c.j)
      (fun a b => M a b ∪ requiredMatrix k c.required a b) k t

def FreshAttachmentData.Check (H : SimpleGraph (Fin n)) (M : ForbiddenMatrix n)
    (k t : ℕ) (c : FreshAttachmentData n) : Prop :=
  c.i ≠ c.j ∧ (∀ p ∈ c.required, p.Check (freshGraph H c.i c.j) k) ∧
    c.bad.Check (freshGraph H c.i c.j)
      (fun a b => freshMatrix M a b ∪ requiredMatrix k c.required a b) k t

instance (H : SimpleGraph (Fin n)) [DecidableRel H.Adj] (M : ForbiddenMatrix n)
    (k t : ℕ) (c : EdgeAttachmentData n) : Decidable (c.Check H M k t) :=
  inferInstanceAs (Decidable (_ ∧ _))

instance (H : SimpleGraph (Fin n)) [DecidableRel H.Adj] (M : ForbiddenMatrix n)
    (k t : ℕ) (c : FreshAttachmentData n) : Decidable (c.Check H M k t) :=
  inferInstanceAs (Decidable (_ ∧ _))

variable {V : Type} [Fintype V] {G : SimpleGraph V} {H : SimpleGraph (Fin n)}

theorem EdgeAttachmentData.forbids (hCE : CEAlphaTwo) {k t : ℕ}
    (hk : 5 ≤ k) (ht : 1 ≤ t) (hcycle : ¬ HasCycle G (k + 1))
    (hclique : G.cliqueNum ≤ t) (hbound : IndependenceBound G k)
    (f : H →g G) (hf : Function.Injective f) {X : Finset V}
    (hfX : ∀ i, f i ∈ X) (hX : X.card = n)
    {M : ForbiddenMatrix n} (hM : M.Sound G X f)
    (hexpand : ∀ I : Finset V, G.IsIndepSet (I : Set V) → I.Nonempty →
      k * I.card + 1 ≤ (closedNeighborhood G I).card)
    (c : EdgeAttachmentData n) (hc : c.Check H M k t) :
    ¬ OutsidePath G (X : Set V) (f c.i) (f c.j) 0 := by
  intro h
  let F := addedEdgeHom f (outsidePath_zero.mp h)
  have hR := requiredMatrix_sound (by omega) hcycle F hf hfX c.required hc.1
  exact c.bad.false_of_check hCE hk ht hcycle hclique hbound F hf hfX hX
    (hM.union hR) hexpand hc.2

theorem FreshAttachmentData.forbids (hCE : CEAlphaTwo) {k t : ℕ}
    (hk : 5 ≤ k) (ht : 1 ≤ t) (hcycle : ¬ HasCycle G (k + 1))
    (hclique : G.cliqueNum ≤ t) (hbound : IndependenceBound G k)
    (f : H →g G) (hf : Function.Injective f) {X : Finset V}
    (hfX : ∀ i, f i ∈ X) (hX : X.card = n)
    {M : ForbiddenMatrix n} (hM : M.Sound G X f)
    (hexpand : ∀ I : Finset V, G.IsIndepSet (I : Set V) → I.Nonempty →
      k * I.card + 1 ≤ (closedNeighborhood G I).card)
    (c : FreshAttachmentData n) (hc : c.Check H M k t) :
    ¬ OutsidePath G (X : Set V) (f c.i) (f c.j) 1 := by
  classical
  intro h
  obtain ⟨z, hz, hiz, hjz⟩ := (outsidePath_one_iff_common_neighbor
    (fun he => hc.1 (hf he))).mp h
  have hjz' := hjz.symm
  let F := freshHom f z hiz hjz'
  have hF := freshHom_injective f hf hfX hz hiz hjz'
  have hFX := freshHom_mem f hfX hiz hjz'
  have hX' : (insert z X).card = n + 1 := by rw [Finset.card_insert_of_notMem hz, hX]
  have hM' := freshMatrix_sound f hM hiz hjz'
  have hR := requiredMatrix_sound (by omega) hcycle F hF hFX c.required hc.2.1
  exact c.bad.false_of_check hCE hk ht hcycle hclique hbound F hF hFX hX'
    (hM'.union hR) hexpand hc.2.2

end CycleClique.Construction

end OAI
