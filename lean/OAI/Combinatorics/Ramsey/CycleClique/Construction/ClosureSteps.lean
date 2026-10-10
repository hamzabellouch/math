import OAI.Combinatorics.Ramsey.CycleClique.Construction.ClosureCertificates

namespace OAI

/-! A finite sequence of locally checked hypothetical attachments builds
only sound forbidden entries. Every step reads the preceding matrix. -/

namespace CycleClique.Construction
inductive ClosureStep (n : ℕ)
  | edge : EdgeAttachmentData n → ClosureStep n
  | fresh : FreshAttachmentData n → ClosureStep n
  deriving DecidableEq

namespace ClosureStep

variable {n : ℕ}

def source : ClosureStep n → Fin n
  | .edge c => c.i
  | .fresh c => c.i

def target : ClosureStep n → Fin n
  | .edge c => c.j
  | .fresh c => c.j

def parameter : ClosureStep n → ℕ
  | .edge _ => 0
  | .fresh _ => 1

def Check (H : SimpleGraph (Fin n)) (M : ForbiddenMatrix n) (k t : ℕ) : ClosureStep n → Prop
  | .edge c => c.Check H M k t
  | .fresh c => c.Check H M k t

instance (H : SimpleGraph (Fin n)) [DecidableRel H.Adj] (M : ForbiddenMatrix n)
    (k t : ℕ) (c : ClosureStep n) : Decidable (c.Check H M k t) := by
  cases c <;> dsimp only [Check] <;> infer_instance

def entryMatrix (c : ClosureStep n) : ForbiddenMatrix n := fun i j =>
  if (i = c.source ∧ j = c.target) ∨ (i = c.target ∧ j = c.source)
    then {c.parameter} else ∅

def apply (c : ClosureStep n) (M : ForbiddenMatrix n) : ForbiddenMatrix n :=
  fun i j => M i j ∪ c.entryMatrix i j

end ClosureStep

variable {n : ℕ}

def closureMatrix (M : ForbiddenMatrix n) : List (ClosureStep n) → ForbiddenMatrix n
  | [] => M
  | c :: C => closureMatrix (c.apply M) C

def ClosureCheck (H : SimpleGraph (Fin n)) (M : ForbiddenMatrix n) (k t : ℕ) :
    List (ClosureStep n) → Prop
  | [] => True
  | c :: C => c.Check H M k t ∧ ClosureCheck H (c.apply M) k t C

instance (H : SimpleGraph (Fin n)) [DecidableRel H.Adj] (M : ForbiddenMatrix n)
    (k t : ℕ) (C : List (ClosureStep n)) : Decidable (ClosureCheck H M k t C) := by
  induction C generalizing M with
  | nil => exact isTrue trivial
  | cons c C ih =>
    letI := ih (c.apply M)
    exact inferInstanceAs (Decidable (_ ∧ _))

variable {V : Type} [Fintype V] {G : SimpleGraph V} {H : SimpleGraph (Fin n)}

theorem ClosureStep.apply_sound (hCE : CEAlphaTwo) {k t : ℕ}
    (hk : 5 ≤ k) (ht : 1 ≤ t) (hcycle : ¬ HasCycle G (k + 1))
    (hclique : G.cliqueNum ≤ t) (hbound : IndependenceBound G k)
    (f : H →g G) (hf : Function.Injective f) {X : Finset V}
    (hfX : ∀ i, f i ∈ X) (hX : X.card = n)
    {M : ForbiddenMatrix n} (hM : M.Sound G X f)
    (hexpand : ∀ I : Finset V, G.IsIndepSet (I : Set V) → I.Nonempty →
      k * I.card + 1 ≤ (closedNeighborhood G I).card)
    (c : ClosureStep n) (hc : c.Check H M k t) : (c.apply M).Sound G X f := by
  have hb : ¬ OutsidePath G (X : Set V) (f c.source) (f c.target) c.parameter := by
    cases c with
    | edge c => exact c.forbids hCE hk ht hcycle hclique hbound f hf hfX hX hM hexpand hc
    | fresh c => exact c.forbids hCE hk ht hcycle hclique hbound f hf hfX hX hM hexpand hc
  apply hM.union
  intro i j d hd
  have hpair : (i = c.source ∧ j = c.target) ∨ (i = c.target ∧ j = c.source) := by
    by_contra hn
    simp only [ClosureStep.entryMatrix, hn, ↓reduceIte, Finset.notMem_empty] at hd
  have heq : d = c.parameter := by
    simpa only [ClosureStep.entryMatrix, hpair, ↓reduceIte, Finset.mem_singleton] using hd
  subst d
  rcases hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact hb
  · exact fun h => hb h.reverse

theorem closureMatrix_sound (hCE : CEAlphaTwo) {k t : ℕ}
    (hk : 5 ≤ k) (ht : 1 ≤ t) (hcycle : ¬ HasCycle G (k + 1))
    (hclique : G.cliqueNum ≤ t) (hbound : IndependenceBound G k)
    (f : H →g G) (hf : Function.Injective f) {X : Finset V}
    (hfX : ∀ i, f i ∈ X) (hX : X.card = n)
    {M : ForbiddenMatrix n} (hM : M.Sound G X f)
    (hexpand : ∀ I : Finset V, G.IsIndepSet (I : Set V) → I.Nonempty →
      k * I.card + 1 ≤ (closedNeighborhood G I).card)
    (C : List (ClosureStep n)) (hC : ClosureCheck H M k t C) :
    (closureMatrix M C).Sound G X f := by
  induction C generalizing M with
  | nil => exact hM
  | cons c C ih =>
    exact ih (c.apply_sound hCE hk ht hcycle hclique hbound f hf hfX hX hM hexpand hC.1) hC.2

end CycleClique.Construction

end OAI
