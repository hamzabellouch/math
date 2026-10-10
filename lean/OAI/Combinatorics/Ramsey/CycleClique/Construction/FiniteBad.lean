import OAI.Combinatorics.Ramsey.CycleClique.Construction.PackingCertificate
import OAI.Combinatorics.Ramsey.CycleClique.Construction.RequiredCertificates

namespace OAI

/-! The terminal certificate for a finite state is either a required edge
whose outside parameter zero is forbidden, or an excessive packing. -/

namespace CycleClique.Construction
structure BadData (n : ℕ) where
  edge : Option (Fin n × Fin n)
  packing : Finset (Fin n × ℕ)
  deriving DecidableEq

def BadData.Check {n : ℕ} (H : SimpleGraph (Fin n)) (M : ForbiddenMatrix n)
    (k t : ℕ) (b : BadData n) : Prop :=
  match b.edge with
  | some (i, j) => H.Adj i j ∧ 0 ∈ M i j
  | none => PackingCheck M k t b.packing

instance {n : ℕ} (H : SimpleGraph (Fin n)) [DecidableRel H.Adj]
    (M : ForbiddenMatrix n) (k t : ℕ) (b : BadData n) : Decidable (b.Check H M k t) := by
  unfold BadData.Check
  split <;> infer_instance

variable {V : Type} [Fintype V] {G : SimpleGraph V}

theorem BadData.false_of_check (hCE : CEAlphaTwo) {n k t : ℕ}
    (hk : 5 ≤ k) (ht : 1 ≤ t) (hcycle : ¬ HasCycle G (k + 1))
    (hclique : G.cliqueNum ≤ t) (hbound : IndependenceBound G k)
    {H : SimpleGraph (Fin n)} (f : H →g G) (hf : Function.Injective f)
    {X : Finset V} (hfX : ∀ i, f i ∈ X) (hX : X.card = n)
    {M : ForbiddenMatrix n} (hM : M.Sound G X f)
    (hexpand : ∀ I : Finset V, G.IsIndepSet (I : Set V) → I.Nonempty →
      k * I.card + 1 ≤ (closedNeighborhood G I).card)
    (b : BadData n) (hb : b.Check H M k t) : False := by
  cases hbe : b.edge with
  | none =>
    exact packingCheck_false hCE hk ht hcycle hclique hbound hf hfX hX hM hexpand
      b.packing (by simpa only [Check, hbe] using hb)
  | some ij =>
    have hh : H.Adj ij.1 ij.2 ∧ 0 ∈ M ij.1 ij.2 := by simpa only [Check, hbe] using hb
    exact hM.no_required_edge hh.2 (f.map_adj hh.1)

end CycleClique.Construction

end OAI
