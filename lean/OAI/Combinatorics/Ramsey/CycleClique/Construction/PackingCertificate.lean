import OAI.Combinatorics.Ramsey.CycleClique.Construction.FinitePacking

namespace OAI

/-! A weighted packing witness is validated by finite arithmetic and
pairwise matrix lookups. Its soundness needs only the established matrix. -/

namespace CycleClique.Construction
open scoped BigOperators

def PackingCheck {n : ℕ} (M : ForbiddenMatrix n) (k t : ℕ)
    (I : Finset (Fin n × ℕ)) : Prop :=
  (∀ p ∈ I, p.2 ≠ 0 → 0 < k + 1 + (zeroAvoidSet M p.1).card - n) ∧
  (∀ p ∈ I, ∀ q ∈ I, p ≠ q → indexedOptionsCompatible M p q) ∧
  k < ∑ p ∈ I, indexedOptionWeight M k t p

instance {n : ℕ} (M : ForbiddenMatrix n) (k t : ℕ) (I : Finset (Fin n × ℕ)) :
    Decidable (PackingCheck M k t I) := inferInstanceAs (Decidable (_ ∧ _))

variable {V : Type} [Fintype V] {G : SimpleGraph V}

theorem packingCheck_false (hCE : CEAlphaTwo) {n k t : ℕ}
    (hk : 5 ≤ k) (ht : 1 ≤ t) (hcycle : ¬ HasCycle G (k + 1))
    (hclique : G.cliqueNum ≤ t) (hbound : IndependenceBound G k)
    {X : Finset V} {f : Fin n → V} (hf : Function.Injective f)
    (hfX : ∀ i, f i ∈ X) (hX : X.card = n)
    {M : ForbiddenMatrix n} (hM : M.Sound G X f)
    (hexpand : ∀ I : Finset V, G.IsIndepSet (I : Set V) → I.Nonempty →
      k * I.card + 1 ≤ (closedNeighborhood G I).card)
    (I : Finset (Fin n × ℕ)) (hc : PackingCheck M k t I) : False := by
  have hb := indexed_packing_bound hCE hk ht hcycle hclique hbound hf hfX hX hM
    hexpand I hc.1 hc.2.1
  exact Nat.not_lt_of_ge hb hc.2.2

end CycleClique.Construction

end OAI
