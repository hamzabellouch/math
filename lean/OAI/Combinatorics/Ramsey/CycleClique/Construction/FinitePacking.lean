import OAI.Combinatorics.Ramsey.CycleClique.Construction.FiniteBallBounds
import OAI.Combinatorics.Ramsey.CycleClique.Construction.PackingOptions

namespace OAI

/-! A finite weighted packing certificate is sound whenever its forbidden
matrix is sound. Its numerical sum is suitable for kernel computation. -/

namespace CycleClique.Construction
open scoped BigOperators

def indexedOptionWeight {n : ℕ} (M : ForbiddenMatrix n) (k t : ℕ)
    (p : Fin n × ℕ) : ℕ :=
  match p.2 with
  | 0 => 1
  | r + 1 => (indexedBallState M k t p.1 r).2

def indexedOptionsCompatible {n : ℕ} (M : ForbiddenMatrix n)
    (p q : Fin n × ℕ) : Prop :=
  p.1 ≠ q.1 ∧
    if p.2 = 0 ∧ q.2 = 0 then 0 ∈ M p.1 q.1
    else Finset.Icc 1 (p.2 + q.2) ⊆ M p.1 q.1

instance {n : ℕ} (M : ForbiddenMatrix n) (p q : Fin n × ℕ) :
    Decidable (indexedOptionsCompatible M p q) := by
  unfold indexedOptionsCompatible
  infer_instance

variable {V : Type} [Fintype V] {G : SimpleGraph V}

theorem indexed_packing_bound (hCE : CEAlphaTwo) {n k t : ℕ}
    (hk : 5 ≤ k) (ht : 1 ≤ t) (hcycle : ¬ HasCycle G (k + 1))
    (hclique : G.cliqueNum ≤ t) (hbound : IndependenceBound G k)
    {X : Finset V} {f : Fin n → V} (hf : Function.Injective f)
    (hfX : ∀ i, f i ∈ X) (hX : X.card = n)
    {M : ForbiddenMatrix n} (hM : M.Sound G X f)
    (hexpand : ∀ I : Finset V, G.IsIndepSet (I : Set V) → I.Nonempty →
      k * I.card + 1 ≤ (closedNeighborhood G I).card)
    (I : Finset (Fin n × ℕ))
    (hbase : ∀ p ∈ I, p.2 ≠ 0 → 0 < k + 1 + (zeroAvoidSet M p.1).card - n)
    (hcompat : ∀ p ∈ I, ∀ q ∈ I, p ≠ q → indexedOptionsCompatible M p q) :
    (∑ p ∈ I, indexedOptionWeight M k t p) ≤ k := by
  classical
  have hinj : Function.Injective (fun p : I => f p.val.1) := by
    intro p q he
    by_contra hn
    have hne : p.val ≠ q.val := by intro he; exact hn (Subtype.ext he)
    exact (hcompat p p.property q q.property hne).1 (hf he)
  have hweight : ∀ p : I, HasIndependent
      (G.induce (packingRegion G X (f p.val.1) p.val.2 : Set V))
      (indexedOptionWeight M k t p.val) := by
    intro p
    cases hr : p.val.2 with
    | zero =>
      simp only [indexedOptionWeight, hr, packingRegion]
      exact hasIndependent_one_of_nonempty (by simp)
    | succ r =>
      have hb := indexedBallState_sound hCE hk ht hcycle hclique hf hfX hX hM hexpand
        p.val.1 (hbase p p.property (by omega)) r
      simpa only [indexedOptionWeight, hr, packingRegion] using hb.2
  have hsep : ∀ p q : I, p ≠ q →
      PackingCompatible G (X : Set V) (f p.val.1) p.val.2 (f q.val.1) q.val.2 := by
    intro p q hpq
    have hne : p.val ≠ q.val := by intro he; exact hpq (Subtype.ext he)
    have hc := (hcompat p p.property q q.property hne).2
    unfold PackingCompatible
    split_ifs with hzero
    · simp only [hzero] at hc
      exact hM p.val.1 q.val.1 0 hc
    · simp only [hzero, ↓reduceIte] at hc
      intro d hd hdb
      exact hM p.val.1 q.val.1 d (hc (Finset.mem_Icc.mpr ⟨hd, hdb⟩))
  have hp := packing_test hbound X (fun p : I => f p.val.1)
    (fun p => p.val.2) (fun p => indexedOptionWeight M k t p.val)
    hinj (fun p => hfX p.val.1) hweight hsep
  simpa only [Finset.sum_coe_sort] using hp

end CycleClique.Construction

end OAI
