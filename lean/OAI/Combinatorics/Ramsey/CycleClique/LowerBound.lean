import Mathlib
import OAI.Combinatorics.Ramsey.CycleClique.Basic
import OAI.Combinatorics.Ramsey.CycleClique.Exceptional

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem RamseyProperty.on_fintype {m n N : ℕ} (h : RamseyProperty m n N)
    {V : Type*} [Fintype V] (hNV : N ≤ Fintype.card V) (G : SimpleGraph V) :
    SimpleGraph.cycleGraph m ⊑ G ∨ (⊤ : SimpleGraph (Fin n)) ⊑ Gᶜ := by
  classical
  obtain ⟨f⟩ := Function.Embedding.nonempty_of_card_le (show Fintype.card (Fin N) ≤
    Fintype.card V by simpa using hNV)
  let H := G.comap f
  have hc : H ⊑ G := ⟨⟨⟨f, fun {a b} hab => hab⟩, f.injective⟩⟩
  have hcc : Hᶜ ⊑ Gᶜ := by
    refine ⟨⟨⟨f, fun {a b} hab => ?_⟩, f.injective⟩⟩
    exact ⟨fun heq => hab.1 (f.injective heq), hab.2⟩
  rcases h H with hcycle | hclique
  · exact Or.inl (hcycle.trans hc)
  · exact Or.inr (hclique.trans hcc)

 
def disjointCliques (a k : ℕ) : SimpleGraph (Fin a × Fin k) where
  Adj u v := u.1 = v.1 ∧ u.2 ≠ v.2
  symm := ⟨fun _ _ h => ⟨h.1.symm, Ne.symm h.2⟩⟩
  loopless := ⟨fun _ h => h.2 rfl⟩

 
theorem disjointCliques_walk_fiber {a k : ℕ} {u v : Fin a × Fin k}
    (p : (disjointCliques a k).Walk u v) : u.1 = v.1 := by
  induction p with
  | nil => rfl
  | cons h p ih => exact h.1.trans ih

 
theorem disjointCliques_no_cycle {m a k : ℕ} (hm : 0 < m) (hk : k < m) :
    ¬ SimpleGraph.cycleGraph m ⊑ disjointCliques a k := by
  rintro ⟨f⟩
  let x : Fin m := ⟨0, hm⟩
  have hfiber : ∀ i : Fin m, (f x).1 = (f i).1 := by
    intro i
    obtain ⟨p⟩ := SimpleGraph.cycleGraph_preconnected x i
    exact disjointCliques_walk_fiber (p.map f.toHom)
  have hinj : Function.Injective (fun i : Fin m => (f i).2) := by
    intro i j hij
    apply f.injective
    exact Prod.ext ((hfiber i).symm.trans (hfiber j)) hij
  have hc := Fintype.card_le_of_injective _ hinj
  simp only [Fintype.card_fin] at hc
  omega

 
theorem disjointCliques_no_compl_clique {n a k : ℕ} (ha : a < n) :
    ¬ (⊤ : SimpleGraph (Fin n)) ⊑ (disjointCliques a k)ᶜ := by
  rintro ⟨f⟩
  have hinj : Function.Injective (fun i : Fin n => (f i).1) := by
    intro i j hij
    by_contra hne
    have hadj := f.toHom.map_adj (show (⊤ : SimpleGraph (Fin n)).Adj i j from hne)
    apply hadj.2
    exact ⟨hij, fun heq => hne (f.injective (Prod.ext hij heq))⟩
  have hc := Fintype.card_le_of_injective _ hinj
  simp only [Fintype.card_fin] at hc
  omega

 
theorem ramsey_lower_counterexample {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) :
    ¬ RamseyProperty m n ((m - 1) * (n - 1)) := by
  intro h
  have hd := h.on_fintype (G := disjointCliques (n - 1) (m - 1)) (by
    simp only [Fintype.card_prod, Fintype.card_fin]
    exact le_of_eq (Nat.mul_comm _ _))
  rcases hd with hc | hk
  · exact disjointCliques_no_cycle (by omega) (by omega) hc
  · exact disjointCliques_no_compl_clique (by omega) hk

 
theorem ramsey_property_lower_bound {m n N : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n)
    (hN : RamseyProperty m n N) : (m - 1) * (n - 1) + 1 ≤ N := by
  by_contra hnle
  exact ramsey_lower_counterexample hm hn (hN.mono (by omega))

end CycleClique

end OAI
