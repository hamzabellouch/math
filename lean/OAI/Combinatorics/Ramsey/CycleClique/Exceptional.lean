import Mathlib
import OAI.Combinatorics.Ramsey.CycleClique.Basic
import OAI.Combinatorics.Ramsey.CycleClique.ColouredPaths

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem neighborhood_compl_clique_of_triangle_free {V : Type*} {G : SimpleGraph V}
    (hfree : ¬ (⊤ : SimpleGraph (Fin 3)) ⊑ G) (v : V) :
    Gᶜ.IsClique (G.neighborSet v) := by
  classical
  intro a ha b hb hab
  refine ⟨hab, fun hadj => ?_⟩
  have hc : G.IsNClique 3 {v, a, b} :=
    SimpleGraph.is3Clique_triple_iff.mpr ⟨ha, hb, hadj⟩
  exact hfree ((SimpleGraph.not_cliqueFree_iff_top_isContained 3).mp hc.not_cliqueFree)

 
theorem ramsey_three_three_upper : RamseyProperty 3 3 6 := by
  classical
  intro G
  rw [SimpleGraph.cycleGraph_three_eq_top]
  by_contra hn
  obtain ⟨hred, hblue⟩ := not_or.mp hn
  have h₁ := clique_ncard_lt hblue (neighborhood_compl_clique_of_triangle_free hred (0 : Fin 6))
  have hred' : ¬ (⊤ : SimpleGraph (Fin 3)) ⊑ Gᶜᶜ := by simpa using hred
  have h₂ := clique_ncard_lt hred' (neighborhood_compl_clique_of_triangle_free hblue (0 : Fin 6))
  rw [ncard_neighborSet] at h₁ h₂
  rw [SimpleGraph.degree_compl] at h₂
  simp only [Fintype.card_fin] at h₂
  omega

 
theorem RamseyProperty.mono {m n N M : ℕ} (h : RamseyProperty m n N) (hNM : N ≤ M) :
    RamseyProperty m n M := by
  intro G
  let f : Fin N → Fin M := Fin.castLE hNM
  let H := G.comap f
  have hc : H ⊑ G := ⟨⟨⟨f, fun {a b} hab => hab⟩, Fin.castLE_injective hNM⟩⟩
  have hcc : Hᶜ ⊑ Gᶜ := by
    refine ⟨⟨⟨f, fun {a b} hab => ?_⟩, Fin.castLE_injective hNM⟩⟩
    exact ⟨fun heq => hab.1 (Fin.castLE_injective hNM heq), hab.2⟩
  rcases h H with hcycle | hclique
  · exact Or.inl (hcycle.trans hc)
  · exact Or.inr (hclique.trans hcc)

 
theorem ramsey_three_three_lower : ¬ RamseyProperty 3 3 5 := by
  intro h
  have proof5 : ∀ a b c : Fin 5,
      ¬ ((SimpleGraph.cycleGraph 5).Adj a b ∧ (SimpleGraph.cycleGraph 5).Adj a c ∧
        (SimpleGraph.cycleGraph 5).Adj b c) ∧
      ¬ ((SimpleGraph.cycleGraph 5)ᶜ.Adj a b ∧ (SimpleGraph.cycleGraph 5)ᶜ.Adj a c ∧
        (SimpleGraph.cycleGraph 5)ᶜ.Adj b c) := by decide
  have hr : (SimpleGraph.cycleGraph 5).CliqueFree 3 := by
    intro s hs
    obtain ⟨a, b, c, hab, hac, hbc, _⟩ := SimpleGraph.is3Clique_iff.mp hs
    exact (proof5 a b c).1 ⟨hab, hac, hbc⟩
  have hb : (SimpleGraph.cycleGraph 5)ᶜ.CliqueFree 3 := by
    intro s hs
    obtain ⟨a, b, c, hab, hac, hbc, _⟩ := SimpleGraph.is3Clique_iff.mp hs
    exact (proof5 a b c).2 ⟨hab, hac, hbc⟩
  rcases h (SimpleGraph.cycleGraph 5) with hred | hblue
  · rw [SimpleGraph.cycleGraph_three_eq_top] at hred
    exact hred.not_cliqueFree hr
  · exact hblue.not_cliqueFree hb

 
theorem exceptional : cycleCliqueRamsey 3 3 = 6 := by
  apply le_antisymm
  · exact Nat.sInf_le ramsey_three_three_upper
  · have hmem : RamseyProperty 3 3 (cycleCliqueRamsey 3 3) :=
      Nat.sInf_mem (s := {N | RamseyProperty 3 3 N}) ⟨6, ramsey_three_three_upper⟩
    by_contra hn
    exact ramsey_three_three_lower (hmem.mono (by omega))

end CycleClique

end OAI
