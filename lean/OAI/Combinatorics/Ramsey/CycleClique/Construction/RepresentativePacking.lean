import OAI.Combinatorics.Ramsey.CycleClique.Construction.RepresentativeBallGrowth

namespace OAI

/-! Two nonclique first balls improve the separated packing from 2t to
2t+2, finishing the parity boundary once the path-system exclusions apply. -/

namespace CycleClique.Construction
open scoped Classical

variable {V : Type} [Fintype V] {G : SimpleGraph V} {X R : Finset V} {k : ℕ}

theorem exists_short_path_of_two_noncliques (hCE : CEAlphaTwo) (hk : 5 ≤ k)
    (hbound : IndependenceBound G k) (hRX : R ⊆ X) (hXk : X.card ≤ k)
    (hRk : R.card < k) (hkR : k ≤ 2 * R.card + 1)
    (hcycle : ¬ HasCycle G (k + 1)) (hclique : G.cliqueNum ≤ R.card)
    (hexpand : ∀ I : Finset V, G.IsIndepSet (I : Set V) → I.Nonempty →
      k * I.card + 1 ≤ (closedNeighborhood G I).card)
    (hspecial : ∃ a ∈ R, ∃ b ∈ R, a ≠ b ∧
      ¬ G.IsClique (outsideBallFinset G X a 1 : Set V) ∧
      ¬ G.IsClique (outsideBallFinset G X b 1 : Set V)) :
    ∃ x ∈ R, ∃ y ∈ R, x ≠ y ∧ ∃ d, 1 ≤ d ∧ d ≤ 6 ∧
      OutsidePath G (X : Set V) x y d := by
  obtain ⟨a, ha, b, hb, hab, hna, hnb⟩ := hspecial
  by_contra hn
  push Not at hn
  have hf : ∀ x ∈ R, ∀ y ∈ R, x ≠ y → ∀ d, 1 ≤ d → d ≤ 6 →
      ¬ OutsidePath G (X : Set V) x y d := by
    intro x hx y hy hne d hd hdb
    exact hn x hx y hy hne d hd hdb
  have hsingle : ∀ v, k + 1 ≤ (closedNeighborhood G {v}).card := by
    intro v
    simpa using hexpand {v} (by simp) (by simp)
  let α : R := ⟨a, ha⟩
  let β : R := ⟨b, hb⟩
  have hαβ : α ≠ β := fun h => hab (congrArg Subtype.val h)
  let weight : R → ℕ := fun i => 2 + (if i = α then 1 else 0) + (if i = β then 1 else 0)
  have hweight : ∀ i : R,
      HasIndependent (G.induce (packingRegion G X i 3 : Set V)) (weight i) := by
    intro i
    by_cases hia : i = α
    · subst i
      have h := representative_ball_two_triple hCE hk ha hRX hXk hRk hcycle hclique hexpand
        (fun y hy hne d hd hdb => hf a ha y hy hne d hd (by omega)) hna
      simpa [packingRegion, weight, α, hαβ] using h
    · by_cases hib : i = β
      · subst i
        have h := representative_ball_two_triple hCE hk hb hRX hXk hRk hcycle hclique hexpand
          (fun y hy hne d hd hdb => hf b hb y hy hne d hd (by omega)) hnb
        simpa [packingRegion, weight, β, hαβ.symm] using h
      · have h := representative_ball_two_pair i.property hRX hXk hclique hsingle
          (fun y hy hne d hd hdb => hf i i.property y hy hne d hd (by omega))
        simpa [packingRegion, weight, hia, hib] using h
  have hp := packing_test hbound X (fun i : R => i.val) (fun _ => 3) weight
    Subtype.val_injective (fun i => hRX i.property) hweight
    (fun i j hij => by
      simp only [PackingCompatible, OfNat.ofNat_ne_zero, false_and, ↓reduceIte]
      intro d hd hdb
      exact hf i i.property j j.property (fun h => hij (Subtype.ext h)) d hd hdb)
  have hsum : ∑ i : R, weight i = 2 * R.card + 2 := by
    simp [weight, Finset.sum_add_distrib, mul_comm]
  rw [hsum] at hp
  omega

end CycleClique.Construction

end OAI
