import OAI.Combinatorics.Ramsey.CycleClique.Construction.TerminalWeights
import OAI.Combinatorics.Ramsey.CycleClique.Construction.PackingOptions

namespace OAI

/-! Uniform packings used in the first three terminal cases. Their graph
premises concern actual balls and forbidden outside paths. -/

namespace CycleClique.Construction
open scoped Classical

variable {V : Type} [Fintype V] {G : SimpleGraph V}

theorem radius_two_triple_of_separated_first_pair (hCE : CEAlphaTwo) {k t : ℕ}
    (hk : 5 ≤ k) (ht : 1 ≤ t) (hcycle : ¬ HasCycle G (k + 1))
    (hclique : G.cliqueNum ≤ t) {X R : Finset V} {x : V}
    (hx : x ∈ R) (hRX : R ⊆ X) (hXk : X.card ≤ k) (hsize : 2 * t < k + R.card)
    (hexpand : ∀ I : Finset V, G.IsIndepSet (I : Set V) → I.Nonempty →
      k * I.card + 1 ≤ (closedNeighborhood G I).card)
    (hforbid : ∀ y ∈ R, x ≠ y → ∀ d, 1 ≤ d → d ≤ 2 →
      ¬ OutsidePath G (X : Set V) x y d)
    (hpair : HasIndependent (G.induce (outsideBallFinset G X x 1 : Set V)) 2) :
    HasIndependent (G.induce (outsideBallFinset G X x 2 : Set V)) 3 := by
  obtain ⟨I, hI, hind, hIcard⟩ := exists_independent_subset hpair
  have hAX : R.erase x ⊆ X := fun _ hy => hRX (Finset.mem_of_mem_erase hy)
  have hf : ∀ y ∈ R.erase x, ∀ d, 1 ≤ d → d ≤ 1 + 1 →
      ¬ PositiveOutsidePath G (X : Set V) x y d := by
    intro y hy d hd hdb hp
    exact hforbid y (Finset.mem_of_mem_erase hy) (Finset.ne_of_mem_erase hy).symm
      d hd (by omega) hp.toOutside
  have havoid := closedNeighborhood_avoids_forbidden (hRX hx) hAX (by simp) hI hf
  have hne : I.Nonempty := Finset.card_pos.mp (by omega)
  have hg := outsideBall_growth hAX hI havoid (hexpand I hind hne)
  rw [hIcard] at hg
  have hc := Finset.card_erase_add_one hx
  have hRpos : 1 ≤ R.card := Finset.card_pos.mpr ⟨x, hx⟩
  simp only [Nat.reduceAdd] at hg
  apply size_test hCE hk ht hcycle hclique (outsideBallFinset G X x 2)
  exact max_lt_iff.mpr ⟨by omega, by omega⟩

theorem radius_two_packing_bound {k : ℕ} (hbound : IndependenceBound G k)
    {X R : Finset V} (hRX : R ⊆ X)
    (hweight : ∀ x ∈ R,
      HasIndependent (G.induce (outsideBallFinset G X x 2 : Set V)) 3)
    (hforbid : ∀ x ∈ R, ∀ y ∈ R, x ≠ y → ∀ d, 1 ≤ d → d ≤ 6 →
      ¬ OutsidePath G (X : Set V) x y d) : 3 * R.card ≤ k := by
  have hp := packing_test hbound X (fun i : R => i.val) (fun _ => 3) (fun _ => 3)
    Subtype.val_injective (fun i => hRX i.property)
    (fun i => by simpa only [packingRegion] using hweight i i.property)
    (fun i j hij => by
      simp only [PackingCompatible, OfNat.ofNat_ne_zero, false_and, ↓reduceIte]
      intro d hd hdb
      exact hforbid i i.property j j.property (fun h => hij (Subtype.ext h)) d hd
        (by omega))
  simpa [Nat.mul_comm] using hp

theorem terminal_uniform_packing_contradiction (hCE : CEAlphaTwo) {k t : ℕ}
    (ht : 9 ≤ t) (hklo : 2 * t - 2 ≤ k) (hkhi : k ≤ 2 * t + 1)
    (hcycle : ¬ HasCycle G (k + 1)) (hclique : G.cliqueNum ≤ t)
    (hbound : IndependenceBound G k) {X R : Finset V}
    (hRX : R ⊆ X) (hXk : X.card ≤ k) (hRlarge : t - 2 ≤ R.card)
    (hexpand : ∀ I : Finset V, G.IsIndepSet (I : Set V) → I.Nonempty →
      k * I.card + 1 ≤ (closedNeighborhood G I).card)
    (hpair : ∀ x ∈ R,
      HasIndependent (G.induce (outsideBallFinset G X x 1 : Set V)) 2)
    (hforbid : ∀ x ∈ R, ∀ y ∈ R, x ≠ y → ∀ d, 1 ≤ d → d ≤ 6 →
      ¬ OutsidePath G (X : Set V) x y d) : False := by
  have htriple : ∀ x ∈ R,
      HasIndependent (G.induce (outsideBallFinset G X x 2 : Set V)) 3 := by
    intro x hx
    exact radius_two_triple_of_separated_first_pair hCE (by omega) (by omega) hcycle
      hclique hx hRX hXk (by omega) hexpand
      (fun y hy hne d hd hdb => hforbid x hx y hy hne d hd (by omega)) (hpair x hx)
  have hp := radius_two_packing_bound hbound hRX htriple hforbid
  omega

theorem terminal_mixed_packing_contradiction (hbound : IndependenceBound G 19)
    {X R A : Finset V} (hRX : R ⊆ X) (hAR : A ⊆ R)
    (hR : R.card = 9) (hA : A.card = 4)
    (hweight : ∀ x ∈ R, HasIndependent
      (G.induce (outsideBallFinset G X x (if x ∈ A then 2 else 1) : Set V))
      (if x ∈ A then 3 else 2))
    (hforbid : ∀ x ∈ R, ∀ y ∈ R, x ≠ y → ∀ d, 1 ≤ d →
      d ≤ (if x ∈ A then 3 else 2) + (if y ∈ A then 3 else 2) →
      ¬ OutsidePath G (X : Set V) x y d) : False := by
  have hp := packing_test hbound X (fun i : R => i.val)
    (fun i => if i.val ∈ A then 3 else 2) (fun i => if i.val ∈ A then 3 else 2)
    Subtype.val_injective (fun i => hRX i.property)
    (fun i => by
      have hi := hweight i i.property
      have hregion : packingRegion G X (i : V) (if (i : V) ∈ A then 3 else 2) =
          outsideBallFinset G X (i : V) (if (i : V) ∈ A then 2 else 1) := by
        split_ifs <;> rfl
      change HasIndependent
        (G.induce (packingRegion G X (i : V) (if (i : V) ∈ A then 3 else 2) : Set V))
        (if (i : V) ∈ A then 3 else 2)
      rw [hregion]
      exact hi)
    (fun i j hij => by
      have hf := hforbid i i.property j j.property (fun h => hij (Subtype.ext h))
      by_cases hia : i.val ∈ A <;> by_cases hja : j.val ∈ A <;>
        simpa only [hia, hja, ↓reduceIte, PackingCompatible, OfNat.ofNat_ne_zero,
          false_and] using hf)
  have hcount : (∑ i : R, if i.val ∈ A then 3 else 2) = 22 := by
    have hpoint : ∀ i : R, (if i.val ∈ A then 3 else 2) =
        2 + (if i.val ∈ A then 1 else 0) := by intro i; split_ifs <;> rfl
    simp_rw [hpoint]
    rw [Finset.sum_add_distrib]
    have hfilter : (Finset.univ.filter (fun i : R => i.val ∈ A)).card = A.card := by
      apply Finset.card_bij (fun i _ => i.val)
      · intro i hi
        exact (Finset.mem_filter.mp hi).2
      · intro i hi j hj he
        exact Subtype.ext he
      · intro a ha
        exact ⟨⟨a, hAR ha⟩, by simp [ha], rfl⟩
    simp only [Finset.sum_const, smul_eq_mul, Finset.card_univ, Fintype.card_coe,
      hR, Finset.sum_boole, hfilter, hA]
    decide
  rw [hcount] at hp
  omega

end CycleClique.Construction

end OAI
