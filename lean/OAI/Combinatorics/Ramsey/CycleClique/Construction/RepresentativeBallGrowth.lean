import OAI.Combinatorics.Ramsey.CycleClique.Construction.RepresentativeExclusion
import OAI.Combinatorics.Ramsey.CycleClique.Construction.BallWeights
import OAI.Combinatorics.Ramsey.CycleClique.Construction.PackingOptions

namespace OAI

/-! The first and second representative-ball bounds of grow:degree and
grow:weights, with explicit forbidden-path premises. -/

namespace CycleClique.Construction
open scoped Classical

variable {V : Type} [Fintype V] {G : SimpleGraph V} {X R : Finset V} {x : V} {k : ℕ}

theorem representative_ball_one (hxR : x ∈ R) (hRX : R ⊆ X) (hXk : X.card ≤ k)
    (hexpand : ∀ v, k + 1 ≤ (closedNeighborhood G {v}).card)
    (hforbid : ∀ y ∈ R, x ≠ y → ¬ OutsidePath G (X : Set V) x y 1) :
    k + R.card ≤ (outsideBallFinset G X x 1).card + X.card := by
  have hxX := hRX hxR
  have hzero := outsideBall_initial_growth (A := ∅) hxX (by simp) (by simp)
    (by simp) (hexpand x)
  simp only [Finset.card_empty, Nat.add_zero] at hzero
  have hnonempty : (outsideBallFinset G X x 0).Nonempty := by
    apply Finset.card_pos.mp
    omega
  obtain ⟨u, hu⟩ := hnonempty
  let A := R.erase x
  have hAX : A ⊆ X := fun _ hv => hRX (Finset.mem_of_mem_erase hv)
  have hxA : x ∉ A := by simp [A]
  have hf : ∀ y ∈ A, ∀ d, 1 ≤ d → d ≤ 0 + 1 →
      ¬ PositiveOutsidePath G (X : Set V) x y d := by
    intro y hy d hd hdb hp
    have he : d = 1 := by omega
    subst d
    exact hforbid y (Finset.mem_of_mem_erase hy)
      (Finset.ne_of_mem_erase hy).symm hp.toOutside
  have hI : ({u} : Finset V) ⊆ outsideBallFinset G X x 0 := by simpa using hu
  have havoid := closedNeighborhood_avoids_forbidden hxX hAX hxA hI hf
  have hg := outsideBall_growth hAX hI havoid (by simpa using hexpand u)
  have hc : A.card + 1 = R.card := Finset.card_erase_add_one hxR
  simp only [Finset.card_singleton, Nat.mul_one, Nat.reduceAdd] at hg
  omega

theorem representative_ball_two_pair (hxR : x ∈ R) (hRX : R ⊆ X) (hXk : X.card ≤ k)
    (hclique : G.cliqueNum ≤ R.card)
    (hexpand : ∀ v, k + 1 ≤ (closedNeighborhood G {v}).card)
    (hforbid : ∀ y ∈ R, x ≠ y → ∀ d, 1 ≤ d → d ≤ 2 →
      ¬ OutsidePath G (X : Set V) x y d) :
    HasIndependent (G.induce (outsideBallFinset G X x 2 : Set V)) 2 := by
  have hfirst := representative_ball_one hxR hRX hXk hexpand
    (fun y hy hne => hforbid y hy hne 1 (by omega) (by omega))
  apply outsideBall_exception_pair (r := 1) (k := k) (t := R.card)
    (A := R.erase x) (hRX hxR) (fun _ hy => hRX (Finset.mem_of_mem_erase hy))
    (by simp) hclique (by omega)
  · have hc := Finset.card_erase_add_one hxR
    omega
  · exact hexpand
  · intro y hy d hd hdb hp
    exact hforbid y (Finset.mem_of_mem_erase hy) (Finset.ne_of_mem_erase hy).symm
      d hd hdb hp.toOutside

theorem representative_ball_two_triple (hCE : CEAlphaTwo) (hk : 5 ≤ k)
    (hxR : x ∈ R) (hRX : R ⊆ X) (hXk : X.card ≤ k) (hRk : R.card < k)
    (hcycle : ¬ HasCycle G (k + 1)) (hclique : G.cliqueNum ≤ R.card)
    (hexpand : ∀ I : Finset V, G.IsIndepSet (I : Set V) → I.Nonempty →
      k * I.card + 1 ≤ (closedNeighborhood G I).card)
    (hforbid : ∀ y ∈ R, x ≠ y → ∀ d, 1 ≤ d → d ≤ 2 →
      ¬ OutsidePath G (X : Set V) x y d)
    (hnotclique : ¬ G.IsClique (outsideBallFinset G X x 1 : Set V)) :
    HasIndependent (G.induce (outsideBallFinset G X x 2 : Set V)) 3 := by
  obtain ⟨I, hI, hind, hIcard⟩ := exists_independent_subset (independent_pair_of_not_clique hnotclique)
  have hAX : R.erase x ⊆ X := fun _ hy => hRX (Finset.mem_of_mem_erase hy)
  have hf : ∀ y ∈ R.erase x, ∀ d, 1 ≤ d → d ≤ 1 + 1 →
      ¬ PositiveOutsidePath G (X : Set V) x y d := by
    intro y hy d hd hdb hp
    exact hforbid y (Finset.mem_of_mem_erase hy) (Finset.ne_of_mem_erase hy).symm
      d hd hdb hp.toOutside
  have havoid := closedNeighborhood_avoids_forbidden (hRX hxR) hAX (by simp) hI hf
  have hne : I.Nonempty := Finset.card_pos.mp (by omega)
  have hg := outsideBall_growth hAX hI havoid (hexpand I hind hne)
  have hc := Finset.card_erase_add_one hxR
  have hRpos : 1 ≤ R.card := Finset.card_pos.mpr ⟨x, hxR⟩
  apply size_test hCE hk hRpos hcycle hclique (outsideBallFinset G X x 2)
  rw [hIcard] at hg
  simp only [Nat.reduceAdd] at hg
  exact max_lt_iff.mpr ⟨by omega, by omega⟩

theorem exists_short_path_of_twice_card_gt (hbound : IndependenceBound G k)
    (hRX : R ⊆ X) (hXk : X.card ≤ k) (hclique : G.cliqueNum ≤ R.card)
    (hexpand : ∀ v, k + 1 ≤ (closedNeighborhood G {v}).card)
    (hlarge : k < 2 * R.card) :
    ∃ x ∈ R, ∃ y ∈ R, x ≠ y ∧ ∃ d, 1 ≤ d ∧ d ≤ 6 ∧
      OutsidePath G (X : Set V) x y d := by
  by_contra hn
  push Not at hn
  have hf : ∀ x ∈ R, ∀ y ∈ R, x ≠ y → ∀ d, 1 ≤ d → d ≤ 6 →
      ¬ OutsidePath G (X : Set V) x y d := by
    intro x hx y hy hne d hd hdb
    exact hn x hx y hy hne d hd hdb
  have hpack := packing_test hbound X (fun i : R => i.val) (fun _ => 3) (fun _ => 2)
    Subtype.val_injective (fun i => hRX i.property)
    (fun i => by
      have h := representative_ball_two_pair i.property hRX hXk hclique hexpand
        (fun y hy hne d hd hdb => hf i i.property y hy hne d hd (by omega))
      simpa [packingRegion] using h)
    (fun i j hij => by
      simp only [PackingCompatible, OfNat.ofNat_ne_zero, false_and, ↓reduceIte]
      intro d hd hdb
      exact hf i i.property j j.property (fun h => hij (Subtype.ext h)) d hd hdb)
  have hnum : 2 * R.card ≤ k := by simpa [mul_comm] using hpack
  omega

end CycleClique.Construction

end OAI
