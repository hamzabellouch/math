import OAI.Combinatorics.Ramsey.CycleClique.Construction.BallRecurrence
import OAI.Combinatorics.Ramsey.CycleClique.Construction.OutsidePathRules

namespace OAI

/-! Soundness of the finite checker's numerical ball recurrence on labelled
ground vertices. A matrix entry records a proved forbidden outside parameter. -/

namespace CycleClique.Construction
abbrev ForbiddenMatrix (n : ℕ) := Fin n → Fin n → Finset ℕ

def ForbiddenMatrix.Sound {V : Type*} {n : ℕ} (M : ForbiddenMatrix n)
    (G : SimpleGraph V) (X : Finset V) (f : Fin n → V) : Prop :=
  ∀ i j d, d ∈ M i j → ¬ OutsidePath G (X : Set V) (f i) (f j) d

def zeroAvoidSet {n : ℕ} (M : ForbiddenMatrix n) (i : Fin n) : Finset (Fin n) :=
  Finset.univ.filter (fun j => i ≠ j ∧ 0 ∈ M i j)

def ballAvoidSet {n : ℕ} (M : ForbiddenMatrix n) (i : Fin n) (b : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun j => i ≠ j ∧ Finset.Icc 1 b ⊆ M i j)

def indexedBallState {n : ℕ} (M : ForbiddenMatrix n) (k t : ℕ) (i : Fin n) :
    ℕ → ℕ × ℕ
  | 0 =>
    let b := k + 1 + (zeroAvoidSet M i).card - n
    (b, if t ≤ b then 2 else 1)
  | r + 1 =>
    let prev := indexedBallState M k t i r
    let T := (ballAvoidSet M i (r + 1)).card
    (nextBallSize k n T prev.1 prev.2, nextBallWeight k n t T prev.1 prev.2)

theorem indexedBallState_positive {n : ℕ} (M : ForbiddenMatrix n) (k t : ℕ)
    (i : Fin n) (hbase : 0 < k + 1 + (zeroAvoidSet M i).card - n) (r : ℕ) :
    0 < (indexedBallState M k t i r).1 ∧ 0 < (indexedBallState M k t i r).2 := by
  induction r with
  | zero =>
    dsimp only [indexedBallState]
    exact ⟨hbase, by split_ifs <;> omega⟩
  | succ r ih =>
    dsimp only [indexedBallState, nextBallSize, nextBallWeight, ordinaryBallWeight]
    constructor
    · exact ih.1.trans_le (le_max_left _ _)
    · split_ifs <;> omega

variable {V : Type} [Fintype V] {G : SimpleGraph V}

theorem indexedBallState_sound (hCE : CEAlphaTwo) {n k t : ℕ}
    (hk : 5 ≤ k) (ht : 1 ≤ t) (hcycle : ¬ HasCycle G (k + 1))
    (hclique : G.cliqueNum ≤ t) {X : Finset V} {f : Fin n → V}
    (hf : Function.Injective f) (hfX : ∀ i, f i ∈ X) (hX : X.card = n)
    {M : ForbiddenMatrix n} (hM : M.Sound G X f)
    (hexpand : ∀ I : Finset V, G.IsIndepSet (I : Set V) → I.Nonempty →
      k * I.card + 1 ≤ (closedNeighborhood G I).card)
    (i : Fin n) (hbase : 0 < k + 1 + (zeroAvoidSet M i).card - n) (r : ℕ) :
    (indexedBallState M k t i r).1 ≤ (outsideBallFinset G X (f i) r).card ∧
      HasIndependent (G.induce (outsideBallFinset G X (f i) r : Set V))
        (indexedBallState M k t i r).2 := by
  classical
  induction r with
  | zero =>
    let A := (zeroAvoidSet M i).image f
    have hAX : A ⊆ X := by
      intro v hv
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hv
      exact hfX j
    have hiA : f i ∉ A := by
      intro hv
      obtain ⟨j, hj, he⟩ := Finset.mem_image.mp hv
      have hj' : i ≠ j ∧ 0 ∈ M i j := by
        simpa only [zeroAvoidSet, Finset.mem_filter, Finset.mem_univ, true_and] using hj
      exact hj'.1 (hf he).symm
    have hanti : ∀ v ∈ A, ¬ G.Adj (f i) v := by
      intro v hv
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hv
      have hj' : i ≠ j ∧ 0 ∈ M i j := by
        simpa only [zeroAvoidSet, Finset.mem_filter, Finset.mem_univ, true_and] using hj
      exact fun hadj => hM i j 0 hj'.2
        (outsidePath_zero.mpr hadj)
    have hAc : A.card = (zeroAvoidSet M i).card := Finset.card_image_of_injective _ hf
    have hsingle : k + 1 ≤ (closedNeighborhood G {f i}).card := by
      simpa only [Finset.card_singleton, Nat.mul_one] using
        hexpand {f i} (by simp) (by simp)
    have hb := outsideBall_initial_bounds (hfX i) hAX hiA hanti hclique hsingle
      (by rw [hAc, hX]; exact hbase)
    simpa only [indexedBallState, hAc, hX] using hb
  | succ r ih =>
    let A := (ballAvoidSet M i (r + 1)).image f
    have hAX : A ⊆ X := by
      intro v hv
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hv
      exact hfX j
    have hiA : f i ∉ A := by
      intro hv
      obtain ⟨j, hj, he⟩ := Finset.mem_image.mp hv
      have hj' : i ≠ j ∧ Finset.Icc 1 (r + 1) ⊆ M i j := by
        simpa only [ballAvoidSet, Finset.mem_filter, Finset.mem_univ, true_and] using hj
      exact hj'.1 (hf he).symm
    have hforbid : ∀ y ∈ A, ∀ d, 1 ≤ d → d ≤ r + 1 →
        ¬ PositiveOutsidePath G (X : Set V) (f i) y d := by
      intro y hy d hd hdb hp
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hy
      have hj' : i ≠ j ∧ Finset.Icc 1 (r + 1) ⊆ M i j := by
        simpa only [ballAvoidSet, Finset.mem_filter, Finset.mem_univ, true_and] using hj
      exact hM i j d (hj'.2 (Finset.mem_Icc.mpr ⟨hd, hdb⟩))
        hp.toOutside
    have hAc : A.card = (ballAvoidSet M i (r + 1)).card :=
      Finset.card_image_of_injective _ hf
    have hpos := indexedBallState_positive M k t i hbase r
    have hb := outsideBall_recursive_bounds hCE hk ht (hfX i) hAX hiA hcycle hclique
      hpos.1 ih.1 hpos.2 ih.2 hexpand hforbid
    simpa only [indexedBallState, hX, hAc] using hb

end CycleClique.Construction

end OAI
