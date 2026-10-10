import OAI.Combinatorics.Ramsey.CycleClique.Construction.BallWeights
import OAI.Combinatorics.Ramsey.CycleClique.Construction.IndependentPacking

namespace OAI

/-! The numerical size/weight recurrence of `finite:ball-bounds`.
Negative size lower bounds may be truncated to zero, because a radius-zero
option is used only when its lower bound is positive. -/

namespace CycleClique.Construction
def nextBallSize (k n T b u : ℕ) : ℕ := max b (k * u + 1 + T - n)

def ordinaryBallWeight (k t b u : ℕ) : ℕ :=
  max u (if max k (2 * t) < b then 3 else if t < b then 2 else 1)

def nextBallWeight (k n t T b u : ℕ) : ℕ :=
  let b' := nextBallSize k n T b u
  let u' := ordinaryBallWeight k t b' u
  if u' = 1 ∧ b = t ∧ b' = t ∧ n + t ≤ k + 1 + T then 2 else u'

variable {V : Type} [Fintype V] {G : SimpleGraph V}

theorem outsideBall_initial_bounds {X A : Finset V} {x : V} {k t : ℕ}
    (hx : x ∈ X) (hAX : A ⊆ X) (hxA : x ∉ A)
    (hanti : ∀ v ∈ A, ¬ G.Adj x v) (ht : G.cliqueNum ≤ t)
    (hexpand : k + 1 ≤ (closedNeighborhood G {x}).card)
    (hpos : 0 < k + 1 + A.card - X.card) :
    let b := k + 1 + A.card - X.card
    b ≤ (outsideBallFinset G X x 0).card ∧
      HasIndependent (G.induce (outsideBallFinset G X x 0 : Set V))
        (if t ≤ b then 2 else 1) := by
  dsimp only
  have hg := outsideBall_initial_growth hx hAX hxA hanti hexpand
  have hb : k + 1 + A.card - X.card ≤ (outsideBallFinset G X x 0).card := by omega
  refine ⟨hb, ?_⟩
  split_ifs with h
  · exact outsideBall_initial_pair hx ht (h.trans hb)
  · exact hasIndependent_one_of_nonempty (Finset.card_pos.mp (by omega))

theorem outsideBall_growth_of_weight {X A : Finset V} {x : V} {r k u : ℕ}
    (hx : x ∈ X) (hAX : A ⊆ X) (hxA : x ∉ A) (hu : 0 < u)
    (hind : HasIndependent (G.induce (outsideBallFinset G X x r : Set V)) u)
    (hexpand : ∀ I : Finset V, G.IsIndepSet (I : Set V) → I.Nonempty →
      k * I.card + 1 ≤ (closedNeighborhood G I).card)
    (hforbid : ∀ y ∈ A, ∀ d, 1 ≤ d → d ≤ r + 1 →
      ¬ PositiveOutsidePath G (X : Set V) x y d) :
    k * u + 1 + A.card ≤ (outsideBallFinset G X x (r + 1)).card + X.card := by
  obtain ⟨I, hI, hIind, hIcard⟩ := exists_independent_subset hind
  have hIne : I.Nonempty := Finset.card_pos.mp (by omega)
  have hg := outsideBall_growth hAX hI
    (closedNeighborhood_avoids_forbidden hx hAX hxA hI hforbid) (hexpand I hIind hIne)
  simpa only [hIcard] using hg

/-- One recursive step, retaining the exact strict pair/triple thresholds
and the equality exception under the alpha-two Hamiltonicity hypothesis. -/
theorem outsideBall_recursive_bounds (hCE : CEAlphaTwo)
    {X A : Finset V} {x : V} {r k t b u : ℕ}
    (hk : 5 ≤ k) (ht : 1 ≤ t) (hx : x ∈ X) (hAX : A ⊆ X) (hxA : x ∉ A)
    (hcycle : ¬ HasCycle G (k + 1)) (hclique : G.cliqueNum ≤ t)
    (hbpos : 0 < b) (hb : b ≤ (outsideBallFinset G X x r).card) (hu : 0 < u)
    (hind : HasIndependent (G.induce (outsideBallFinset G X x r : Set V)) u)
    (hexpand : ∀ I : Finset V, G.IsIndepSet (I : Set V) → I.Nonempty →
      k * I.card + 1 ≤ (closedNeighborhood G I).card)
    (hforbid : ∀ y ∈ A, ∀ d, 1 ≤ d → d ≤ r + 1 →
      ¬ PositiveOutsidePath G (X : Set V) x y d) :
    nextBallSize k X.card A.card b u ≤ (outsideBallFinset G X x (r + 1)).card ∧
      HasIndependent (G.induce (outsideBallFinset G X x (r + 1) : Set V))
        (nextBallWeight k X.card t A.card b u) := by
  have hmono := outsideBallFinset_mono (G := G) (X := X) (x := x) (Nat.le_succ r)
  have hcardmono := Finset.card_le_card hmono
  change (outsideBallFinset G X x r).card ≤
    (outsideBallFinset G X x (r + 1)).card at hcardmono
  have hg := outsideBall_growth_of_weight hx hAX hxA hu hind hexpand hforbid
  have hb' : nextBallSize k X.card A.card b u ≤
      (outsideBallFinset G X x (r + 1)).card := by
    change max b (k * u + 1 + A.card - X.card) ≤ _
    apply max_le
    · exact hb.trans hcardmono
    · omega
  refine ⟨hb', ?_⟩
  have hu' : HasIndependent (G.induce (outsideBallFinset G X x (r + 1) : Set V))
      (ordinaryBallWeight k t (nextBallSize k X.card A.card b u) u) := by
    apply hasIndependent_iff_le_indepNum.mpr
    apply max_le
    · exact (hasIndependent_induce_mono hmono hind).le_indepNum
    · split_ifs with hlarge hpair
      · exact (size_test hCE hk ht hcycle hclique _ (hlarge.trans_le hb')).le_indepNum
      · exact (independent_pair_of_card_gt_cliqueNum hclique
          (hpair.trans_le hb')).le_indepNum
      · exact (hasIndependent_one_of_nonempty
          (Finset.card_pos.mp (by omega))).le_indepNum
  unfold nextBallWeight
  dsimp only
  split_ifs with hexc
  · apply outsideBall_exception_pair hx hAX hxA hclique (by omega) hexc.2.2.2
      (fun v => ?_) hforbid
    simpa only [Finset.card_singleton, Nat.mul_one] using
      hexpand {v} (by simp) (by simp)
  · exact hu'

end CycleClique.Construction

end OAI
