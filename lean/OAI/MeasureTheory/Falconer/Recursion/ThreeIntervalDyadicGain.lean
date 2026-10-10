import OAI.MeasureTheory.Falconer.Estimates.DyadicLocalGain
import OAI.MeasureTheory.Falconer.Recursion.ThreeIntervalData

namespace OAI

/-! # The three-interval cap gain on the actual occupied source tree -/

namespace Falconer
open Set MeasureTheory NormedSpace
open scoped ENNReal BigOperators
variable {d : ℕ}

theorem three_interval_dyadic_gain (μ ν : Measure (Space d))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (Q : DyadicCube d) (hQ : 0 < Q.side) {a b N J : ℕ}
    (hab : a ≤ b) (hbN : b ≤ N) (hJ : J ≤ b-a)
    (A P : Set (Space d)) (hA : μ Aᶜ = 0) {s : ℝ} (hs : 0 < s)
    (hsep : ∀ z ∈ A, ∀ x ∈ P, s ≤ ‖z-x‖)
    (G : Set (Space d × Space d)) (hG : MeasurableSet G)
    (hGcore : G ⊆ Q.occupiedTreeCore μ N ×ˢ P)
    (W : ℕ → ℝ) (cost : ℕ → ℝ≥0∞)
    {q c β γ η ξ : ℝ} (hc : 0 ≤ c)
    (hwidth : β*(N:ℝ) ≤ (b-a:ℕ))
    (hconst : ((2:ℝ)^J)^(q+c) ≤ ((2:ℝ)^N)^ξ)
    (hbudget : 20*η+4*ξ+γ ≤ c*β)
    (hsmall : ∀ j < 3,
      Real.sqrt d*(Q.side/(2:ℝ)^(threeIntervalDepth a b N (j+1))) ≤ s/2)
    (hW : ∀ j < 3,
      2*(Real.sqrt d*(Q.side/(2:ℝ)^(threeIntervalDepth a b N (j+1))))/(s/2)+
        2*(1/(2:ℝ)^N) ≤ W j)
    (hlocal : ∀ j < 3, ∀ p ∈ Q.occupiedPaths μ (threeIntervalDepth a b N j),
      ∃ H : Set (Space d × Space d), MeasurableSet H ∧
      ((ProbabilityTheory.cond μ (Q.descendant p).carrier).prod ν)
        ((G ∩ ((Q.descendant p).carrier ×ˢ univ)) \ H) ≤ cost j ∧
      ∀ z ∈ H, radialCollisionMass (ProbabilityTheory.cond μ (Q.descendant p).carrier)
        (W j) z ≤ threeIntervalFactor a b N J q c η j) :
    ∃ G' : Set (Space d × Space d), MeasurableSet G' ∧ G' ⊆ G ∧
      (μ.prod ν) (G \ G') ≤ (∑ j ∈ Finset.range 3, cost j)+
        4*ENNReal.ofReal (((2:ℝ)^N)^(-ξ)) ∧
      ∀ x u : Space d, μ {z | (z,x) ∈ G' ∧ ‖normalize (z-x)-u‖ ≤ 1/(2:ℝ)^N} ≤
        ENNReal.ofReal (((2:ℝ)^N)^(-q-γ)) := by
  obtain ⟨G',hG',hsub,hdel,hbound⟩ := dyadic_gain_of_local_prunings μ ν Q hQ N 3
    (threeIntervalDepth a b N) (fun _ hj => threeIntervalDepth_le hab hbN hj)
    (fun _ hj => threeIntervalDepth_mono hab hbN hj) A P hA hs hsep G hG hGcore
    (1/(2:ℝ)^N) W (ENNReal.ofReal (((2:ℝ)^N)^(-ξ)))
    (threeIntervalFactor a b N J q c η) cost (by positivity) ENNReal.ofReal_ne_top hsmall hW hlocal
  refine ⟨G',hG',hsub,?_,fun x u => (hbound x u).trans ?_⟩
  · norm_num at hdel
    exact hdel
  · exact threeIntervalFactor_product hab hbN hJ hc hwidth hconst hbudget

end Falconer

end OAI
