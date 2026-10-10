import OAI.MeasureTheory.Falconer.Graphs.GraphNormalization
import OAI.MeasureTheory.Falconer.Recursion.BranchExponentAlgebra

namespace OAI

/-! # The scheduled branch ledger with the ambient dimension retained

The policy branches and their payment identities are scalar combinatorics.
Their final-potential bound uses the dimension-dependent Lipschitz
constant.
-/
namespace Falconer
open PlanarFalconer
open scoped BigOperators

theorem dimension_profile_increment_le {A : ℕ → ℝ} {N : ℕ} {d : ℝ}
    (hN : 0 < N) (hd : 0 ≤ d)
    (hlip : ∀ i j, i ≤ N → j ≤ N → |A i-A j| ≤ d*|(i:ℝ)-j|/N)
    {i j : ℕ} (hi : i ≤ N) (hj : j ≤ N) : |A i-A j| ≤ d := by
  have hNR : (0:ℝ) < N := Nat.cast_pos.mpr hN
  have hi' : (i:ℝ) ≤ N := Nat.cast_le.mpr hi
  have hj' : (j:ℝ) ≤ N := Nat.cast_le.mpr hj
  have habs : |(i:ℝ)-j| ≤ N := abs_le.mpr
    ⟨by linarith [Nat.cast_nonneg (α := ℝ) i],by linarith [Nat.cast_nonneg (α := ℝ) j]⟩
  calc
    _ ≤ d*|(i:ℝ)-j|/N := hlip i j hi hj
    _ ≤ d*(N:ℝ)/N := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left habs hd) hNR.le
    _ = d := by field_simp

theorem dimension_branch_cost_le {A : ℕ → ℝ} {N q : ℕ} {σ d : ℝ}
    (hN : 0 < N) (hq : 0 < q) (hd : 0 ≤ d)
    (hlip : ∀ i j, i ≤ N → j ≤ N → |A i-A j| ≤ d*|(i:ℝ)-j|/N)
    {s u : BranchState} {l : BranchLabel} (h : BranchStep A N q σ s l u)
    (hs : s.Valid N σ) (hu : u.Valid N σ) : branchCost A s l u ≤ d := by
  have hbound {a t i : ℕ} (hat : a ≤ t) (ht : t ≤ N) (hi : i ≤ N) :
      A i-intervalMin A a t ≤ d := by
    obtain ⟨j,_,hjt,hmin⟩ := intervalMin_attained A hat
    rw [hmin]
    exact (le_abs_self _).trans (dimension_profile_increment_le hN hd hlip hi (hjt.trans ht))
  have hn := h.nested hq hs
  have hsd := BranchState.valid_depths hs
  have hud := BranchState.valid_depths hu
  cases h <;> simp only [branchCost]
  · exact hbound hn.2 hsd.2 hud.2
  · exact hd
  · exact hbound hn.1 (hud.1.trans hud.2) (hud.1.trans hud.2)
  · exact hd
  · exact hd
  · exact hbound hn.1 (hud.1.trans hud.2) (hud.1.trans hud.2)

theorem dimension_ancestor_exponent_bound {A : ℕ → ℝ} {N q n : ℕ} {lam σ ε d : ℝ}
    (b : PolicyBranch A N q σ n) (hN : 0 < N) (hq : 0 < q) (hd : 0 ≤ d)
    (hloss : 0 ≤ 4000*(lam+σ))
    (hlip : ∀ i j, i ≤ N → j ≤ N → |A i-A j| ≤ d*|(i:ℝ)-j|/N) :
    ∑ j ∈ Finset.range n, branchExponent A lam σ ε (b.state j) (b.label j) (b.state (j+1)) ≤
      (n:ℝ)*(3*d+4000*(lam+σ)+ε) := by
  calc
    _ ≤ ∑ _j ∈ Finset.range n, (3*d+4000*(lam+σ)+ε) := by
      apply Finset.sum_le_sum
      intro j hj
      have hj' := Finset.mem_range.mp hj
      have hs := b.valid j hj'.le
      have hu := b.valid (j+1) (by omega)
      have hc := dimension_branch_cost_le hN hq hd hlip (b.step j hj') hs hu
      have hi := abs_le.mp (dimension_profile_increment_le hN hd hlip
        ((BranchState.valid_depths hu).1.trans (BranchState.valid_depths hu).2)
        ((BranchState.valid_depths hs).1.trans (BranchState.valid_depths hs).2))
      unfold branchExponent
      split_ifs <;> linarith
    _ = _ := by simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul]

theorem dimension_branch_cost_bound {A : ℕ → ℝ} {N q n : ℕ} {σ d : ℝ}
    (b : PolicyBranch A N q σ n) (hN : 0 < N) (hq : 0 < q)
    (hslack : σ*(N:ℝ) ≤ q) (hd : 0 ≤ d)
    (hlip : ∀ i j, i ≤ N → j ≤ N → |A i-A j| ≤ d*|(i:ℝ)-j|/N)
    (hinit : (b.state 0).start+10*q ≤ (b.state 0).finish) :
    ∑ j ∈ Finset.range n, branchCost A (b.state j) (b.label j) (b.state (j+1)) ≤
      2*A (b.state n).start+20*d*(q:ℝ)/N-
        potential A (b.state 0).start (b.state 0).finish (10*q) := by
  have hQ : 0 < 10*q := by omega
  have hpot (a t f : ℕ) (hw : a+10*q ≤ t) (ht : t ≤ N)
      (haf : a ≤ f) (hft : f ≤ t) :
      potential A a t (10*q) ≤ 2*A f+20*d*(q:ℝ)/N := by
    have hh := last_potential_bound A hQ hw haf hft hd hN
      (fun i _ hit => hlip i f (hit.trans ht) (hft.trans ht))
    convert hh using 1
    push_cast
    ring
  have hfinal := BranchState.valid_depths (b.valid n le_rfl)
  by_cases hw : (b.state n).start+10*q ≤ (b.state n).finish
  · have hc := b.costs_le_potential hq hslack hw
    have hf := hpot _ _ _ hw hfinal.2 le_rfl hfinal.1
    linarith
  · cases n with
    | zero => exact (hw hinit).elim
    | succ n =>
      have hs := b.step n (by omega)
      have hn := hs.nested hq (b.valid n (by omega))
      have hp := hs.nonterminal
      have hpwide : (b.state n).start+10*q ≤ (b.state n).finish := by omega
      have hdepth := BranchState.valid_depths (b.valid n (by omega))
      have hc := (b.initialSegment n (by omega)).costs_le_potential hq hslack hpwide
      dsimp only [PolicyBranch.initialSegment] at hc
      have hz := hs.short_cost_zero hq (b.valid n (by omega)) hslack (by omega)
      have hf := hpot _ _ _ hpwide hdepth.2 hn.1 (hfinal.1.trans hn.2)
      rw [Finset.sum_range_succ,hz,add_zero]
      linarith

theorem dimension_source_branch_exponent {A : ℕ → ℝ} {N n : ℕ} {lam σ κ η d : ℝ}
    (hN : 0 < N) (hlam : 0 ≤ lam) (hσ : 0 < σ) (hκ : 0 < κ) (hκ1 : κ ≤ 1)
    (hη : 0 < η) (hd : 0 ≤ d)
    (hceil : ⌈10*σ*(N:ℝ)⌉₊ < sourcePolicyBlock N κ)
    (hslack : σ*(N:ℝ) ≤ sourcePolicyBlock N κ)
    (hlip : ∀ i j, i ≤ N → j ≤ N → |A i-A j| ≤ d*|(i:ℝ)-j|/N)
    (b : PolicyBranch A N (sourcePolicyBlock N κ) σ n)
    (hinit : (b.state 0).start+10*sourcePolicyBlock N κ ≤ (b.state 0).finish) :
    ∑ j ∈ Finset.range n,
      branchExponent A lam σ (η/(2*(1+20/κ+1/σ))) (b.state j) (b.label j) (b.state (j+1)) ≤
      2*A (b.state 0).start-
        potential A (b.state 0).start (b.state 0).finish (10*sourcePolicyBlock N κ)+
        20*d*(sourcePolicyBlock N κ:ℝ)/N+80000*(lam+σ)/κ+η/2 := by
  have hc := dimension_branch_cost_bound b hN (sourcePolicyBlock_pos hN hκ)
    hslack hd hlip hinit
  have hb := source_branch_count_bounds hN hσ hκ hκ1 hceil b
  let D : ℝ := 1+20/κ+1/σ
  have hD : 0 < D := by dsimp [D]; positivity
  have hηD : 0 ≤ η/(2*D) := by positivity
  have htime : (n:ℝ)*(η/(2*D)) ≤ η/2 := by
    have hn : (n:ℝ) ≤ D := by dsimp [D]; linarith [hb.2.2]
    calc
      _ ≤ D*(η/(2*D)) := mul_le_mul_of_nonneg_right hn hηD
      _ = η/2 := by field_simp
  have hloss : (branchNonlowCount b.label n:ℝ)*(4000*(lam+σ)) ≤ 80000*(lam+σ)/κ := by
    calc
      _ ≤ (20/κ)*(4000*(lam+σ)) := mul_le_mul_of_nonneg_right hb.1 (by positivity)
      _ = _ := by ring
  rw [branch_exponent_sum]
  dsimp only [D] at htime
  linarith

end Falconer

end OAI
