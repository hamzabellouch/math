import OAI.MeasureTheory.Falconer.Recursion.BranchCounts
import OAI.MeasureTheory.Falconer.Recursion.BranchValidity

namespace OAI

namespace PlanarFalconer

noncomputable def branchCost (A : ℕ → ℝ) (s : BranchState) : BranchLabel → BranchState → ℝ
  | .suffix, u => A u.finish-intervalMin A u.finish s.finish
  | .high, u | .direct, u => height A s.start u.start
  | _, _ => 0

theorem BranchStep.cost_nonneg {A : ℕ → ℝ} {N q : ℕ} {sig : ℝ}
    {s u : BranchState} {label : BranchLabel} (h : BranchStep A N q sig s label u)
    (hq : 0 < q) (hv : s.Valid N sig) : 0 ≤ branchCost A s label u := by
  have hn := h.nested hq hv
  cases h <;> simp only [branchCost]
  · exact sub_nonneg.mpr (intervalMin_le A le_rfl hn.2)
  · exact le_rfl
  · exact height_nonneg A hn.1
  · exact le_rfl
  · exact le_rfl
  · exact height_nonneg A hn.1

theorem BranchStep.paid_width {A : ℕ → ℝ} {N q : ℕ} {sig : ℝ}
    {s u : BranchState} {label : BranchLabel} (h : BranchStep A N q sig s label u)
    (hq : 0 < q) (hv : s.Valid N sig) (hslack : sig*(N:ℝ) ≤ q)
    (hc : label = .suffix ∨ label = .high ∨ label = .direct) : u.start+10*q ≤ u.finish := by
  cases h with
  | suffix hw hs => exact (actual_suffix_policy_payment A hq hv.2 hw hs).1
  | high hw hs hm hg =>
    have hm := Finset.mem_Ioc.mp hm
    exact (actual_prefix_policy_payment A hq hv.2 hw hs hm.2 (high_depth_gap hm.2 hg hslack)).1
  | direct _ he => exact he.width
  | _ => simp at hc

theorem BranchStep.potential_payment {A : ℕ → ℝ} {N q : ℕ} {sig : ℝ}
    {s u : BranchState} {label : BranchLabel} (h : BranchStep A N q sig s label u)
    (hq : 0 < q) (hv : s.Valid N sig) (hslack : sig*(N:ℝ) ≤ q)
    (hu : u.start+10*q ≤ u.finish) :
    potential A s.start s.finish (10*q)+branchCost A s label u ≤
      potential A u.start u.finish (10*q) := by
  have hn := h.nested hq hv
  have hm := potential_mono A (by omega : 0 < 10*q) hu hn.1 hn.2
  cases h with
  | suffix hw hs => exact (actual_suffix_policy_payment A hq hv.2 hw hs).2
  | high hw hs hmem hg =>
    have hmem := Finset.mem_Ioc.mp hmem
    exact (actual_prefix_policy_payment A hq hv.2 hw hs hmem.2 (high_depth_gap hmem.2 hg hslack)).2
  | direct _ he => exact he.payment
  | _ => simpa only [branchCost,add_zero] using hm

theorem BranchStep.short_cost_zero {A : ℕ → ℝ} {N q : ℕ} {sig : ℝ}
    {s u : BranchState} {label : BranchLabel} (h : BranchStep A N q sig s label u)
    (hq : 0 < q) (hv : s.Valid N sig) (hslack : sig*(N:ℝ) ≤ q)
    (hu : u.finish < u.start+10*q) : branchCost A s label u = 0 := by
  have hc : ¬ (label = .suffix ∨ label = .high ∨ label = .direct) := by
    intro hl
    exact (not_le_of_gt hu) (h.paid_width hq hv hslack hl)
  cases label <;> simp_all [branchCost]

def DiscreteProfileLipschitz (A : ℕ → ℝ) (N : ℕ) : Prop :=
  ∀ i ≤ N, ∀ j ≤ N, |A i-A j| ≤ |(i:ℝ)-j|/(N:ℝ)

theorem potential_le_final_start {A : ℕ → ℝ} {N a t f Q : ℕ}
    (hN : 0 < N) (hA : DiscreteProfileLipschitz A N)
    (hQ : 0 < Q) (hw : a+Q ≤ t) (ht : t ≤ N) (haf : a ≤ f) (hft : f ≤ t) :
    potential A a t Q ≤ 2*A f+2*(Q:ℝ)/N := by
  have hNR : (0:ℝ) < N := Nat.cast_pos.mpr hN
  have hb := potential_near_final A hQ hw haf hft (e := (Q:ℝ)/N) ?_
  · simpa only [mul_div_assoc] using hb
  intro j _ hjt hjf hfj
  have hd : |(j:ℝ)-f| ≤ (Q:ℝ) := by
    have hjR : (j:ℝ) ≤ (f:ℝ)+Q := by exact_mod_cast hjf
    have hfR : (f:ℝ) ≤ (j:ℝ)+Q := by exact_mod_cast hfj
    exact abs_le.mpr ⟨by linarith,by linarith⟩
  have hh := (hA j (hjt.trans ht) f (hft.trans ht)).trans (div_le_div_of_nonneg_right hd hNR.le)
  have hh' := (le_abs_self (A j-A f)).trans hh
  linarith

namespace PolicyBranch
variable {A : ℕ → ℝ} {N q n : ℕ} {sig : ℝ}

theorem costs_le_potential (b : PolicyBranch A N q sig n) (hq : 0 < q)
    (hslack : sig*(N:ℝ) ≤ q) (hfinal : (b.state n).start+10*q ≤ (b.state n).finish) :
    ∑ j ∈ Finset.range n, branchCost A (b.state j) (b.label j) (b.state (j+1)) ≤
      potential A (b.state n).start (b.state n).finish (10*q)-
        potential A (b.state 0).start (b.state 0).finish (10*q) := by
  apply branch_cost_bound (fun j => potential A (b.state j).start (b.state j).finish (10*q))
    (fun j => branchCost A (b.state j) (b.label j) (b.state (j+1))) n
  intro j hj
  apply (b.step j hj).potential_payment hq (b.valid j hj.le) hslack
  by_cases he : j+1 = n
  · simpa only [he] using hfinal
  · have hw := (b.step (j+1) (by omega)).nonterminal
    omega

theorem costs_le_final_start (b : PolicyBranch A N q sig n) (hN : 0 < N) (hq : 0 < q)
    (hslack : sig*(N:ℝ) ≤ q) (hA : DiscreteProfileLipschitz A N)
    (hinit : (b.state 0).start+10*q ≤ (b.state 0).finish) :
    ∑ j ∈ Finset.range n, branchCost A (b.state j) (b.label j) (b.state (j+1)) ≤
      2*A (b.state n).start+20*(q:ℝ)/N-potential A (b.state 0).start (b.state 0).finish (10*q) := by
  have hQ : 0 < 10*q := by omega
  have hfinal := BranchState.valid_depths (b.valid n le_rfl)
  by_cases hw : (b.state n).start+10*q ≤ (b.state n).finish
  · have hc := b.costs_le_potential hq hslack hw
    have hf := potential_le_final_start hN hA hQ hw hfinal.2 (le_refl _) hfinal.1
    norm_num only [Nat.cast_mul,Nat.cast_ofNat] at hf
    linear_combination hc+hf
  · cases n with
    | zero => exact (hw hinit).elim
    | succ n =>
      have hs := b.step n (by omega)
      have hn := hs.nested hq (b.valid n (by omega))
      have hp := hs.nonterminal
      have hpwide : (b.state n).start+10*q ≤ (b.state n).finish := by omega
      have hd := BranchState.valid_depths (b.valid n (by omega))
      have hc := (b.initialSegment n (by omega)).costs_le_potential hq hslack hpwide
      dsimp only [initialSegment] at hc
      have hz := hs.short_cost_zero hq (b.valid n (by omega)) hslack (by omega)
      have hf := potential_le_final_start hN hA hQ hpwide hd.2 hn.1 (hfinal.1.trans hn.2)
      norm_num only [Nat.cast_mul,Nat.cast_ofNat] at hf
      rw [Finset.sum_range_succ,hz,add_zero]
      linear_combination hc+hf

end PolicyBranch

end PlanarFalconer

end OAI
