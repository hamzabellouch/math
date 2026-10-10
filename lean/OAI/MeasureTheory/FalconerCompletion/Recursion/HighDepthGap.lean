import Mathlib
import OAI.MeasureTheory.Falconer.Estimates.ActualDirectBuffer
import OAI.MeasureTheory.Falconer.Estimates.ActualFarBuffer
import OAI.MeasureTheory.Falconer.Estimates.ActualOuterMasks
import OAI.MeasureTheory.Falconer.Model
import OAI.MeasureTheory.Falconer.Recursion.ActualPolicyPayments
import OAI.MeasureTheory.Falconer.Recursion.BranchCounts
import OAI.MeasureTheory.Falconer.Recursion.BranchPotential
import OAI.MeasureTheory.Falconer.Recursion.BranchRepresentativeCharges
import OAI.MeasureTheory.Falconer.Recursion.BranchTransitions
import OAI.MeasureTheory.Falconer.Recursion.BranchValidity
import OAI.MeasureTheory.Falconer.Recursion.InteriorPolicy
import OAI.MeasureTheory.Falconer.Recursion.Ledger
import OAI.MeasureTheory.Falconer.Recursion.PolicyInteriorInterval
import OAI.MeasureTheory.Falconer.Recursion.Potential
import OAI.MeasureTheory.Falconer.Recursion.PrefixPolicyGeometry
import OAI.MeasureTheory.Falconer.Recursion.SourceBranchDepth
import OAI.MeasureTheory.FalconerCompletion.Estimates.InitialSegment

namespace OAI

/-! Recursive policies and quantitative depth estimates. -/

open _root_.OAI.PlanarFalconer

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace CurrentFalconer.DimensionalPolicy
open PlanarFalconer

theorem high_depth_gap {N q t v : ℕ} {sig : ℝ} (hv : v ≤ t)
    (hgap : (t:ℝ)-v < sig*N) (hslack : sig*(N:ℝ) ≤ q) : t-v ≤ q := by
  have hcast : ((t-v:ℕ):ℝ) = (t:ℝ)-v := Nat.cast_sub hv
  exact Nat.cast_le.mp (by rw [hcast]; exact hgap.le.trans hslack)

theorem BranchStep.valid_successor {A : ℕ → ℝ} {N q offset : ℕ} {sig : ℝ}
    (hq : 0 < q) (hslack : sig*(N:ℝ) ≤ q)
    (hbuffer : ∀ L t a : ℕ, a < t-2*sourceFarBuffer N L sig →
      t-2*sourceFarBuffer N L sig+offset < t)
    {s u : BranchState} {label : BranchLabel}
    (h : BranchStep A N q offset sig s label u) (hv : s.Valid N sig) : u.Valid N sig := by
  cases h with
  | suffix hw _ =>
    have hp := policyDepth_interior A hq (policyBlocks_nonempty hq hv.2 hw)
    dsimp only [BranchState.Valid] at *
    omega
  | low _ hm _ =>
    have hm := Finset.mem_Ioc.mp hm
    dsimp only [BranchState.Valid] at *
    omega
  | high hw hs hm hg =>
    have hm := Finset.mem_Ioc.mp hm
    have hgap := high_depth_gap hm.2 hg hslack
    have hp := actual_prefix_policy_payment A hq hv.2 hw hs hm.2 hgap
    have hi := policyDepth_interior A hq (policyBlocks_nonempty hq hv.2 hw)
    exact ⟨by omega,by omega,hm.2,hv.2,by linarith⟩
  | near _ hs =>
    dsimp only [BranchState.Valid,BranchState.nearDepth,BranchState.finish,BranchState.descriptors] at *
    exact ⟨by omega,Nat.sub_le _ _,hv.2.2⟩
  | far _ hs hm =>
    have hb := hbuffer _ _ _ hs
    have hm := Finset.mem_Icc.mp hm
    dsimp only [BranchState.Valid,BranchState.nearDepth,BranchState.finish,BranchState.descriptors] at *
    exact ⟨by omega,by omega⟩
  | direct _ hw =>
    exact ⟨hv.1.trans hw.anchor_gt.le,hw.anchor_lt.le,hv.2.2⟩

theorem uniform_branch_successor_validity (offset : ℕ) {sig kap : ℝ}
    (hsig : 0 < sig) (hkap : 0 < kap) (hgap : sig < kap/1000) :
    ∃ N₀ : ℕ, 0 < N₀ ∧ ∀ N ≥ N₀, ∀ A : ℕ → ℝ,
      ∀ s u : BranchState, ∀ label : BranchLabel,
      s.Valid N sig → BranchStep A N (sourcePolicyBlock N kap) offset sig s label u →
      u.Valid N sig ∧ s.start ≤ u.start ∧ u.finish ≤ s.finish := by
  obtain ⟨N₁,hN₁,h₁⟩ := uniform_source_ceiling_slack hsig hgap
  obtain ⟨N₂,h₂⟩ := uniform_far_offset_buffer hsig offset
  refine ⟨max N₁ N₂,by omega,?_⟩
  intro N hN A s u label hv h
  have hq := sourcePolicyBlock_pos (by omega : 0 < N) hkap
  have hb : ∀ L t a : ℕ, a < t-2*sourceFarBuffer N L sig →
      t-2*sourceFarBuffer N L sig+offset < t := by
    intro L t a ha
    have hh := h₂ N (by omega) L t a ha
    omega
  exact ⟨h.valid_successor hq (h₁ N (by omega)).2.2 hb hv,h.nested hq hv⟩

noncomputable def branchCost (A : ℕ → ℝ) (s : BranchState) : BranchLabel → BranchState → ℝ
  | .suffix, u => A u.finish-intervalMin A u.finish s.finish
  | .high, u | .direct, u => height A s.start u.start
  | _, _ => 0

theorem BranchStep.cost_nonneg {A : ℕ → ℝ} {N q offset : ℕ} {sig : ℝ}
    {s u : BranchState} {label : BranchLabel} (h : BranchStep A N q offset sig s label u)
    (hq : 0 < q) (hv : s.Valid N sig) : 0 ≤ branchCost A s label u := by
  have hn := h.nested hq hv
  cases h <;> simp only [branchCost]
  · exact sub_nonneg.mpr (intervalMin_le A le_rfl hn.2)
  · exact le_rfl
  · exact height_nonneg A hn.1
  · exact le_rfl
  · exact le_rfl
  · exact height_nonneg A hn.1

theorem BranchStep.paid_width {A : ℕ → ℝ} {N q offset : ℕ} {sig : ℝ}
    {s u : BranchState} {label : BranchLabel} (h : BranchStep A N q offset sig s label u)
    (hq : 0 < q) (hv : s.Valid N sig) (hslack : sig*(N:ℝ) ≤ q)
    (hc : label = .suffix ∨ label = .high ∨ label = .direct) : u.start+10*q ≤ u.finish := by
  cases h with
  | suffix hw hs => exact (actual_suffix_policy_payment A hq hv.2 hw hs).1
  | high hw hs hm hg =>
    have hm := Finset.mem_Ioc.mp hm
    exact (actual_prefix_policy_payment A hq hv.2 hw hs hm.2 (high_depth_gap hm.2 hg hslack)).1
  | direct _ he => exact he.width
  | _ => simp at hc

theorem BranchStep.potential_payment {A : ℕ → ℝ} {N q offset : ℕ} {sig : ℝ}
    {s u : BranchState} {label : BranchLabel} (h : BranchStep A N q offset sig s label u)
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

theorem BranchStep.short_cost_zero {A : ℕ → ℝ} {N q offset : ℕ} {sig : ℝ}
    {s u : BranchState} {label : BranchLabel} (h : BranchStep A N q offset sig s label u)
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
  · convert hb using 1; ring
  intro j _ hjt hjf hfj
  have hd : |(j:ℝ)-f| ≤ (Q:ℝ) := by
    have hjR : (j:ℝ) ≤ (f:ℝ)+Q := by exact_mod_cast hjf
    have hfR : (f:ℝ) ≤ (j:ℝ)+Q := by exact_mod_cast hfj
    exact abs_le.mpr ⟨by linarith,by linarith⟩
  have hh := (hA j (hjt.trans ht) f (hft.trans ht)).trans (div_le_div_of_nonneg_right hd hNR.le)
  have hh' := (le_abs_self (A j-A f)).trans hh
  linarith

end CurrentFalconer.DimensionalPolicy
end GraphLiteralSupport
end
end

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace CurrentFalconer.DimensionalPolicy
open PlanarFalconer
namespace PolicyBranch
variable {A : ℕ → ℝ} {N q n offset : ℕ} {sig : ℝ}

theorem costs_le_potential (b : PolicyBranch A N q offset sig n) (hq : 0 < q)
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

theorem costs_le_final_start (b : PolicyBranch A N q offset sig n) (hN : 0 < N) (hq : 0 < q)
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
end CurrentFalconer.DimensionalPolicy
end GraphLiteralSupport
end
end

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace CurrentFalconer.DimensionalPolicy
open PlanarFalconer

def branchNonlowCount (label : ℕ → BranchLabel) (n : ℕ) : ℕ :=
  branchCount label n .high + branchCount label n .direct + branchCount label n .near +
    branchCount label n .far + branchCount label n .suffix

theorem branch_count_total (label : ℕ → BranchLabel) (n : ℕ) :
    branchNonlowCount label n + branchCount label n .low = n := by
  induction n with
  | zero => simp [branchNonlowCount,branchCount]
  | succ n ih =>
    simp only [branchNonlowCount] at *
    simp only [branchCount_succ]
    cases h : label n <;> simp <;> omega

theorem source_branch_count_bounds {A : ℕ → ℝ} {N n offset : ℕ} {sig kap : ℝ}
    (hN : 0 < N) (hsig : 0 < sig) (hkap : 0 < kap) (hkap1 : kap ≤ 1)
    (hceil : ⌈10*sig*(N:ℝ)⌉₊ < sourcePolicyBlock N kap)
    (b : PolicyBranch A N (sourcePolicyBlock N kap) offset sig n) :
    (branchNonlowCount b.label n:ℝ) ≤ 20/kap ∧
      (branchCount b.label n .low:ℝ) ≤ 1/sig ∧ (n:ℝ) ≤ 20/kap+1/sig := by
  have hq := sourcePolicyBlock_pos hN hkap
  have hNR : (0:ℝ) < N := Nat.cast_pos.mpr hN
  have hstart := BranchState.valid_depths (b.valid 0 (Nat.zero_le _))
  have hS := b.suffix_total_decrease hq
  have hSR : (branchCount b.label n .suffix:ℝ)*(sourcePolicyBlock N kap:ℝ) ≤ N := by
    exact_mod_cast (show branchCount b.label n .suffix*sourcePolicyBlock N kap ≤ N by omega)
  have hblock := source_policy_block_lower N kap
  have hSb := mul_le_mul_of_nonneg_left hblock (Nat.cast_nonneg (branchCount b.label n .suffix))
  have hSbound : (branchCount b.label n .suffix:ℝ) ≤ 1/kap := by
    apply (le_div_iff₀ hkap).mpr
    apply (mul_le_mul_iff_left₀ hNR).mp
    nlinarith [hSb.trans hSR]
  have hL := b.low_total_decrease hq
  have hLR : ((b.state 0).finish:ℝ) ≤ N := Nat.cast_le.mpr hstart.2
  have hLbound : (branchCount b.label n .low:ℝ) ≤ 1/sig := by
    apply (le_div_iff₀ hsig).mpr
    apply (mul_le_mul_iff_left₀ hNR).mp
    nlinarith [show (0:ℝ) ≤ (b.state n).finish from Nat.cast_nonneg _]
  have hG := (b.representative_counts hq).1
  have hK := b.near_count hq hceil
  have hF := b.far_count
  have hB := source_representatives_real_bound A hN hkap hkap1
  have hnonlow : branchNonlowCount b.label n ≤
      2*(policyRepresentatives A N (sourcePolicyBlock N kap)).card + branchCount b.label n .suffix+2 := by
    dsimp only [branchNonlowCount]
    omega
  have hnonlowR : (branchNonlowCount b.label n:ℝ) ≤
      2*((policyRepresentatives A N (sourcePolicyBlock N kap)).card:ℝ) +
        (branchCount b.label n .suffix:ℝ)+2 := by exact_mod_cast hnonlow
  have hone : 1 ≤ 1/kap := (le_div_iff₀ hkap).mpr (by simpa using hkap1)
  have hbound : (branchNonlowCount b.label n:ℝ) ≤ 20/kap := by
    have he : 20/kap = 20*(1/kap) := by ring
    have he2 : 2/kap = 2*(1/kap) := by ring
    rw [he2] at hB
    rw [he]
    linarith
  refine ⟨hbound,hLbound,?_⟩
  have ht : (branchNonlowCount b.label n:ℝ)+(branchCount b.label n .low:ℝ) = n := by
    exact_mod_cast branch_count_total b.label n
  linarith

theorem source_smoothing_reserve {sig kap : ℝ} (hsig : 0 < sig) (hkap : 0 < kap) :
    1+20/kap+1/sig < (sourceSmoothingLevels sig kap:ℝ) := by
  have hceil : 100*(1/sig+1/kap)+100 ≤ (sourceSmoothingLevels sig kap:ℝ) := Nat.le_ceil _
  have he : 20/kap = 20*(1/kap) := by ring
  rw [he]
  have hk : 0 < 1/kap := by positivity
  have hs : 0 < 1/sig := by positivity
  linarith

theorem source_branch_index_bound {A : ℕ → ℝ} {N n offset : ℕ} {sig kap : ℝ}
    (hN : 0 < N) (hsig : 0 < sig) (hkap : 0 < kap) (hkap1 : kap ≤ 1)
    (hceil : ⌈10*sig*(N:ℝ)⌉₊ < sourcePolicyBlock N kap)
    (b : PolicyBranch A N (sourcePolicyBlock N kap) offset sig n) (hi : (b.state 0).index = 0)
    {j : ℕ} (hj : j ≤ n) :
    ((b.state j).index:ℝ)+1 ≤ 1+20/kap+1/sig ∧ (b.state j).index+1 < sourceSmoothingLevels sig kap := by
  let c := b.initialSegment j hj
  have hc := source_branch_count_bounds hN hsig hkap hkap1 hceil c
  have hind := c.index_identity
  change (b.state j).index = (b.state 0).index + branchCount b.label j .suffix +
    branchCount b.label j .low + branchCount b.label j .far at hind
  rw [hi] at hind
  have hn : (b.state j).index ≤ branchNonlowCount b.label j + branchCount b.label j .low := by
    dsimp only [branchNonlowCount]
    omega
  have hnR : ((b.state j).index:ℝ) ≤ (branchNonlowCount b.label j:ℝ)+(branchCount b.label j .low:ℝ) := by
    exact_mod_cast hn
  change (branchNonlowCount b.label j:ℝ) ≤ _ ∧ (branchCount b.label j .low:ℝ) ≤ _ ∧ _ at hc
  have hb : ((b.state j).index:ℝ)+1 ≤ 1+20/kap+1/sig := by linarith [hc.1,hc.2.1]
  refine ⟨hb,?_⟩
  have hh := hb.trans_lt (source_smoothing_reserve hsig hkap)
  exact_mod_cast hh

theorem uniform_source_branch_depth (offset : ℕ) {sig kap : ℝ}
    (hsig : 0 < sig) (hkap : 0 < kap) (hkap1 : kap ≤ 1) (hgap : sig < kap/1000) :
    ∃ N₀ : ℕ, 0 < N₀ ∧ ∀ N ≥ N₀, ∀ A : ℕ → ℝ, ∀ n : ℕ,
      ∀ b : PolicyBranch A N (sourcePolicyBlock N kap) offset sig n,
      (b.state 0).index = 0 →
      (branchNonlowCount b.label n:ℝ) ≤ 20/kap ∧
      (branchCount b.label n .low:ℝ) ≤ 1/sig ∧ (n:ℝ) ≤ 20/kap+1/sig ∧
      ∀ j ≤ n, ((b.state j).index:ℝ)+1 ≤ 1+20/kap+1/sig ∧
        (b.state j).index+1 < sourceSmoothingLevels sig kap := by
  obtain ⟨N₀,hN₀,h₀⟩ := uniform_source_ceiling_slack hsig hgap
  refine ⟨N₀,hN₀,?_⟩
  intro N hN A n b hi
  have hNp : 0 < N := hN₀.trans_le hN
  have hc := source_branch_count_bounds hNp hsig hkap hkap1 (h₀ N hN).1 b
  exact ⟨hc.1,hc.2.1,hc.2.2,fun j hj => source_branch_index_bound
    hNp hsig hkap hkap1 (h₀ N hN).1 b hi hj⟩

end CurrentFalconer.DimensionalPolicy
end GraphLiteralSupport
end
end

end OAI
