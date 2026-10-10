import Mathlib
import OAI.MeasureTheory.Falconer.Estimates.ActualDirectBuffer
import OAI.MeasureTheory.Falconer.Estimates.ActualFarBuffer
import OAI.MeasureTheory.Falconer.Estimates.ActualOuterMasks
import OAI.MeasureTheory.Falconer.Model
import OAI.MeasureTheory.Falconer.Recursion.BranchCounts
import OAI.MeasureTheory.Falconer.Recursion.BranchExponent
import OAI.MeasureTheory.Falconer.Recursion.BranchPotential
import OAI.MeasureTheory.Falconer.Recursion.BranchTransitions
import OAI.MeasureTheory.Falconer.Recursion.DirectPolicyWitness
import OAI.MeasureTheory.Falconer.Recursion.InheritedPolicyState
import OAI.MeasureTheory.Falconer.Recursion.InteriorPolicy
import OAI.MeasureTheory.Falconer.Recursion.Ledger
import OAI.MeasureTheory.Falconer.Recursion.PolicyDescriptors
import OAI.MeasureTheory.Falconer.Recursion.Potential
import OAI.MeasureTheory.Falconer.Recursion.SourceBranchDepth
import OAI.MeasureTheory.FalconerCompletion.Recursion.HighDepthGap

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

def ProfileLipschitzND (A : ℕ → ℝ) (N : ℕ) (L : ℝ) : Prop :=
  ∀ i ≤ N, ∀ j ≤ N, |A i-A j| ≤ L*|(i:ℝ)-j|/(N:ℝ)

lemma adjusted_profile_lipschitzND (m : ℕ → ℝ) {N : ℕ} {d : ℝ}
    (hN : 0 < N) (_hd : 0 ≤ d)
    (hinc : ∀ i j, i ≤ j → j ≤ N →
      0 ≤ m j-m i ∧ m j-m i ≤ d*((j:ℝ)-i)/(N:ℝ)) :
    ProfileLipschitzND (fun n => m n-(d/2)*(n:ℝ)/N) N (d/2) := by
  intro i hi j hj
  have hNr : 0 < (N:ℝ) := by exact_mod_cast hN
  rcases le_total i j with hij | hji
  · have hh := hinc i j hij hj
    have hdij : (i:ℝ) ≤ j := by exact_mod_cast hij
    rw [abs_of_nonpos (sub_nonpos.mpr hdij)]
    dsimp only
    simp only [div_eq_mul_inv] at hh ⊢
    apply abs_le.mpr
    constructor <;> nlinarith [hh.1,hh.2]
  · have hh := hinc j i hji hi
    have hdji : (j:ℝ) ≤ i := by exact_mod_cast hji
    rw [abs_of_nonneg (sub_nonneg.mpr hdji)]
    dsimp only
    simp only [div_eq_mul_inv] at hh ⊢
    apply abs_le.mpr
    constructor <;> nlinarith [hh.1,hh.2]

lemma potential_le_final_startND {A : ℕ → ℝ} {N a t f Q : ℕ} {L : ℝ}
    (hN : 0 < N) (hL : 0 ≤ L) (hA : ProfileLipschitzND A N L)
    (hQ : 0 < Q) (hw : a+Q ≤ t) (ht : t ≤ N) (haf : a ≤ f) (hft : f ≤ t) :
    potential A a t Q ≤ 2*A f+2*L*(Q:ℝ)/N := by
  have hNR : (0:ℝ) < N := Nat.cast_pos.mpr hN
  have hb := potential_near_final A hQ hw haf hft (e := L*(Q:ℝ)/N) ?_
  · convert hb using 1; ring
  intro j _ hjt hjf hfj
  have hd : |(j:ℝ)-f| ≤ (Q:ℝ) := by
    have hjR : (j:ℝ) ≤ (f:ℝ)+Q := by exact_mod_cast hjf
    have hfR : (f:ℝ) ≤ (j:ℝ)+Q := by exact_mod_cast hfj
    exact abs_le.mpr ⟨by linarith,by linarith⟩
  have hh := (hA j (hjt.trans ht) f (hft.trans ht)).trans
    (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hd hL) hNR.le)
  have hh' := (le_abs_self (A j-A f)).trans hh
  linarith

theorem policy_costs_le_final_startND {A : ℕ → ℝ} {N q n offset : ℕ} {sig L : ℝ}
    (b : PolicyBranch A N q offset sig n) (hN : 0 < N) (hq : 0 < q)
    (hslack : sig*(N:ℝ) ≤ q) (hL : 0 ≤ L) (hA : ProfileLipschitzND A N L)
    (hinit : (b.state 0).start+10*q ≤ (b.state 0).finish) :
    ∑ j ∈ Finset.range n, branchCost A (b.state j) (b.label j) (b.state (j+1)) ≤
      2*A (b.state n).start+20*L*(q:ℝ)/N-
        potential A (b.state 0).start (b.state 0).finish (10*q) := by
  have hQ : 0 < 10*q := by omega
  have hfinal := BranchState.valid_depths (b.valid n le_rfl)
  by_cases hw : (b.state n).start+10*q ≤ (b.state n).finish
  · have hc := b.costs_le_potential hq hslack hw
    have hf := potential_le_final_startND hN hL hA hQ hw hfinal.2 (le_refl _) hfinal.1
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
      dsimp only [PolicyBranch.initialSegment] at hc
      have hz := hs.short_cost_zero hq (b.valid n (by omega)) hslack (by omega)
      have hf := potential_le_final_startND hN hL hA hQ hpwide hd.2 hn.1
        (hfinal.1.trans hn.2)
      norm_num only [Nat.cast_mul,Nat.cast_ofNat] at hf
      rw [Finset.sum_range_succ,hz,add_zero]
      linear_combination hc+hf

noncomputable def branchExponentND (A : ℕ → ℝ) (C lam sig eps : ℝ)
    (s : BranchState) (label : BranchLabel) (u : BranchState) : ℝ :=
  -2*(A u.start-A s.start)+branchCost A s label u+
    (if label = .low then 0 else C*(lam+sig))+eps

lemma branch_exponent_sumND (A : ℕ → ℝ) (C lam sig eps : ℝ)
    (state : ℕ → BranchState) (label : ℕ → BranchLabel) (n : ℕ) :
    (∑ j ∈ Finset.range n, branchExponentND A C lam sig eps
      (state j) (label j) (state (j+1))) =
      2*A (state 0).start-2*A (state n).start+
      (∑ j ∈ Finset.range n, branchCost A (state j) (label j) (state (j+1)))+
      (branchNonlowCount label n:ℝ)*(C*(lam+sig))+(n:ℝ)*eps := by
  simp only [branchExponentND,Finset.sum_add_distrib]
  rw [profile_increments_telescope A (fun j => (state j).start) n,branch_nonlow_loss_sum]
  simp [branchNonlowCount,PlanarFalconer.branchNonlowCount,branchCount,PlanarFalconer.branchCount]

theorem source_branch_exponentND {A : ℕ → ℝ} {N n offset : ℕ} {lam sig kap eta L C : ℝ}
    (hN : 0 < N) (hlam : 0 ≤ lam) (hsig : 0 < sig) (hkap : 0 < kap) (hkap1 : kap ≤ 1)
    (heta : 0 < eta) (hL : 0 ≤ L) (hC : 0 ≤ C)
    (hceil : ⌈10*sig*(N:ℝ)⌉₊ < sourcePolicyBlock N kap)
    (hslack : sig*(N:ℝ) ≤ sourcePolicyBlock N kap)
    (hqratio : (sourcePolicyBlock N kap:ℝ)/(N:ℝ) ≤ 2*kap)
    (hA : ProfileLipschitzND A N L)
    (b : PolicyBranch A N (sourcePolicyBlock N kap) offset sig n)
    (hinit : (b.state 0).start+10*sourcePolicyBlock N kap ≤ (b.state 0).finish) :
    let eps := eta/(2*(1+20/kap+1/sig))
    (∑ j ∈ Finset.range n, branchExponentND A C lam sig eps
      (b.state j) (b.label j) (b.state (j+1)))+
      (200*L*(sourcePolicyBlock N kap:ℝ)/N+C*lam+eta/2) ≤
      2*A (b.state 0).start-potential A (b.state 0).start (b.state 0).finish
        (10*sourcePolicyBlock N kap)+500*L*kap+100*C*(lam+sig)/kap+eta := by
  dsimp only
  have hq := sourcePolicyBlock_pos hN hkap
  have hc := policy_costs_le_final_startND b hN hq hslack hL hA hinit
  have hb := source_branch_count_bounds hN hsig hkap hkap1 hceil b
  let D : ℝ := 1+20/kap+1/sig
  have hD : 0 < D := by dsimp [D]; positivity
  have heps : 0 ≤ eta/(2*D) := by positivity
  have htime : (n:ℝ)*(eta/(2*D)) ≤ eta/2 := by
    have hn : (n:ℝ) ≤ D := by dsimp [D]; linarith [hb.2.2]
    calc
      _ ≤ D*(eta/(2*D)) := mul_le_mul_of_nonneg_right hn heps
      _ = eta/2 := by field_simp
  have hloss : (branchNonlowCount b.label n:ℝ)*(C*(lam+sig)) ≤ 20*C*(lam+sig)/kap := by
    calc
      _ ≤ (20/kap)*(C*(lam+sig)) := mul_le_mul_of_nonneg_right hb.1 (by positivity)
      _ = _ := by ring
  have hlamK : C*lam ≤ C*(lam+sig)/kap := by
    apply (le_div_iff₀ hkap).mpr
    have hh := mul_le_mul_of_nonneg_left hkap1 (mul_nonneg hC hlam)
    have hcs := mul_nonneg hC hsig.le
    nlinarith
  have hbudget : 0 ≤ C*(lam+sig)/kap := by positivity
  have hwidth := mul_le_mul_of_nonneg_left hqratio (show 0 ≤ 220*L by positivity)
  have hLK : 0 ≤ L*kap := by positivity
  rw [branch_exponent_sumND]
  dsimp only [D] at htime
  simp only [mul_div_assoc] at hc hloss hlamK hbudget hwidth ⊢
  nlinarith

theorem uniform_source_branch_exponentND (offset : ℕ) {lam sig kap eta L C : ℝ}
    (hlam : 0 ≤ lam) (hsig : 0 < sig) (hkap : 0 < kap) (hkap1 : kap ≤ 1)
    (hgap : sig < kap/1000) (heta : 0 < eta) (hL : 0 ≤ L) (hC : 0 ≤ C) :
    ∃ N₀ : ℕ, 0 < N₀ ∧ ∀ N ≥ N₀, ∀ A : ℕ → ℝ,
      ProfileLipschitzND A N L → ∀ n : ℕ,
      ∀ b : PolicyBranch A N (sourcePolicyBlock N kap) offset sig n,
      (b.state 0).start+10*sourcePolicyBlock N kap ≤ (b.state 0).finish →
      (∑ j ∈ Finset.range n, branchExponentND A C lam sig (eta/(2*(1+20/kap+1/sig)))
        (b.state j) (b.label j) (b.state (j+1)))+
        (200*L*(sourcePolicyBlock N kap:ℝ)/N+C*lam+eta/2) ≤
      2*A (b.state 0).start-potential A (b.state 0).start (b.state 0).finish
        (10*sourcePolicyBlock N kap)+500*L*kap+100*C*(lam+sig)/kap+eta := by
  obtain ⟨N₁,hN₁,h₁⟩ := uniform_source_ceiling_slack hsig hgap
  obtain ⟨N₂,hN₂⟩ := exists_nat_gt (1/kap)
  refine ⟨max N₁ N₂,by omega,?_⟩
  intro N hN A hA n b hi
  have hNp : 0 < N := by omega
  have hNR : (0:ℝ) < N := Nat.cast_pos.mpr hNp
  have hkn : 1 < kap*(N:ℝ) := by
    have hh := (div_lt_iff₀ hkap).mp (hN₂.trans_le (Nat.cast_le.mpr (show N₂ ≤ N by omega)))
    linarith
  have hq : (sourcePolicyBlock N kap:ℝ) < kap*N+1 :=
    Nat.ceil_lt_add_one (mul_nonneg hkap.le hNR.le)
  have hqr : (sourcePolicyBlock N kap:ℝ)/(N:ℝ) ≤ 2*kap :=
    (div_le_iff₀ hNR).mpr (by linarith)
  exact source_branch_exponentND hNp hlam hsig hkap hkap1 heta hL hC
    (h₁ N (by omega)).1 (h₁ N (by omega)).2.2 hqr hA b hi

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

theorem BranchStep.strict_progress {A : ℕ → ℝ} {N q offset : ℕ} {sig : ℝ}
    (hN : 0 < N) (hq : 0 < q) (hsig : 0 < sig)
    {s u : BranchState} {label : BranchLabel}
    (h : BranchStep A N q offset sig s label u) (hv : s.Valid N sig) :
    s.start < u.start ∨ u.finish < s.finish := by
  cases h with
  | suffix hw hs =>
    have hp := policyDepth_interior A hq (policyBlocks_nonempty hq hv.2 hw)
    right
    dsimp [BranchState.finish]
    omega
  | @low a t i v hw hm hg =>
    right
    have hpos : 0 < sig*(N:ℝ) := mul_pos hsig (Nat.cast_pos.mpr hN)
    dsimp [BranchState.finish]
    exact_mod_cast (show (v : ℝ) < t by linarith [hg])
  | high hw hs hm hg =>
    have hp := policyDepth_interior A hq (policyBlocks_nonempty hq hv.2 hw)
    left
    dsimp [BranchState.start]
    omega
  | near hw hs => exact Or.inl hs
  | far hw hs hm =>
    left
    have hh := (Finset.mem_Icc.mp hm).1
    dsimp [BranchState.start]
    omega
  | direct hw hd => exact Or.inl hd.anchor_gt

theorem BranchStep.width_decreases {A : ℕ → ℝ} {N q offset : ℕ} {sig : ℝ}
    (hN : 0 < N) (hq : 0 < q) (hsig : 0 < sig)
    {s u : BranchState} {label : BranchLabel}
    (h : BranchStep A N q offset sig s label u) (hv : s.Valid N sig)
    (hu : u.Valid N sig) :
    u.finish-u.start < s.finish-s.start := by
  have hn := h.nested hq hv
  have hp := h.strict_progress hN hq hsig hv
  have hd := BranchState.valid_depths hu
  omega

theorem valid_step_wellFounded (A : ℕ → ℝ) {N q offset : ℕ} {sig : ℝ}
    (hN : 0 < N) (hq : 0 < q) (hsig : 0 < sig) :
    WellFounded (fun (u s : {s : BranchState // s.Valid N sig}) =>
      ∃ label, BranchStep A N q offset sig s.1 label u.1) := by
  apply Subrelation.wf (r := (measure fun (s : {s : BranchState // s.Valid N sig}) =>
    s.1.finish-s.1.start).rel) ?_ (measure _).wf
  intro u s h
  obtain ⟨label,hh⟩ := h
  exact hh.width_decreases hN hq hsig s.2 u.2

theorem nonterminal_has_step (A : ℕ → ℝ) {N q offset : ℕ} {sig : ℝ}
    (hN : 0 < N) (hq : 0 < q) (hsig : 0 < sig)
    (hceil : ⌈10*sig*(N:ℝ)⌉₊ < q)
    (hslack : sig*(N:ℝ) ≤ q) (hslack10 : 10*sig*(N:ℝ) ≤ q)
    (s : BranchState) (hv : s.Valid N sig) (hw : s.start+100*q < s.finish) :
    ∃ label u, BranchStep A N q offset sig s label u := by
  cases s with
  | D a t i =>
    by_cases hs : a+t < 2*policyDepth A N q a t
    · exact ⟨.suffix,_,.suffix hw hs⟩
    · refine ⟨.high,_,.high (v := t) hw (by omega) ?_ ?_⟩
      · exact Finset.mem_Ioc.mpr ⟨by change a+100*q<t at hw; omega,le_rfl⟩
      · have hh : 0 < sig*(N:ℝ) := mul_pos hsig (Nat.cast_pos.mpr hN)
        simpa only [sub_self] using hh
  | H a₀ t₀ a t i =>
    by_cases hh : a < (BranchState.H a₀ t₀ a t i).nearDepth A N q sig
    · exact ⟨.near,_,.near hw hh⟩
    · have hdir : t-2*sourceFarBuffer N
          ((remainingPolicyDescriptors A N q a₀ t₀ a).sup descriptorLength) sig ≤ a := by
        simpa only [BranchState.nearDepth,BranchState.finish,BranchState.descriptors] using
          (not_lt.mp hh)
      obtain ⟨e,he⟩ := actual_direct_policy_witness A hsig.le hq hceil hslack hslack10
        hv.2.2.2.2 hw hdir
      exact ⟨.direct,_,.direct hw he⟩

namespace PolicyBranch

def prepend {A : ℕ → ℝ} {N q offset n : ℕ} {sig : ℝ}
    (b : PolicyBranch A N q offset sig n) (s : BranchState) (label : BranchLabel)
    (hs : s.Valid N sig) (hstep : BranchStep A N q offset sig s label (b.state 0)) :
    PolicyBranch A N q offset sig (n+1) where
  state := fun j => match j with | 0 => s | k+1 => b.state k
  label := fun j => match j with | 0 => label | k+1 => b.label k
  valid := by
    intro j hj
    cases j with
    | zero => exact hs
    | succ k => exact b.valid k (by omega)
  step := by
    intro j hj
    cases j with
    | zero => exact hstep
    | succ k => exact b.step k (by omega)

end PolicyBranch

theorem exists_terminal_branch (A : ℕ → ℝ) {N q offset : ℕ} {sig : ℝ}
    (hN : 0 < N) (hq : 0 < q) (hsig : 0 < sig)
    (hceil : ⌈10*sig*(N:ℝ)⌉₊ < q)
    (hslack : sig*(N:ℝ) ≤ q) (hslack10 : 10*sig*(N:ℝ) ≤ q)
    (hbuffer : ∀ L t a : ℕ, a < t-2*sourceFarBuffer N L sig →
      t-2*sourceFarBuffer N L sig+offset < t)
    (s : BranchState) (hs : s.Valid N sig) :
    ∃ n, ∃ b : PolicyBranch A N q offset sig n,
      b.state 0 = s ∧ (b.state n).finish ≤ (b.state n).start+100*q := by
  have wf := valid_step_wellFounded A (offset := offset) hN hq hsig
  suffices hh : ∀ x : {s : BranchState // s.Valid N sig},
      ∃ n, ∃ b : PolicyBranch A N q offset sig n,
        b.state 0 = x.1 ∧ (b.state n).finish ≤ (b.state n).start+100*q from hh ⟨s,hs⟩
  intro x
  induction x using wf.induction with
  | h x ih =>
    by_cases hw : x.1.start+100*q < x.1.finish
    · obtain ⟨label,u,hu⟩ := nonterminal_has_step A hN hq hsig hceil hslack hslack10 x.1 x.2 hw
      have huv := hu.valid_successor hq hslack hbuffer x.2
      obtain ⟨n,b,hb,ht⟩ := ih ⟨u,huv⟩ ⟨label,hu⟩
      have hh : BranchStep A N q offset sig x.1 label (b.state 0) := by rw [hb]; exact hu
      exact ⟨n+1,b.prepend x.1 label x.2 hh,rfl,ht⟩
    · let b : PolicyBranch A N q offset sig 0 :=
        ⟨fun _ => x.1,fun _ => .near,fun _ _ => x.2,fun j hj => (Nat.not_lt_zero j hj).elim⟩
      exact ⟨0,b,rfl,not_lt.mp hw⟩

theorem uniform_terminal_branch (offset : ℕ) {sig kap : ℝ}
    (hsig : 0 < sig) (hkap : 0 < kap) (hkap1 : kap ≤ 1) (hgap : sig < kap/1000) :
    ∃ N₀ : ℕ, 0 < N₀ ∧ ∀ N ≥ N₀, ∀ A : ℕ → ℝ, ∀ s : BranchState,
      s.Valid N sig → s.index = 0 →
      ∃ n, ∃ b : PolicyBranch A N (sourcePolicyBlock N kap) offset sig n,
        b.state 0 = s ∧ (b.state n).finish ≤ (b.state n).start+100*sourcePolicyBlock N kap ∧
        (branchNonlowCount b.label n:ℝ) ≤ 20/kap ∧
        (branchCount b.label n .low:ℝ) ≤ 1/sig ∧ (n:ℝ) ≤ 20/kap+1/sig ∧
        ∀ j ≤ n, (b.state j).index+1 < sourceSmoothingLevels sig kap := by
  obtain ⟨N₁,hN₁,h₁⟩ := uniform_source_ceiling_slack hsig hgap
  obtain ⟨N₂,h₂⟩ := uniform_far_offset_buffer hsig offset
  refine ⟨max N₁ N₂,by omega,?_⟩
  intro N hN A s hs hi
  have hNp : 0 < N := by omega
  have hq := sourcePolicyBlock_pos hNp hkap
  obtain ⟨hc,hs10,hsl⟩ := h₁ N (by omega)
  obtain ⟨n,b,hb,ht⟩ := exists_terminal_branch A hNp hq hsig hc hsl hs10
    (h₂ N (by omega)) s hs
  have hcounts := source_branch_count_bounds hNp hsig hkap hkap1 hc b
  refine ⟨n,b,hb,ht,hcounts.1,hcounts.2.1,hcounts.2.2,?_⟩
  intro j hj
  exact (source_branch_index_bound hNp hsig hkap hkap1 hc b (by rw [hb]; exact hi) hj).2

end CurrentFalconer.DimensionalPolicy
end GraphLiteralSupport
end
end

end OAI
