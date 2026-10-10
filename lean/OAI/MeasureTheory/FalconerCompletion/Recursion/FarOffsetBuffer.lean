import Mathlib
import OAI.MeasureTheory.Falconer.Angular.AngularNearProgress
import OAI.MeasureTheory.Falconer.Estimates.ActualFarBuffer
import OAI.MeasureTheory.Falconer.Model
import OAI.MeasureTheory.Falconer.Recursion.BranchCounts
import OAI.MeasureTheory.Falconer.Recursion.BranchTransitions
import OAI.MeasureTheory.Falconer.Recursion.DirectPolicyWitness
import OAI.MeasureTheory.Falconer.Recursion.InteriorPolicy
import OAI.MeasureTheory.Falconer.Recursion.PolicyDescriptors
import OAI.MeasureTheory.Falconer.Recursion.PolicyInteriorInterval
import OAI.MeasureTheory.FalconerCompletion.Graphs.GraphJetMul

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

lemma uniform_far_offset_buffer {sig : ℝ} (hsig : 0 < sig) (offset : ℕ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L t a : ℕ,
      a < t-2*sourceFarBuffer N L sig →
      t-2*sourceFarBuffer N L sig+offset < t := by
  obtain ⟨N₀,h₀⟩ := exists_nat_gt (((offset:ℝ)+1)/sig)
  refine ⟨N₀,?_⟩
  intro N hN L t a ha
  have hn := h₀.trans_le (Nat.cast_le.mpr hN)
  have hh := (div_lt_iff₀ hsig).mp hn
  have hs := sourceFarBuffer_ge_slack N L sig
  have hmul : 0 ≤ sig*(N:ℝ) := mul_nonneg hsig.le (Nat.cast_nonneg _)
  have hb : offset < 2*sourceFarBuffer N L sig := by
    exact_mod_cast (show (offset:ℝ) < 2*(sourceFarBuffer N L sig:ℝ) by nlinarith)
  omega

inductive BranchStep (A : ℕ → ℝ) (N q offset : ℕ) (sig : ℝ) :
    BranchState → BranchLabel → BranchState → Prop where
  | suffix {a t i : ℕ} (wide : a+100*q < t)
      (side : a+t < 2*policyDepth A N q a t) :
      BranchStep A N q offset sig (.D a t i) .suffix (.D a (policyDepth A N q a t) (i+1))
  | low {a t i v : ℕ} (wide : a+100*q < t)
      (mem : v ∈ Finset.Ioc a t) (gap : sig*N ≤ (t:ℝ)-v) :
      BranchStep A N q offset sig (.D a t i) .low (.D a v (i+1))
  | high {a t i v : ℕ} (wide : a+100*q < t)
      (side : 2*policyDepth A N q a t ≤ a+t)
      (mem : v ∈ Finset.Ioc a t) (gap : (t:ℝ)-v < sig*N) :
      BranchStep A N q offset sig (.D a t i) .high (.H a t (policyDepth A N q a t) v i)
  | near {a₀ t₀ a t i : ℕ} (wide : a+100*q < t)
      (side : a < (BranchState.H a₀ t₀ a t i).nearDepth A N q sig) :
      BranchStep A N q offset sig (.H a₀ t₀ a t i) .near
        (.H a₀ t₀ ((BranchState.H a₀ t₀ a t i).nearDepth A N q sig) t i)
  | far {a₀ t₀ a t i b : ℕ} (wide : a+100*q < t)
      (side : a < (BranchState.H a₀ t₀ a t i).nearDepth A N q sig)
      (mem : b ∈ Finset.Icc (a+1) ((BranchState.H a₀ t₀ a t i).nearDepth A N q sig+offset)) :
      BranchStep A N q offset sig (.H a₀ t₀ a t i) .far (.D b t (i+1))
  | direct {a₀ t₀ a t i : ℕ} {e : PolicyDescriptor} (wide : a+100*q < t)
      (witness : DirectPolicyWitness A N q a₀ t₀ a t sig e) :
      BranchStep A N q offset sig (.H a₀ t₀ a t i) .direct (.H a₀ t₀ (descriptorAnchor e) t i)

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
namespace BranchStep
variable {A : ℕ → ℝ} {N q offset : ℕ} {sig : ℝ}
variable {s u : BranchState} {label : BranchLabel}

theorem nonterminal (h : BranchStep A N q offset sig s label u) : s.start+100*q < s.finish := by
  cases h <;> assumption

theorem nested (h : BranchStep A N q offset sig s label u) (hq : 0 < q)
    (hv : s.Valid N sig) : s.start ≤ u.start ∧ u.finish ≤ s.finish := by
  cases h with
  | suffix hw _ =>
    have hp := policyDepth_interior A hq (policyBlocks_nonempty hq hv.2 hw)
    simp only [BranchState.start,BranchState.finish]
    omega
  | low _ hm _ =>
    have hm := Finset.mem_Ioc.mp hm
    exact ⟨le_rfl,hm.2⟩
  | high hw _ hm _ =>
    have hp := policyDepth_interior A hq (policyBlocks_nonempty hq hv.2 hw)
    have hm := Finset.mem_Ioc.mp hm
    exact ⟨by dsimp [BranchState.start]; omega,hm.2⟩
  | near _ hs => exact ⟨hs.le,le_rfl⟩
  | far _ _ hm =>
    have hm := Finset.mem_Icc.mp hm
    exact ⟨by dsimp [BranchState.start]; omega,le_rfl⟩
  | direct _ hw => exact ⟨hw.anchor_gt.le,le_rfl⟩

theorem index_change (h : BranchStep A N q offset sig s label u) :
    u.index = s.index + (if label = .suffix ∨ label = .low ∨ label = .far then 1 else 0) := by
  cases h <;> simp [BranchState.index]

theorem episode_balance (h : BranchStep A N q offset sig s label u) :
    u.angular + (if label = .far then 1 else 0) =
      s.angular + (if label = .high then 1 else 0) := by
  cases h <;> simp [BranchState.angular]

theorem suffix_decrease (h : BranchStep A N q offset sig s .suffix u) (hq : 0 < q)
    (hv : s.Valid N sig) : u.finish+q ≤ s.finish := by
  cases h with
  | suffix hw _ =>
    have hp := policyDepth_interior A hq (policyBlocks_nonempty hq hv.2 hw)
    dsimp only [BranchState.finish]
    omega

theorem low_decrease (h : BranchStep A N q offset sig s .low u) :
    (u.finish:ℝ)+sig*N ≤ s.finish := by
  cases h with
  | low _ _ hg => dsimp only [BranchState.finish]; linarith

theorem graph_charge (h : BranchStep A N q offset sig s label u) (hq : 0 < q)
    (hv : s.Valid N sig) (hg : label = .high ∨ label = .direct) :
    s.start < u.start ∧ u.start ∈ policyRepresentatives A N q := by
  cases h with
  | high hw _ _ _ =>
    have hn := policyBlocks_nonempty hq hv.2 hw
    have hp := policyDepth_interior A hq hn
    exact ⟨by dsimp [BranchState.start]; omega,policyDepth_mem_representatives A hn⟩
  | direct _ hw =>
    exact ⟨hw.anchor_gt,policyDescriptor_anchor_mem A hq (Finset.mem_filter.mp hw.mem).1⟩
  | _ => simp at hg

end BranchStep
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

def ChargedNear (A : ℕ → ℝ) (N q : ℕ) (s u : BranchState) : Prop :=
  u.start+100*q < u.finish ∧ ∃ e ∈ s.descriptors A N q,
    descriptorLength e = (s.descriptors A N q).sup descriptorLength ∧
    s.start < descriptorAnchor e ∧ descriptorAnchor e ≤ u.start

theorem near_uncharged_next_direct {A : ℕ → ℝ} {N q offset : ℕ} {sig : ℝ}
    (hq : 0 < q) (hceil : ⌈10*sig*(N:ℝ)⌉₊ < q)
    {s u w : BranchState} {label : BranchLabel}
    (h : BranchStep A N q offset sig s .near u) (hn : ¬ ChargedNear A N q s u)
    (hnext : BranchStep A N q offset sig u label w) : label = .direct := by
  have hw := hnext.nonterminal
  cases h with
  | near hwide hnear =>
    obtain ht | hp | he := actual_near_progress A hq hceil hnear
    · exact (not_lt_of_ge ht hw).elim
    · obtain ⟨e,hm,hL,ha,hb,_⟩ := hp
      exact (hn ⟨hw,e,hm,hL,ha,hb⟩).elim
    · simp only [BranchState.finish] at he
      cases hnext with
      | near _ hs =>
        simp only [BranchState.nearDepth,BranchState.finish,BranchState.descriptors] at hs
        rw [he.2] at hs
        exact (Nat.lt_irrefl _ hs).elim
      | far _ hs _ =>
        simp only [BranchState.nearDepth,BranchState.finish,BranchState.descriptors] at hs
        rw [he.2] at hs
        exact (Nat.lt_irrefl _ hs).elim
      | direct _ _ => rfl

def branchCount (label : ℕ → BranchLabel) (n : ℕ) (kind : BranchLabel) : ℕ :=
  ∑ j ∈ Finset.range n, if label j = kind then 1 else 0

theorem branchCount_card (label : ℕ → BranchLabel) (n : ℕ) (kind : BranchLabel) :
    branchCount label n kind = ((Finset.range n).filter fun j => label j = kind).card := by
  simp [branchCount]

theorem branchCount_succ (label : ℕ → BranchLabel) (n : ℕ) (kind : BranchLabel) :
    branchCount label (n+1) kind = branchCount label n kind + if label n = kind then 1 else 0 := by
  simp only [branchCount,Finset.sum_range_succ]

structure PolicyBranch (A : ℕ → ℝ) (N q offset : ℕ) (sig : ℝ) (n : ℕ) where
  state : ℕ → BranchState
  label : ℕ → BranchLabel
  valid : ∀ j ≤ n, (state j).Valid N sig
  step : ∀ j < n, BranchStep A N q offset sig (state j) (label j) (state (j+1))

end CurrentFalconer.DimensionalPolicy
end GraphLiteralSupport
end
end

end OAI
