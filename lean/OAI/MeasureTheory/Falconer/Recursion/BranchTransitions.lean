import OAI.MeasureTheory.Falconer.Angular.AngularNearProgress
import OAI.MeasureTheory.Falconer.Recursion.BranchRepresentativeCharges

namespace OAI

namespace PlanarFalconer

inductive BranchState where
  | D (a t i : ℕ)
  | H (a₀ t₀ a t i : ℕ)
  deriving DecidableEq

namespace BranchState

def start : BranchState → ℕ
  | .D a _ _ | .H _ _ a _ _ => a
def finish : BranchState → ℕ
  | .D _ t _ | .H _ _ _ t _ => t
def index : BranchState → ℕ
  | .D _ _ i | .H _ _ _ _ i => i
def angular : BranchState → ℕ
  | .D .. => 0
  | .H .. => 1

def Valid (N : ℕ) (sig : ℝ) : BranchState → Prop
  | .D a t _ => a ≤ t ∧ t ≤ N
  | .H a₀ t₀ a t _ => a₀ ≤ a ∧ a ≤ t ∧ t ≤ t₀ ∧ t₀ ≤ N ∧ (t₀:ℝ) ≤ t+sig*N

noncomputable def descriptors (A : ℕ → ℝ) (N q : ℕ) : BranchState → Finset PolicyDescriptor
  | .D a t _ => policyDescriptorList A N q a t
  | .H a₀ t₀ a _ _ => remainingPolicyDescriptors A N q a₀ t₀ a

noncomputable def nearDepth (A : ℕ → ℝ) (N q : ℕ) (sig : ℝ) (s : BranchState) : ℕ :=
  s.finish-2*sourceFarBuffer N ((s.descriptors A N q).sup descriptorLength) sig

theorem valid_depths {N : ℕ} {sig : ℝ} {s : BranchState} (h : s.Valid N sig) :
    s.start ≤ s.finish ∧ s.finish ≤ N := by
  cases s <;> simp only [Valid,start,finish] at *
  · exact h
  · omega

end BranchState

inductive BranchLabel where
  | suffix | low | high | near | far | direct
  deriving DecidableEq

inductive BranchStep (A : ℕ → ℝ) (N q : ℕ) (sig : ℝ) :
    BranchState → BranchLabel → BranchState → Prop where
  | suffix {a t i : ℕ} (wide : a+100*q < t)
      (side : a+t < 2*policyDepth A N q a t) :
      BranchStep A N q sig (.D a t i) .suffix (.D a (policyDepth A N q a t) (i+1))
  | low {a t i v : ℕ} (wide : a+100*q < t)
      (mem : v ∈ Finset.Ioc a t) (gap : sig*N ≤ (t:ℝ)-v) :
      BranchStep A N q sig (.D a t i) .low (.D a v (i+1))
  | high {a t i v : ℕ} (wide : a+100*q < t)
      (side : 2*policyDepth A N q a t ≤ a+t)
      (mem : v ∈ Finset.Ioc a t) (gap : (t:ℝ)-v < sig*N) :
      BranchStep A N q sig (.D a t i) .high (.H a t (policyDepth A N q a t) v i)
  | near {a₀ t₀ a t i : ℕ} (wide : a+100*q < t)
      (side : a < (BranchState.H a₀ t₀ a t i).nearDepth A N q sig) :
      BranchStep A N q sig (.H a₀ t₀ a t i) .near
        (.H a₀ t₀ ((BranchState.H a₀ t₀ a t i).nearDepth A N q sig) t i)
  | far {a₀ t₀ a t i b : ℕ} (wide : a+100*q < t)
      (side : a < (BranchState.H a₀ t₀ a t i).nearDepth A N q sig)
      (mem : b ∈ Finset.Icc (a+9) ((BranchState.H a₀ t₀ a t i).nearDepth A N q sig+6)) :
      BranchStep A N q sig (.H a₀ t₀ a t i) .far (.D b t (i+1))
  | direct {a₀ t₀ a t i : ℕ} {e : PolicyDescriptor} (wide : a+100*q < t)
      (witness : DirectPolicyWitness A N q a₀ t₀ a t sig e) :
      BranchStep A N q sig (.H a₀ t₀ a t i) .direct (.H a₀ t₀ (descriptorAnchor e) t i)

namespace BranchStep
variable {A : ℕ → ℝ} {N q : ℕ} {sig : ℝ}
variable {s u : BranchState} {label : BranchLabel}

theorem nonterminal (h : BranchStep A N q sig s label u) : s.start+100*q < s.finish := by
  cases h <;> assumption

theorem nested (h : BranchStep A N q sig s label u) (hq : 0 < q)
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

theorem index_change (h : BranchStep A N q sig s label u) :
    u.index = s.index + (if label = .suffix ∨ label = .low ∨ label = .far then 1 else 0) := by
  cases h <;> simp [BranchState.index]

theorem episode_balance (h : BranchStep A N q sig s label u) :
    u.angular + (if label = .far then 1 else 0) =
      s.angular + (if label = .high then 1 else 0) := by
  cases h <;> simp [BranchState.angular]

theorem suffix_decrease (h : BranchStep A N q sig s .suffix u) (hq : 0 < q)
    (hv : s.Valid N sig) : u.finish+q ≤ s.finish := by
  cases h with
  | suffix hw _ =>
    have hp := policyDepth_interior A hq (policyBlocks_nonempty hq hv.2 hw)
    dsimp only [BranchState.finish]
    omega

theorem low_decrease (h : BranchStep A N q sig s .low u) :
    (u.finish:ℝ)+sig*N ≤ s.finish := by
  cases h with
  | low _ _ hg => dsimp only [BranchState.finish]; linarith

theorem graph_charge (h : BranchStep A N q sig s label u) (hq : 0 < q)
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

def ChargedNear (A : ℕ → ℝ) (N q : ℕ) (s u : BranchState) : Prop :=
  u.start+100*q < u.finish ∧ ∃ e ∈ s.descriptors A N q,
    descriptorLength e = (s.descriptors A N q).sup descriptorLength ∧
    s.start < descriptorAnchor e ∧ descriptorAnchor e ≤ u.start

theorem near_uncharged_next_direct {A : ℕ → ℝ} {N q : ℕ} {sig : ℝ}
    (hq : 0 < q) (hceil : ⌈10*sig*(N:ℝ)⌉₊ < q)
    {s u w : BranchState} {label : BranchLabel}
    (h : BranchStep A N q sig s .near u) (hn : ¬ ChargedNear A N q s u)
    (hnext : BranchStep A N q sig u label w) : label = .direct := by
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

end PlanarFalconer

end OAI
