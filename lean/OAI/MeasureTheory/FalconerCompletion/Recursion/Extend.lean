import Mathlib
import OAI.MeasureTheory.Falconer.Estimates.ActualDirectBuffer
import OAI.MeasureTheory.Falconer.Estimates.ActualOuterMasks
import OAI.MeasureTheory.Falconer.Model
import OAI.MeasureTheory.Falconer.Recursion.BranchCounts
import OAI.MeasureTheory.Falconer.Recursion.BranchPotential
import OAI.MeasureTheory.Falconer.Recursion.BranchTransitions
import OAI.MeasureTheory.Falconer.Recursion.Ledger
import OAI.MeasureTheory.Falconer.Recursion.Potential
import OAI.MeasureTheory.Falconer.Recursion.SourceBranchDepth
import OAI.MeasureTheory.FalconerCompletion.Recursion.ProfileLipschitz

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

namespace PolicyBranch
variable {A : ℕ → ℝ} {N q n offset : ℕ} {sig : ℝ}

def extend (b : PolicyBranch A N q offset sig n) {u : BranchState} {l : BranchLabel}
    (hu : u.Valid N sig) (hstep : BranchStep A N q offset sig (b.state n) l u) :
    PolicyBranch A N q offset sig (n+1) where
  state j := if j ≤ n then b.state j else u
  label j := if j < n then b.label j else l
  valid j hj := by
    split_ifs with h
    · exact b.valid j h
    · exact hu
  step j hj := by
    by_cases h : j < n
    · simpa only [ite_eq_left h, ite_eq_left (show j ≤ n by omega),
        ite_eq_left (show j+1 ≤ n by omega)] using b.step j h
    · have he : j = n := by omega
      subst j
      simpa using hstep

@[simp] theorem extend_state_le (b : PolicyBranch A N q offset sig n)
    {u : BranchState} {l : BranchLabel} (hu : u.Valid N sig)
    (hstep : BranchStep A N q offset sig (b.state n) l u) {j : ℕ} (hj : j ≤ n) :
    (b.extend hu hstep).state j = b.state j := ite_eq_left hj

@[simp] theorem extend_label_lt (b : PolicyBranch A N q offset sig n)
    {u : BranchState} {l : BranchLabel} (hu : u.Valid N sig)
    (hstep : BranchStep A N q offset sig (b.state n) l u) {j : ℕ} (hj : j < n) :
    (b.extend hu hstep).label j = b.label j := ite_eq_left hj

@[simp] theorem extend_last_state (b : PolicyBranch A N q offset sig n)
    {u : BranchState} {l : BranchLabel} (hu : u.Valid N sig)
    (hstep : BranchStep A N q offset sig (b.state n) l u) :
    (b.extend hu hstep).state (n+1) = u := ite_eq_right (by omega)

@[simp] theorem extend_last_label (b : PolicyBranch A N q offset sig n)
    {u : BranchState} {l : BranchLabel} (hu : u.Valid N sig)
    (hstep : BranchStep A N q offset sig (b.state n) l u) :
    (b.extend hu hstep).label n = l := ite_eq_right (Nat.lt_irrefl n)

end PolicyBranch

namespace PolicyBranch
variable {A : ℕ → ℝ} {N q n offset : ℕ} {sig : ℝ}

noncomputable def exponentSum (b : PolicyBranch A N q offset sig n) (C lam eps : ℝ) : ℝ :=
  ∑ j ∈ Finset.range n, branchExponentND A C lam sig eps (b.state j) (b.label j) (b.state (j+1))

noncomputable def weight (b : PolicyBranch A N q offset sig n) (C lam eps : ℝ) : ℝ :=
  ((2:ℝ)^N)^(b.exponentSum C lam eps)

theorem weight_pos (b : PolicyBranch A N q offset sig n) (C lam eps : ℝ) : 0 < b.weight C lam eps := by
  unfold weight
  positivity

theorem exponentSum_extend (b : PolicyBranch A N q offset sig n) (C lam eps : ℝ)
    {u : BranchState} {l : BranchLabel} (hu : u.Valid N sig)
    (hstep : BranchStep A N q offset sig (b.state n) l u) :
    (b.extend hu hstep).exponentSum C lam eps = b.exponentSum C lam eps+
      branchExponentND A C lam sig eps (b.state n) l u := by
  unfold exponentSum
  rw [Finset.sum_range_succ]
  congr 1
  · apply Finset.sum_congr rfl
    intro j hj
    have hj := Finset.mem_range.mp hj
    rw [b.extend_state_le hu hstep hj.le,b.extend_label_lt hu hstep hj,
      b.extend_state_le hu hstep (by omega : j+1 ≤ n)]
  · rw [b.extend_state_le hu hstep le_rfl,b.extend_last_label,b.extend_last_state]

theorem weight_extend (b : PolicyBranch A N q offset sig n) (C lam eps : ℝ)
    {u : BranchState} {l : BranchLabel} (hu : u.Valid N sig)
    (hstep : BranchStep A N q offset sig (b.state n) l u) :
    (b.extend hu hstep).weight C lam eps = b.weight C lam eps*
      ((2:ℝ)^N)^(branchExponentND A C lam sig eps (b.state n) l u) := by
  unfold weight
  rw [exponentSum_extend,Real.rpow_add (by positivity)]

theorem weight_eq_product (b : PolicyBranch A N q offset sig n) (C lam eps : ℝ) :
    b.weight C lam eps = ∏ j ∈ Finset.range n,
      ((2:ℝ)^N)^(branchExponentND A C lam sig eps (b.state j) (b.label j) (b.state (j+1))) :=
  Real.rpow_sum_of_pos (by positivity) _ _

theorem weight_zero (b : PolicyBranch A N q offset sig 0) (C lam eps : ℝ) : b.weight C lam eps = 1 := by
  simp [weight,exponentSum]

end PolicyBranch

theorem ProfileLipschitzND.increment_le {A : ℕ → ℝ} {N i j : ℕ} {L : ℝ}
    (hA : ProfileLipschitzND A N L) (hN : 0 < N) (hL : 0 ≤ L)
    (hi : i ≤ N) (hj : j ≤ N) : |A i-A j| ≤ L := by
  apply (hA i hi j hj).trans
  apply (div_le_iff₀ (Nat.cast_pos.mpr hN)).mpr
  apply mul_le_mul_of_nonneg_left _ hL
  have hi' : (i:ℝ) ≤ N := Nat.cast_le.mpr hi
  have hj' : (j:ℝ) ≤ N := Nat.cast_le.mpr hj
  exact abs_le.mpr ⟨by linarith [Nat.cast_nonneg (α := ℝ) i],
    by linarith [Nat.cast_nonneg (α := ℝ) j]⟩

theorem ProfileLipschitzND.minimum_cost_le {A : ℕ → ℝ} {N a t i : ℕ} {L : ℝ}
    (hA : ProfileLipschitzND A N L) (hN : 0 < N) (hL : 0 ≤ L)
    (hat : a ≤ t) (ht : t ≤ N) (hi : i ≤ N) : A i-intervalMin A a t ≤ L := by
  obtain ⟨j,_,hjt,hmin⟩ := intervalMin_attained A hat
  rw [hmin]
  exact (le_abs_self _).trans (hA.increment_le hN hL hi (hjt.trans ht))

theorem BranchStep.cost_le {A : ℕ → ℝ} {N q offset : ℕ} {sig L : ℝ}
    (hA : ProfileLipschitzND A N L) (hN : 0 < N) (hq : 0 < q) (hL : 0 ≤ L)
    {s u : BranchState} {l : BranchLabel} (h : BranchStep A N q offset sig s l u)
    (hs : s.Valid N sig) (hu : u.Valid N sig) : branchCost A s l u ≤ L := by
  have hn := h.nested hq hs
  have hsd := BranchState.valid_depths hs
  have hud := BranchState.valid_depths hu
  cases h <;> simp only [branchCost]
  · exact hA.minimum_cost_le hN hL hn.2 hsd.2 hud.2
  · exact hL
  · exact hA.minimum_cost_le hN hL hn.1 (hud.1.trans hud.2) (hud.1.trans hud.2)
  · exact hL
  · exact hL
  · exact hA.minimum_cost_le hN hL hn.1 (hud.1.trans hud.2) (hud.1.trans hud.2)

theorem BranchStep.exponent_leND {A : ℕ → ℝ} {N q offset : ℕ} {C lam sig eps L : ℝ}
    (hA : ProfileLipschitzND A N L) (hN : 0 < N) (hq : 0 < q)
    (hL : 0 ≤ L) (hloss : C*(lam+sig) ≤ 1)
    {s u : BranchState} {l : BranchLabel} (h : BranchStep A N q offset sig s l u)
    (hs : s.Valid N sig) (hu : u.Valid N sig) :
    branchExponentND A C lam sig eps s l u ≤ 3*L+1+eps := by
  have hc := h.cost_le hA hN hq hL hs hu
  have hsd := BranchState.valid_depths hs
  have hud := BranchState.valid_depths hu
  have hi := abs_le.mp (hA.increment_le hN hL (hud.1.trans hud.2) (hsd.1.trans hsd.2))
  unfold branchExponentND
  split_ifs <;> linarith

theorem PolicyBranch.ancestor_exponent_boundND {A : ℕ → ℝ} {N q n offset : ℕ}
    {C lam sig eps L : ℝ} (b : PolicyBranch A N q offset sig n)
    (hA : ProfileLipschitzND A N L) (hN : 0 < N) (hq : 0 < q)
    (hL : 0 ≤ L) (hloss : C*(lam+sig) ≤ 1) :
    b.exponentSum C lam eps ≤ (n:ℝ)*(3*L+1+eps) := by
  apply le_trans (Finset.sum_le_sum fun j hj =>
    (b.step j (Finset.mem_range.mp hj)).exponent_leND hA hN hq hL hloss
      (b.valid j (by have := Finset.mem_range.mp hj; omega))
      (b.valid (j+1) (by have := Finset.mem_range.mp hj; omega)))
  simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul,le_refl]

theorem uniform_source_weighted_terminalND (offset : ℕ) {lam sig kap eta L C : ℝ}
    (hlam : 0 ≤ lam) (hsig : 0 < sig) (hkap : 0 < kap) (hkap1 : kap ≤ 1)
    (hgap : sig < kap/1000) (heta : 0 < eta) (hL : 0 ≤ L) (hC : 0 ≤ C) :
    ∃ N₀ : ℕ, 0 < N₀ ∧ ∀ N ≥ N₀, ∀ A : ℕ → ℝ,
      ProfileLipschitzND A N L → ∀ n : ℕ,
      ∀ b : PolicyBranch A N (sourcePolicyBlock N kap) offset sig n,
      (b.state 0).start+10*sourcePolicyBlock N kap ≤ (b.state 0).finish →
      b.weight C lam (eta/(2*(1+20/kap+1/sig))) *
        ((2:ℝ)^N)^(200*L*(sourcePolicyBlock N kap:ℝ)/N+C*lam+eta/2) ≤
      ((2:ℝ)^N)^(2*A (b.state 0).start-potential A (b.state 0).start (b.state 0).finish
        (10*sourcePolicyBlock N kap)+500*L*kap+100*C*(lam+sig)/kap+eta) := by
  obtain ⟨N₀,hN₀,h₀⟩ := uniform_source_branch_exponentND offset hlam hsig hkap hkap1 hgap heta hL hC
  refine ⟨N₀,hN₀,?_⟩
  intro N hN A hA n b hi
  rw [PolicyBranch.weight,← Real.rpow_add (by positivity : 0 < (2:ℝ)^N)]
  exact Real.rpow_le_rpow_of_exponent_le (one_le_pow₀ (by norm_num)) (h₀ N hN A hA n b hi)

theorem uniform_source_weighted_errorND (offset : ℕ) {lam sig kap T eps L C B : ℝ}
    (hsig : 0 < sig) (hkap : 0 < kap) (hkap1 : kap ≤ 1) (hgap : sig < kap/1000)
    (hL : 0 ≤ L) (hloss : C*(lam+sig) ≤ 1) (heps : eps ≤ 1)
    (hT : (3*L+2)*(20/kap+1/sig)+B ≤ T) :
    ∃ N₀ : ℕ, 0 < N₀ ∧ ∀ N ≥ N₀, ∀ A : ℕ → ℝ,
      ProfileLipschitzND A N L → ∀ n : ℕ,
      ∀ b : PolicyBranch A N (sourcePolicyBlock N kap) offset sig n,
      b.weight C lam eps*((2:ℝ)^N)^(-T) ≤ ((2:ℝ)^N)^(-B) := by
  obtain ⟨N₀,hN₀,h₀⟩ := uniform_source_ceiling_slack hsig hgap
  refine ⟨N₀,hN₀,?_⟩
  intro N hN A hA n b
  have hNp : 0 < N := by omega
  have hn := (source_branch_count_bounds hNp hsig hkap hkap1 (h₀ N hN).1 b).2.2
  have he := b.ancestor_exponent_boundND (eps := eps) hA hNp (sourcePolicyBlock_pos hNp hkap) hL hloss
  have hexp : b.exponentSum C lam eps-T ≤ -B := by
    have h₁ := mul_le_mul_of_nonneg_left hn (show 0 ≤ 3*L+2 by positivity)
    have h₂ := mul_le_mul_of_nonneg_left heps (Nat.cast_nonneg (α := ℝ) n)
    nlinarith
  rw [PolicyBranch.weight,← Real.rpow_add (by positivity : 0 < (2:ℝ)^N)]
  exact Real.rpow_le_rpow_of_exponent_le (one_le_pow₀ (by norm_num)) (by simpa [sub_eq_add_neg] using hexp)

end CurrentFalconer.DimensionalPolicy
end GraphLiteralSupport
end
end

end OAI
