import Mathlib
import OAI.MeasureTheory.Falconer.Estimates.ActualDirectBuffer
import OAI.MeasureTheory.Falconer.Estimates.ActualOuterMasks
import OAI.MeasureTheory.Falconer.Model
import OAI.MeasureTheory.Falconer.Recursion.BranchCounts
import OAI.MeasureTheory.Falconer.Recursion.BranchTransitions
import OAI.MeasureTheory.Falconer.Recursion.SourceBranchDepth
import OAI.MeasureTheory.FalconerCompletion.Graphs.SuffixDescendants
import OAI.MeasureTheory.FalconerCompletion.Recursion.Extend

namespace OAI

/-! Quantitative estimates for the distance-set construction. -/

open _root_.OAI.PlanarFalconer

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport.CurrentFalconer.DimensionalPolicy
open PlanarFalconer

theorem uniform_source_weighted_error_generalND (offset : ℕ) {sig kap T eps L C B : ℝ}
    (hsig : 0<sig) (hkap : 0<kap) (hkap1 : kap≤1) (hgap : sig<kap/1000)
    (hL : 0≤L) (hC : 0≤C) (heps : eps≤1)
    (hT : (3*L+C*(sig+sig)+1)*(20/kap+1/sig)+B≤T) :
    ∃ N₀ : ℕ,0<N₀ ∧ ∀ N≥N₀,∀ A : ℕ → ℝ,ProfileLipschitzND A N L →
      ∀ j : ℕ,∀ b : PolicyBranch A N (sourcePolicyBlock N kap) offset sig j,
      b.weight C sig eps*((2:ℝ)^N)^(-T)≤((2:ℝ)^N)^(-B) := by
  obtain ⟨N₀,hN₀,h₀⟩ := uniform_source_ceiling_slack hsig hgap
  refine ⟨N₀,hN₀,?_⟩
  intro N hN A hA j b
  have hNp : 0<N := by omega
  have hq := sourcePolicyBlock_pos hNp hkap
  have hn := (source_branch_count_bounds hNp hsig hkap hkap1 (h₀ N hN).1 b).2.2
  have hb : b.exponentSum C sig eps≤(j:ℝ)*(3*L+C*(sig+sig)+eps) := by
    unfold PolicyBranch.exponentSum
    have hterm : ∀ k∈Finset.range j,
        branchExponentND A C sig sig eps (b.state k) (b.label k) (b.state (k+1))≤3*L+C*(sig+sig)+eps := by
      intro k hk
      have hk := Finset.mem_range.mp hk
      have hv := b.valid k hk.le
      have hu := b.valid (k+1) (by omega)
      have hc := (b.step k hk).cost_le hA hNp hq hL hv hu
      have hsd := BranchState.valid_depths hv
      have hud := BranchState.valid_depths hu
      have hi := abs_le.mp (hA.increment_le hNp hL (hud.1.trans hud.2) (hsd.1.trans hsd.2))
      have hloss : 0≤C*(sig+sig) := by positivity
      unfold branchExponentND
      split_ifs <;> linarith
    simpa only [Finset.sum_const,Finset.card_range,nsmul_eq_mul] using Finset.sum_le_sum hterm
  have hexp : b.exponentSum C sig eps-T≤-B := by
    have h₁ := mul_le_mul_of_nonneg_left hn (show 0≤3*L+C*(sig+sig)+1 by positivity)
    have h₂ := mul_le_mul_of_nonneg_left heps (Nat.cast_nonneg (α:=ℝ) j)
    nlinarith only [hb,h₁,h₂,hT]
  rw [PolicyBranch.weight,←Real.rpow_add (by positivity : 0<(2:ℝ)^N)]
  exact Real.rpow_le_rpow_of_exponent_le (one_le_pow₀ (by norm_num)) (by simpa only [sub_eq_add_neg] using hexp)
end GraphLiteralSupport.CurrentFalconer.DimensionalPolicy
end
end

end OAI
