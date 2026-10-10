import OAI.NumberTheory.Ostmann.Characters.DiagonalEstimateFiniteRates
import OAI.NumberTheory.Ostmann.Characters.DiagonalEstimateSourceHistoryZero
import OAI.NumberTheory.Ostmann.Characters.DiagonalEstimateSupportRemoval
import OAI.NumberTheory.Ostmann.Characters.DiagonalEstimateSupportRemovalCombine
import OAI.NumberTheory.Ostmann.Characters.HigherBiasCancellationEndpoints
import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedCancellationSourceCore

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters.HigherBiasContradiction
open Construction Preliminaries Template HigherBiasSource HigherBiasSource.SourceTemplate
open InitialCharacterScale Filter DiagonalEstimate TemplateOneSidedSourceScales
attribute [local instance] Classical.propDecidable

theorem actual_diagonalCancellation (d : Decomposition) (δ : ℝ) (k : ℕ)
    {α β ρ γ c₀ c BD : ℝ} (hα : 0 < α) (hαβ : α < β)
    (hρ : 0 < ρ) (hγ : 0 < γ) (hc₀ : 0 < c₀) (hc : 0 < c) (hBD : 0 ≤ BD) :
    DiagonalCancellation d δ α β ρ γ c₀ c BD k := by
  choose rates hrates hcores using fun i : Fin k=>
    TemplateOneSidedCancellation.eventually_sourceCorePairMean_small k i.val i.isLt
      BD α β ρ γ c₀ c hBD hα hαβ hρ hγ hc₀ hc
  obtain ⟨rate,hrate,hrate_le⟩ := exists_positive_uniform_rate rates hrates
  obtain ⟨Kerr,hKerr,herr⟩ := exists_eventually_sourceHistoryPairMean_sub_core k
    hα hαβ hρ hγ hc₀ hc hBD
  have hexponent : 0 < lowerExponent α γ := by
    exact lt_min hα (div_pos (div_pos hγ (by norm_num)) (by norm_num))
  obtain ⟨K,hK,τ,hτ,αpair,hαpair,hcombine⟩ := supportRemoval_combine_eventually Kerr 0
    (c₁:=(1/4:ℝ)) (α₁:=α) (c₂:=rate) (α₂:=lowerExponent α γ)
    (by norm_num) hrate hα hexponent
  refine ⟨K,τ,αpair,hτ,hαpair,?_⟩
  filter_upwards [Filter.eventually_all.mpr hcores,herr,hcombine] with L hcores herr hcombine
  intro E hE hband s w j hj P hP e he h h'
  have hbad : e∉codePreservingMatchings w.configuration (wordSize k L) j :=
    (Finset.mem_sdiff.mp he).2
  by_cases hbulk : ∀i,IsCopiedBulk w.configuration (wordSize k L) j (e i) ↔
      IsCopiedBulk w.configuration (wordSize k L) j i
  · by_cases hroot : h.val.1=h'.val.1
    · let B : ℕ→ℤ := fun l=>(⌊Real.exp (sourcePivotTarget w.configuration s.J
        (gapSchedule BD k L) l+sourceAtomWidth k c)⌋₊:ℕ)
      let V : ℕ→ℤ := fun l=>(HistoryFrequencyBudget.bound
        (BD+20*Real.log (depthScale k)) (wordSize k L:ℝ) l:ℤ)
      have hc := hcores ⟨j,hj⟩ d E δ hE hband s w B P hP e hbulk hbad h h' hroot
      have hc' : ‖sourceCorePairMean w j hj B V P e h h'‖ ≤
          Real.exp ((0:ℝ)*L^2-rate*Real.exp (lowerExponent α γ*L)) := by
        apply hc.trans
        apply Real.exp_le_exp.mpr
        simp only [zero_mul,zero_sub]
        simpa only [neg_mul] using neg_le_neg (mul_le_mul_of_nonneg_right
          (hrate_le ⟨j,hj⟩) (Real.exp_pos (lowerExponent α γ*L)).le)
      exact hcombine _ _ (herr d E δ hE hband s w j hj B V P hP e h h' hroot) hc'
    · have hroot' : historyRootIndex j
          (HistoryFrequencyBudget.ranges (BD+20*Real.log (depthScale k)) (wordSize k L:ℝ) j) [] h' ≠
          historyRootIndex j
          (HistoryFrequencyBudget.ranges (BD+20*Real.log (depthScale k)) (wordSize k L:ℝ) j) [] h := by
        intro hh
        exact hroot (congrArg Subtype.val hh).symm
      rw [sourceHistoryPairMean_eq_zero_of_root_ne w j hj _ _ P e h h' hroot',norm_zero]
      exact (Real.exp_pos _).le
  · rw [sourceHistoryPairMean_eq_zero_of_not_preserves_bulk w j hj _ _ P e h h' hbulk,norm_zero]
    exact (Real.exp_pos _).le

end Ostmann.Characters.HigherBiasContradiction

end

end OAI
