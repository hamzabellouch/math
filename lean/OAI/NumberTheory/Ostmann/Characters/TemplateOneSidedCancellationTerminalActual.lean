import OAI.NumberTheory.Ostmann.Characters.HigherBiasCancellationEndpoints
import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedCancellationTerminalError
import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedCancellationTerminalSourceCore
import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedTerminalSupportRemovalEnd
import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedTerminalSupportRemovalError

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters.HigherBiasContradiction
open Construction Preliminaries Template HigherBiasSource HigherBiasSource.SourceTemplate
open InitialCharacterScale Filter DiagonalEstimate ParityActions TemplateOneSidedSourceScales
open TemplateOneSidedCancellation TemplateOneSidedTerminalSupportRemoval
attribute [local instance] Classical.propDecidable

theorem actual_terminalCancellation (d : Decomposition) (δ : ℝ) (n : ℕ)
    {α β ρ γ c₀ c BD : ℝ} (hα : 0 < α) (hαβ : α < β)
    (hρ : 0 < ρ) (hγ : 0 < γ) (hc₀ : 0 < c₀) (hc : 0 < c) (hBD : 0 ≤ BD) :
    TerminalCancellation d δ α β ρ γ c₀ c BD n := by
  obtain ⟨coreRate,hcoreRate,hcore⟩ := eventually_sourceTerminalCoreMean_small (n+1) n
    (le_refl _) hα hαβ hρ hγ hc₀ hc hBD
  have hlo : 0 < lowerExponent α γ :=
    lt_min hα (div_pos (div_pos hγ (by norm_num)) (by norm_num))
  obtain ⟨rate,exponent,hrate,hexponent,hcombine⟩ := eventually_terminal_error_combine
    (c₁:=(1/8:ℝ)) (α₁:=α) (c₂:=coreRate) (α₂:=lowerExponent α γ)
    (by norm_num) hcoreRate hα hlo
  refine ⟨rate,exponent,hrate,hexponent,?_⟩
  filter_upwards [hcore,eventually_terminal_mean_sub_core_le n hα hαβ hρ hγ hc₀ hc hBD,
    hcombine] with L hcore herr hcombine
  intro E hE hband s w σ τ hστ h h'
  by_cases hroot : h.val.1=h'.val.1
  · have he := herr d E δ hE hband s w
      (sourceRecurrenceB w.configuration s.J (gapSchedule BD (n+1) L) c)
      (sourceRecurrenceV BD (n+1) L) σ τ h h' hroot
    rw [terminalCoreMean_eq_sourceTerminalCoreMean w n σ τ h h'] at he
    exact hcombine _ _ he (hcore d E δ hE hband s w σ τ hστ h h' hroot
      (fun _ _=>1) (by intro i q;norm_num) (terminalPolynomialGate w n σ τ h h'))
  · have hz : SourceTemplate.sourceHistoryPairMean w
        (sourceRecurrenceB w.configuration s.J (gapSchedule BD (n+1) L) c)
        (sourceRecurrenceV BD (n+1) L) n σ τ h h'=0 := by
      simp only [SourceTemplate.sourceHistoryPairMean,terminalHistoryPairMean,hroot,ite_false,
        FinitePrior.cmean,mul_zero,Finset.sum_const_zero]
    rw [hz,norm_zero]
    exact (Real.exp_pos _).le

end Ostmann.Characters.HigherBiasContradiction

end

end OAI
