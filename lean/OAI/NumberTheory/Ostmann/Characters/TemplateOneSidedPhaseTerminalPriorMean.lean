import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedPhaseTerminalPriorDefs

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators ComplexConjugate
namespace Ostmann.Characters.Template.OneSidedPhase
open Construction Preliminaries HigherBiasSource HigherBiasSource.SourceTemplate
open HistoryFrequencyLabels HistoryFrequencyBudget InitialCharacterScale HigherBiasSourceRoleBounds HigherBiasSourceWord
open DiagonalEstimate ParityActions
attribute [local instance] Classical.propDecidable

section
variable {d : Decomposition} {E : Finset ℕ} {δ ℓ α β ρ γ c₀ c BD : ℝ} {k : ℕ}
    {s : SelectedWordSource d E δ ℓ k α β ρ γ c₀} (w : FixedConfigurationWitness s c BD)
    (B V : (l:ℕ)→State k (l+1)→ℤ) (n : ℕ)
    (σ τ : Reassignments k n (wordSize k ℓ))
    (h h' : SourceHistory (k:=k) (L:=ℓ) (BD:=BD) (n+1))

theorem terminal_sourceHistoryPairMean_eq_cmean (hroot : h.val.1=h'.val.1) :
    SourceTemplate.sourceHistoryPairMean w B V n σ τ h h' =
      (productPrior (sourceTerminalCoordinatePrior w n)).cmean
        (sourceTerminalKernel w n B V σ τ h h') := by
  unfold SourceTemplate.sourceHistoryPairMean terminalHistoryPairMean
  congr 1
  funext x
  rw [ite_eq_left hroot]
  have hp (υ : Reassignments k n (wordSize k ℓ)) :
      samplePrimeSupport (schedule k (n+1)) (sourceWidth w.configuration (wordSize k ℓ))
        (constituentAssignment (schedule k (n+1)) (sourceWidth w.configuration (wordSize k ℓ))
          (sourceTerminalPermutation w n υ) x) ↔
      samplePrimeSupport (schedule k (n+1)) (sourceWidth w.configuration (wordSize k ℓ)) x :=
    samplePrimeSupport_comp_perm _ _ x (sourceTerminalPermutation w n υ).symm
  change _ = sourceTerminalKernel w n B V σ τ h h' x
  unfold terminalHistoryTerm
  have hpσ := hp σ
  have hpτ := hp τ
  simp only [sourceTerminalPermutation] at hpσ hpτ
  simp only [hpσ,hpτ,sourceTerminalKernel]
  split_ifs with hx
  · simp only [sourceTerminalPhasePair,sourceTerminalAmplitude,map_mul]
    rw [←hroot]
    ring
  · simp only [map_zero,mul_zero]

theorem terminal_sourceHistoryPairMean_eq_two_prime_slices (hroot : h.val.1=h'.val.1)
    (L S : (schedule k (n+1)).Constituent (sourceWidth w.configuration (wordSize k ℓ))) :
    SourceTemplate.sourceHistoryPairMean w B V n σ τ h h' =
      (productPrior (sourceTerminalCoordinatePrior w n)).cmean (fun p=>
        (sourceTerminalCoordinatePrior w n L).cmean (fun q=>
          (sourceTerminalCoordinatePrior w n S).cmean (fun r=>
            sourceTerminalKernel w n B V σ τ h h' (twoPrimeSample p L S q r)))) := by
  rw [terminal_sourceHistoryPairMean_eq_cmean w B V n σ τ h h' hroot]
  exact productPrior_cmean_update_two (sourceTerminalCoordinatePrior w n) L S _

theorem norm_terminal_sourceHistoryPairMean_le_of_slices (hroot : h.val.1=h'.val.1)
    (L S : (schedule k (n+1)).Constituent (sourceWidth w.configuration (wordSize k ℓ)))
    (ε : ℝ) (hslice : ∀p,(productPrior (sourceTerminalCoordinatePrior w n)).mass p≠0→
      ‖(sourceTerminalCoordinatePrior w n L).cmean (fun q=>
        (sourceTerminalCoordinatePrior w n S).cmean (fun r=>
          sourceTerminalKernel w n B V σ τ h h' (twoPrimeSample p L S q r)))‖≤ε) :
    ‖SourceTemplate.sourceHistoryPairMean w B V n σ τ h h'‖≤ε := by
  rw [terminal_sourceHistoryPairMean_eq_cmean w B V n σ τ h h' hroot]
  exact norm_productPrior_cmean_le_of_two_coordinate (sourceTerminalCoordinatePrior w n) L S _ ε hslice

end
end Ostmann.Characters.Template.OneSidedPhase

end

end OAI
