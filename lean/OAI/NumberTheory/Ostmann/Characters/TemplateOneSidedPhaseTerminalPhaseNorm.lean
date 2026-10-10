import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedPhaseTerminalIndexedNormEventual

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators ComplexConjugate
namespace Ostmann.Characters.Template.OneSidedPhase
open Construction Preliminaries HigherBiasSource HigherBiasSource.SourceTemplate
open HistoryFrequencyLabels HistoryFrequencyBudget InitialCharacterScale HigherBiasSourceRoleBounds HigherBiasSourceWord
open DiagonalEstimate ParityActions Filter
attribute [local instance] Classical.propDecidable

theorem norm_primeGraphPhase_le_one {I : Type*} [Fintype I]
    (D : I→I→ℤ) (p : I→ℕ) (hp : ∀i,(p i).Prime)
    (χ : ∀i,MulChar (ZMod (p i)) ℂ) (ν : I→ℂ) (hν : ∀i,‖ν i‖≤1) :
    ‖primeGraphPhase D p χ ν‖≤1 := by
  rw [primeGraphPhase,norm_prod]
  apply Finset.prod_le_one₀ (fun i _=>norm_nonneg _)
  intro i hi
  rw [norm_mul]
  have hh : ‖∏j,χ i (p j)^D i j‖≤1 := by
    rw [norm_prod]
    apply Finset.prod_le_one₀ (fun j _=>norm_nonneg _)
    intro j hj
    exact norm_character_power_le_of_prime (hp i) (χ i) (p j) (D i j)
  exact (mul_le_mul (hν i) hh (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)

section
variable {d : Decomposition} {E : Finset ℕ} {δ ℓ α β ρ γ c₀ c BD : ℝ} {k : ℕ}
    {s : SelectedWordSource d E δ ℓ k α β ρ γ c₀} (w : FixedConfigurationWitness s c BD)
    (n : ℕ)

theorem sourceTerminal_guardedPhase_norm_le_of_mass {U : ℕ}
    (σ τ : Reassignments k n (wordSize k ℓ))
    (h h' : SourceHistory (k:=k) (L:=ℓ) (BD:=BD) (n+1)) (hroot : h.val.1=h'.val.1)
    (hrange : ∀path f,f∈ranges (BD+20*Real.log (depthScale k)) (wordSize k ℓ : ℝ) (n+1) path→
      f≠0 ∧ f.natAbs≤U)
    (hlarge : ∀i q,q∈sourceScheduledShells w (n+1) i→U<q.val)
    (x : (schedule k (n+1)).Constituent (sourceWidth w.configuration (wordSize k ℓ))→PrimeUpTo s.locations.Q)
    (hx : (productPrior (sourceTerminalCoordinatePrior w n)).mass x≠0) :
    ‖if samplePrimeSupport (schedule k (n+1)) (sourceWidth w.configuration (wordSize k ℓ)) x then
      sourceTerminalPhasePair w n σ τ x h.val.1 h.val.2 h'.val.2 else 0‖≤1 := by
  split_ifs with hc
  · rw [sourceTerminalPhasePair_eq_graph w n σ τ x hc]
    apply norm_primeGraphPhase_le_one _ _ (fun i=>primeUpTo_prime (x i))
    intro i
    have hi : x i∈sourceScheduledShells w (n+1) i :=
      primeProductPrior_mem_of_mass_ne_zero (sourceScheduledShells w (n+1))
        (sourceScheduledShells_pos w (n+1)) x hx i
    exact sourceTerminalPairedUnary_norm_le w n σ τ h h' hroot hrange i (x i)
      (fixedConfiguration_scheduled_shell_subset w (n+1) i hi) (hlarge i (x i) hi)
  · simp only [norm_zero,zero_le_one]
end

theorem eventually_sourceTerminal_guardedPhase_norm (k : ℕ) (BD c α : ℝ)
    (hBD : 0≤BD) (hα : 0<α) :
    ∀ᶠ ℓ : ℝ in atTop,∀(d : Decomposition)(E : Finset ℕ)(δ β ρ γ c₀ : ℝ),
      (∀q∈E,α*ℓ≤Real.log (Real.log q) ∧ Real.log (Real.log q)≤β*ℓ) →
      ∀(s : SelectedWordSource d E δ ℓ k α β ρ γ c₀)(w : FixedConfigurationWitness s c BD),
      ∀n,n+1≤k → ∀(σ τ : Reassignments k n (wordSize k ℓ))
        (h h' : SourceHistory (k:=k) (L:=ℓ) (BD:=BD) (n+1)),h.val.1=h'.val.1 →
      ∀x : (schedule k (n+1)).Constituent (sourceWidth w.configuration (wordSize k ℓ))→PrimeUpTo s.locations.Q,
        (productPrior (sourceTerminalCoordinatePrior w n)).mass x≠0 →
        ‖if samplePrimeSupport (schedule k (n+1)) (sourceWidth w.configuration (wordSize k ℓ)) x then
          sourceTerminalPhasePair w n σ τ x h.val.1 h.val.2 h'.val.2 else 0‖≤1 := by
  filter_upwards [actualFrequencyCutoff_eventually k hBD hα] with ℓ hfreq
  intro d E δ β ρ γ c₀ hband s w n hn σ τ h h' hroot x hx
  apply sourceTerminal_guardedPhase_norm_le_of_mass w n σ τ h h' hroot
    (hfreq.1 (n+1) hn) _ x hx
  intro i q hq
  exact hfreq.2 q.val (fixedConfiguration_scheduled_log_bounds w hband (n+1) i q hq).1

end Ostmann.Characters.Template.OneSidedPhase

end

end OAI
