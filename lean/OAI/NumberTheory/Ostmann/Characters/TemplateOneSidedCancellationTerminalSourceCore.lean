import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedCancellationTerminalSourceBound

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters.TemplateOneSidedCancellation
open Construction Preliminaries Template Template.OneSidedPhase TemplateSupportRemoval
open HigherBiasSource HigherBiasSource.SourceTemplate InitialCharacterScale HigherBiasSourceRoleBounds
open DiagonalEstimate ParityActions TemplateOneSidedSourceScales Filter
attribute [local instance] Classical.propDecidable

section
variable {d : Decomposition} {E : Finset ℕ} {δ ℓ α β ρ γ c₀ c BD : ℝ} {k : ℕ}
    {s : SelectedWordSource d E δ ℓ k α β ρ γ c₀} (w : FixedConfigurationWitness s c BD)
    (n : ℕ) (σ τ : Reassignments k n (wordSize k ℓ))
    (h h' : SourceHistory (k:=k) (L:=ℓ) (BD:=BD) (n+1))
    (masks : (schedule k (n+1)).Constituent (sourceWidth w.configuration (wordSize k ℓ))→ℕ→ℂ)
    (gate : Bool)

def sourceTerminalCoreMean : ℂ :=
  (productPrior (sourceTerminalCoordinatePrior w n)).cmean (fun x=>
    sourceTerminalMaskedPhase w n σ τ masks x h.val.1 h.val.2 h'.val.2 *
      sourceTerminalCoreAmplitude w n σ τ h h' gate (fun i=>((x i).val:ℤ)))

theorem sourceTerminalCoreMean_eq_slices
    (L S : (schedule k (n+1)).Constituent (sourceWidth w.configuration (wordSize k ℓ))) :
    sourceTerminalCoreMean w n σ τ h h' masks gate =
    (productPrior (sourceTerminalCoordinatePrior w n)).cmean (fun p=>
      (sourceTerminalCoordinatePrior w n L).cmean (fun q=>
        (sourceTerminalCoordinatePrior w n S).cmean (fun r=>
          sourceTerminalCoreSlice w n σ τ h h' masks p L S gate q r))) := by
  unfold sourceTerminalCoreMean
  rw [productPrior_cmean_update_two (sourceTerminalCoordinatePrior w n) L S]
  rfl

end

theorem eventually_sourceTerminalCoreMean_small (k n : ℕ) (hn : n+1≤k)
    {α β ρ γ c₀ c BD : ℝ} (hα : 0<α) (hαβ : α<β)
    (hρ : 0<ρ) (hγ : 0<γ) (hc₀ : 0<c₀) (hc : 0<c) (hBD : 0≤BD) :
    ∃decay : ℝ,0<decay ∧ ∀ᶠ ℓ : ℝ in atTop,
    ∀(d : Decomposition)(E : Finset ℕ)(δ : ℝ),
      (∀q∈E,q.Prime) →
      (∀q∈E,α*ℓ≤Real.log (Real.log q) ∧ Real.log (Real.log q)≤β*ℓ) →
    ∀(s : SelectedWordSource d E δ ℓ k α β ρ γ c₀)(w : FixedConfigurationWitness s c BD)
      (σ τ : Reassignments k n (wordSize k ℓ)),σ≠τ →
    ∀(h h' : SourceHistory (k:=k) (L:=ℓ) (BD:=BD) (n+1)),h.val.1=h'.val.1 →
    ∀(masks : (schedule k (n+1)).Constituent (sourceWidth w.configuration (wordSize k ℓ))→ℕ→ℂ),
      (∀i q,‖masks i q‖≤1) → ∀gate : Bool,
    ‖sourceTerminalCoreMean w n σ τ h h' masks gate‖ ≤
      Real.exp (-decay*Real.exp (lowerExponent α γ*ℓ)) := by
  obtain ⟨decay,hdecay,hbound⟩ := eventually_sourceTerminalCoreSlice_bound k n hn
    hα hαβ hρ hγ hc₀ hc hBD
  refine ⟨decay,hdecay,?_⟩
  filter_upwards [hbound] with ℓ hℓ
  intro d E δ hE hband s w σ τ hστ h h' hroot masks hmasks gate
  obtain ⟨L,S,_hLS,hslice⟩ := hℓ d E δ hE hband s w σ τ hστ
  rw [sourceTerminalCoreMean_eq_slices w n σ τ h h' masks gate L S]
  apply norm_cmean_le_of_mass_support
  intro p hp
  exact hslice h h' hroot masks hmasks p hp gate

end Ostmann.Characters.TemplateOneSidedCancellation

end

end OAI
