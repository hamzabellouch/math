import OAI.NumberTheory.Ostmann.Characters.DiagonalEstimateMarginalScales
import OAI.NumberTheory.Ostmann.Characters.SourceTemplateWindow
import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedCancellationPrimePriorsGrid
import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedCancellationTerminalSourceMean
import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedPhaseTerminalMaskedNormEventual
import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedPhaseTerminalSourceScales

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters.TemplateOneSidedCancellation
open Construction Preliminaries Template Template.OneSidedPhase TemplateSupportRemoval
open HigherBiasSource HigherBiasSource.SourceTemplate InitialCharacterScale HigherBiasSourceRoleBounds
open DiagonalEstimate ParityActions TemplateOneSidedNumericInputs TemplateOneSidedSourceScales
open HistoryFrequencyBudget HistoryFrequencyLabels Filter
attribute [local instance] Classical.propDecidable

theorem eventually_sourceTerminalCoreSlice_bound (k n : ℕ) (hn : n+1≤k)
    {α β ρ γ c₀ c BD : ℝ} (hα : 0<α) (hαβ : α<β)
    (hρ : 0<ρ) (hγ : 0<γ) (hc₀ : 0<c₀) (hc : 0<c) (hBD : 0≤BD) :
    ∃decay : ℝ,0<decay ∧ ∀ᶠ ℓ : ℝ in atTop,
    ∀(d : Decomposition)(E : Finset ℕ)(δ : ℝ),
      (∀q∈E,q.Prime) →
      (∀q∈E,α*ℓ≤Real.log (Real.log q) ∧ Real.log (Real.log q)≤β*ℓ) →
    ∀(s : SelectedWordSource d E δ ℓ k α β ρ γ c₀)(w : FixedConfigurationWitness s c BD)
      (σ τ : Reassignments k n (wordSize k ℓ)),σ≠τ →
    ∃L S : (schedule k (n+1)).Constituent (sourceWidth w.configuration (wordSize k ℓ)),L≠S ∧
    ∀(h h' : SourceHistory (k:=k) (L:=ℓ) (BD:=BD) (n+1)),h.val.1=h'.val.1 →
    ∀(masks : (schedule k (n+1)).Constituent (sourceWidth w.configuration (wordSize k ℓ))→ℕ→ℂ),
      (∀i q,‖masks i q‖≤1) →
    ∀p : (schedule k (n+1)).Constituent (sourceWidth w.configuration (wordSize k ℓ))→PrimeUpTo s.locations.Q,
      (productPrior (sourceTerminalCoordinatePrior w n)).mass p≠0 → ∀gate : Bool,
    ‖(sourceTerminalCoordinatePrior w n L).cmean (fun q=>
      (sourceTerminalCoordinatePrior w n S).cmean (fun r=>
        sourceTerminalCoreSlice w n σ τ h h' masks p L S gate q r))‖ ≤
      Real.exp (-decay*Real.exp (lowerExponent α γ*ℓ)) := by
  let a := sourceFrequencyRate BD k
  let z := depthScale k
  let Cmod := terminalModulusCost a k n
  have ha : 0≤a := add_nonneg hBD
    (mul_nonneg (by norm_num) (Real.log_nonneg (one_le_depthScale k)))
  have hz : 0<z := depthScale_pos k
  have hβ : 0<β := hα.trans hαβ
  have hCmod : 0<Cmod := terminalModulusCost_pos ha k n
  obtain ⟨C,hC,hcore⟩ := exists_terminal_core_prime_bound k n 1
    (sourceAtomWidth k c) (configurationProductWidth k c) hz ha hCmod.le hβ.le
  obtain ⟨decay,hdecay,hgrid⟩ := eventually_original_prime_priors_scale_grid
    (τ:=Fin (2^(n+1)) ⊕ Fin (2^(n+1))) C z (β+1) 4 α β γ β
    hC.le hz (by linarith) hα hγ hβ.le
  refine ⟨decay,hdecay,?_⟩
  filter_upwards [hgrid,eventually_terminal_sourceWidth_le k,
    eventually_terminal_frequency_height ha hz.le hβ k n,
    eventually_sourceTerminalMaskedFactors_norms k BD c α hBD hα,
    eventually_sourceScheduled_marginal_bounds k hα hαβ hρ hγ hc₀ hc,
    (wordSize_tendsto k).eventually_ge_atTop 1,eventually_gt_atTop (0:ℝ)]
    with ℓ hgridL hw hfreq hnorm hmass hmR hℓ
  intro d E δ hE hband s w σ τ hστ
  have hm : 1≤wordSize k ℓ := by exact_mod_cast hmR
  obtain ⟨L,S,positive,b,hLS,hforward,hreverse,hb,hlo,hls,hsl,hshort,hlong,hsep⟩ :=
    sourceTerminal_changed_edge_scales w n hα hγ hℓ hband hn hστ
  refine ⟨L,S,hLS,?_⟩
  intro h h' hroot masks hmasks p hp gate
  have hnorms := hnorm d E δ β ρ γ c₀ hband s w n hn σ τ h h' hroot masks hmasks p hp L S
  have hwidth := hw d E δ α β ρ γ c₀ c BD s w
  have hX : (1:ℝ)≤ s.locations.X := by
    have hpX : 0<s.locations.X := by exact_mod_cast fixedConfiguration_X_pos w
    exact_mod_cast hpX
  have ht : RangeSupported (ranges a (wordSize k ℓ:ℝ) (n+1)) (n+1) [] h.val.1 h.val.2 := h.property
  have hu : RangeSupported (ranges a (wordSize k ℓ:ℝ) (n+1)) (n+1) [] h'.val.1 h'.val.2 := h'.property
  have hQ := terminalPair_modulus_le_cost ha k n z ℓ hm
    (sourceWidth w.configuration (wordSize k ℓ)) hwidth (wordSize k ℓ)
    (by rw [sourceWidth_word];omega) σ τ h.val.1 h'.val.1 h.val.2 h'.val.2 ht hu
  have hh := hcore ℓ (β+1) (lowerExponent α γ) (shortExponent γ b.val)
    (longExponent γ b.val+scaleStep γ) β decay (hgridL b hb)
    (sourceScheduledShells w (n+1) L) (sourceScheduledShells w (n+1) S)
    (sourceScheduledShells_pos w (n+1) L) (sourceScheduledShells_pos w (n+1) S)
    (sourceWidth w.configuration (wordSize k ℓ)) (wordSize k ℓ+1) (wordSize k ℓ)
    (by rw [sourceWidth_word];omega)
    (fun j=>sourceRecurrenceB w.configuration s.J (gapSchedule BD k ℓ) c j (fun _=>0))
    (sourcePivotTarget w.configuration s.J (gapSchedule BD k ℓ)) s.J h.val.1 h'.val.1
    σ τ h.val.2 h'.val.2 L (fun r=>heldPrimeCoordinates p L S r.val) gate s.locations.X
    (fun r=>exposedCharacter (sourceTerminalCharacters w n S r.val.val) positive)
    (fun q=>sourceTerminalMaskedLongFactor w n σ τ masks p L S h.val.1 h.val.2 h'.val.2 q.val)
    (fun r=>sourceTerminalMaskedShortFactor w n σ τ masks p L S h.val.1 h.val.2 h'.val.2 r.val.val)
    hmR hX hwidth (by simp only [one_mul];exact le_rfl) ht hu hfreq hQ
    (fun q hq r=>sourceTerminalHeldCoordinates_height w n hCmod.le hband p hp L S q r.val hq r.property)
    (fun r=>sourceTerminal_shell_exposedCharacter_ne_one w n S r.val r.property positive)
    hnorms.1 (fun r=>hnorms.2 r.val r.property)
    (hmass d E δ BD hE hband s w (n+1) L).1
    (hmass d E δ BD hE hband s w (n+1) S).1
    (fun q hq=>(hshort q hq).1) (fun q hq=>(hshort q hq).2)
    (fun q hq=>(hlong q hq).1) (fun q hq=>(hlong q hq).2)
  rw [sourceTerminalCoreSlice_eq_analytic w n σ τ h h' masks p L S hLS hsep
    positive hforward hreverse gate]
  simpa only [sourceTerminalCoreAmplitude,sourceTerminalCoordinatePrior,sourceRecurrenceV,
    initialGap,sourceFrequencyRate,wordSize,a,z] using hh

end Ostmann.Characters.TemplateOneSidedCancellation

end

end OAI
