import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedPhaseTerminalEdge
import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedSourceScalesBands

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters.Template.OneSidedPhase
open Construction Preliminaries HigherBiasSource HigherBiasSource.SourceTemplate
open InitialCharacterScale HigherBiasSourceWord ParityActions TemplateOneSidedSourceScales DiagonalEstimate
attribute [local instance] Classical.propDecidable
section
variable {d : Decomposition} {E : Finset ℕ} {δ ℓ α β ρ γ c₀ c BD : ℝ} {k : ℕ}
    {s : SelectedWordSource d E δ ℓ k α β ρ γ c₀} (w : FixedConfigurationWitness s c BD)
    (n : ℕ)

abbrev sourceTerminalBulk (z : BulkSlot k n (wordSize k ℓ)) :=
  prefixBulkEmbedding k n (sourceWidth w.configuration (wordSize k ℓ)) (wordSize k ℓ)
    (by rw [sourceWidth_word];omega) z

abbrev sourceTerminalAnchor (hn : n+1≤k) (j : Fin (n+1)) (b : Bool) :=
  smallAnchorConstituent k n hn (sourceWidth w.configuration (wordSize k ℓ))
    (by intro j;rw [sourceWidth_anchor];omega) j b

theorem sourceTerminalBulk_shell (z : BulkSlot k n (wordSize k ℓ)) :
    sourceScheduledShells w (n+1) (sourceTerminalBulk w n z)=s.locations.base 0 :=
  scheduled_sourceShell_prefix w.configuration (wordSize k ℓ) n _
    (s.locations.base 0) (s.locations.base 2) s.locations.primes z

theorem sourceTerminalAnchor_shell (hn : n+1≤k) (j : Fin (n+1)) (b : Bool) :
    sourceScheduledShells w (n+1) (sourceTerminalAnchor w n hn j b)=
      boundedRawLogCell s.locations.primes
        (w.configuration.1 (anchorCoordinate ⟨j.val,j.isLt.trans_le hn⟩ false)) := by
  exact scheduledPrimeShells_anchor w.configuration (wordSize k ℓ) (n+1)
    (s.locations.base 0) (s.locations.base 2) s.locations.primes
    (retiredAnchors k (n+1) hn false j b).val ⟨j.val,j.isLt.trans_le hn⟩ false
    (retiredAnchors k (n+1) hn false j b).property.2 _

theorem sourceTerminal_edge_bands (hn : n+1≤k) (z : BulkSlot k n (wordSize k ℓ))
    (j : Fin (n+1)) (b : Bool) :
    (∀q∈sourceScheduledShells w (n+1) (sourceTerminalAnchor w n hn j b),
      Real.log q.val≤Real.exp (shortUpper s.locations false)) ∧
    (∀q∈sourceScheduledShells w (n+1) (sourceTerminalBulk w n z),
      Real.exp (longLower s.locations false)≤Real.log q.val) := by
  constructor
  · intro q hq
    rw [sourceTerminalAnchor_shell] at hq
    exact (fixedConfiguration_anchor_log_bounds w _ false q hq).2
  · intro q hq
    rw [sourceTerminalBulk_shell] at hq
    exact (boundedInterval_log_bounds s.locations.primes s.locations.B
      (s.locations.B+s.locations.w) q hq).1.le

theorem sourceTerminal_changed_edge_scales (hα : 0<α) (hγ : 0<γ) (hℓ : 0<ℓ)
    (hband : ∀q∈E,α*ℓ≤Real.log (Real.log q) ∧ Real.log (Real.log q)≤β*ℓ)
    (hn : n+1≤k) {σ τ : Reassignments k n (wordSize k ℓ)} (hστ : σ≠τ) :
    ∃L S : (schedule k (n+1)).Constituent (sourceWidth w.configuration (wordSize k ℓ)),
      ∃positive : Bool, ∃a : Fin (scaleCount β γ),
      L≠S ∧ sourceTerminalGraph w n σ τ S L=(if positive then 2 else -2) ∧
      sourceTerminalGraph w n σ τ L S=0 ∧
      0<a.val ∧ 0<lowerExponent α γ ∧ lowerExponent α γ ≤ shortExponent γ a.val ∧
      shortExponent γ a.val<longExponent γ a.val ∧
      (∀q∈sourceScheduledShells w (n+1) S,
        Real.exp (lowerExponent α γ*ℓ)≤Real.log q.val ∧
          Real.log q.val≤Real.exp (shortExponent γ a.val*ℓ)) ∧
      (∀q∈sourceScheduledShells w (n+1) L,
        Real.exp ((longExponent γ a.val+scaleStep γ)*ℓ)≤Real.log q.val ∧
          Real.log q.val≤Real.exp (β*ℓ)) ∧
      (∀q∈sourceScheduledShells w (n+1) L,
        ∀r∈sourceScheduledShells w (n+1) S,q.val.Coprime r.val) := by
  obtain ⟨z,j,b,positive,hLS,hf,hr⟩ := sourceTerminal_changed_edge w n hn hστ
  obtain ⟨a,ha,has,hal⟩ := actual_location_grid s.locations hγ hℓ false
  have he := scale_exponents hα hγ ha
  have hb := sourceTerminal_edge_bands w n hn z j b
  refine ⟨sourceTerminalBulk w n z,sourceTerminalAnchor w n hn j b,
    positive,a,hLS,hf,hr,ha,he.1,he.2.1,he.2.2,?_,?_,?_⟩
  · intro q hq
    constructor
    · exact (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (min_le_left _ _) hℓ.le)).trans
        (fixedConfiguration_scheduled_log_bounds w hband (n+1) _ q hq).1
    · exact (hb.1 q hq).trans (Real.exp_le_exp.mpr has)
  · intro q hq
    exact ⟨(Real.exp_le_exp.mpr hal).trans (hb.2 q hq),
      (fixedConfiguration_scheduled_log_bounds w hband (n+1) _ q hq).2⟩
  · have hg := (actual_location_gap s.locations hγ hℓ false).2.2
    have hs : shortUpper s.locations false<longLower s.locations false := by
      linarith [mul_pos hγ hℓ]
    intro q hq r hr
    apply (primeUpTo_prime q).coprime_iff_not_dvd.mpr
    intro hd
    have hqr : q.val=r.val := ((primeUpTo_prime r).eq_one_or_self_of_dvd q.val hd).resolve_left
      (primeUpTo_prime q).ne_one
    have hsmall := (hb.1 r hr).trans_lt (Real.exp_lt_exp.mpr hs)
    have hlarge := hb.2 q hq
    rw [hqr] at hlarge
    exact (not_lt_of_ge hlarge) hsmall
end
end Ostmann.Characters.Template.OneSidedPhase

end

end OAI
