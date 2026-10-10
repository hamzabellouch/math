import OAI.NumberTheory.Ostmann.Characters.TemplateSourceFactorialBudget
import OAI.NumberTheory.Ostmann.Characters.TemplateSourceParityUpperExponent

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters.HigherBiasSource.SourceTemplate
open Construction Preliminaries Template HigherBiasSourceWord HigherBiasSourceRoleBounds
open InitialCharacterScale Filter DiagonalEstimate ParityActions
attribute [local instance] Classical.propDecidable

theorem exists_sourceTerminal_separation_threshold_with_exponent (d : Decomposition)
    {δ α β ρ γ c₀ c BD : ℝ} (hα : 0<α) (hαβ : α<β)
    (hρ : 0<ρ) (hγ : 0<γ) (hBD : 0<BD) (A : ℝ) :
    ∃N : ℕ,∀n : ℕ,N≤n → ∀τ αpair : ℝ,0<τ → 0<αpair →
      ∀ᶠ L : ℝ in atTop,∀ E : Finset ℕ,(∀p∈E,p.Prime) →
      (∀p∈E,α*L≤Real.log (Real.log p) ∧ Real.log (Real.log p)≤β*L) →
      ∀s : SelectedWordSource d E δ L (n+1) α β ρ γ c₀,∀w : FixedConfigurationWitness s c BD,
      ∀B V : (l:ℕ) → State (n+1) (l+1) → ℤ,
      (∀σ υ : Reassignments (n+1) n (wordSize (n+1) L),σ≠υ →
        ∀h h',‖sourceHistoryPairMean w B V n σ υ h h'‖ ≤ Real.exp (-τ*Real.exp (αpair*L))) →
      ‖sourceAmplitudeSequence w B V (n+1)‖ <
        Real.exp (-A*(2:ℝ)^(n+1)*(wordSize (n+1) L:ℝ)) := by
  obtain ⟨N,hN⟩ := exists_sourceFactorial_threshold A BD β
  refine ⟨N,?_⟩
  intro n hn τ αpair hτ hαpair
  filter_upwards [eventually_sourceParity_upper_of_pairs_with_exponent (δ:=δ) (c₀:=c₀) (c:=c)
      d (n+1) n le_rfl hα hαβ hρ hγ hBD hτ hαpair,hN n hn αpair τ hαpair hτ] with L hu hs
  intro E hE hband s w B V hpair
  have ht := (hu E hE hband s w B V hpair).trans_lt hs
  have he : Real.exp (-2*A*(2:ℝ)^(n+1)*(wordSize (n+1) L:ℝ)) =
      (Real.exp (-A*(2:ℝ)^(n+1)*(wordSize (n+1) L:ℝ)))^2 := by
    rw [pow_two,←Real.exp_add]
    congr 1
    ring
  rw [he] at ht
  nlinarith [norm_nonneg (sourceAmplitudeSequence w B V (n+1)),
    Real.exp_pos (-A*(2:ℝ)^(n+1)*(wordSize (n+1) L:ℝ))]

end Ostmann.Characters.HigherBiasSource.SourceTemplate

end

end OAI
