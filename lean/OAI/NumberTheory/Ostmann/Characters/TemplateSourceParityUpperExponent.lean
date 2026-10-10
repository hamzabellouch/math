import OAI.NumberTheory.Ostmann.Characters.TemplateSourceParity
import OAI.NumberTheory.Ostmann.Characters.TemplateTerminalGramCardAbsorption
import OAI.NumberTheory.Ostmann.Characters.TemplateTerminalRootCard

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Characters.HigherBiasSource.SourceTemplate
open Construction Preliminaries Template HistoryFrequencyLabels HistoryFrequencyBudget
open HigherBiasSourceWord HigherBiasSourceRoleBounds InitialCharacterScale Filter DiagonalEstimate ParityActions
attribute [local instance] Classical.propDecidable

theorem eventually_sourceParity_upper_of_pairs_with_exponent (d : Decomposition) (k n : ℕ) (hn : n+1≤k)
    {δ α β ρ γ c₀ c BD τ αpair : ℝ} (hα : 0<α) (hαβ : α<β)
    (hρ : 0<ρ) (hγ : 0<γ) (hBD : 0<BD) (hτ : 0<τ) (hαpair : 0<αpair) :
    ∀ᶠ L : ℝ in atTop,∀ E : Finset ℕ,(∀p∈E,p.Prime) →
      (∀p∈E,α*L≤Real.log (Real.log p) ∧ Real.log (Real.log p)≤β*L) →
      ∀s : SelectedWordSource d E δ L k α β ρ γ c₀,∀w : FixedConfigurationWitness s c BD,
      ∀B V : (l:ℕ) → State k (l+1) → ℤ,
      (∀σ υ : Reassignments k n (wordSize k L),σ≠υ →
        ∀h h',‖sourceHistoryPairMean w B V n σ υ h h'‖ ≤ Real.exp (-τ*Real.exp (αpair*L))) →
      ‖sourceAmplitudeSequence w B V (n+1)‖^2 ≤
        2*Real.exp ((BD+20*Real.log (depthScale k)+1)*(2:ℝ)^(n+1)*(wordSize k L:ℝ))*
          (Real.exp ((2*β+3)*(2:ℝ)^(n+1)*(wordSize k L:ℝ))/(factorialCount n (wordSize k L):ℝ)+
            Real.exp (-(τ/2)*Real.exp (αpair*L))) := by
  have hrate : 0 ≤ BD+20*Real.log (depthScale k) :=
    add_nonneg hBD.le (mul_nonneg (by norm_num) (Real.log_nonneg (one_le_depthScale k)))
  filter_upwards [eventually_sourceRootEnergy_le (δ:=δ) (c₀:=c₀) (c:=c) d k (n+1) hn hα hαβ hρ hγ hBD,
    terminalRoot_card_eventually (n+1) (a:=BD+20*Real.log (depthScale k))
      (δ:=1) (depthScale_pos k) (by norm_num),
    terminalHistoryPair_card_eventually (n+1) (depthScale_pos k) hrate hαpair hτ,
    eventually_ge_atTop (0:ℝ),(wordSize_tendsto k).eventually_ge_atTop 1]
    with L hnorm hcard hhist hL hm
  intro E hE hband s w B V hpair
  have hr : (1:ℝ)≤(2:ℝ)^(n+1) := one_le_pow₀ (by norm_num)
  have hm0 : (0:ℝ)≤wordSize k L := Nat.cast_nonneg _
  have hLm : L≤2*(wordSize k L:ℝ) := by
    have hlower := (wordSize_bounds k hL).1
    have hzL := mul_le_mul_of_nonneg_right (one_le_depthScale k) hL
    nlinarith
  have henergy : sourceRootEnergy w B V (n+1) ≤
      Real.exp ((2*β+3)*(2:ℝ)^(n+1)*(wordSize k L:ℝ)) := by
    apply (hnorm E hE hband s w B V).trans
    apply Real.exp_le_exp.mpr
    have hβ : 0 ≤ β+1 := by linarith
    have ha := mul_le_mul_of_nonneg_left hLm (mul_nonneg hβ (by positivity : 0≤(2:ℝ)^(n+1)))
    have hb := mul_le_mul_of_nonneg_right hr hm0
    nlinarith
  have hroot : (Fintype.card ↥(ranges (BD+20*Real.log (depthScale k))
      (wordSize k L:ℝ) (n+1) []) : ℝ) ≤
      2*Real.exp ((BD+20*Real.log (depthScale k)+1)*(2:ℝ)^(n+1)*(wordSize k L:ℝ)) := by
    apply hcard.trans
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    apply Real.exp_le_exp.mpr
    change ((2:ℝ)^(n+1)*(BD+20*Real.log (depthScale k))+1)*(wordSize k L:ℝ) ≤ _
    have hh := mul_le_mul_of_nonneg_right hr hm0
    nlinarith
  have hcomp := sourceParity_comparison w B V n (Real.exp_pos _).le hpair
  have hbracket := add_le_add
    (div_le_div_of_nonneg_right henergy (Nat.cast_nonneg (factorialCount n (wordSize k L)))) hhist
  exact (hcomp.trans (mul_le_mul_of_nonneg_left hbracket (Nat.cast_nonneg _))).trans
    (mul_le_mul_of_nonneg_right hroot (by positivity))

end Ostmann.Characters.HigherBiasSource.SourceTemplate

end

end OAI
