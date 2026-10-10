import OAI.NumberTheory.Ostmann.Characters.InitialCharacterStatisticScaleBasic
import OAI.NumberTheory.Ostmann.Characters.SourceTemplateDefs
import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedCancellationTerminalDataBudget

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators SchwartzMap
namespace Ostmann.Characters.TemplateOneSidedCancellation
open Template TemplateOneSidedBudget Arithmetic HigherBiasSource HigherBiasSource.SourceTemplate
open InitialCharacterScale Filter TemplateOneSidedNumericInputs
attribute [local instance] Classical.propDecidable

theorem eventually_terminal_sourceWidth_le (k : ℕ) :
    ∀ᶠL : ℝ in atTop,∀(d : Decomposition) (E : Finset ℕ) (δ α β ρ γ c₀ c BD : ℝ),
      ∀(s : SelectedWordSource d E δ L k α β ρ γ c₀) (w : FixedConfigurationWitness s c BD),
      ∀r,sourceWidth w.configuration (wordSize k L) r ≤ wordSize k L+1 := by
  filter_upwards [(wordSize_tendsto k).eventually_ge_atTop (2*Real.exp (2*((1/10000:ℝ)*k)))]
    with L hL
  intro d E δ α β ρ γ c₀ c BD s w r
  have hlen (i : Fin (k+1)) : (w.configuration.2 i).length ≤ wordSize k L := by
    exact_mod_cast (w.geometry.length_upper i).trans hL
  cases r with
  | word => exact le_rfl
  | pivot j =>
    simp only [sourceWidth]
    split_ifs with hj
    · exact (hlen _).trans (Nat.le_add_right _ _)
    · omega
  | anchor j b => simp only [sourceWidth]; omega
  | filler => exact (hlen _).trans (Nat.le_add_right _ _)

theorem exists_terminal_width_profile_budget (k n : ℕ) (ρ : 𝓢(ℝ,ℂ))
    {z a C β : ℝ} (Wl : ℝ) (hz : 0 < z) (ha : 0 ≤ a) (hC : 0 ≤ C) (hβ : 0 ≤ β) :
    ∃C' : ℝ,0 < C' ∧ ∀L : ℝ,
      let m := ⌊z*L⌋₊
      let D := obstructionSizeFactor k (n+1)*(2*(m+2)+1)
      Real.exp ((-a*(m:ℝ)+Wl)/2)*leafProfileBound ρ ≤
        Real.exp (historyPolynomialCost C' z 4 L) ∧
      ((2*sourceDegreeFactor k (n+1)*(2*(m+2)+1)+1:ℕ):ℝ) ≤
        Real.exp (historyPolynomialCost C' z 4 L) ∧
      3+(∑_i:Fin (2^(n+1)) ⊕ Fin (2^(n+1)),
        ((-a*(m:ℝ)+Wl)-coarseLower D (rowLogHeight C z β L) (a*(m:ℝ)) Wl)) ≤
        Real.exp (historyPolynomialCost C' z 4 L) := by
  obtain ⟨C',hC',hb⟩ := exists_terminal_source_profile_budget k (n+1) ρ Wl hz ha hC
    (show (0:ℝ) ≤ (obstructionSizeFactor k (n+1)*(2*1+3):ℕ) by positivity)
    (show (0:ℝ) ≤ (2*(1+1):ℕ) by positivity) hβ
  refine ⟨C',hC',?_⟩
  intro L
  have hh := terminalProfile_linear_budgets k (n+1) (⌊z*L⌋₊+1) ⌊z*L⌋₊ 1 (by omega)
  simpa only [Nat.add_assoc,show 1+1=2 by rfl] using
    hb L (obstructionSizeFactor k (n+1)*(2*(⌊z*L⌋₊+1+1)+1))
      (2*(⌊z*L⌋₊+1+1))
      (by simpa only [Nat.cast_mul,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat] using hh.1)
      (by simpa only [Nat.cast_mul,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat] using hh.2)

end Ostmann.Characters.TemplateOneSidedCancellation

end

end OAI
