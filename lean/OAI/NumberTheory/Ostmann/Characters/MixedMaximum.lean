import OAI.NumberTheory.Ostmann.Characters.MixedBounds

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate
namespace Ostmann.Characters
variable {p : ℕ} [Fact p.Prime]

def nonprincipalBias (S : Finset (ZMod p)) : NNReal :=
  Finset.univ.sup (fun z : MulChar (ZMod p) ℂ × ZMod p =>
    if z.1 = 1 then 0 else ‖translatedMean S z.1 z.2‖₊)

theorem translatedBias_le_nonprincipalBias (S : Finset (ZMod p))
    (χ : MulChar (ZMod p) ℂ) (hχ : χ ≠ 1) (a : ZMod p) :
    translatedBias S χ a ≤ (nonprincipalBias S : ℝ) := by
  have h := Finset.le_sup (s := Finset.univ)
    (f := fun z : MulChar (ZMod p) ℂ × ZMod p =>
      if z.1 = 1 then (0:NNReal) else ‖translatedMean S z.1 z.2‖₊)
    (Finset.mem_univ (χ,a))
  have hh : ‖translatedMean S χ a‖₊ ≤ nonprincipalBias S := by
    simpa only [nonprincipalBias, hχ, ite_false] using h
  exact_mod_cast hh

theorem norm_mixed_principal_le (S : Finset (ZMod p))
    (hlo : 1/4 ≤ Supply.density S) (hhi : Supply.density S ≤ 3/4)
    (a : ZMod p) :
    ‖FiniteField.mixedCorrelation (Supply.additiveTransform S) 1 a‖ ≤
      4 / Real.sqrt p := by
  rw [mixed_additiveTransform_principal, norm_div, Complex.norm_real,
    Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _)]
  apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
  unfold Supply.normalizedIndicator Supply.centeredIndicator
  rw [abs_div, abs_of_nonneg (Real.sqrt_nonneg _)]
  have hl := balanced_sqrt_lower hlo hhi
  apply (div_le_iff₀ (by linarith : 0 < Real.sqrt
    (Supply.density S * (1-Supply.density S)))).mpr
  split_ifs <;> rw [abs_le] <;> constructor <;> linarith

theorem correlationBound_le (S : Finset (ZMod p))
    (hlo : 1/4 ≤ Supply.density S) (hhi : Supply.density S ≤ 3/4) :
    (FiniteField.correlationBound (Supply.additiveTransform S) : ℝ) ≤
      4 * (nonprincipalBias S : ℝ) + 4 / Real.sqrt p := by
  have hr : 0 ≤ 4 * (nonprincipalBias S : ℝ) + 4 / Real.sqrt p := by positivity
  change ((Finset.univ.sup (fun z : MulChar (ZMod p) ℂ × ZMod p =>
    ‖FiniteField.mixedCorrelation (Supply.additiveTransform S) z.1 z.2‖₊) : NNReal) : ℝ) ≤ _
  change Finset.univ.sup (fun z : MulChar (ZMod p) ℂ × ZMod p =>
    ‖FiniteField.mixedCorrelation (Supply.additiveTransform S) z.1 z.2‖₊) ≤ ⟨_,hr⟩
  apply Finset.sup_le
  intro z hz
  change ‖FiniteField.mixedCorrelation (Supply.additiveTransform S) z.1 z.2‖ ≤ _
  by_cases hχ : z.1 = 1
  · rw [hχ]
    exact (norm_mixed_principal_le S hlo hhi z.2).trans (le_add_of_nonneg_left (by positivity))
  · calc
      _ ≤ 4 * translatedBias S z.1⁻¹ z.2 :=
        norm_mixed_additiveTransform_le S hlo hhi z.1 hχ z.2
      _ ≤ 4 * (nonprincipalBias S : ℝ) := mul_le_mul_of_nonneg_left
        (translatedBias_le_nonprincipalBias S z.1⁻¹ (inv_ne_one.mpr hχ) z.2) (by norm_num)
      _ ≤ _ := le_add_of_nonneg_right (by positivity)
end Ostmann.Characters

end

end OAI
