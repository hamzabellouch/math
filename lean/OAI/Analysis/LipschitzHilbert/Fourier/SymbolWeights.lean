import OAI.Analysis.LipschitzHilbert.Fourier.SeparatedSymbolFourier
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket

namespace OAI

/-! Integrable fixed polynomial weights for the separated symbol.
The same weight is allocated to the two waves and to the selector,
leaving an integrable outside coefficient. Only a fixed seminorm is used. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform
namespace LipschitzHilbert.PacketRepresentation

def symbolWeight (q : ℕ) (nu : SymbolSpace) : ℝ := ((1+‖nu‖)^q)⁻¹

theorem symbolWeight_pos (q : ℕ) (nu : SymbolSpace) : 0<symbolWeight q nu :=
  inv_pos.mpr (pow_pos (by positivity) q)

theorem symbolWeight_integrable (q : ℕ) (hq : 4≤q) : Integrable (symbolWeight q) := by
  have hi : Integrable (fun nu : SymbolSpace => (1+‖nu‖)^(-(q:ℝ))) :=
    integrable_one_add_norm (by simp only [SymbolSpace, finrank_euclideanSpace_fin]; exact_mod_cast (by omega : 3<q))
  apply hi.congr
  filter_upwards [] with nu
  rw [Real.rpow_neg (by positivity), Real.rpow_natCast]
  rfl

def symbolCoefficientBound (S : SchwartzMap SymbolSpace ℂ) (q : ℕ) : ℝ :=
  2^(4*q) * (Finset.Iic (4*q,0)).sup
    (fun m => SchwartzMap.seminorm ℝ m.1 m.2) (𝓕 S) + 1

theorem symbolCoefficientBound_pos (S : SchwartzMap SymbolSpace ℂ) (q : ℕ) :
    0<symbolCoefficientBound S q := by unfold symbolCoefficientBound; positivity

theorem symbol_coefficient_decay (S : SchwartzMap SymbolSpace ℂ) (q : ℕ) (nu : SymbolSpace) :
    ‖𝓕 S nu‖≤symbolCoefficientBound S q*(symbolWeight q nu)^4 := by
  have h := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ)
    (m := (4*q,0)) (k := 4*q) (n := 0) le_rfl le_rfl (𝓕 S) nu
  have h0 : ‖iteratedFDeriv ℝ 0 (𝓕 S : SchwartzMap SymbolSpace ℂ) nu‖=‖𝓕 S nu‖ := by simp
  rw [h0] at h
  have hr : 0<1+‖nu‖ := by positivity
  have hp : (symbolWeight q nu)^4=((1+‖nu‖)^(4*q))⁻¹ := by
    simp only [symbolWeight, inv_pow, ← pow_mul, Nat.mul_comm]
  rw [hp, ← div_eq_mul_inv]
  apply (le_div_iff₀ (pow_pos hr _)).2
  unfold symbolCoefficientBound
  linarith only [h]

def weightedSelector (S : SchwartzMap SymbolSpace ℂ) (q : ℕ) (nu : SymbolSpace) (U : ℝ) : ℂ :=
  (𝓕 S nu / ((symbolWeight q nu : ℝ):ℂ)^3)*selectorCharacter nu U

theorem weightedSelector_bound (S : SchwartzMap SymbolSpace ℂ) (q : ℕ)
    (nu : SymbolSpace) (U : ℝ) :
    ‖weightedSelector S q nu U‖≤symbolCoefficientBound S q*symbolWeight q nu := by
  have hw := symbolWeight_pos q nu
  have hwc : ‖(symbolWeight q nu : ℂ)‖=symbolWeight q nu := by
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hw]
  rw [weightedSelector, norm_mul, norm_selectorCharacter, mul_one, norm_div, norm_pow, hwc]
  apply (div_le_iff₀ (pow_pos hw 3)).2
  exact (symbol_coefficient_decay S q nu).trans_eq (by ring)

theorem symbolWeight_coordinate (q k : ℕ) (hk : k≤q) (nu : SymbolSpace) (i : Fin 3) :
    |nu i|^k*symbolWeight q nu≤1 := by
  have hr : 1≤1+‖nu‖ := by linarith only [norm_nonneg nu]
  have hi : |nu i|≤1+‖nu‖ := by
    rw [← Real.norm_eq_abs]
    exact (PiLp.norm_apply_le nu i).trans (by linarith only [norm_nonneg nu])
  have hp : |nu i|^k≤(1+‖nu‖)^q :=
    (pow_le_pow_left₀ (abs_nonneg _) hi k).trans (pow_le_pow_right₀ hr hk)
  unfold symbolWeight
  exact (mul_le_mul_of_nonneg_right hp (inv_nonneg.mpr (pow_nonneg (zero_le_one.trans hr) _))).trans_eq
    (mul_inv_cancel₀ (pow_pos (by positivity : (0:ℝ)<1+‖nu‖) q).ne')

theorem weighted_symbol_identity (S : SchwartzMap SymbolSpace ℂ) (q : ℕ) (X Y U : ℝ) :
    S (symbolPoint X Y U)=∫ nu : SymbolSpace,
      (symbolWeight q nu : ℂ)*
        ((symbolWeight q nu : ℂ)*frequencyCharacter nu X Y)*
        (symbolWeight q nu : ℂ)*weightedSelector S q nu U := by
  rw [separated_symbol_fourier S X Y U]
  apply integral_congr_ae
  filter_upwards [] with nu
  have hw : (symbolWeight q nu : ℂ)≠0 := by exact_mod_cast (symbolWeight_pos q nu).ne'
  unfold weightedSelector
  field_simp

end LipschitzHilbert.PacketRepresentation

end

end OAI
