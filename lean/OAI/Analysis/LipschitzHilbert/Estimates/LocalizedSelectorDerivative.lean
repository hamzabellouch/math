import OAI.Analysis.LipschitzHilbert.Fourier.AnnularSelector
import Mathlib.Analysis.Fourier.FourierTransformDeriv

namespace OAI

/-! The separated selector has a derivative bound uniform in the Fourier
parameter. The fixed polynomial weight absorbs its linear growth. -/
noncomputable section
open scoped FourierTransform
namespace LipschitzHilbert.PacketRepresentation

theorem selectorCharacter_hasDerivAt (nu : SymbolSpace) (U : ℝ) :
    HasDerivAt (selectorCharacter nu)
      (((2*Real.pi*nu 2 : ℝ):ℂ)*Complex.I*selectorCharacter nu U) U := by
  have h := (Real.hasDerivAt_fourierChar (nu 2*U)).scomp U
    ((hasDerivAt_id U).const_mul (nu 2))
  convert h using 1
  · rfl
  · simp only [Complex.real_smul, selectorCharacter, mul_one]
    push_cast
    ring

theorem weightedSelector_hasDerivAt (S : SchwartzMap SymbolSpace ℂ)
    (q : ℕ) (nu : SymbolSpace) (U : ℝ) :
    HasDerivAt (weightedSelector S q nu)
      (((2*Real.pi*nu 2 : ℝ):ℂ)*Complex.I*weightedSelector S q nu U) U := by
  convert (selectorCharacter_hasDerivAt nu U).const_mul
    (𝓕 S nu/((symbolWeight q nu:ℝ):ℂ)^3) using 1
  · rfl
  · unfold weightedSelector
    ring

theorem symbolWeight_le_one (q : ℕ) (nu : SymbolSpace) : symbolWeight q nu≤1 := by
  simpa only [pow_zero, one_mul] using symbolWeight_coordinate q 0 (Nat.zero_le q) nu 0

theorem weightedSelector_norm_le (S : SchwartzMap SymbolSpace ℂ)
    (q : ℕ) (nu : SymbolSpace) (U : ℝ) :
    ‖weightedSelector S q nu U‖≤symbolCoefficientBound S q :=
  (weightedSelector_bound S q nu U).trans
    ((mul_le_mul_of_nonneg_left (symbolWeight_le_one q nu)
      (symbolCoefficientBound_pos S q).le).trans_eq (mul_one _))

theorem weightedSelector_deriv_bound (S : SchwartzMap SymbolSpace ℂ)
    (q : ℕ) (hq : 1≤q) (nu : SymbolSpace) (U : ℝ) :
    ‖deriv (weightedSelector S q nu) U‖≤2*Real.pi*symbolCoefficientBound S q := by
  have hC : 0≤symbolCoefficientBound S q := (symbolCoefficientBound_pos S q).le
  rw [(weightedSelector_hasDerivAt S q nu U).deriv, norm_mul, norm_mul,
    Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_mul,
    abs_of_pos Real.pi_pos, abs_of_pos (by norm_num : (0:ℝ)<2)]
  calc
    _ ≤ (2*Real.pi*|nu 2|)*(symbolCoefficientBound S q*symbolWeight q nu) :=
      mul_le_mul_of_nonneg_left (weightedSelector_bound S q nu U) (by positivity)
    _ = (2*Real.pi*symbolCoefficientBound S q)*(|nu 2| * symbolWeight q nu) := by ring
    _ ≤ (2*Real.pi*symbolCoefficientBound S q)*1 :=
      mul_le_mul_of_nonneg_left
        (by simpa only [pow_one] using symbolWeight_coordinate q 1 hq nu 2) (by positivity)
    _ = _ := mul_one _

theorem localizedSelector_deriv_bound (chi : SchwartzMap ℝ ℝ) (hchi : ∀ U, |chi U|≤1)
    (S : SchwartzMap SymbolSpace ℂ) (q : ℕ) (hq : 1≤q) (nu : SymbolSpace) (U : ℝ) :
    ‖deriv (localizedSelector chi S q nu) U‖≤
      (SchwartzMap.seminorm ℝ 0 1 chi+2*Real.pi)*symbolCoefficientBound S q := by
  have hd := (chi.hasDerivAt U).ofReal_comp.mul (weightedSelector_hasDerivAt S q nu U)
  change HasDerivAt (localizedSelector chi S q nu) _ U at hd
  rw [hd.deriv]
  have hchi' : ‖deriv chi U‖≤SchwartzMap.seminorm ℝ 0 1 chi := by
    simpa only [iteratedDeriv_one, pow_zero, one_mul] using
      SchwartzMap.le_seminorm' ℝ 0 1 chi U
  calc
    _ ≤ ‖((deriv chi U:ℝ):ℂ)*weightedSelector S q nu U‖+
        ‖(chi U:ℂ)*(((2*Real.pi*nu 2:ℝ):ℂ)*Complex.I*weightedSelector S q nu U)‖ :=
      norm_add_le _ _
    _ = ‖deriv chi U‖*‖weightedSelector S q nu U‖+
        |chi U| * ‖deriv (weightedSelector S q nu) U‖ := by
      rw [← (weightedSelector_hasDerivAt S q nu U).deriv]
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    _ ≤ SchwartzMap.seminorm ℝ 0 1 chi*symbolCoefficientBound S q+
        1*(2*Real.pi*symbolCoefficientBound S q) := by
      gcongr
      · exact weightedSelector_norm_le S q nu U
      · exact hchi U
      · exact weightedSelector_deriv_bound S q hq nu U
    _ = _ := by ring

end LipschitzHilbert.PacketRepresentation

end

end OAI
