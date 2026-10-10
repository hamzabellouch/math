import OAI.NumberTheory.SiegelZeros.Differentials.GammaFactorDerivative
import OAI.NumberTheory.SiegelZeros.Structure.CanonicalGoodMass

namespace OAI

namespace SiegelZeros

noncomputable section
open scoped Classical
namespace WeightedTorusJets.W63

def NormalizedZeroSumAt {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (s : ℝ) : Prop :=
  Summable (fun i : SiegelZerosAwei.W51.ZeroIndex χ =>
    (((s : ℂ) - SiegelZerosAwei.W51.zeroValue χ i)⁻¹).re) ∧
  (logDeriv (SiegelZerosAwei.W51.normalizedCompletion χ) (s : ℂ)).re =
    ∑' i : SiegelZerosAwei.W51.ZeroIndex χ,
      (((s : ℂ) - SiegelZerosAwei.W51.zeroValue χ i)⁻¹).re

theorem parity_complex_cast {q : ℕ} (χ : DirichletCharacter ℂ q) :
    ((parity χ : ℝ) : ℂ) = if χ.Even then (0 : ℂ) else 1 := by
  unfold parity
  split_ifs <;> norm_num

theorem normalized_logDerivative_real {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hnp : χ ≠ 1) {s : ℝ} (hs : 1 < s) :
    (logDeriv (SiegelZerosAwei.W51.normalizedCompletion χ) (s : ℂ)).re =
      (1 / 2 : ℝ) * Real.log ((q : ℝ) / Real.pi) +
      (1 / 2 : ℝ) *
        (SiegelZerosAwei.W52.gammaLogDerivative
          (((s + (parity χ : ℝ)) / 2 : ℝ) : ℂ)).re +
      (logDeriv χ.LFunction (s : ℂ)).re := by
  have h := congrArg Complex.re
    (SiegelZerosAwei.W52.logDeriv_normalizedCompletion_eq χ hnp
      (s := (s : ℂ)) (by simpa using hs))
  have harg : (((s + (parity χ : ℝ)) / 2 : ℝ) : ℂ) =
      ((s : ℂ) + if χ.Even then (0 : ℂ) else 1) / 2 := by
    rw [Complex.ofReal_div, Complex.ofReal_add, parity_complex_cast]
    norm_num
  rw [harg]
  have hq : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne q)
  rw [Real.log_div hq Real.pi_ne_zero]
  simp only [Complex.add_re, Complex.sub_re, Complex.div_ofNat_re,
    Complex.log_ofReal_re, ← Complex.ofReal_natCast] at h
  linarith

theorem NormalizedZeroSumAt.to_HadamardFormulaAt {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hnp : χ ≠ 1) {s : ℝ} (hs : 1 < s)
    (hzeroSum : NormalizedZeroSumAt χ s) : HadamardFormulaAt χ s := by
  refine ⟨hzeroSum.1, ?_⟩
  have hnormal := normalized_logDerivative_real χ hnp hs
  have hneg : (-deriv χ.LFunction (s : ℂ) / χ.LFunction (s : ℂ)).re =
      -(logDeriv χ.LFunction (s : ℂ)).re := by
    rw [logDeriv_apply, neg_div, Complex.neg_re]
  rw [hneg]
  linarith [hzeroSum.2]

theorem normalizedZeroSum_of_regularized_identity {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hnp : χ ≠ 1) (hprimitive : χ.IsPrimitive)
    (s : ℝ) (B : ℂ)
    (hsquare : Summable (fun i : SiegelZerosAwei.W51.ZeroIndex χ =>
      1 / ‖SiegelZerosAwei.W51.zeroValue χ i‖ ^ 2))
    (hregularized : Summable (fun i : SiegelZerosAwei.W51.ZeroIndex χ =>
      ((s : ℂ) - SiegelZerosAwei.W51.zeroValue χ i)⁻¹ +
        (SiegelZerosAwei.W51.zeroValue χ i)⁻¹))
    (hidentity : logDeriv (SiegelZerosAwei.W51.normalizedCompletion χ) (s : ℂ) =
      B + ∑' i : SiegelZerosAwei.W51.ZeroIndex χ,
        (((s : ℂ) - SiegelZerosAwei.W51.zeroValue χ i)⁻¹ +
          (SiegelZerosAwei.W51.zeroValue χ i)⁻¹))
    (hcancellation : B.re + ∑' i : SiegelZerosAwei.W51.ZeroIndex χ,
      ((SiegelZerosAwei.W51.zeroValue χ i)⁻¹).re = 0) :
    NormalizedZeroSumAt χ s := by
  have hstrip : ∀ i : SiegelZerosAwei.W51.ZeroIndex χ,
      0 ≤ (SiegelZerosAwei.W51.zeroValue χ i).re ∧
        (SiegelZerosAwei.W51.zeroValue χ i).re ≤ 1 := by
    intro i
    have h := SiegelZerosAwei.W51.zeroValue_mem_strip χ hnp hprimitive i
    exact ⟨h.1.le, h.2.le⟩
  have hinv := SiegelZerosAwei.W03.summable_reciprocal_re
    (SiegelZerosAwei.W51.zeroValue χ) hstrip hsquare
  have hsum := SiegelZerosAwei.W03.summable_real_zero_contributions
    (SiegelZerosAwei.W51.zeroValue χ) (s : ℂ) hregularized hinv
  refine ⟨hsum, ?_⟩
  have hsplit := SiegelZerosAwei.W03.real_regularized_tsum
    (SiegelZerosAwei.W51.zeroValue χ) (s : ℂ) hregularized hinv
  have h := congrArg Complex.re hidentity
  rw [Complex.add_re, Complex.re_tsum hregularized] at h
  linarith

theorem exists_good_mass_of_normalizedZeroSum :
    ∃ C : ℝ, 0 < C ∧ ∀ H : ℕ, 2 ≤ H → ∃ CH : ℝ,
      ∀ (q : ℕ) [NeZero q], 3 ≤ q →
      ∀ χ : DirichletCharacter ℂ q, χ.IsPrimitive → χ ≠ 1 →
      (∀ a : ZMod q, (χ a).im = 0) → ∀ β X : ℝ,
      0 < β → β < 1 → χ.LFunction (β : ℂ) = 0 → 3 ≤ X →
      NormalizedZeroSumAt χ (1 + 1 / Real.log X) →
      Real.log X - C * Real.log q -
        C * (((1 - β) * Real.log q) * Real.log X ^ 2 / Real.log q) - CH ≤
      SiegelZeros.W07.primeMass
        (SiegelZeros.W07.goodPrimes χ (SiegelZeros.W08.primesUpTo X) H) := by
  obtain ⟨C, hC, hmass⟩ := exists_good_mass_for_actual_zeros_of_HadamardFormula
  refine ⟨C, hC, ?_⟩
  intro H hH
  obtain ⟨CH, hCH⟩ := hmass H hH
  refine ⟨CH, ?_⟩
  intro q _ hq χ hprimitive hnp hreal β X hβ0 hβ1 hzero hX hzeroSum
  exact hCH q hq χ hprimitive hnp hreal β X hβ0 hβ1 hzero hX
    (hzeroSum.to_HadamardFormulaAt hnp (W04.logarithmic_parameter_range X hX).1)

end WeightedTorusJets.W63

end

end SiegelZeros

end OAI
