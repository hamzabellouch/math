import OAI.NumberTheory.DirichletL.Detector.PrimePhase

namespace OAI

noncomputable section
namespace SevenEighths.ProbePrimePower
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT ConcretePrimeRowBridge CubicEisenstein
local notation "O" => ActualEisensteinCubic.O

def localGamma (p : O) (hp : p ≠ 0) [(Ideal.span {p} : Ideal O).IsMaximal]
    (hg : goodLambda ∉ Ideal.span {p}) (r : ℕ) : ℂ :=
  ConcreteBreveE.normalizedTraceGauss p hp (actualSextic (Ideal.span {p}) hg ^ r)

lemma localGamma_norm_one (p : O) (hp : p ≠ 0) [(Ideal.span {p} : Ideal O).IsMaximal]
    (hg : goodLambda ∉ Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p}) ≠ 2)
    (r : ℕ) (hr : r ≠ 0) (hr6 : r < 6) : ‖localGamma p hp hg r‖ = 1 :=
  MixedGaussConversion.norm_localGauss p hp hg hc r hr hr6

lemma actualSextic_six (P : Ideal O) [P.IsMaximal]
    (hg : goodLambda ∉ P) (hc : ringChar (O ⧸ P) ≠ 2) : actualSextic P hg ^ 6 = 1 :=
  (actualSextic_pow_eq_one_iff P hg hc 6).mpr (by decide)

lemma actualSextic_neg_one_sq (P : Ideal O) [P.IsMaximal]
    (hg : goodLambda ∉ P) : actualSextic P hg (-1)^2 = 1 := by
  rw [← map_pow]
  norm_num

theorem localGamma_inverse_pair (p : O) (hp : p ≠ 0)
    [(Ideal.span {p} : Ideal O).IsMaximal]
    (hg : goodLambda ∉ Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p}) ≠ 2)
    (r : ℕ) (hr : r ≠ 0) (hr6 : r < 6) :
    localGamma p hp hg r * localGamma p hp hg (6-r) =
      actualSextic (Ideal.span {p}) hg (-1)^r := by
  let : Field (O ⧸ Ideal.span {p}) := Ideal.Quotient.field _
  let : Fintype (O ⧸ Ideal.span {p}) := Fintype.ofFinite _
  let χ := actualSextic (Ideal.span {p}) hg
  have hχ : χ^r ≠ 1 := by
    intro he
    have hd := (actualSextic_pow_eq_one_iff _ hg hc r).mp he
    exact (Nat.not_dvd_of_pos_of_lt (Nat.pos_of_ne_zero hr) hr6) hd
  have hinv : (χ^r)⁻¹ = χ^(6-r) := by
    apply inv_eq_of_mul_eq_one_right
    rw [← pow_add, Nat.add_sub_of_le hr6.le]
    exact actualSextic_six _ hg hc
  have hψ : (quotientTrace p hp).IsPrimitive :=
    GeneralPrimitiveTrace.eisTraceModChar_breveE_primitive p hp
  have he := ProbeGauss.normalizedGauss_inverse_pair (χ^r) (quotientTrace p hp) hχ hψ
  rw [hinv] at he
  simp only [localGamma, ProbePhase.normalizedTraceGauss_eq_normalizedGauss]
  simpa only [MulChar.pow_apply' _ hr] using he

lemma localGamma_two_four (p : O) (hp : p ≠ 0)
    [(Ideal.span {p} : Ideal O).IsMaximal]
    (hg : goodLambda ∉ Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p}) ≠ 2) :
    localGamma p hp hg 2 * localGamma p hp hg 4 = 1 := by
  have he := localGamma_inverse_pair p hp hg hc 2 (by decide) (by decide)
  simpa only [show 6-2=4 from rfl, actualSextic_neg_one_sq] using he

theorem localGamma_one_two_signal (p : O) (hp : p ≠ 0)
    [(Ideal.span {p} : Ideal O).IsMaximal]
    (hg : goodLambda ∉ Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p}) ≠ 2)
    (hprimary : goodLambda^2 ∣ p-1) :
    localGamma p hp hg 1 * localGamma p hp hg 2 =
      -FiniteGaussPhase.angularFactor p * MixedGaussConversion.localG p hp hg := by
  have he := breveGamma1_gamma2_eq_neg_alpha_G (Ideal.span {p}) hg hc p rfl hp hprimary
  simpa only [localGamma, ConcreteBreveE.normalizedTraceGauss, pow_one,
    breveGamma1, breveGamma2, MixedGaussConversion.localG, FiniteGaussPhase.angularFactor,
    neg_div] using he

lemma actualSextic_pow_six_mul_add (P : Ideal O) [P.IsMaximal]
    (hg : goodLambda ∉ P) (hc : ringChar (O ⧸ P) ≠ 2) (r j : ℕ) :
    actualSextic P hg ^ (6*r+j) = actualSextic P hg ^ j := by
  rw [pow_add, pow_mul, actualSextic_six P hg hc, one_pow, one_mul]

lemma actualSextic_fifth_inverse (P : Ideal O) [P.IsMaximal]
    (hg : goodLambda ∉ P) (hc : ringChar (O ⧸ P) ≠ 2) :
    actualSextic P hg ^ 5 = (actualSextic P hg)⁻¹ := by
  symm
  apply inv_eq_of_mul_eq_one_right
  rw [← pow_succ']
  exact actualSextic_six P hg hc

lemma primeGauss_inverse_pair (p : O) (hp : p ≠ 0)
    [(Ideal.span {p} : Ideal O).IsMaximal]
    (χ : MulChar (O ⧸ Ideal.span {p}) ℂ) (hχ : χ ≠ 1) :
    primeGauss p hp χ 1 * primeGauss p hp χ⁻¹ 1 =
      χ (-1) * (Ideal.absNorm (Ideal.span {p}):ℂ) := by
  let : Field (O ⧸ Ideal.span {p}) := Ideal.Quotient.field _
  let : Fintype (O ⧸ Ideal.span {p}) := Fintype.ofFinite _
  have ht := ProbeGauss.gauss_inverse_pair χ (quotientTrace p hp) hχ
    (GeneralPrimitiveTrace.eisTraceModChar_breveE_primitive p hp)
  have hcard : Nat.card (O ⧸ Ideal.span {p}) = Ideal.absNorm (Ideal.span {p}) := rfl
  simpa only [primeGauss, tsum_fintype, map_one, one_mul, gaussSum,
    ← Nat.card_eq_fintype_card, hcard] using ht

end SevenEighths.ProbePrimePower
end

end OAI
