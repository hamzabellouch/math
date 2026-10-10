import OAI.NumberTheory.DirichletL.Hecke.RowNonprincipal
import OAI.NumberTheory.DirichletL.CenteredExceptionalCount

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.CenteredExceptionalProfile
open UniqueFactorizationMonoid HeckeFamily CanonicalRowCompletion
open ConcretePrimeRowBridge hiding O
open CompletedGauss hiding O
open ConcreteTraceCRT
local notation "O" => HeckeFamily.O
open CenteredExceptionalCount CenteredMomentCanonical
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

theorem split_at_prime (I P : Ideal O) (hI : I ≠ 0) [P.IsMaximal] :
    ∃ J : Ideal O, I = P ^ valuation I P * J ∧ J ≠ 0 ∧ IsCoprime J P := by
  let S := (normalizedFactors I).toFinset
  let J := ∏ Q ∈ S.erase P, Q ^ valuation I Q
  have hsplit : I = P ^ valuation I P * J := by
    calc
      I = (normalizedFactors I).prod := (Ideal.prod_normalizedFactors_eq_self hI).symm
      _ = ∏ Q ∈ S, Q ^ valuation I Q := Finset.prod_multiset_count _
      _ = P ^ valuation I P * J := by
        by_cases hP : P ∈ S
        · exact (Finset.mul_prod_erase S (fun Q => Q ^ valuation I Q) hP).symm
        · have hz : valuation I P = 0 := Multiset.count_eq_zero.mpr
            (fun h => hP (Multiset.mem_toFinset.mpr h))
          simp only [J, Finset.erase_eq_of_notMem hP, hz, pow_zero, one_mul]
  refine ⟨J, hsplit, ?_, ?_⟩
  · intro hz
    apply hI
    rw [hsplit, hz, mul_zero]
  · apply IsCoprime.prod_left
    intro Q hQ
    obtain ⟨hQP, hQS⟩ := Finset.mem_erase.mp hQ
    have hp := prime_of_normalized_factor Q (Multiset.mem_toFinset.mp hQS)
    let : Q.IsMaximal := (Ideal.isPrime_of_prime hp).isMaximal hp.ne_zero
    exact (Ideal.isCoprime_of_isMaximal hQP).pow_left

theorem exists_unit_probe (Q K P : Ideal O) (hK : K ≠ 0) [P.IsMaximal]
    (hQP : IsCoprime Q P) (u : (O ⧸ P)ˣ) :
    ∃ n : O, n - 1 ∈ Q ∧ IsCoprime (Ideal.span {n}) K ∧
      Ideal.Quotient.mk P n = (u : O ⧸ P) := by
  obtain ⟨J, hsplit, hJ, hJP⟩ := split_at_prime K P hK
  let e := Ideal.quotientInfEquivQuotientProd (Q * J) P (hQP.mul_left hJP)
  obtain ⟨x, hx⟩ := e.surjective ((1 : O ⧸ Q * J), (u : O ⧸ P))
  obtain ⟨n, rfl⟩ := Ideal.Quotient.mk_surjective x
  change (Ideal.Quotient.mk (Q * J) n, Ideal.Quotient.mk P n) = (1, (u : O ⧸ P)) at hx
  have hnQJ := congrArg Prod.fst hx
  have hnP := congrArg Prod.snd hx
  dsimp only at hnQJ hnP
  have hn : n - 1 ∈ Q * J := Ideal.Quotient.eq.mp (by simpa using hnQJ)
  have hnJ : Ideal.Quotient.mk J n = 1 :=
    (Ideal.Quotient.mk_eq_one_iff_sub_mem _).mpr (Ideal.mul_le_right hn)
  have hcJ : IsCoprime (Ideal.span {n}) J :=
    (IdealCharacter.isUnit_mk_iff_isCoprime _ _).mp (hnJ ▸ isUnit_one)
  have hcP : IsCoprime (Ideal.span {n}) P :=
    (IdealCharacter.isUnit_mk_iff_isCoprime _ _).mp (hnP ▸ u.isUnit)
  refine ⟨n, Ideal.mul_le_left hn, ?_, hnP⟩
  rw [hsplit]
  exact hcP.pow_right.mul_right hcJ

theorem valuation_mod_six_of_unit_agreement (Q K I J P : Ideal O)
    (hK : K ≠ 0) (hI : CanonicalQuadraticSieve.Supported I)
    (hJ : CanonicalQuadraticSieve.Supported J) [P.IsMaximal]
    (hg : λ₀ ∉ P) (hchar : ringChar (O ⧸ P) ≠ 2)
    (hQP : IsCoprime Q P)
    (heq : ∀ n : O, n - 1 ∈ Q → IsCoprime (Ideal.span {n}) K →
      idealRowHom n I = idealRowHom n J) :
    valuation I P % 6 = valuation J P % 6 := by
  obtain ⟨I₀, hsplitI, hI₀, hcI⟩ := split_at_prime I P hI.1
  obtain ⟨J₀, hsplitJ, hJ₀, hcJ⟩ := split_at_prime J P hJ.1
  have hsI : CanonicalQuadraticSieve.Supported I₀ :=
    ((CanonicalQuadraticSieve.supported_mul_iff _ _).mp (hsplitI ▸ hI)).2
  have hsJ : CanonicalQuadraticSieve.Supported J₀ :=
    ((CanonicalQuadraticSieve.supported_mul_iff _ _).mp (hsplitJ ▸ hJ)).2
  have hpows : actualSextic P hg ^ valuation I P = actualSextic P hg ^ valuation J P := by
    apply MulChar.ext
    intro u
    obtain ⟨n, hn, hcK, hnP⟩ := exists_unit_probe (Q * I₀ * J₀) K P hK
      ((hQP.mul_left hcI).mul_left hcJ) u
    have hval := heq n (Ideal.mul_le_left (Ideal.mul_le_left hn)) hcK
    have hIn : n - 1 ∈ I₀ := Ideal.mul_le_right (Ideal.mul_le_left hn)
    have hJn : n - 1 ∈ J₀ := Ideal.mul_le_right hn
    rw [hsplitI, hsplitJ, map_mul, map_mul, map_pow, map_pow,
      idealRowHom_congr_mod I₀ n 1 hIn, idealRowHom_congr_mod J₀ n 1 hJn,
      idealRowHom_one_supported I₀ hsI, idealRowHom_one_supported J₀ hsJ,
      mul_one, mul_one, idealRowHom_prime n P hg, hnP] at hval
    simpa only [MulChar.pow_apply_coe] using hval
  have hm := (pow_eq_pow_iff_modEq.mp hpows)
  rw [actualSextic_order_six P hg hchar] at hm
  exact hm

def InducedBy (χ ψ : Character) : Prop :=
  ∀ I : Ideal O, idealCoeff χ I =
    if IsCoprime I χ.modulus then idealCoeff ψ I else 0

theorem exists_primitive_inducedBy (χ : Character) :
    ∃ ψ : Character, FiniteFourier.IsPrimitiveOnIdeals ψ.residue ∧
      χ.modulus ≤ ψ.modulus ∧ InducedBy χ ψ := by
  obtain ⟨ψ, hmod, hprim, _, hmask⟩ := exists_primitive_character χ
  exact ⟨ψ, hprim, hmod, hmask⟩

theorem elementCoeff_eq_of_inducedBy (χ ψ : Character) (h : InducedBy χ ψ)
    (n : O) (hn : n ≠ 0) (hc : IsCoprime (Ideal.span {n}) χ.modulus) :
    elementCoeff χ n = elementCoeff ψ n := by
  have he := h (Ideal.span {n})
  simp only [hc, ite_true, idealCoeff_span χ hn, idealCoeff_span ψ hn] at he
  exact he

theorem elementCoeff_eq_one_of_inducedBy (χ ψ : Character) (h : InducedBy χ ψ)
    (Q : Ideal O) (hQ : Q ≠ ⊤) (hψ : Q ≤ ψ.modulus)
    (n : O) (hn : n - 1 ∈ Q) (hc : IsCoprime (Ideal.span {n}) χ.modulus) :
    elementCoeff χ n = 1 := by
  have hn0 : n ≠ 0 := by
    intro hz
    have h1 : (1 : O) ∈ Q := by simpa [hz] using Q.neg_mem hn
    exact hQ ((Ideal.eq_top_iff_one Q).mpr h1)
  rw [elementCoeff_eq_of_inducedBy χ ψ h n hn0 hc]
  change ψ.residue (Ideal.Quotient.mk ψ.modulus n) = 1
  rw [(Ideal.Quotient.mk_eq_one_iff_sub_mem _).mpr (hψ hn), map_one]

theorem local_rows_profile (η χ₁ χ₂ ψ₁ ψ₂ : Character)
    (h₁ : InducedBy χ₁ ψ₁) (h₂ : InducedBy χ₂ ψ₂)
    (Q K I J P : Ideal O) (hQ : Q ≠ ⊤) (hK : K ≠ 0)
    (hψ₁ : Q ≤ ψ₁.modulus) (hψ₂ : Q ≤ ψ₂.modulus)
    (hI : CanonicalQuadraticSieve.Supported I)
    (hJ : CanonicalQuadraticSieve.Supported J) [P.IsMaximal]
    (hg : λ₀ ∉ P) (hchar : ringChar (O ⧸ P) ≠ 2)
    (hQP : IsCoprime Q P)
    (hrow₁ : ∀ n : O, n - 1 ∈ Q → IsCoprime (Ideal.span {n}) K →
      elementCoeff χ₁ n = elementCoeff η n * idealRowHom n I)
    (hrow₂ : ∀ n : O, n - 1 ∈ Q → IsCoprime (Ideal.span {n}) K →
      elementCoeff χ₂ n = elementCoeff η n * idealRowHom n J) :
    valuation I P % 6 = valuation J P % 6 := by
  let L := ((K * η.modulus) * χ₁.modulus) * χ₂.modulus
  have hL : L ≠ 0 := mul_ne_zero
    (mul_ne_zero (mul_ne_zero hK η.modulus_ne_bot) χ₁.modulus_ne_bot) χ₂.modulus_ne_bot
  apply valuation_mod_six_of_unit_agreement Q L I J P hL hI hJ hg hchar hQP
  intro n hn hc
  obtain ⟨⟨⟨hcK, hcη⟩, hc₁⟩, hc₂⟩ :=
    (show ((IsCoprime (Ideal.span {n}) K ∧ IsCoprime (Ideal.span {n}) η.modulus) ∧
      IsCoprime (Ideal.span {n}) χ₁.modulus) ∧ IsCoprime (Ideal.span {n}) χ₂.modulus from by
        simpa only [L, IsCoprime.mul_right_iff] using hc)
  have he₁ := elementCoeff_eq_one_of_inducedBy χ₁ ψ₁ h₁ Q hQ hψ₁ n hn hc₁
  have he₂ := elementCoeff_eq_one_of_inducedBy χ₂ ψ₂ h₂ Q hQ hψ₂ n hn hc₂
  rw [hrow₁ n hn hcK] at he₁
  rw [hrow₂ n hn hcK] at he₂
  have hη : elementCoeff η n ≠ 0 := MulChar.apply_ne_zero_iff.mpr
    ((IdealCharacter.isUnit_mk_iff_isCoprime _ _).mpr hcη)
  exact mul_left_cancel₀ hη (he₁.trans he₂.symm)

theorem actual_row_on_fixed_units (η χ : Character) (m f z : O)
    (hmLam : λ₀ ∣ m) (hm2 : (2 : O) ∣ m)
    (u : Oˣ) (a b : ℕ) (r : O)
    (hr : CanonicalQuadraticSieve.Supported (Ideal.span {r}))
    (hpr : λ₀ ^ 2 ∣ r - 1)
    (hx : f ^ 4 * z = (u : O) * λ₀ ^ a * (2 : O) ^ b * r)
    (hχ : ∀ n, elementCoeff χ n = rowTwist (HeckeRowClosure.elementHom η) m f z n)
    (n : O) (hn : n - 1 ∈ Ideal.span {(72 : O)})
    (hc : IsCoprime (Ideal.span {n}) (Ideal.span {m})) :
    elementCoeff χ n = elementCoeff η n * idealRowHom n (Ideal.span {r}) := by
  have hd72 : λ₀ ^ 2 ∣ (72 : O) := ActualEisensteinCubic.lambda_sq_dvd_three.trans
    (show (3 : O) ∣ 72 from ⟨24, by norm_num⟩)
  have hp : λ₀ ^ 2 ∣ n - 1 := hd72.trans (Ideal.mem_span_singleton.mp hn)
  rw [hχ n, rowTwist_eq_actualPeriodicRow_primary _ _ _ _ hmLam hm2 u a b r hr hpr hx n hp]
  change ((elementCoeff η n * coprimalityMask m n) * numeratorBadTwist u a b r hr n) *
    idealRowHom n (Ideal.span {r}) = _
  have hm : coprimalityMask m n = 1 := by
    change (if IsCoprime m n then (1 : ℂ) else 0) = 1
    simp only [((Ideal.isCoprime_span_singleton_iff _ _).mp hc).symm, ite_true]
  rw [hm, numeratorBadTwist_periodic u a b r hr n 1 hn, map_one, mul_one, mul_one]

theorem actual_rows_good_profile (η χ₁ χ₂ ψ₁ ψ₂ : Character)
    (h₁ : InducedBy χ₁ ψ₁) (h₂ : InducedBy χ₂ ψ₂)
    (Q : Ideal O) (hQ : Q ≠ ⊤) (hQ72 : Q ≤ Ideal.span {(72 : O)})
    (hψ₁ : Q ≤ ψ₁.modulus) (hψ₂ : Q ≤ ψ₂.modulus)
    (m f z₁ z₂ : O) (hm : m ≠ 0) (hmLam : λ₀ ∣ m) (hm2 : (2 : O) ∣ m)
    (u₁ u₂ : Oˣ) (a₁ b₁ a₂ b₂ : ℕ) (r₁ r₂ : O)
    (hr₁ : CanonicalQuadraticSieve.Supported (Ideal.span {r₁}))
    (hr₂ : CanonicalQuadraticSieve.Supported (Ideal.span {r₂}))
    (hpr₁ : λ₀ ^ 2 ∣ r₁ - 1) (hpr₂ : λ₀ ^ 2 ∣ r₂ - 1)
    (hx₁ : f ^ 4 * z₁ = (u₁ : O) * λ₀ ^ a₁ * (2 : O) ^ b₁ * r₁)
    (hx₂ : f ^ 4 * z₂ = (u₂ : O) * λ₀ ^ a₂ * (2 : O) ^ b₂ * r₂)
    (hχ₁ : ∀ n, elementCoeff χ₁ n = rowTwist (HeckeRowClosure.elementHom η) m f z₁ n)
    (hχ₂ : ∀ n, elementCoeff χ₂ n = rowTwist (HeckeRowClosure.elementHom η) m f z₂ n)
    (P : Ideal O) [P.IsMaximal] (hg : λ₀ ∉ P)
    (hchar : ringChar (O ⧸ P) ≠ 2) (hQP : IsCoprime Q P) :
    valuation (Ideal.span {r₁}) P % 6 = valuation (Ideal.span {r₂}) P % 6 := by
  apply local_rows_profile η χ₁ χ₂ ψ₁ ψ₂ h₁ h₂ Q (Ideal.span {m})
    (Ideal.span {r₁}) (Ideal.span {r₂}) P hQ (Ideal.span_singleton_eq_bot.not.mpr hm)
    hψ₁ hψ₂ hr₁ hr₂ hg hchar hQP
  · intro n hn hc
    exact actual_row_on_fixed_units η χ₁ m f z₁ hmLam hm2 u₁ a₁ b₁ r₁ hr₁ hpr₁ hx₁ hχ₁ n (hQ72 hn) hc
  · intro n hn hc
    exact actual_row_on_fixed_units η χ₂ m f z₂ hmLam hm2 u₂ a₂ b₂ r₂ hr₂ hpr₂ hx₂ hχ₂ n (hQ72 hn) hc

theorem valuation_span_eq_zero_of_not_mem (x : O) (P : Ideal O) (hx : x ∉ P) :
    valuation (Ideal.span {x}) P = 0 := by
  have hx0 : x ≠ 0 := fun hz => hx (hz ▸ P.zero_mem)
  apply Multiset.count_eq_zero.mpr
  intro hP
  have hle := ((Ideal.mem_normalizedFactors_iff (Ideal.span_singleton_eq_bot.not.mpr hx0)).mp hP).2
  exact hx (hle (Ideal.subset_span (by simp)))

theorem valuation_supported_numerator (x : O) (u : Oˣ) (a b : ℕ) (r : O)
    (hr : r ≠ 0) (hx : x = (u : O) * λ₀ ^ a * (2 : O) ^ b * r)
    (P : Ideal O) (hg : λ₀ ∉ P) (h2 : (2 : O) ∉ P) :
    valuation (Ideal.span {x}) P = valuation (Ideal.span {r}) P := by
  have hu : Ideal.span {(u : O)} = (1 : Ideal O) := by
    simpa only [Ideal.one_eq_top] using (Ideal.span_singleton_eq_top.mpr u.isUnit)
  have hl0 : Ideal.span {λ₀} ≠ (0 : Ideal O) :=
    Ideal.span_singleton_eq_bot.not.mpr PrimaryIdealUnitReindex.lambda_prime_actual.ne_zero
  have h20 : Ideal.span {(2 : O)} ≠ (0 : Ideal O) :=
    Ideal.span_singleton_eq_bot.not.mpr (by norm_num)
  have hr0 : Ideal.span {r} ≠ (0 : Ideal O) := Ideal.span_singleton_eq_bot.not.mpr hr
  rw [hx]
  simp only [← Ideal.span_singleton_mul_span_singleton, ← Ideal.span_singleton_pow, hu, one_mul]
  rw [valuation_mul _ _ _ (mul_ne_zero (pow_ne_zero _ hl0) (pow_ne_zero _ h20)) hr0,
    valuation_mul _ _ _ (pow_ne_zero _ hl0) (pow_ne_zero _ h20), valuation_pow, valuation_pow,
    valuation_span_eq_zero_of_not_mem λ₀ P hg, valuation_span_eq_zero_of_not_mem (2 : O) P h2]
  omega

theorem valuation_mod_six_cancel_frozen (A I J P : Ideal O)
    (hA : A ≠ 0) (hI : I ≠ 0) (hJ : J ≠ 0)
    (h : valuation (A * I) P % 6 = valuation (A * J) P % 6) :
    valuation I P % 6 = valuation J P % 6 := by
  rw [valuation_mul A I P hA hI, valuation_mul A J P hA hJ] at h
  exact Nat.ModEq.add_left_cancel' (valuation A P) h

theorem actual_rows_profile (η χ₁ χ₂ ψ₁ ψ₂ : Character)
    (h₁ : InducedBy χ₁ ψ₁) (h₂ : InducedBy χ₂ ψ₂)
    (Q : Ideal O) (hQ : Q ≠ ⊤) (hQ72 : Q ≤ Ideal.span {(72 : O)})
    (hψ₁ : Q ≤ ψ₁.modulus) (hψ₂ : Q ≤ ψ₂.modulus)
    (m f z₁ z₂ : O) (hm : m ≠ 0) (hf : f ≠ 0) (hz₁ : z₁ ≠ 0) (hz₂ : z₂ ≠ 0)
    (hmLam : λ₀ ∣ m) (hm2 : (2 : O) ∣ m)
    (hχ₁ : ∀ n, elementCoeff χ₁ n = rowTwist (HeckeRowClosure.elementHom η) m f z₁ n)
    (hχ₂ : ∀ n, elementCoeff χ₂ n = rowTwist (HeckeRowClosure.elementHom η) m f z₂ n)
    (P : Ideal O) [P.IsMaximal] (hg : λ₀ ∉ P) (h2 : (2 : O) ∉ P)
    (hQP : IsCoprime Q P) :
    valuation (Ideal.span {z₁}) P % 6 = valuation (Ideal.span {z₂}) P % 6 := by
  obtain ⟨u₁, a₁, b₁, r₁, hr₁, hpr₁, hx₁⟩ :=
    exists_supported_numerator_factorization (f ^ 4 * z₁) (mul_ne_zero (pow_ne_zero _ hf) hz₁)
  obtain ⟨u₂, a₂, b₂, r₂, hr₂, hpr₂, hx₂⟩ :=
    exists_supported_numerator_factorization (f ^ 4 * z₂) (mul_ne_zero (pow_ne_zero _ hf) hz₂)
  have hr₁0 := Ideal.span_singleton_eq_bot.not.mp hr₁.1
  have hr₂0 := Ideal.span_singleton_eq_bot.not.mp hr₂.1
  have h := actual_rows_good_profile η χ₁ χ₂ ψ₁ ψ₂ h₁ h₂ Q hQ hQ72 hψ₁ hψ₂
    m f z₁ z₂ hm hmLam hm2 u₁ u₂ a₁ b₁ a₂ b₂ r₁ r₂ hr₁ hr₂ hpr₁ hpr₂ hx₁ hx₂
    hχ₁ hχ₂ P hg (ActualEisensteinCubic.quotient_char_ne_two_of_two_not_mem P h2) hQP
  rw [← valuation_supported_numerator _ u₁ a₁ b₁ r₁ hr₁0 hx₁ P hg h2,
    ← valuation_supported_numerator _ u₂ a₂ b₂ r₂ hr₂0 hx₂ P hg h2,
    ← Ideal.span_singleton_mul_span_singleton, ← Ideal.span_singleton_mul_span_singleton] at h
  exact valuation_mod_six_cancel_frozen _ _ _ P
    (Ideal.span_singleton_eq_bot.not.mpr (pow_ne_zero _ hf))
    (Ideal.span_singleton_eq_bot.not.mpr hz₁) (Ideal.span_singleton_eq_bot.not.mpr hz₂) h

theorem local_row_valuation_zero (η χ ψ : Character) (h : InducedBy χ ψ)
    (Q K I P : Ideal O) (hQ : Q ≠ ⊤) (hK : K ≠ 0)
    (hψ : Q ≤ ψ.modulus) (hI : CanonicalQuadraticSieve.Supported I)
    [P.IsMaximal] (hg : λ₀ ∉ P) (hchar : ringChar (O ⧸ P) ≠ 2)
    (hQP : IsCoprime Q P) (hηP : IsCoprime η.modulus P)
    (hrow : ∀ n : O, n - 1 ∈ Q → IsCoprime (Ideal.span {n}) K →
      elementCoeff χ n = elementCoeff η n * idealRowHom n I) :
    valuation I P % 6 = 0 := by
  have hzero : valuation (1 : Ideal O) P % 6 = 0 := by
    simp only [valuation, normalizedFactors_one, Multiset.count_zero, Nat.zero_mod]
  rw [← hzero]
  apply valuation_mod_six_of_unit_agreement (Q * η.modulus) (K * χ.modulus) I 1 P
    (mul_ne_zero hK χ.modulus_ne_bot) hI
    (by constructor; exact one_ne_zero; simp only [normalizedFactors_one, Multiset.notMem_zero, false_implies, implies_true]) hg hchar
    (hQP.mul_left hηP)
  intro n hn hc
  obtain ⟨hcK, hcχ⟩ := IsCoprime.mul_right_iff.mp hc
  have hnQ := Ideal.mul_le_left hn
  have hη : elementCoeff η n = 1 := by
    change η.residue (Ideal.Quotient.mk η.modulus n) = 1
    rw [(Ideal.Quotient.mk_eq_one_iff_sub_mem _).mpr (Ideal.mul_le_right hn), map_one]
  have he := elementCoeff_eq_one_of_inducedBy χ ψ h Q hQ hψ n hnQ hcχ
  rw [hrow n hnQ hcK, hη, one_mul] at he
  simpa only [map_one] using he

theorem actual_row_numerator_valuation_zero (η χ ψ : Character) (h : InducedBy χ ψ)
    (Q : Ideal O) (hQ : Q ≠ ⊤) (hQ72 : Q ≤ Ideal.span {(72 : O)}) (hψ : Q ≤ ψ.modulus)
    (m f z : O) (hm : m ≠ 0) (hf : f ≠ 0) (hz : z ≠ 0)
    (hmLam : λ₀ ∣ m) (hm2 : (2 : O) ∣ m)
    (hχ : ∀ n, elementCoeff χ n = rowTwist (HeckeRowClosure.elementHom η) m f z n)
    (P : Ideal O) [P.IsMaximal] (hg : λ₀ ∉ P) (h2 : (2 : O) ∉ P)
    (hQP : IsCoprime Q P) (hηP : IsCoprime η.modulus P) :
    valuation (Ideal.span {f ^ 4 * z}) P % 6 = 0 := by
  obtain ⟨u, a, b, r, hr, hpr, hx⟩ :=
    exists_supported_numerator_factorization (f ^ 4 * z) (mul_ne_zero (pow_ne_zero _ hf) hz)
  rw [valuation_supported_numerator _ u a b r (Ideal.span_singleton_eq_bot.not.mp hr.1) hx P hg h2]
  apply local_row_valuation_zero η χ ψ h Q (Ideal.span {m}) (Ideal.span {r}) P hQ
    (Ideal.span_singleton_eq_bot.not.mpr hm) hψ hr hg
    (ActualEisensteinCubic.quotient_char_ne_two_of_two_not_mem P h2) hQP hηP
  intro n hn hc
  exact actual_row_on_fixed_units η χ m f z hmLam hm2 u a b r hr hpr hx hχ n (hQ72 hn) hc

theorem actual_row_forced_residue_four (η χ ψ : Character) (h : InducedBy χ ψ)
    (Q : Ideal O) (hQ : Q ≠ ⊤) (hQ72 : Q ≤ Ideal.span {(72 : O)}) (hψ : Q ≤ ψ.modulus)
    (m A z : O) (hm : m ≠ 0) (hA : A ≠ 0) (hz : z ≠ 0)
    (hmLam : λ₀ ∣ m) (hm2 : (2 : O) ∣ m)
    (hχ : ∀ n, elementCoeff χ n = rowTwist (HeckeRowClosure.elementHom η) m 1 (A * z) n)
    (P : Ideal O) [P.IsMaximal] (hg : λ₀ ∉ P) (h2 : (2 : O) ∉ P)
    (hQP : IsCoprime Q P) (hηP : IsCoprime η.modulus P)
    (hA2 : valuation (Ideal.span {A}) P % 6 = 2) :
    valuation (Ideal.span {z}) P % 6 = 4 := by
  have he := actual_row_numerator_valuation_zero η χ ψ h Q hQ hQ72 hψ m 1 (A * z)
    hm one_ne_zero (mul_ne_zero hA hz) hmLam hm2 hχ P hg h2 hQP hηP
  simp only [one_pow, one_mul] at he
  rw [← Ideal.span_singleton_mul_span_singleton, valuation_mul _ _ _
    (Ideal.span_singleton_eq_bot.not.mpr hA) (Ideal.span_singleton_eq_bot.not.mpr hz),
    Nat.add_mod, hA2] at he
  omega

theorem actual_forced_fourth_power (η χ ψ : Character) (h : InducedBy χ ψ)
    (Q : Ideal O) (hQ : Q ≠ ⊤) (hQ72 : Q ≤ Ideal.span {(72 : O)}) (hψ : Q ≤ ψ.modulus)
    (m A z : O) (hm : m ≠ 0) (hA : A ≠ 0) (hz : z ≠ 0)
    (hmLam : λ₀ ∣ m) (hm2 : (2 : O) ∣ m)
    (hχ : ∀ n, elementCoeff χ n = rowTwist (HeckeRowClosure.elementHom η) m 1 (A * z) n)
    (D : Ideal O) (hD : Squarefree D)
    (hgood : ∀ P ∈ normalizedFactors D, λ₀ ∉ P ∧ (2 : O) ∉ P ∧
      IsCoprime Q P ∧ IsCoprime η.modulus P ∧ valuation (Ideal.span {A}) P % 6 = 2) :
    D ^ 4 ∣ sixthRemainder (Ideal.span {z}) ∧
      (Ideal.absNorm D : ℝ) ^ 4 ≤ Ideal.absNorm (sixthRemainder (Ideal.span {z})) := by
  have hf : ∀ P ∈ normalizedFactors D, valuation (Ideal.span {z}) P % 6 = 4 := by
    intro P hP
    have hp := prime_of_normalized_factor P hP
    let : P.IsMaximal := (Ideal.isPrime_of_prime hp).isMaximal hp.ne_zero
    obtain ⟨hg, h2, hQP, hηP, hA2⟩ := hgood P hP
    exact actual_row_forced_residue_four η χ ψ h Q hQ hQ72 hψ m A z hm hA hz hmLam hm2 hχ
      P hg h2 hQP hηP hA2
  exact ⟨forced_fourth_power_dvd _ D hD hf, forced_fourth_power_norm_le _ D hD hf⟩

def FixedInducingRow (η : Character) (Q : Ideal O) (m A z : O) : Prop :=
  ∃ χ ψ : Character, FiniteFourier.IsPrimitiveOnIdeals ψ.residue ∧
    InducedBy χ ψ ∧ Q ≤ ψ.modulus ∧
    ∀ n, elementCoeff χ n = rowTwist (HeckeRowClosure.elementHom η) m 1 (A * z) n

theorem fixed_inducing_rows_profile (η : Character) (Q : Ideal O)
    (hQ : Q ≠ ⊤) (hQ72 : Q ≤ Ideal.span {(72 : O)})
    (m A z₁ z₂ : O) (hm : m ≠ 0) (hA : A ≠ 0) (hz₁ : z₁ ≠ 0) (hz₂ : z₂ ≠ 0)
    (hmLam : λ₀ ∣ m) (hm2 : (2 : O) ∣ m)
    (h₁ : FixedInducingRow η Q m A z₁) (h₂ : FixedInducingRow η Q m A z₂)
    (P : Ideal O) [P.IsMaximal] (hg : λ₀ ∉ P) (h2 : (2 : O) ∉ P)
    (hQP : IsCoprime Q P) :
    valuation (Ideal.span {z₁}) P % 6 = valuation (Ideal.span {z₂}) P % 6 := by
  obtain ⟨χ₁, ψ₁, _, hi₁, hψ₁, hχ₁⟩ := h₁
  obtain ⟨χ₂, ψ₂, _, hi₂, hψ₂, hχ₂⟩ := h₂
  have he := actual_rows_profile η χ₁ χ₂ ψ₁ ψ₂ hi₁ hi₂ Q hQ hQ72 hψ₁ hψ₂
    m 1 (A * z₁) (A * z₂) hm one_ne_zero (mul_ne_zero hA hz₁) (mul_ne_zero hA hz₂)
    hmLam hm2 hχ₁ hχ₂ P hg h2 hQP
  rw [← Ideal.span_singleton_mul_span_singleton, ← Ideal.span_singleton_mul_span_singleton] at he
  exact valuation_mod_six_cancel_frozen _ _ _ P (Ideal.span_singleton_eq_bot.not.mpr hA)
    (Ideal.span_singleton_eq_bot.not.mpr hz₁) (Ideal.span_singleton_eq_bot.not.mpr hz₂) he

theorem fixed_inducing_rows_same_remainder (η : Character) (Q : Ideal O)
    (hQ : Q ≠ ⊤) (hQ72 : Q ≤ Ideal.span {(72 : O)})
    (m A z₁ z₂ : O) (hm : m ≠ 0) (hA : A ≠ 0) (hz₁ : z₁ ≠ 0) (hz₂ : z₂ ≠ 0)
    (hmLam : λ₀ ∣ m) (hm2 : (2 : O) ∣ m)
    (h₁ : FixedInducingRow η Q m A z₁) (h₂ : FixedInducingRow η Q m A z₂)
    (S : Finset (Ideal O))
    (houtside : ∀ P : Ideal O, Prime P → P ∉ S →
      λ₀ ∉ P ∧ (2 : O) ∉ P ∧ IsCoprime Q P)
    (hsector : ∀ P ∈ S, valuation (Ideal.span {z₁}) P % 6 = valuation (Ideal.span {z₂}) P % 6) :
    sixthRemainder (Ideal.span {z₁}) = sixthRemainder (Ideal.span {z₂}) := by
  apply sixthRemainder_eq_of_prime_profile (sixthRemainder_ne_zero _)
  intro P hP
  rw [sixthRemainder_valuation]
  by_cases hPS : P ∈ S
  · exact hsector P hPS
  · let : P.IsMaximal := (Ideal.isPrime_of_prime hP).isMaximal hP.ne_zero
    obtain ⟨hg, h2, hQP⟩ := houtside P hP hPS
    exact fixed_inducing_rows_profile η Q hQ hQ72 m A z₁ z₂ hm hA hz₁ hz₂ hmLam hm2
      h₁ h₂ P hg h2 hQP

theorem fixed_inducing_remainder_card (η : Character) (Q : Ideal O)
    (hQ : Q ≠ ⊤) (hQ72 : Q ≤ Ideal.span {(72 : O)})
    (m A : O) (hm : m ≠ 0) (hA : A ≠ 0) (hmLam : λ₀ ∣ m) (hm2 : (2 : O) ∣ m)
    (S : Finset (Ideal O))
    (houtside : ∀ P : Ideal O, Prime P → P ∉ S →
      λ₀ ∉ P ∧ (2 : O) ∉ P ∧ IsCoprime Q P)
    (T : Finset O) (hT : ∀ z ∈ T, z ≠ 0)
    (hex : ∀ z ∈ T, FixedInducingRow η Q m A z) :
    (T.image (fun z => sixthRemainder (Ideal.span {z}))).card ≤ 6 ^ S.card := by
  let Rs := T.image (fun z => sixthRemainder (Ideal.span {z}))
  let code : Ideal O → (S → Fin 6) :=
    fun R P => ⟨valuation R P.val % 6, Nat.mod_lt _ (by decide)⟩
  have hinj : (Rs : Set (Ideal O)).InjOn code := by
    intro R hR R' hR' he
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hR
    obtain ⟨z', hz', rfl⟩ := Finset.mem_image.mp hR'
    apply fixed_inducing_rows_same_remainder η Q hQ hQ72 m A z z' hm hA (hT z hz) (hT z' hz')
      hmLam hm2 (hex z hz) (hex z' hz') S houtside
    intro P hP
    have hh := congrArg (fun f : S → Fin 6 => (f ⟨P, hP⟩).val) he
    simpa only [code, sixthRemainder_valuation, Nat.mod_mod] using hh
  have hc := Finset.card_le_card_of_injOn code (t := Finset.univ)
    (fun _ _ => Finset.mem_univ _) hinj
  simpa only [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_coe, Rs] using hc

theorem fixed_inducing_row_count (η : Character) (Q : Ideal O)
    (hQ : Q ≠ ⊤) (hQ72 : Q ≤ Ideal.span {(72 : O)})
    (m A : O) (hm : m ≠ 0) (hA : A ≠ 0) (hmLam : λ₀ ∣ m) (hm2 : (2 : O) ∣ m)
    (S : Finset (Ideal O))
    (houtside : ∀ P : Ideal O, Prime P → P ∉ S →
      λ₀ ∉ P ∧ (2 : O) ∉ P ∧ IsCoprime Q P)
    (T : Finset O) (hT : ∀ z ∈ T, z ≠ 0)
    (hex : ∀ z ∈ T, FixedInducingRow η Q m A z)
    (D : Ideal O) (hD : Squarefree D)
    (hgood : ∀ P ∈ normalizedFactors D, λ₀ ∉ P ∧ (2 : O) ∉ P ∧
      IsCoprime Q P ∧ IsCoprime η.modulus P ∧ valuation (Ideal.span {A}) P % 6 = 2)
    (Z C M F : ℝ) (hZ : 0 < Z) (hC : 0 ≤ C)
    (hDnorm : Z ^ (F / 2) ≤ (Ideal.absNorm D : ℝ))
    (hN : ∀ z ∈ T, (Ideal.absNorm (Ideal.span {z}) : ℝ) ≤ C * Z ^ M) :
    (T.card : ℝ) ≤ 768 * (6 : ℝ) ^ S.card * C ^ (1 / 6 : ℝ) * Z ^ ((M - 2 * F) / 6) := by
  let Rs := T.image (fun z => sixthRemainder (Ideal.span {z}))
  have hRs : ∀ R ∈ Rs, R ≠ 0 := by
    intro R hR
    obtain ⟨z, _, rfl⟩ := Finset.mem_image.mp hR
    exact sixthRemainder_ne_zero _
  have hRnorm : ∀ R ∈ Rs, Z ^ (2 * F) ≤ (Ideal.absNorm R : ℝ) := by
    intro R hR
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hR
    obtain ⟨χ, ψ, _, hi, hψ, hχ⟩ := hex z hz
    have hf := (actual_forced_fourth_power η χ ψ hi Q hQ hQ72 hψ m A z hm hA
      (hT z hz) hmLam hm2 hχ D hD hgood).2
    calc
      Z ^ (2 * F) = (Z ^ (F / 2)) ^ (4 : ℕ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hZ.le]
        congr 1
        norm_num
        ring
      _ ≤ (Ideal.absNorm D : ℝ) ^ (4 : ℕ) := pow_le_pow_left₀ (Real.rpow_nonneg hZ.le _) hDnorm _
      _ ≤ _ := hf
  have hcount := element_count_power_scale_family T Rs hRs Z C M (2 * F) hZ hC hRnorm hT
    (fun z hz => Finset.mem_image.mpr ⟨z, hz, rfl⟩) hN
  have hcard : (Rs.card : ℝ) ≤ (6 : ℝ) ^ S.card := by
    exact_mod_cast fixed_inducing_remainder_card η Q hQ hQ72 m A hm hA hmLam hm2 S houtside T hT hex
  apply hcount.trans
  gcongr

theorem outside_fixed_support (Q : Ideal O) (hQ : Q ≠ 0)
    (hQ72 : Q ≤ Ideal.span {(72 : O)}) (P : Ideal O) (hP : Prime P)
    (hPS : P ∉ (normalizedFactors Q).toFinset) :
    λ₀ ∉ P ∧ (2 : O) ∉ P ∧ IsCoprime Q P := by
  let : P.IsMaximal := (Ideal.isPrime_of_prime hP).isMaximal hP.ne_zero
  have hcop : IsCoprime Q P := by
    apply Ideal.coprime_of_no_prime_ge
    intro J hQJ hPJ hJ
    have hPJ' : P = J := (inferInstance : P.IsMaximal).eq_of_le hJ.ne_top hPJ
    apply hPS
    apply Multiset.mem_toFinset.mpr
    apply (Ideal.mem_normalizedFactors_iff hQ).mpr
    exact ⟨Ideal.isPrime_of_prime hP, hPJ' ▸ hQJ⟩
  have h72 : (72 : O) ∉ P := by
    intro hh
    have hle : Q ≤ P := hQ72.trans ((Ideal.span_singleton_le_iff_mem _).mpr hh)
    have he := Ideal.isCoprime_iff_sup_eq.mp hcop
    rw [sup_eq_right.mpr hle] at he
    exact hP.ne_one (by simpa only [Ideal.one_eq_top] using he)
  have hl : λ₀ ∣ (72 : O) :=
    (dvd_pow_self λ₀ (by decide : (2 : ℕ) ≠ 0)).trans
      (ActualEisensteinCubic.lambda_sq_dvd_three.trans (show (3 : O) ∣ 72 from ⟨24, by norm_num⟩))
  have h2 : (2 : O) ∣ 72 := ⟨36, by norm_num⟩
  refine ⟨?_, ?_, hcop⟩
  · intro hh
    obtain ⟨v, hv⟩ := hl
    exact h72 (hv ▸ P.mul_mem_right v hh)
  · intro hh
    obtain ⟨v, hv⟩ := h2
    exact h72 (hv ▸ P.mul_mem_right v hh)

theorem fixed_support_exceptional_count (η : Character) (Q : Ideal O)
    (hQ0 : Q ≠ 0) (hQ : Q ≠ ⊤) (hQ72 : Q ≤ Ideal.span {(72 : O)})
    (m A : O) (hm : m ≠ 0) (hA : A ≠ 0) (hmLam : λ₀ ∣ m) (hm2 : (2 : O) ∣ m)
    (T : Finset O) (hT : ∀ z ∈ T, z ≠ 0)
    (hex : ∀ z ∈ T, FixedInducingRow η Q m A z)
    (D : Ideal O) (hD : Squarefree D)
    (hgood : ∀ P ∈ normalizedFactors D, λ₀ ∉ P ∧ (2 : O) ∉ P ∧
      IsCoprime Q P ∧ IsCoprime η.modulus P ∧ valuation (Ideal.span {A}) P % 6 = 2)
    (Z C M F : ℝ) (hZ : 0 < Z) (hC : 0 ≤ C)
    (hDnorm : Z ^ (F / 2) ≤ (Ideal.absNorm D : ℝ))
    (hN : ∀ z ∈ T, (Ideal.absNorm (Ideal.span {z}) : ℝ) ≤ C * Z ^ M) :
    (T.card : ℝ) ≤ 768 * (6 : ℝ) ^ (normalizedFactors Q).toFinset.card *
      C ^ (1 / 6 : ℝ) * Z ^ ((M - 2 * F) / 6) :=
  fixed_inducing_row_count η Q hQ hQ72 m A hm hA hmLam hm2
    (normalizedFactors Q).toFinset (outside_fixed_support Q hQ0 hQ72) T hT hex
    D hD hgood Z C M F hZ hC hDnorm hN

theorem fixed_support_exceptional_count_weaker (η : Character) (Q : Ideal O)
    (hQ0 : Q ≠ 0) (hQ : Q ≠ ⊤) (hQ72 : Q ≤ Ideal.span {(72 : O)})
    (m A : O) (hm : m ≠ 0) (hA : A ≠ 0) (hmLam : λ₀ ∣ m) (hm2 : (2 : O) ∣ m)
    (T : Finset O) (hT : ∀ z ∈ T, z ≠ 0)
    (hex : ∀ z ∈ T, FixedInducingRow η Q m A z)
    (D : Ideal O) (hD : Squarefree D)
    (hgood : ∀ P ∈ normalizedFactors D, λ₀ ∉ P ∧ (2 : O) ∉ P ∧
      IsCoprime Q P ∧ IsCoprime η.modulus P ∧ valuation (Ideal.span {A}) P % 6 = 2)
    (Z C M F : ℝ) (hZ : 1 ≤ Z) (hC : 0 ≤ C) (hF : 0 ≤ F)
    (hDnorm : Z ^ (F / 2) ≤ (Ideal.absNorm D : ℝ))
    (hN : ∀ z ∈ T, (Ideal.absNorm (Ideal.span {z}) : ℝ) ≤ C * Z ^ M) :
    (T.card : ℝ) ≤ 768 * (6 : ℝ) ^ (normalizedFactors Q).toFinset.card *
      C ^ (1 / 6 : ℝ) * Z ^ ((M - F) / 6) := by
  apply (fixed_support_exceptional_count η Q hQ0 hQ hQ72 m A hm hA hmLam hm2 T hT hex
    D hD hgood Z C M F (zero_lt_one.trans_le hZ) hC hDnorm hN).trans
  gcongr
  linarith

theorem fixed_inducing_rows_empty (η : Character) (Q : Ideal O)
    (hQ : Q ≠ ⊤) (hQ72 : Q ≤ Ideal.span {(72 : O)})
    (m A : O) (hm : m ≠ 0) (hA : A ≠ 0) (hmLam : λ₀ ∣ m) (hm2 : (2 : O) ∣ m)
    (T : Finset O) (hT : ∀ z ∈ T, z ≠ 0)
    (hex : ∀ z ∈ T, FixedInducingRow η Q m A z)
    (D : Ideal O) (hD : Squarefree D)
    (hgood : ∀ P ∈ normalizedFactors D, λ₀ ∉ P ∧ (2 : O) ∉ P ∧
      IsCoprime Q P ∧ IsCoprime η.modulus P ∧ valuation (Ideal.span {A}) P % 6 = 2)
    (H : ℝ) (hH : H < (Ideal.absNorm D : ℝ) ^ 4)
    (hN : ∀ z ∈ T, (Ideal.absNorm (Ideal.span {z}) : ℝ) ≤ H) : T = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro z hz
  obtain ⟨χ, ψ, _, hi, hψ, hχ⟩ := hex z hz
  have hf := (actual_forced_fourth_power η χ ψ hi Q hQ hQ72 hψ m A z hm hA
    (hT z hz) hmLam hm2 hχ D hD hgood).2
  have hr := sixthRemainder_norm_le (Ideal.span {z}) (Ideal.span_singleton_eq_bot.not.mpr (hT z hz))
  exact (not_le_of_gt hH) (hf.trans (hr.trans (hN z hz)))

end SevenEighths.CenteredExceptionalProfile

end

end OAI
