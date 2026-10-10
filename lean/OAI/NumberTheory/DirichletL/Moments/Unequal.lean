import OAI.NumberTheory.DirichletL.Moments.Canonical
import OAI.NumberTheory.DirichletL.Moments.FullCorrelation
import OAI.NumberTheory.DirichletL.Moments.Fourier

namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.CenteredMomentUnequal
open CenteredMomentCorrelation CenteredMomentCommonSupport

section Domain
variable {A : Type*} [CommRing A] [IsDomain A]

theorem divisor_congruence (v t k : A) (hv : v ≠ 0)
    (x : Residue (v * t)) (y : Residue v) :
    scaledResidue (v * t) v ((v * t) * v) rfl x -
      scaledResidue v (v * t) ((v * t) * v) (mul_comm _ _) y =
      Ideal.Quotient.mk _ (v * k) ↔
      x = scaledResidue v t (v * t) rfl y + Ideal.Quotient.mk _ k := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
  rw [scaledResidue_congruence, scaledResidue_mk, ← map_add, Ideal.Quotient.eq, Ideal.mem_span_singleton]
  change (v * t) * v ∣ v * x - (v * t) * y - v * k ↔ v * t ∣ x - (t * y + k)
  rw [show (v * t) * v = v * (v * t) by ring,
    show v * x - (v * t) * y - v * k = v * (x - (t * y + k)) by ring]
  exact mul_dvd_mul_iff_left hv

theorem fullCorrelation_divisor (v t k : A) (hv : v ≠ 0)
    [Fintype (Residue (v * t))] [Fintype (Residue v)]
    (χu : MulChar (Residue (v * t)) ℂ) (χv : MulChar (Residue v) ℂ) :
    fullModulusCorrelation (v * t) v χu χv (v * k) =
      ∑ y : Residue v, χu (scaledResidue v t (v * t) rfl y + Ideal.Quotient.mk _ k) *
        star (χv y) := by
  unfold fullModulusCorrelation fullCorrelation
  simp_rw [divisor_congruence v t k hv]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]

theorem fullCorrelation_divisor_constant (v t k : A) (hv : v ≠ 0)
    [Fintype (Residue (v * t))] [Fintype (Residue v)]
    (χu : MulChar (Residue (v * t)) ℂ) (χv : MulChar (Residue v) ℂ)
    (hχ : ∀ y : Residue v,
      χu (scaledResidue v t (v * t) rfl y + Ideal.Quotient.mk _ k) = χu (Ideal.Quotient.mk _ k)) :
    fullModulusCorrelation (v * t) v χu χv (v * k) =
      χu (Ideal.Quotient.mk _ k) * star (∑ y : Residue v, χv y) := by
  rw [fullCorrelation_divisor v t k hv χu χv]
  simp_rw [hχ]
  rw [← Finset.mul_sum, star_sum]

omit [IsDomain A] in
theorem divisor_lift_constant (p v t k : A) (hpt : p ∣ t)
    (χu : MulChar (Residue (v * t)) ℂ) (χ : MulChar (Residue p) ℂ)
    (hχ : ∀ x : A, χu (Ideal.Quotient.mk _ x) = χ (Ideal.Quotient.mk _ x)) :
    ∀ y : Residue v, χu (scaledResidue v t (v * t) rfl y + Ideal.Quotient.mk _ k) =
      χu (Ideal.Quotient.mk _ k) := by
  intro y
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
  rw [scaledResidue_mk, ← map_add, hχ, hχ, map_add, map_mul]
  have ht : Ideal.Quotient.mk (Ideal.span {p}) t = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr hpt)
  rw [ht, zero_mul, zero_add]

omit [IsDomain A] in
theorem lifted_character_sum_zero (p v : A) (hpv : p ∣ v)
    [Fintype (Residue p)] [Fintype (Residue v)]
    (χv : MulChar (Residue v) ℂ) (χ : MulChar (Residue p) ℂ) (hχ : χ ≠ 1)
    (hlift : ∀ x : A, χv (Ideal.Quotient.mk _ x) = χ (Ideal.Quotient.mk _ x)) :
    (∑ y : Residue v, χv y) = 0 := by
  let π : Residue v →+* Residue p :=
    Ideal.Quotient.factor (Ideal.span_singleton_le_span_singleton.mpr hpv)
  have hπ : Function.Surjective π := Ideal.Quotient.factor_surjective _
  have he (y : Residue v) : χv y = χ (π y) := by
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    exact hlift y
  simp_rw [he]
  rw [sum_reduction π hπ χ, MulChar.sum_eq_zero_of_ne_one hχ, mul_zero]

theorem fullCorrelation_divisor_eq_zero (p v t k : A) (hv : v ≠ 0)
    (hpv : p ∣ v) (hpt : p ∣ t)
    [Fintype (Residue p)] [Fintype (Residue (v * t))] [Fintype (Residue v)]
    (χu : MulChar (Residue (v * t)) ℂ) (χv : MulChar (Residue v) ℂ)
    (ψu ψv : MulChar (Residue p) ℂ) (hψv : ψv ≠ 1)
    (hu : ∀ x : A, χu (Ideal.Quotient.mk _ x) = ψu (Ideal.Quotient.mk _ x))
    (hv' : ∀ x : A, χv (Ideal.Quotient.mk _ x) = ψv (Ideal.Quotient.mk _ x)) :
    fullModulusCorrelation (v * t) v χu χv (v * k) = 0 := by
  rw [fullCorrelation_divisor_constant v t k hv χu χv
    (divisor_lift_constant p v t k hpt χu ψu hu),
    lifted_character_sum_zero p v hpv χv ψv hψv hv', star_zero, mul_zero]

end Domain
section Eisenstein
open ActualEisensteinCubic ConcreteTraceCRT CanonicalQuadraticSieve CanonicalRowCompletion
open CenteredMomentSupportedCorrelation CenteredMomentCanonical CompletedGauss
open ConcretePrimeRowBridge hiding O
local notation "O" => ActualEisensteinCubic.O

theorem supported_power (p : O) (hp : Supported (Ideal.span {p})) (i : ℕ) :
    Supported (Ideal.span {p ^ i}) := by
  rw [← Ideal.span_singleton_pow]
  exact supported_pow hp i

theorem supported_power_character_mk (p : O) [ (Ideal.span {p}).IsMaximal]
    (hp : Supported (Ideal.span {p})) (hg : goodLambda ∉ Ideal.span {p})
    {i : ℕ} (hi : 1 ≤ i) (x : O) :
    supportedModulusCharacter (p ^ i) (supported_power p hp i) (Ideal.Quotient.mk _ x) =
      (actualSextic (Ideal.span {p}) hg ^ i) (Ideal.Quotient.mk _ x) := by
  rw [supportedModulusCharacter_mk, ← Ideal.span_singleton_pow, map_pow,
    idealRowHom_prime x (Ideal.span {p}) hg, MulChar.pow_apply' _ (by omega)]

theorem supported_product_power_character_mk (p : O) [(Ideal.span {p}).IsMaximal]
    (hp : Supported (Ideal.span {p})) (hg : goodLambda ∉ Ideal.span {p})
    {j d : ℕ} (hj : 1 ≤ j) (x : O) :
    supportedModulusCharacter (p ^ j * p ^ d)
      (supported_mul_elements _ _ (supported_power p hp j) (supported_power p hp d))
      (Ideal.Quotient.mk _ x) =
      (actualSextic (Ideal.span {p}) hg ^ (j + d)) (Ideal.Quotient.mk _ x) := by
  rw [supportedModulusCharacter_mk, ← pow_add, ← Ideal.span_singleton_pow, map_pow,
    idealRowHom_prime x (Ideal.span {p}) hg, MulChar.pow_apply' _ (by omega)]

theorem unequal_prime_power_zero_of_not_six (p : O) [(Ideal.span {p}).IsMaximal]
    (hp : Supported (Ideal.span {p})) (hg : goodLambda ∉ Ideal.span {p})
    (hchar : ringChar (O ⧸ Ideal.span {p}) ≠ 2)
    {j d : ℕ} (hj : 1 ≤ j) (hd : 1 ≤ d) (hj6 : ¬ 6 ∣ j) (k : O) :
    actualCorrelation (p ^ j * p ^ d) (p ^ j)
      (supported_mul_elements _ _ (supported_power p hp j) (supported_power p hp d))
      (supported_power p hp j) (p ^ j * k) = 0 := by
  have hp0 := supported_element_ne_zero p hp
  let := finite_quotient_span hp0
  let : Fintype (Residue p) := Fintype.ofFinite _
  let := finite_quotient_span (pow_ne_zero j hp0)
  let : Fintype (Residue (p ^ j)) := Fintype.ofFinite _
  let := finite_quotient_span (mul_ne_zero (pow_ne_zero j hp0) (pow_ne_zero d hp0))
  let : Fintype (Residue (p ^ j * p ^ d)) := Fintype.ofFinite _
  have hχ : actualSextic (Ideal.span {p}) hg ^ j ≠ 1 := by
    intro h
    apply hj6
    rw [← actualSextic_order_six (Ideal.span {p}) hg hchar]
    exact orderOf_dvd_of_pow_eq_one h
  exact fullCorrelation_divisor_eq_zero p (p ^ j) (p ^ d) k (pow_ne_zero j hp0)
    (dvd_pow_self p (by omega)) (dvd_pow_self p (by omega))
    (supportedModulusCharacter _ _ ) (supportedModulusCharacter _ _)
    (actualSextic (Ideal.span {p}) hg ^ (j + d)) (actualSextic (Ideal.span {p}) hg ^ j)
    hχ (supported_product_power_character_mk p hp hg hj)
    (supported_power_character_mk p hp hg hj)

theorem unequal_prime_power_factor (p : O) [(Ideal.span {p}).IsMaximal]
    (hp : Supported (Ideal.span {p})) (hg : goodLambda ∉ Ideal.span {p})
    {j d : ℕ} (hj : 1 ≤ j) (hd : 1 ≤ d) (k : O) :
    actualCorrelation (p ^ j * p ^ d) (p ^ j)
      (supported_mul_elements _ _ (supported_power p hp j) (supported_power p hp d))
      (supported_power p hp j) (p ^ j * k) =
      (actualSextic (Ideal.span {p}) hg ^ (j + d)) (Ideal.Quotient.mk _ k) *
        star (∑' y : Residue (p ^ j), supportedModulusCharacter (p ^ j)
          (supported_power p hp j) y) := by
  have hp0 := supported_element_ne_zero p hp
  let := finite_quotient_span (pow_ne_zero j hp0)
  let : Fintype (Residue (p ^ j)) := Fintype.ofFinite _
  let := finite_quotient_span (mul_ne_zero (pow_ne_zero j hp0) (pow_ne_zero d hp0))
  let : Fintype (Residue (p ^ j * p ^ d)) := Fintype.ofFinite _
  have h := fullCorrelation_divisor_constant (p ^ j) (p ^ d) k (pow_ne_zero j hp0)
    (supportedModulusCharacter _ (supported_mul_elements _ _ (supported_power p hp j) (supported_power p hp d)))
    (supportedModulusCharacter _ (supported_power p hp j))
    (divisor_lift_constant p (p ^ j) (p ^ d) k (dvd_pow_self p (by omega))
      _ (actualSextic (Ideal.span {p}) hg ^ (j + d))
      (supported_product_power_character_mk p hp hg hj))
  rw [supported_product_power_character_mk p hp hg hj k] at h
  simpa only [actualCorrelation, supportedCorrelation, tsum_fintype] using h

theorem unequal_prime_power_zero_of_nonunit (p : O) [(Ideal.span {p}).IsMaximal]
    (hp : Supported (Ideal.span {p})) (hg : goodLambda ∉ Ideal.span {p})
    {j d : ℕ} (hj : 1 ≤ j) (hd : 1 ≤ d) (k : O) (hk : p ∣ k) :
    actualCorrelation (p ^ j * p ^ d) (p ^ j)
      (supported_mul_elements _ _ (supported_power p hp j) (supported_power p hp d))
      (supported_power p hp j) (p ^ j * k) = 0 := by
  rw [unequal_prime_power_factor p hp hg hj hd k]
  have hk0 : Ideal.Quotient.mk (Ideal.span {p}) k = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr hk)
  rw [hk0, MulChar.map_zero, zero_mul]

theorem unequal_prime_power_norm_le (p : O) [(Ideal.span {p}).IsMaximal]
    (hp : Supported (Ideal.span {p})) (hg : goodLambda ∉ Ideal.span {p})
    {j d : ℕ} (hj : 1 ≤ j) (hd : 1 ≤ d) (k : O) :
    ‖actualCorrelation (p ^ j * p ^ d) (p ^ j)
      (supported_mul_elements _ _ (supported_power p hp j) (supported_power p hp d))
      (supported_power p hp j) (p ^ j * k)‖ ≤ (Ideal.absNorm (Ideal.span {p}) : ℝ) ^ j := by
  have hp0 := supported_element_ne_zero p hp
  let := finite_quotient_span hp0
  let : Fintype (Residue p) := Fintype.ofFinite _
  let := finite_quotient_span (pow_ne_zero j hp0)
  let : Fintype (Residue (p ^ j)) := Fintype.ofFinite _
  rw [unequal_prime_power_factor p hp hg hj hd k, norm_mul, norm_star, tsum_fintype]
  calc
    _ ≤ ‖∑ y : Residue (p ^ j), supportedModulusCharacter (p ^ j)
        (supported_power p hp j) y‖ := mul_le_of_le_one_left (norm_nonneg _)
      (QuadraticInitialBound.norm_finite_character_le_one _ _)
    _ ≤ ∑ y : Residue (p ^ j), ‖supportedModulusCharacter (p ^ j)
        (supported_power p hp j) y‖ := norm_sum_le _ _
    _ ≤ ∑ _y : Residue (p ^ j), (1 : ℝ) := Finset.sum_le_sum
      (fun y _ => QuadraticInitialBound.norm_finite_character_le_one _ _)
    _ = _ := by
      rw [← Nat.cast_pow, ← map_pow Ideal.absNorm,
        Ideal.span_singleton_pow]
      simp [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]

theorem unequal_prime_power_support (p : O) [(Ideal.span {p}).IsMaximal]
    (hp : Supported (Ideal.span {p})) (hg : goodLambda ∉ Ideal.span {p})
    (hchar : ringChar (O ⧸ Ideal.span {p}) ≠ 2)
    {j d : ℕ} (hj : 1 ≤ j) (hd : 1 ≤ d) (h : O)
    (hne : actualCorrelation (p ^ j * p ^ d) (p ^ j)
      (supported_mul_elements _ _ (supported_power p hp j) (supported_power p hp d))
      (supported_power p hp j) h ≠ 0) :
    ∃ k : O, h = p ^ j * k ∧ 6 ∣ j ∧ ¬ p ∣ k := by
  have hp0 := supported_element_ne_zero p hp
  let := finite_quotient_span (pow_ne_zero j hp0)
  let : Fintype (Residue (p ^ j)) := Fintype.ofFinite _
  let := finite_quotient_span (mul_ne_zero (pow_ne_zero j hp0) (pow_ne_zero d hp0))
  let : Fintype (Residue (p ^ j * p ^ d)) := Fintype.ofFinite _
  have hdiv : p ^ j ∣ h := by
    by_contra hn
    exact hne (fullModulusCorrelation_eq_zero_of_common_not_dvd _ _ (p ^ j) h
      (supportedModulusCharacter _ _) (supportedModulusCharacter _ _)
      (dvd_mul_right _ _) dvd_rfl hn)
  obtain ⟨k, rfl⟩ := hdiv
  refine ⟨k, rfl, ?_, ?_⟩
  · by_contra hj6
    exact hne (unequal_prime_power_zero_of_not_six p hp hg hchar hj hd hj6 k)
  · intro hk
    exact hne (unequal_prime_power_zero_of_nonunit p hp hg hj hd k hk)

end Eisenstein

end SevenEighths.CenteredMomentUnequal

end

end OAI
