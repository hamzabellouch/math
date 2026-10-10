import OAI.NumberTheory.CubicMoment.Estimates.ShortMoebiusPolynomials
import OAI.NumberTheory.CubicMoment.Estimates.PrimeToThreeIdeals
import OAI.NumberTheory.CubicMoment.Angular.AngularAlgebra
import Mathlib.RingTheory.MvPowerSeries.Expand

namespace OAI

/-! Exact inversion of the cubic completion kernel. The Euler variable
for a prime ideal is first weighted, then replaced by its cube. Thus the
series identities below retain the actual cube-divisor support; they are
not ordinary (uncubed) convolution identities. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

abbrev ComplexIdealSeries := MvPowerSeries EisensteinIdealPrime ℂ

def cubeCompletionSeries (x : EisensteinIdealPrime → ℂ) : ComplexIdealSeries :=
  MvPowerSeries.expand 3 (by norm_num)
    (MvPowerSeries.rescale x (MvPowerSeries.map Complex.ofRealHom idealZeta))

def cubeInverseCompletionSeries (x : EisensteinIdealPrime → ℂ) : ComplexIdealSeries :=
  MvPowerSeries.expand 3 (by norm_num)
    (MvPowerSeries.rescale x (MvPowerSeries.map Complex.ofRealHom idealMoebiusSeries))

lemma cube_completion_inverse (x : EisensteinIdealPrime → ℂ) :
    cubeInverseCompletionSeries x*cubeCompletionSeries x = 1 := by
  unfold cubeInverseCompletionSeries cubeCompletionSeries
  rw [← map_mul,← map_mul,← map_mul,idealMoebiusSeries_mul_zeta,map_one,map_one,map_one]

lemma cube_completion_inversion (x : EisensteinIdealPrime → ℂ)
    (A : ComplexIdealSeries) :
    cubeInverseCompletionSeries x*(cubeCompletionSeries x*A) = A := by
  rw [← mul_assoc,cube_completion_inverse,one_mul]

lemma cubeCompletionSeries_coeff (x : EisensteinIdealPrime → ℂ)
    (ν : EisensteinIdealExponent) :
    MvPowerSeries.coeff (3 • ν) (cubeCompletionSeries x) =
      ν.prod (fun p k => x p^k) := by
  rw [cubeCompletionSeries,MvPowerSeries.coeff_expand_smul,MvPowerSeries.coeff_rescale,
    MvPowerSeries.coeff_map]
  simp [MvPowerSeries.coeff_apply,idealZeta]

lemma cubeInverseCompletionSeries_coeff (x : EisensteinIdealPrime → ℂ)
    (ν : EisensteinIdealExponent) :
    MvPowerSeries.coeff (3 • ν) (cubeInverseCompletionSeries x) =
      ν.prod (fun p k => x p^k)*((MvPowerSeries.coeff ν idealMoebiusSeries:ℝ):ℂ) := by
  rw [cubeInverseCompletionSeries,MvPowerSeries.coeff_expand_smul,
    MvPowerSeries.coeff_rescale,MvPowerSeries.coeff_map]
  rfl

lemma cubeCompletionSeries_coeff_zero (x : EisensteinIdealPrime → ℂ)
    {ν : EisensteinIdealExponent} {p : EisensteinIdealPrime} (h : ¬3 ∣ ν p) :
    MvPowerSeries.coeff ν (cubeCompletionSeries x) = 0 :=
  MvPowerSeries.coeff_expand_of_not_dvd 3 (by norm_num) _ h

lemma cubeInverseCompletionSeries_coeff_zero (x : EisensteinIdealPrime → ℂ)
    {ν : EisensteinIdealExponent} {p : EisensteinIdealPrime} (h : ¬3 ∣ ν p) :
    MvPowerSeries.coeff ν (cubeInverseCompletionSeries x) = 0 :=
  MvPowerSeries.coeff_expand_of_not_dvd 3 (by norm_num) _ h

/-- The inverse identity is a literal finite sum at every ideal. -/
theorem cube_completion_finite_inverse (x : EisensteinIdealPrime → ℂ)
    (A : ComplexIdealSeries) (ν : EisensteinIdealExponent) :
    (∑ d ∈ Finset.HasAntidiagonal.antidiagonal ν,
      MvPowerSeries.coeff d.1 (cubeInverseCompletionSeries x)*
        ∑ e ∈ Finset.HasAntidiagonal.antidiagonal d.2,
          MvPowerSeries.coeff e.1 (cubeCompletionSeries x)*MvPowerSeries.coeff e.2 A) =
      MvPowerSeries.coeff ν A := by
  have h := congrArg (MvPowerSeries.coeff ν) (cube_completion_inversion x A)
  simpa only [MvPowerSeries.coeff_mul] using h

/-- Arbitrary finite norm weights may be applied after cube inversion. -/
theorem cube_completion_weighted_inverse (x : EisensteinIdealPrime → ℂ)
    (A : ComplexIdealSeries) (S : Finset EisensteinIdealExponent) (W : ℝ → ℂ) :
    (∑ ν ∈ S, W (idealExponentNorm ν)*
      ∑ d ∈ Finset.HasAntidiagonal.antidiagonal ν,
        MvPowerSeries.coeff d.1 (cubeInverseCompletionSeries x)*
          ∑ e ∈ Finset.HasAntidiagonal.antidiagonal d.2,
            MvPowerSeries.coeff e.1 (cubeCompletionSeries x)*MvPowerSeries.coeff e.2 A) =
      ∑ ν ∈ S, W (idealExponentNorm ν)*MvPowerSeries.coeff ν A := by
  apply Finset.sum_congr rfl
  intro ν _
  rw [cube_completion_finite_inverse]

private lemma primary_nat_pow {a : Eisenstein} (ha : primary a) (k : ℕ) :
    primary (a^k) := by
  induction k with
  | zero => simp [primary]
  | succ k ih => simpa only [pow_succ] using primary_mul ih ha

lemma idealPrimaryGenerator_eq_normalized_prime_product {a : Eisenstein}
    (ha : primary a) {ν : EisensteinIdealExponent} (hν : ν ≤ idealExponentOf a) :
    idealPrimaryGenerator ν =
      ν.prod (fun p k => primaryNormalize (idealPrimeRepresentative p)^k) := by
  have hpp (p : EisensteinIdealPrime) (hp : p ∈ ν.support) :
      primary (primaryNormalize (idealPrimeRepresentative p)) := by
    apply primaryNormalize_primary
    apply unit_residue_of_dvd_primary ha
    apply (idealPrime_dvd_iff (primary_ne_zero ha) p).mpr
    have hpos : 0 < ν p := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hp)
    exact hpos.trans_le (hν p)
  have hp : primary (ν.prod (fun p k => primaryNormalize (idealPrimeRepresentative p)^k)) :=
    primary_finset_prod _ _ (fun p hp => primary_nat_pow (hpp p hp) _)
  apply primary_associated_eq (idealPrimaryGenerator_primary ha hν) hp
  apply (primaryNormalize_associated _).symm.trans
  unfold idealExponentGenerator
  exact Associated.prod _ _ _ (fun p _ => Associated.pow_pow (n := ν p)
    (primaryNormalize_associated (idealPrimeRepresentative p)))

lemma normalized_prime_product_character {a : Eisenstein} (ha : primary a)
    {ν : EisensteinIdealExponent} (hν : ν ≤ idealExponentOf a)
    (χ : Eisenstein → ℂ) (h1 : χ 1 = 1)
    (hχ : ∀ x y, primary x → primary y → χ (x*y) = χ x*χ y) :
    ν.prod (fun p k => (χ (primaryNormalize (idealPrimeRepresentative p)))^k) =
      χ (idealPrimaryGenerator ν) := by
  rw [idealPrimaryGenerator_eq_normalized_prime_product ha hν]
  have hp (p : EisensteinIdealPrime) (hpm : p ∈ ν.support) :
      primary (primaryNormalize (idealPrimeRepresentative p)) := by
    apply primaryNormalize_primary
    apply unit_residue_of_dvd_primary ha
    apply (idealPrime_dvd_iff (primary_ne_zero ha) p).mpr
    exact (Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hpm)).trans_le (hν p)
  have hpow (b : Eisenstein) (hb : primary b) (k : ℕ) : χ (b^k) = (χ b)^k := by
    induction k with
    | zero => simpa using h1
    | succ k ih => rw [pow_succ,hχ _ _ (primary_nat_pow hb k) hb,ih,pow_succ]
  change (∏ p ∈ ν.support, χ (primaryNormalize (idealPrimeRepresentative p))^ν p) =
    χ (∏ p ∈ ν.support, primaryNormalize (idealPrimeRepresentative p)^ν p)
  suffices hfin : ∀ S : Finset EisensteinIdealPrime,
      (∀ p ∈ S, primary (primaryNormalize (idealPrimeRepresentative p))) →
      (∏ p ∈ S, χ (primaryNormalize (idealPrimeRepresentative p))^ν p) =
        χ (∏ p ∈ S, primaryNormalize (idealPrimeRepresentative p)^ν p) from hfin _ hp
  intro S hS
  induction S using Finset.induction_on with
  | empty => simpa using h1.symm
  | @insert p S hps ih =>
    have hp' := hS p (Finset.mem_insert_self p S)
    have hS' : ∀ q ∈ S, primary (primaryNormalize (idealPrimeRepresentative q)) :=
      fun q hq => hS q (Finset.mem_insert_of_mem hq)
    rw [Finset.prod_insert hps,Finset.prod_insert hps,
      hχ _ _ (primary_nat_pow hp' _) (primary_finset_prod S _
        (fun q hq => primary_nat_pow (hS' q hq) _)),hpow _ hp']
    congr 1
    exact ih hS'

/-- The precise inverse-completion weight, including the norm phase
created by replacing the length by `U / (Nc)^3`. -/
def metaplecticCompletionWeight (r : Eisenstein) (ℓ : ℤ) (t : ℝ)
    (c : Eisenstein) : ℂ :=
  if IsCoprime c r then
    (Real.sqrt (norm c):ℂ)*theta (3*ℓ) c*(norm c:ℂ)^((3*t:ℝ)*Complex.I)
  else 0

@[simp] lemma metaplecticCompletionWeight_one (r : Eisenstein) (ℓ : ℤ) (t : ℝ) :
    metaplecticCompletionWeight r ℓ t 1 = 1 := by
  simp [metaplecticCompletionWeight,norm_one_eq,isCoprime_one_left]

lemma metaplecticCompletionWeight_mul (r : Eisenstein) (ℓ : ℤ) (t : ℝ)
    {a b : Eisenstein} (_ha : primary a) (_hb : primary b) :
    metaplecticCompletionWeight r ℓ t (a*b) =
      metaplecticCompletionWeight r ℓ t a*metaplecticCompletionWeight r ℓ t b := by
  unfold metaplecticCompletionWeight
  rw [IsCoprime.mul_left_iff]
  by_cases har : IsCoprime a r
  · by_cases hbr : IsCoprime b r
    · simp only [har,hbr,and_self,ite_true,norm_mul_eq,theta_mul,
        Real.sqrt_mul (norm_nonneg a),Complex.ofReal_mul]
      rw [Complex.mul_cpow_ofReal_nonneg (norm_nonneg a) (norm_nonneg b)]
      ring
    · simp [har,hbr]
  · simp [har]

/-- At a primary principal ideal the expanded inverse kernel has
exactly the arithmetic weight `mu(c)|c| theta_(3ell)(c)(Nc)^(3it)`.
There is no assumption that `c` is squarefree. -/
theorem cubeInverseCompletionSeries_at_primary (r : Eisenstein) (ℓ : ℤ) (t : ℝ)
    {c : Eisenstein} (hc : primary c) :
    MvPowerSeries.coeff (3 • idealExponentOf c)
      (cubeInverseCompletionSeries (fun p => metaplecticCompletionWeight r ℓ t
        (primaryNormalize (idealPrimeRepresentative p)))) =
      (idealMoebius c:ℂ)*metaplecticCompletionWeight r ℓ t c := by
  rw [cubeInverseCompletionSeries_coeff,normalized_prime_product_character hc le_rfl
    (metaplecticCompletionWeight r ℓ t) (metaplecticCompletionWeight_one r ℓ t)
    (fun _ _ ha hb => metaplecticCompletionWeight_mul r ℓ t ha hb),
    idealPrimaryGenerator_at_element hc,idealMoebiusSeries_at_element (primary_ne_zero hc)]
  push_cast
  ring

theorem cubeCompletionSeries_at_primary (r : Eisenstein) (ℓ : ℤ) (t : ℝ)
    {c : Eisenstein} (hc : primary c) :
    MvPowerSeries.coeff (3 • idealExponentOf c)
      (cubeCompletionSeries (fun p => metaplecticCompletionWeight r ℓ t
        (primaryNormalize (idealPrimeRepresentative p)))) =
      metaplecticCompletionWeight r ℓ t c := by
  rw [cubeCompletionSeries_coeff,normalized_prime_product_character hc le_rfl
    (metaplecticCompletionWeight r ℓ t) (metaplecticCompletionWeight_one r ℓ t)
    (fun _ _ ha hb => metaplecticCompletionWeight_mul r ℓ t ha hb),
    idealPrimaryGenerator_at_element hc]

lemma norm_metaplecticCompletionWeight {c : Eisenstein} (hc : primary c)
    (r : Eisenstein) (ℓ : ℤ) (t : ℝ) :
    ‖metaplecticCompletionWeight r ℓ t c‖ =
      if IsCoprime c r then Real.sqrt (norm c) else 0 := by
  unfold metaplecticCompletionWeight
  split_ifs
  · rw [norm_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _),norm_theta (primary_ne_zero hc),mul_one,
      Complex.norm_cpow_eq_rpow_re_of_pos (norm_pos_of_ne_zero (primary_ne_zero hc))]
    simp
  · exact norm_zero

theorem norm_cubeInverseCompletionSeries_at_primary
    (r : Eisenstein) (ℓ : ℤ) (t : ℝ) {c : Eisenstein} (hc : primary c) :
    ‖MvPowerSeries.coeff (3 • idealExponentOf c)
      (cubeInverseCompletionSeries (fun p => metaplecticCompletionWeight r ℓ t
        (primaryNormalize (idealPrimeRepresentative p))))‖ ≤ Real.sqrt (norm c) := by
  rw [cubeInverseCompletionSeries_at_primary r ℓ t hc,norm_mul]
  have hmu : ‖(idealMoebius c:ℂ)‖ ≤ 1 := by
    have h := idealMoebiusSeries_abs_le_one (idealExponentOf c)
    rw [idealMoebiusSeries_at_element (primary_ne_zero hc)] at h
    have he : (idealMoebius c:ℂ) = ((idealMoebius c:ℝ):ℂ) := by norm_cast
    rw [he,Complex.norm_real,Real.norm_eq_abs]
    exact h
  have hw : ‖metaplecticCompletionWeight r ℓ t c‖ ≤ Real.sqrt (norm c) := by
    rw [norm_metaplecticCompletionWeight hc]
    split_ifs
    · rfl
    · exact Real.sqrt_nonneg _
  exact (mul_le_mul_of_nonneg_right hmu (_root_.norm_nonneg _)).trans (by simpa using hw)

end CubicFirstMoment

end

end OAI
