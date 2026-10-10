import Mathlib
import OAI.NumberTheory.PrimePackets.IdealCoefficients

namespace OAI

section
noncomputable section
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal
open MeasureTheory Filter Set Module
universe u
open scoped TensorProduct
open Set Module
open MeasureTheory Set
open scoped ENNReal
open IsDiscreteValuationRing IsLocalRing
open scoped ENNReal BigOperators
open MeasureTheory Set IsDiscreteValuationRing
open Filter
open scoped BigOperators Topology
open NumberField
open scoped NumberField nonZeroDivisors
open scoped BigOperators ArithmeticFunction.zeta
open Finset
open scoped BigOperators Classical ArithmeticFunction.Moebius
open Finset Nat ArithmeticFunction BoundingSieve
open scoped BigOperators Classical
open Finset Nat
open scoped BigOperators
open Filter Topology
open scoped nonZeroDivisors
open Ideal NumberField Finset UniqueFactorizationMonoid
namespace PrimeDegreePackets

open scoped ArithmeticFunction.vonMangoldt

 
lemma vonMangoldt_floor_identity (N : ℕ) :
    (∑ d ∈ Icc 1 N, ArithmeticFunction.vonMangoldt d * (N / d : ℕ)) =
      ∑ m ∈ Icc 1 N, Real.log m := by
  have H := sum_divisors_initial (fun d _ => ArithmeticFunction.vonMangoldt d) N
  simpa only [ArithmeticFunction.vonMangoldt_sum, sum_const, Nat.card_Icc,
    Nat.add_sub_cancel, nsmul_eq_mul, mul_comm] using H.symm

lemma nat_floor_quotient_half {N d : ℕ} (hd : 0 < d) (hN : d ≤ N) :
    (N:ℝ) / (2*d) ≤ (N / d : ℕ) := by
  have hq : 1 ≤ N/d := (Nat.le_div_iff_mul_le hd).mpr (by simpa)
  have hlt : N < (N/d+1)*d := (Nat.div_lt_iff_lt_mul hd).mp (Nat.lt_succ_self _)
  have hn : N ≤ 2*(N/d)*d := by nlinarith
  apply (div_le_iff₀ (by positivity : (0:ℝ) < 2*d)).mpr
  have H : (N:ℝ) ≤ 2*(N/d:ℕ)*d := by exact_mod_cast hn
  nlinarith

 

theorem vonMangoldt_reciprocal_sum (N : ℕ) :
    (∑ d ∈ Icc 1 N, ArithmeticFunction.vonMangoldt d / d) ≤ 2 * Real.log N := by
  by_cases hN : N = 0
  · simp [hN]
  have hN0 : (0:ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
  have H : (N:ℝ)/2 * (∑ d ∈ Icc 1 N, ArithmeticFunction.vonMangoldt d / d) ≤
      (N:ℝ) * Real.log N := by
    calc
      _ = ∑ d ∈ Icc 1 N, ArithmeticFunction.vonMangoldt d * ((N:ℝ)/(2*d)) := by
        rw [mul_sum]
        apply sum_congr rfl
        intro d _
        ring
      _ ≤ ∑ d ∈ Icc 1 N, ArithmeticFunction.vonMangoldt d * (N/d:ℕ) := by
        apply sum_le_sum
        intro d hd
        exact mul_le_mul_of_nonneg_left
          (nat_floor_quotient_half (mem_Icc.mp hd).1 (mem_Icc.mp hd).2)
          ArithmeticFunction.vonMangoldt_nonneg
      _ = ∑ m ∈ Icc 1 N, Real.log m := vonMangoldt_floor_identity N
      _ ≤ (N:ℝ) * Real.log N := by
        calc
          _ ≤ ∑ _m ∈ Icc 1 N, Real.log N := by
            apply sum_le_sum
            intro m hm
            exact Real.log_le_log (by exact_mod_cast (mem_Icc.mp hm).1)
              (by exact_mod_cast (mem_Icc.mp hm).2)
          _ = _ := by simp
  nlinarith

 
lemma finite_euler_lower (f : ArithmeticFunction ℝ) (hf : f.IsMultiplicative)
    (hf0 : ∀m, 0 ≤ f m) (hs : Summable f) (S : Finset ℕ)
    (hS : ∀p ∈ S, p.Prime) :
    (∏ p ∈ S, (1 + f p)) ≤ ∑' m, f m := by
  have hnorm : Summable (fun m => ‖f m‖) := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hf0 _)] using hs
  calc
    _ ≤ ∏ p ∈ S, ∑'j : ℕ, f (p^j) := by
      apply Finset.prod_le_prod₀ (fun prime _ => by linarith [hf0 prime])
      intro p hp
      have hsp := hs.comp_injective (Nat.pow_right_injective (hS p hp).one_lt)
      have H := hsp.sum_le_tsum (range 2) (fun j _ => hf0 (p^j))
      simpa [sum_range_succ, hf.1] using H
    _ = ∑' m : Nat.factoredNumbers S, f m := by
      have H := EulerProduct.prod_filter_prime_tsum_eq_tsum_factoredNumbers hf.1
        (fun {_ _} h => hf.map_mul_of_coprime h) hnorm S
      simpa only [Finset.filter_true_of_mem hS] using H
    _ ≤ ∑' m, f m := by
      exact Summable.tsum_subtype_le f (Nat.factoredNumbers S) hf0 hs

lemma log_one_add_lower_quadratic (x : ℝ) (hx : 0 ≤ x) : x - x^2 ≤ Real.log (1+x) := by
  apply le_trans ?_ (Real.le_log_one_add_of_nonneg hx)
  apply (le_div_iff₀ (by linarith : (0:ℝ) < x+2)).mpr
  nlinarith [sq_nonneg x, mul_nonneg hx (sq_nonneg x)]

 

lemma prime_exp_le_euler (f : ArithmeticFunction ℝ) (hf : f.IsMultiplicative)
    (hf0 : ∀m, 0 ≤ f m) (hs : Summable f) (S : Finset ℕ)
    (hS : ∀p ∈ S, p.Prime) :
    Real.exp (∑p ∈ S, f p) ≤ Real.exp (∑p ∈ S, (f p)^2) * ∑'m, f m := by
  have H : (∑p ∈ S, f p) ≤ (∑p ∈ S, (f p)^2) + ∑p ∈ S, Real.log (1+f p) := by
    rw [← sum_add_distrib]
    apply sum_le_sum
    intro p _
    linarith [log_one_add_lower_quadratic (f p) (hf0 p)]
  calc
    _ ≤ Real.exp ((∑p ∈ S, (f p)^2) + ∑p ∈ S, Real.log (1+f p)) := Real.exp_le_exp.mpr H
    _ = Real.exp (∑p ∈ S, (f p)^2) * ∏p ∈ S, (1+f p) := by
      rw [Real.exp_add]
      congr 1
      rw [Real.exp_sum]
      apply prod_congr rfl
      intro p _
      exact Real.exp_log (by linarith [hf0 p])
    _ ≤ _ := mul_le_mul_of_nonneg_left (finite_euler_lower f hf hf0 hs S hS)
      (Real.exp_pos _).le

lemma realDirichletTerm_multiplicative {f : ArithmeticFunction ℝ}
    (hf : f.IsMultiplicative) (s : ℝ) : (realDirichletTerm f s).IsMultiplicative := by
  refine ⟨by simp [realDirichletTerm,hf.1], ?_⟩
  intro m n hmn
  simp only [realDirichletTerm, ArithmeticFunction.coe_mk,
    hf.map_mul_of_coprime hmn, Nat.cast_mul,
    Real.mul_rpow (Nat.cast_nonneg m) (Nat.cast_nonneg n), mul_div_mul_comm]

lemma realDirichletTerm_nonneg {f : ArithmeticFunction ℝ}
    (hf0 : ∀m, 0 ≤ f m) (s : ℝ) (m : ℕ) : 0 ≤ realDirichletTerm f s m := by
  exact div_nonneg (hf0 m) (Real.rpow_nonneg (Nat.cast_nonneg m) s)

lemma realDirichletTerm_le_div {f : ArithmeticFunction ℝ} (hf0 : ∀m, 0 ≤ f m)
    {s B : ℝ} (hs : 1 ≤ s) {m : ℕ} (hm : 1 ≤ m) (hB : f m ≤ B) :
    realDirichletTerm f s m ≤ B / m := by
  have hm0 : (0:ℝ) < m := by exact_mod_cast hm
  have hm1 : (1:ℝ) ≤ m := by exact_mod_cast hm
  calc
    _ ≤ f m / m := by
      apply div_le_div_of_nonneg_left (hf0 m) hm0
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hm1 hs
    _ ≤ _ := div_le_div_of_nonneg_right hB hm0.le

 
lemma prime_quadratic_sum_le {f : ArithmeticFunction ℝ} (hf0 : ∀m, 0 ≤ f m)
    {s B : ℝ} (hs : 1 ≤ s) (hB : ∀p, p.Prime → f p ≤ B)
    (S : Finset ℕ) (hS : ∀p ∈ S, p.Prime) :
    (∑p ∈ S, (realDirichletTerm f s p)^2) ≤ B^2 * ∑'m:ℕ, ((m:ℝ)^2)⁻¹ := by
  have hsum : Summable (fun m:ℕ => ((m:ℝ)^2)⁻¹) := Real.summable_nat_pow_inv.mpr (by norm_num)
  calc
    _ ≤ ∑p ∈ S, (B/(p:ℝ))^2 := by
      apply sum_le_sum
      intro p hp
      exact pow_le_pow_left₀ (realDirichletTerm_nonneg hf0 s p)
        (realDirichletTerm_le_div hf0 hs (hS p hp).one_le (hB p (hS p hp))) 2
    _ = B^2 * ∑p ∈ S, ((p:ℝ)^2)⁻¹ := by
      rw [mul_sum]
      apply sum_congr rfl
      intro p _
      simp only [div_eq_mul_inv, mul_pow, inv_pow]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (hsum.sum_le_tsum S (fun m _ => by positivity)) (sq_nonneg B)

 
lemma reciprocal_dirichlet_difference {x h : ℝ} (hx : 0 < x) :
    1/x - 1/x^(1+h) ≤ h * Real.log x / x := by
  have H := Real.add_one_le_exp (-h * Real.log x)
  have heq : 1/x^(1+h) = Real.exp (-h * Real.log x)/x := by
    rw [Real.rpow_add hx, Real.rpow_one, Real.rpow_def_of_pos hx h]
    rw [show -h * Real.log x = -(Real.log x * h) by ring, Real.exp_neg]
    field_simp
  rw [heq, ← sub_div]
  apply (div_le_div_iff_of_pos_right hx).mpr
  linarith

lemma prime_reciprocal_log_sum (N : ℕ) :
    (∑p ∈ (Finset.Icc 1 N).filter Nat.Prime, Real.log p / p) ≤ 2 * Real.log N := by
  calc
    _ = ∑p ∈ (Finset.Icc 1 N).filter Nat.Prime, ArithmeticFunction.vonMangoldt p / p := by
      apply sum_congr rfl
      intro p hp
      rw [ArithmeticFunction.vonMangoldt_apply_prime (mem_filter.mp hp).2]
    _ ≤ ∑d ∈ Icc 1 N, ArithmeticFunction.vonMangoldt d / d := by
      apply sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
      intro d _ _
      exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg d)
    _ ≤ _ := vonMangoldt_reciprocal_sum N

lemma shifted_prime_sum_le {f : ArithmeticFunction ℝ} (hf0 : ∀m, 0 ≤ f m)
    {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀p, p.Prime → f p ≤ B)
    {N : ℕ} (hN : 2 ≤ N) :
    (∑p ∈ (Finset.Icc 1 N).filter Nat.Prime, f p / p) ≤
      (∑p ∈ (Finset.Icc 1 N).filter Nat.Prime, realDirichletTerm f (1+1/Real.log N) p) + 2*B := by
  have hlog : 0 < Real.log N := Real.log_pos (by exact_mod_cast hN)
  have HH : (∑p ∈ (Finset.Icc 1 N).filter Nat.Prime,
      (f p / p - realDirichletTerm f (1+1/Real.log N) p)) ≤ 2*B := by
    calc
      _ ≤ ∑p ∈ (Finset.Icc 1 N).filter Nat.Prime, (B/Real.log N) * (Real.log p / p) := by
        apply sum_le_sum
        intro p hp
        have hpP := (mem_filter.mp hp).2
        have hp0 : (0:ℝ) < p := by exact_mod_cast hpP.pos
        have hpl : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hpP.one_le)
        calc
          _ = f p * (1/(p:ℝ) - 1/(p:ℝ)^(1+1/Real.log N)) := by
            simp only [realDirichletTerm,ArithmeticFunction.coe_mk]
            ring
          _ ≤ f p * ((1/Real.log N) * Real.log p / p) :=
            mul_le_mul_of_nonneg_left (reciprocal_dirichlet_difference hp0) (hf0 p)
          _ ≤ B * ((1/Real.log N) * Real.log p / p) := by
            exact mul_le_mul_of_nonneg_right (hB p hpP) (by positivity)
          _ = _ := by ring
      _ = (B/Real.log N) * ∑p ∈ (Finset.Icc 1 N).filter Nat.Prime, Real.log p / p :=
        (mul_sum _ _ _).symm
      _ ≤ (B/Real.log N) * (2*Real.log N) :=
        mul_le_mul_of_nonneg_left (prime_reciprocal_log_sum N) (div_nonneg hB0 hlog.le)
      _ = 2*B := by field_simp
  rw [sum_sub_distrib] at HH
  linarith

 

theorem prime_exponential_le_dirichlet {f : ArithmeticFunction ℝ}
    (hf : f.IsMultiplicative) (hf0 : ∀m, 0 ≤ f m)
    {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀p, p.Prime → f p ≤ B)
    {N : ℕ} (hN : 2 ≤ N)
    (hs : Summable (realDirichletTerm f (1+1/Real.log N))) :
    Real.exp (∑p ∈ (Finset.Icc 1 N).filter Nat.Prime, f p / p) ≤
      Real.exp (2*B + B^2 * ∑'m:ℕ, ((m:ℝ)^2)⁻¹) *
        ∑'m, realDirichletTerm f (1+1/Real.log N) m := by
  let S := (Finset.Icc 1 N).filter Nat.Prime
  have hS : ∀p ∈ S, p.Prime := fun _ hp => (mem_filter.mp hp).2
  have hlog : 0 < Real.log N := Real.log_pos (by exact_mod_cast hN)
  have H := prime_exp_le_euler (realDirichletTerm f (1+1/Real.log N))
    (realDirichletTerm_multiplicative hf _) (realDirichletTerm_nonneg hf0 _) hs S hS
  have HQ := prime_quadratic_sum_le hf0 (show 1 ≤ 1+1/Real.log N by linarith [one_div_pos.mpr hlog]) hB S hS
  calc
    _ ≤ Real.exp ((∑p ∈ S, realDirichletTerm f (1+1/Real.log N) p) + 2*B) :=
      Real.exp_le_exp.mpr (shifted_prime_sum_le hf0 hB0 hB hN)
    _ = Real.exp (2*B) * Real.exp (∑p ∈ S, realDirichletTerm f (1+1/Real.log N) p) := by
      rw [Real.exp_add,mul_comm]
    _ ≤ Real.exp (2*B) * (Real.exp (∑p ∈ S, (realDirichletTerm f (1+1/Real.log N) p)^2) *
        ∑'m, realDirichletTerm f (1+1/Real.log N) m) :=
      mul_le_mul_of_nonneg_left H (Real.exp_pos _).le
    _ ≤ Real.exp (2*B) * (Real.exp (B^2*∑'m:ℕ, ((m:ℝ)^2)⁻¹) *
        ∑'m, realDirichletTerm f (1+1/Real.log N) m) := by
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
      exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr HQ)
        (tsum_nonneg (realDirichletTerm_nonneg hf0 _))
    _ = _ := by rw [←mul_assoc,←Real.exp_add]

end PrimeDegreePackets


namespace PrimeDegreePackets
variable (K : Type*) [Field K] [NumberField K]

lemma idealCoefficientReal_prime_le {p : ℕ} (hp : p.Prime) :
    idealCoefficientReal K p ≤ (Module.finrank ℤ (𝓞 K) : ℝ) := by
  change (idealCoefficient K p : ℝ) ≤ (Module.finrank ℤ (𝓞 K) : ℝ)
  exact_mod_cast idealCoefficient_prime_le K hp

 

theorem ideal_prime_exponential_le_zeta {N : ℕ} (hN : 2 ≤ N) :
    Real.exp (∑p ∈ (Finset.Icc 1 N).filter Nat.Prime, idealCoefficientReal K p / p) ≤
      Real.exp (2*(Module.finrank ℤ (𝓞 K):ℝ) +
        (Module.finrank ℤ (𝓞 K):ℝ)^2 * ∑'m:ℕ, ((m:ℝ)^2)⁻¹) *
      (NumberField.dedekindZeta K (1+1/Real.log N)).re := by
  have hlog : 0 < Real.log N := Real.log_pos (by exact_mod_cast hN)
  have H := prime_exponential_le_dirichlet (idealCoefficientReal_multiplicative K)
    (idealCoefficientReal_nonneg K) (by positivity)
    (fun p hp => idealCoefficientReal_prime_le K hp) hN
    (idealCoefficient_real_summable K (by linarith [one_div_pos.mpr hlog]))
  have heq := congrArg Complex.re (idealDirichlet_eq_dedekindZeta K (1+1/Real.log N))
  simp only [Complex.ofReal_re] at heq
  rw [heq] at H
  simpa using H

end PrimeDegreePackets


namespace PrimeDegreePackets
variable (K : Type*) [Field K] [NumberField K]

 
def coprimeIdealCoefficient (q : ℕ) : ArithmeticFunction ℝ where
  toFun m := if m.Coprime q then idealCoefficientReal K m else 0
  map_zero' := by simp

lemma coprimeIdealCoefficient_multiplicative (q : ℕ) :
    (coprimeIdealCoefficient K q).IsMultiplicative := by
  refine ⟨by simp [coprimeIdealCoefficient,idealCoefficientReal,idealCoefficient_one], ?_⟩
  intro m n hmn
  simp only [coprimeIdealCoefficient,ArithmeticFunction.coe_mk,Nat.coprime_mul_iff_left]
  rw [(idealCoefficientReal_multiplicative K).map_mul_of_coprime hmn]
  split_ifs <;> simp_all

lemma coprimeIdealCoefficient_bounds (q m : ℕ) :
    0 ≤ coprimeIdealCoefficient K q m ∧
      coprimeIdealCoefficient K q m ≤
        (nFoldDivisor (Module.finrank ℤ (𝓞 K)+1) m : ℝ) := by
  simp only [coprimeIdealCoefficient,ArithmeticFunction.coe_mk]
  split_ifs
  · exact ⟨idealCoefficientReal_nonneg K m, by
      change (idealCoefficient K m : ℝ) ≤ _
      exact_mod_cast idealCoefficient_le_divisor K m⟩
  · exact ⟨le_rfl, Nat.cast_nonneg _⟩

lemma coprimeIdealCoefficient_le (q m : ℕ) :
    coprimeIdealCoefficient K q m ≤ idealCoefficientReal K m := by
  simp only [coprimeIdealCoefficient,ArithmeticFunction.coe_mk]
  split_ifs
  · exact le_rfl
  · exact idealCoefficientReal_nonneg K m

 

theorem coprime_ideal_relative_interval (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ η : ℝ, 0 < η → ∃ R : ℕ,
      ∀ (K : Type*) [Field K] [NumberField K], Module.finrank ℤ (𝓞 K) = n →
        ∀ q a b : ℕ, R ≤ b → a ≤ b → η*b ≤ (b:ℝ)-a →
          (∑m ∈ Ioc a b, coprimeIdealCoefficient K q m) ≤
            C * (((b:ℝ)-a)/Real.log b) *
              (NumberField.dedekindZeta K (1+1/Real.log b)).re := by
  obtain ⟨C,hC,hInt⟩ := Sieve.divisor_bounded_relative_interval n
  let E : ℝ := Real.exp (2*(n:ℝ)+(n:ℝ)^2 * ∑'m:ℕ, ((m:ℝ)^2)⁻¹)
  refine ⟨C*E, mul_pos hC (Real.exp_pos _), ?_⟩
  intro η hη
  obtain ⟨R,hR⟩ := hInt η hη
  refine ⟨max R 2, ?_⟩
  intro K _ _ hn q a b hb hab hrel
  have hb2 : 2 ≤ b := (le_max_right R 2).trans hb
  have hbR : R ≤ b := (le_max_left R 2).trans hb
  have hcoeff : ∀ m, 0 ≤ coprimeIdealCoefficient K q m ∧
      coprimeIdealCoefficient K q m ≤ (nFoldDivisor (n+1) m : ℝ) := by
    intro m
    simpa only [hn] using coprimeIdealCoefficient_bounds K q m
  have H := hR (coprimeIdealCoefficient K q)
    (coprimeIdealCoefficient_multiplicative K q) hcoeff a b hbR hab hrel
  have hpe : Real.exp (∑p ∈ Sieve.smallPrimes b, coprimeIdealCoefficient K q p / p) ≤
      E * (NumberField.dedekindZeta K (1+1/Real.log b)).re := by
    calc
      _ ≤ Real.exp (∑p ∈ Sieve.smallPrimes b, idealCoefficientReal K p / p) := by
        apply Real.exp_le_exp.mpr
        exact sum_le_sum (fun p _ => div_le_div_of_nonneg_right
          (coprimeIdealCoefficient_le K q p) (Nat.cast_nonneg p))
      _ ≤ _ := by simpa only [E,hn,Sieve.smallPrimes] using ideal_prime_exponential_le_zeta K hb2
  have hfactor : 0 ≤ C * (((b:ℝ)-a)/Real.log b) := by
    apply mul_nonneg hC.le
    apply div_nonneg
    · exact sub_nonneg.mpr (by exact_mod_cast hab)
    · exact (Real.log_pos (by exact_mod_cast hb2 : (1:ℝ) < b)).le
  calc
    _ ≤ C * (((b:ℝ)-a)/Real.log b) *
        Real.exp (∑p ∈ Sieve.smallPrimes b, coprimeIdealCoefficient K q p / p) := H
    _ ≤ C * (((b:ℝ)-a)/Real.log b) *
        (E * (NumberField.dedekindZeta K (1+1/Real.log b)).re) :=
      mul_le_mul_of_nonneg_left hpe hfactor
    _ = _ := by ring

end PrimeDegreePackets


namespace PrimeDegreePackets

 
def localEulerTailConstant (n : ℕ) : ℝ :=
  ∑' k : ℕ, ((n+1).multichoose (k+2) : ℝ) * (1/2:ℝ)^k

lemma multichoose_succ_eq (n k : ℕ) : (n+1).multichoose k = (k+n).choose n := by
  rw [Nat.multichoose_eq, show n+1+k-1 = k+n by omega]
  rw [← Nat.choose_symm (show k ≤ k+n by omega)]
  congr 1
  omega

lemma summable_multichoose_geometric (n : ℕ) :
    Summable (fun k : ℕ => ((n+1).multichoose k : ℝ) * (1/2:ℝ)^k) := by
  simp_rw [multichoose_succ_eq]
  exact summable_choose_mul_geometric_of_norm_lt_one n
    (by norm_num : ‖(1/2:ℝ)‖ < 1)

lemma summable_localEulerTailConstant (n : ℕ) :
    Summable (fun k : ℕ => ((n+1).multichoose (k+2) : ℝ) * (1/2:ℝ)^k) := by
  have hh : Function.Injective (fun k : ℕ => k+2) := fun a b h => Nat.add_right_cancel h
  have H := ((summable_multichoose_geometric n).comp_injective hh).mul_left (4:ℝ)
  apply H.congr
  intro k
  change 4 * (((n+1).multichoose (k+2) : ℝ)*(1/2:ℝ)^(k+2)) = _
  rw [pow_add]
  ring

lemma localEulerTailConstant_nonneg (n : ℕ) : 0 ≤ localEulerTailConstant n :=
  tsum_nonneg (fun _ => mul_nonneg (Nat.cast_nonneg _) (by positivity))

variable (K : Type*) [Field K] [NumberField K]

 

def idealPrimeEuler (p : ℕ) : ℝ :=
  ∑' k : ℕ, idealCoefficientReal K (p^k) / (p:ℝ)^k

lemma idealPrimeEuler_summable {p : ℕ} (hp : p.Prime) :
    Summable (fun k : ℕ => idealCoefficientReal K (p^k) / (p:ℝ)^k) := by
  have hp2 : (2:ℝ) ≤ p := by exact_mod_cast hp.two_le
  apply Summable.of_nonneg_of_le
    (fun _ => div_nonneg (idealCoefficientReal_nonneg K _) (by positivity))
    (fun k => ?_) (summable_multichoose_geometric (Module.finrank ℤ (𝓞 K)))
  calc
    _ ≤ (((Module.finrank ℤ (𝓞 K)+1).multichoose k : ℕ) : ℝ) / (p:ℝ)^k := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      change (idealCoefficient K (p^k) : ℝ) ≤ _
      rw [multichoose_succ_eq]
      exact_mod_cast idealCoefficient_prime_pow_le K hp k
    _ ≤ (((Module.finrank ℤ (𝓞 K)+1).multichoose k : ℕ) : ℝ) / (2:ℝ)^k := by
      exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by positivity)
        (pow_le_pow_left₀ (by norm_num) hp2 k)
    _ = _ := by simp [div_eq_mul_inv, ←inv_pow]

lemma idealPrimeEuler_one_le {p : ℕ} (hp : p.Prime) :
    1 ≤ idealPrimeEuler K p := by
  have H := (idealPrimeEuler_summable K hp).sum_le_tsum {0}
    (fun _ _ => div_nonneg (idealCoefficientReal_nonneg K _) (by positivity))
  simpa [idealPrimeEuler,idealCoefficientReal,idealCoefficient_one] using H

 

lemma idealPrimeEuler_le {p : ℕ} (hp : p.Prime) :
    idealPrimeEuler K p ≤ 1 + idealCoefficientReal K p / p +
      localEulerTailConstant (Module.finrank ℤ (𝓞 K)) / (p:ℝ)^2 := by
  have hp0 : (0:ℝ) < p := by exact_mod_cast hp.pos
  have hp2 : (2:ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hsum := idealPrimeEuler_summable K hp
  rw [idealPrimeEuler, ← hsum.sum_add_tsum_nat_add 2]
  have hfirst : (∑ k ∈ range 2, idealCoefficientReal K (p^k)/(p:ℝ)^k) =
      1 + idealCoefficientReal K p / p := by
    simp [sum_range_succ,idealCoefficientReal,idealCoefficient_one]
  rw [hfirst]
  apply add_le_add_right
  calc
    _ ≤ ∑' k : ℕ, (((Module.finrank ℤ (𝓞 K)+1).multichoose (k+2) : ℝ) *
        (1/2:ℝ)^k) / (p:ℝ)^2 := by
      apply Summable.tsum_le_tsum _ (hsum.comp_injective (show Function.Injective (fun k : ℕ => k+2) from
          fun a b h => Nat.add_right_cancel h))
        ((summable_localEulerTailConstant _).div_const _)
      intro k
      calc
        _ ≤ (((Module.finrank ℤ (𝓞 K)+1).multichoose (k+2) : ℕ) : ℝ) / (p:ℝ)^(k+2) := by
          apply div_le_div_of_nonneg_right _ (by positivity)
          change (idealCoefficient K (p^(k+2)) : ℝ) ≤ _
          rw [multichoose_succ_eq]
          exact_mod_cast idealCoefficient_prime_pow_le K hp (k+2)
        _ = ((((Module.finrank ℤ (𝓞 K)+1).multichoose (k+2) : ℕ) : ℝ) / (p:ℝ)^k) /
            (p:ℝ)^2 := by rw [pow_add,div_mul_eq_div_div]
        _ ≤ ((((Module.finrank ℤ (𝓞 K)+1).multichoose (k+2) : ℕ) : ℝ) / (2:ℝ)^k) /
            (p:ℝ)^2 := by
          apply div_le_div_of_nonneg_right _ (by positivity)
          exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by positivity)
            (pow_le_pow_left₀ (by norm_num) hp2 k)
        _ = _ := by simp [div_eq_mul_inv, ←inv_pow]
    _ = _ := by rw [tsum_div_const]; rfl

lemma log_idealPrimeEuler_le {p : ℕ} (hp : p.Prime) :
    Real.log (idealPrimeEuler K p) ≤ idealCoefficientReal K p / p +
      localEulerTailConstant (Module.finrank ℤ (𝓞 K)) / (p:ℝ)^2 := by
  have hpos : 0 < idealPrimeEuler K p := lt_of_lt_of_le zero_lt_one (idealPrimeEuler_one_le K hp)
  calc
    _ ≤ idealPrimeEuler K p - 1 := Real.log_le_sub_one_of_pos hpos
    _ ≤ _ := by linarith [idealPrimeEuler_le K hp]

 
def badPrimeEuler (q : ℕ) : ℝ := ∏ p ∈ q.primeFactors, idealPrimeEuler K p

lemma badPrimeEuler_pos (q : ℕ) : 0 < badPrimeEuler K q := by
  apply Finset.prod_pos
  intro p hp
  exact lt_of_lt_of_le zero_lt_one
    (idealPrimeEuler_one_le K (Nat.prime_of_mem_primeFactors hp))

lemma log_badPrimeEuler_le (q : ℕ) :
    Real.log (badPrimeEuler K q) ≤
      (∑p ∈ q.primeFactors, idealCoefficientReal K p / p) +
      localEulerTailConstant (Module.finrank ℤ (𝓞 K)) * ∑'m:ℕ, ((m:ℝ)^2)⁻¹ := by
  rw [badPrimeEuler, Real.log_prod (fun p hp => ne_of_gt
    (lt_of_lt_of_le zero_lt_one (idealPrimeEuler_one_le K (Nat.prime_of_mem_primeFactors hp))))]
  calc
    _ ≤ ∑p ∈ q.primeFactors, (idealCoefficientReal K p / p +
        localEulerTailConstant (Module.finrank ℤ (𝓞 K)) / (p:ℝ)^2) := by
      exact sum_le_sum (fun p hp => log_idealPrimeEuler_le K (Nat.prime_of_mem_primeFactors hp))
    _ = (∑p ∈ q.primeFactors, idealCoefficientReal K p / p) + localEulerTailConstant (Module.finrank ℤ (𝓞 K)) *
        ∑p ∈ q.primeFactors, ((p:ℝ)^2)⁻¹ := by
      rw [sum_add_distrib, mul_sum]
      simp only [div_eq_mul_inv]
    _ ≤ _ := by
      apply add_le_add_right
      apply mul_le_mul_of_nonneg_left _ (localEulerTailConstant_nonneg _)
      exact (Real.summable_nat_pow_inv.mpr (by norm_num : 1 < 2)).sum_le_tsum _
        (fun m _ => by positivity)

end PrimeDegreePackets
end
end

end OAI
