import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.TupleEntryDvdLocation
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.ShiftedPowerLeExponential

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory intervalIntegral
open Finset
open Finset Nat ArithmeticFunction
open scoped ArithmeticFunction.Moebius
open Filter
open MeasureTheory Filter
open MeasureTheory
open MeasureTheory Set
open Set MeasureTheory Complex
open Set
open Finset Filter

namespace OrdinaryTwoScaleCofactor
open Finset OrdinaryDirichletMeanSquare OrdinaryPrimeDirichletMoments
open OrdinaryDirichletFiberMoments SourcePrimeFactor OrdinaryRestrictedCofactor

lemma modulation_norm_le_one {f : ℕ → ℂ} (hf : ∀n,‖f n‖≤1)
    {q : ℕ} (χ : DirichletCharacter ℂ q) (n : ℕ) :
    ‖characterModulation f χ n‖≤1 := by
  simp only [characterModulation,norm_mul,norm_star]
  exact (mul_le_of_le_one_left (norm_nonneg _) (hf n)).trans (χ.norm_le_one _)

lemma prime_coefficient_norm_le {f : ℕ → ℂ} (hf : ∀n,‖f n‖≤1)
    {q : ℕ} (χ : DirichletCharacter ℂ q) (p : ℕ) :
    ‖characterModulation f χ p/(p:ℂ)‖≤(p:ℝ)⁻¹ := by
  rw [norm_div,Complex.norm_natCast,←one_div]
  exact div_le_div_of_nonneg_right (modulation_norm_le_one hf χ p) (Nat.cast_nonneg p)

lemma cofactor_coefficient_norm_le {f : ℕ → ℂ} (hf : ∀n,‖f n‖≤1)
    {q : ℕ} (χ : DirichletCharacter ℂ q) (P : Finset ℕ) (n : ℕ) :
    ‖OrdinaryCofactorDyadicBound.coefficient P (characterModulation f χ) n‖≤
      (n:ℝ)⁻¹ := by
  have hd : ‖(((P.filter (fun p => p∣n)).card:ℂ)+1)‖ =
      ((P.filter (fun p => p∣n)).card:ℝ)+1 := by
    rw [←Nat.cast_one (R:=ℂ),←Nat.cast_add,Complex.norm_natCast,Nat.cast_add,Nat.cast_one]
  rw [OrdinaryCofactorDyadicBound.coefficient,norm_div,norm_div,hd,
    Complex.norm_natCast,←one_div]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
  apply (div_le_iff₀ (by positivity : 0<((P.filter (fun p => p∣n)).card:ℝ)+1)).mpr
  have hh := modulation_norm_le_one hf χ n
  nlinarith [Nat.cast_nonneg (α:=ℝ) (P.filter (fun p => p∣n)).card]

theorem mixedEnergy_arithmetic_moment {f : ℕ → ℂ} (hf : ∀n,‖f n‖≤1)
    {q : ℕ} (χ : DirichletCharacter ℂ q) (A P : Finset ℕ)
    (hA : ∀p∈A,Nat.Prime p) (k : ℕ) {M : ℕ} (hM : 0<M) :
    mixedEnergy f χ A P k M ≤
      (∑p∈A,((p:ℝ)⁻¹)^2)^k * (M:ℝ)⁻¹^2 *
        ∑m∈Icc 1 (2*M), ((primeCount A m+k:ℕ):ℝ)^k := by
  classical
  have hMr : 0<(M:ℝ) := by exact_mod_cast hM
  have hw (v : Fin k → A) (m : ℕ) (hm : m∈Finset.Ioc M (2*M)) :
      ‖mixedWeight f χ A P (v,m)‖^2 ≤
        (∏i,((v i:ℕ):ℝ)⁻¹^2)*(M:ℝ)⁻¹^2 := by
    rw [mixedWeight,norm_mul,mul_pow]
    apply mul_le_mul
    · simp only [tupleCoefficient,norm_prod,←Finset.prod_pow]
      apply Finset.prod_le_prod₀
      · intro i hi; positivity
      · intro i hi
        exact pow_le_pow_left₀ (norm_nonneg _) (prime_coefficient_norm_le hf χ (v i)) 2
    · apply pow_le_pow_left₀ (norm_nonneg _)
      apply (cofactor_coefficient_norm_le hf χ P m).trans
      exact inv_anti₀ hMr (by exact_mod_cast (Finset.mem_Ioc.mp hm).1.le)
    · positivity
    · positivity
  calc
    _ ≤ ∑z∈powersAndCofactors A k M,
        ((primeCount A z.2+k:ℕ):ℝ)^k*‖mixedWeight f χ A P z‖^2 :=
      mixedEnergy_count_bound f χ A P hA k M
    _ ≤ ∑z∈powersAndCofactors A k M,
        ((primeCount A z.2+k:ℕ):ℝ)^k*
          ((∏i,((z.1 i:ℕ):ℝ)⁻¹^2)*(M:ℝ)⁻¹^2) := by
      apply sum_le_sum
      intro z hz
      apply mul_le_mul_of_nonneg_left (hw z.1 z.2 (mem_product.mp hz).2)
      positivity
    _ = (∑p∈A,((p:ℝ)⁻¹)^2)^k * (M:ℝ)⁻¹^2 *
        ∑m∈Ioc M (2*M), ((primeCount A m+k:ℕ):ℝ)^k := by
      unfold powersAndCofactors
      rw [sum_product]
      simp_rw [mul_comm (((primeCount A _+k:ℕ):ℝ)^k),←mul_sum]
      rw [←sum_mul,←sum_mul,←Fintype.sum_pow (fun p : A => ((p:ℕ):ℝ)⁻¹^2) k]
      rw [sum_coe_sort A (fun p : ℕ => ((p:ℝ)⁻¹)^2)]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left
      · apply sum_le_sum_of_subset_of_nonneg
        · intro m hm; simp only [Finset.mem_Icc,Finset.mem_Ioc] at *; omega
        · intro m hm hm'; positivity
      · positivity

theorem mixedEnergy_explicit {f : ℕ → ℂ} (hf : ∀n,‖f n‖≤1)
    {q : ℕ} (χ : DirichletCharacter ℂ q) (A P : Finset ℕ)
    (hA : ∀p∈A,Nat.Prime p) (k : ℕ) {M : ℕ} (hM : 0<M)
    {a : ℝ} (ha : 0<a) :
    mixedEnergy f χ A P k M ≤
      (2/(M:ℝ))*(∑p∈A,((p:ℝ)⁻¹)^2)^k * ((k.factorial:ℝ)/a^k) *
        Real.exp (a*k+(Real.exp a-1)*(∑p∈A,(p:ℝ)⁻¹)) := by
  have hh := OrdinaryCofactorWeight.arithmetic_shifted_primeCount_moment A hA
    (show 0<2*M by omega) k ha
  have hb := mul_le_mul_of_nonneg_left hh
    (by positivity : 0≤(∑p∈A,((p:ℝ)⁻¹)^2)^k*(M:ℝ)⁻¹^2)
  apply (mixedEnergy_arithmetic_moment hf χ A P hA k hM).trans
  unfold primeCount
  apply hb.trans_eq
  have hMr : (M:ℝ)≠0 := by exact_mod_cast hM.ne'
  push_cast
  field_simp

end OrdinaryTwoScaleCofactor

end

end OAI
