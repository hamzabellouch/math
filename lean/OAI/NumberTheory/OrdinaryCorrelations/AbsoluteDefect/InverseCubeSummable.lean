import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.ReciprocalHom

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
open ArithmeticFunction
open MeasureTheory Finset
open Classical
open Classical Finset

namespace OrdinaryCorrelations.SourceSieveEulerProduct
open Classical Finset

lemma inverse_cube_summable : Summable (fun n : ℕ => (n:ℝ)⁻¹^3) := by
  have h := Real.summable_nat_rpow.mpr (show (-3:ℝ) < -1 by norm_num)
  have he (n : ℕ) : (n:ℝ)^(-3:ℝ) = (n:ℝ)⁻¹^3 := by
    rw [show (-3:ℝ) = -(3:ℕ) by norm_num,Real.rpow_neg (Nat.cast_nonneg n),Real.rpow_natCast,inv_pow]
  simpa only [he] using h

lemma correction_sum_le (P : Finset ℕ) (hP : ∀ p ∈ P, 2 ≤ p) :
    (∑ p ∈ P, ((p:ℝ)-1)⁻¹^3) ≤ ∑' n : ℕ, (n:ℝ)⁻¹^3 := by
  have hcast (p : ℕ) (hp : p ∈ P) : ((p-1:ℕ):ℝ) = (p:ℝ)-1 := by
    rw [Nat.cast_sub (by have := hP p hp; omega),Nat.cast_one]
  have hi : ∀ x ∈ P, ∀ y ∈ P, x-1=y-1 → x=y := by
    intro x hx y hy hh
    have := hP x hx
    have := hP y hy
    omega
  have hb := inverse_cube_summable.sum_le_tsum (P.image (fun p => p-1))
    (fun n _ => by positivity)
  rw [Finset.sum_image (by exact hi)] at hb
  have he : (∑ p ∈ P, ((p-1:ℕ):ℝ)⁻¹^3) = ∑ p ∈ P, ((p:ℝ)-1)⁻¹^3 :=
    Finset.sum_congr rfl (fun p hp => by rw [hcast p hp])
  rwa [he] at hb

lemma local_four_factor (p : ℕ) (hp : 2 ≤ p) :
    (1-4/(p:ℝ)+6/(p:ℝ)^2-3/(p:ℝ)^3) =
      (1-(p:ℝ)⁻¹)^4 * (1+((p:ℝ)-1)⁻¹^3) := by
  have hpR : (2:ℝ) ≤ p := by exact_mod_cast hp
  have hp0 : (p:ℝ) ≠ 0 := by linarith
  have hp1 : (p:ℝ)-1 ≠ 0 := by linarith
  field_simp
  ring

lemma finite_four_correction (P : Finset ℕ) (hP : ∀ p ∈ P, 2 ≤ p) :
    (∏ p ∈ P, (1-4/(p:ℝ)+6/(p:ℝ)^2-3/(p:ℝ)^3)) ≤
      Real.exp (∑' n : ℕ, (n:ℝ)⁻¹^3) * (∏ p ∈ P, (1-(p:ℝ)⁻¹))^4 := by
  have he : (∏ p ∈ P, (1-4/(p:ℝ)+6/(p:ℝ)^2-3/(p:ℝ)^3)) =
      (∏ p ∈ P, (1-(p:ℝ)⁻¹))^4 * ∏ p ∈ P, (1+((p:ℝ)-1)⁻¹^3) := by
    calc
      _ = ∏ p ∈ P, ((1-(p:ℝ)⁻¹)^4 * (1+((p:ℝ)-1)⁻¹^3)) :=
        Finset.prod_congr rfl (fun p hp => local_four_factor p (hP p hp))
      _ = _ := by rw [Finset.prod_mul_distrib,Finset.prod_pow]
  have hc : (∏ p ∈ P, (1+((p:ℝ)-1)⁻¹^3)) ≤ Real.exp (∑' n : ℕ, (n:ℝ)⁻¹^3) := by
    calc
      _ ≤ ∏ p ∈ P, Real.exp (((p:ℝ)-1)⁻¹^3) := by
        apply Finset.prod_le_prod₀
        · intro p hp
          have hpR : (2:ℝ) ≤ p := by exact_mod_cast hP p hp
          have : 0 ≤ (p:ℝ)-1 := by linarith
          positivity
        · intro p _
          simpa only [add_comm] using Real.add_one_le_exp (((p:ℝ)-1)⁻¹^3)
      _ = Real.exp (∑ p ∈ P, ((p:ℝ)-1)⁻¹^3) := (Real.exp_sum _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr (correction_sum_le P hP)
  rw [he,mul_comm]
  exact mul_le_mul_of_nonneg_right hc (by positivity)

theorem prime_four_product (N : ℕ) (hN : 1 ≤ N) :
    (∏ p ∈ (N+1).primesBelow, (1-4/(p:ℝ)+6/(p:ℝ)^2-3/(p:ℝ)^3)) ≤
      Real.exp (∑' n : ℕ, (n:ℝ)⁻¹^3) * (Real.log (N+1:ℕ))⁻¹^4 := by
  have hP (p : ℕ) (hp : p ∈ (N+1).primesBelow) := (Nat.prime_of_mem_primesBelow hp).two_le
  have hpos : 0 ≤ ∏ p ∈ (N+1).primesBelow, (1-(p:ℝ)⁻¹) := by
    apply Finset.prod_nonneg
    intro p hp
    have hpR : (1:ℝ) < p := by exact_mod_cast (Nat.prime_of_mem_primesBelow hp).one_lt
    have hi := (inv_lt_one₀ (show (0:ℝ)<p by linarith)).mpr hpR
    linarith
  exact (finite_four_correction _ hP).trans
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hpos (prime_product_le_log_inv N hN) 4)
      (Real.exp_pos _).le)

end OrdinaryCorrelations.SourceSieveEulerProduct

end

end OAI
