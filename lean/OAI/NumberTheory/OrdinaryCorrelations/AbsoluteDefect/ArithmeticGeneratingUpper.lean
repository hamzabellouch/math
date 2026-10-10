import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.BernoulliWeight
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.FloorIntersectionError

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

namespace OrdinaryCofactorWeight
open Finset

lemma arithmetic_generating_upper (P : Finset ℕ) (hP : ∀p∈P,Nat.Prime p)
    {N : ℕ} (hN : 0<N) {z : ℝ} (hz : z∈Set.Icc (0:ℝ) 1) :
    arithmeticGenerating P N z ≤
      Real.exp (-(1-z)*(∑p∈P,(p:ℝ)⁻¹))+2^P.card/(N:ℝ) := by
  have hv (p : ↥P) : 0≤(p:ℝ)⁻¹ ∧ (p:ℝ)⁻¹≤1 := by
    have hp : (1:ℝ)≤p := by exact_mod_cast (hP p p.property).one_le
    constructor
    · positivity
    · exact inv_le_one_of_one_le₀ hp
  have hh := generating_le_exp (fun p : ↥P => (p:ℝ)⁻¹) hv hz
  rw [generating_polynomial,Finset.sum_coe_sort P (fun p : ℕ => (p:ℝ)⁻¹)] at hh
  have he := arithmetic_generating_error P hP hN hz
  have hl := le_abs_self (arithmeticGenerating P N z-∏p : ↥P,(1-(1-z)*(p:ℝ)⁻¹))
  linarith

lemma continuous_arithmeticGenerating (P : Finset ℕ) (N : ℕ) :
    Continuous (arithmeticGenerating P N) := by
  unfold arithmeticGenerating
  fun_prop

theorem arithmetic_reciprocal_count_second_moment (P : Finset ℕ)
    (hP : ∀p∈P,Nat.Prime p) {N : ℕ} (hN : 0<N)
    (hL : 0<∑p∈P,(p:ℝ)⁻¹) :
    (∑n∈Finset.Icc 1 N,(N:ℝ)⁻¹/
      (((P.filter (fun p => p∣n)).card:ℝ)+1)^2)≤
      2/(∑p∈P,(p:ℝ)⁻¹)^2+2^P.card/(N:ℝ) := by
  let L : ℝ := ∑p∈P,(p:ℝ)⁻¹
  let E : ℝ := 2^P.card/(N:ℝ)
  have hE : 0≤E := by dsimp [E]; positivity
  have hb : (∫z in (0:ℝ)..1,2*(1-z))=1 := by
    simpa using beta_integral 0
  have he : (∫z in (0:ℝ)..1,2*(1-z)*(Real.exp (-(1-z)*L)+E))=
      (∫z in (0:ℝ)..1,2*(1-z)*Real.exp (-(1-z)*L))+E := by
    simp_rw [mul_add]
    rw [intervalIntegral.integral_add]
    · rw [intervalIntegral.integral_mul_const,hb,one_mul]
    · exact (by fun_prop : Continuous (fun z : ℝ =>
        2*(1-z)*Real.exp (-(1-z)*L))).intervalIntegrable _ _
    · exact (by fun_prop : Continuous (fun z : ℝ => 2*(1-z)*E)).intervalIntegrable _ _
  calc
    _ = ∑n∈Finset.Icc 1 N,(N:ℝ)⁻¹/(count (primeBits P n)+1:ℝ)^2 := by
      simp_rw [count_primeBits]
    _ ≤ ∑n∈Finset.Icc 1 N,(N:ℝ)⁻¹*
        (∫z in (0:ℝ)..1,2*(1-z)*z^count (primeBits P n)) := by
      apply sum_le_sum
      intro n hn
      simpa only [div_eq_mul_inv,one_mul,one_div] using
        mul_le_mul_of_nonneg_left (reciprocal_count_sq_le_beta (count (primeBits P n)))
          (by positivity : (0:ℝ)≤(N:ℝ)⁻¹)
    _ = ∫z in (0:ℝ)..1,2*(1-z)*arithmeticGenerating P N z := by
      simp_rw [←intervalIntegral.integral_const_mul]
      rw [←intervalIntegral.integral_finsetSum]
      · apply intervalIntegral.integral_congr
        intro z hz
        dsimp only [arithmeticGenerating]
        rw [mul_sum]
        apply sum_congr rfl
        intro n hn
        ring
      · intro n hn
        exact (by fun_prop : Continuous (fun z : ℝ =>
          (N:ℝ)⁻¹*(2*(1-z)*z^count (primeBits P n)))).intervalIntegrable _ _
    _ ≤ ∫z in (0:ℝ)..1,2*(1-z)*(Real.exp (-(1-z)*L)+E) := by
      apply intervalIntegral.integral_mono_on (by norm_num)
      · exact ((by fun_prop : Continuous (fun z : ℝ => 2*(1-z))).mul
          (continuous_arithmeticGenerating P N)).intervalIntegrable _ _
      · exact (by fun_prop : Continuous (fun z : ℝ =>
          2*(1-z)*(Real.exp (-(1-z)*L)+E))).intervalIntegrable _ _
      · intro z hz
        exact mul_le_mul_of_nonneg_left (arithmetic_generating_upper P hP hN hz)
          (by nlinarith [hz.2])
    _ ≤ _ := by
      rw [he]
      have hh := exponential_beta_bound hL
      dsimp only [L,E]
      linarith

theorem arithmetic_cofactor_second_moment (P : Finset ℕ)
    (hP : ∀p∈P,Nat.Prime p) {N : ℕ} (hN : 0<N)
    (hL : 0<∑p∈P,(p:ℝ)⁻¹) (f : ℕ → ℂ) (hf : ∀n,‖f n‖≤1) :
    (N:ℝ)⁻¹*∑n∈Finset.Icc 1 N,
      ‖f n/(((P.filter (fun p => p∣n)).card:ℂ)+1)‖^2 ≤
      2/(∑p∈P,(p:ℝ)⁻¹)^2+2^P.card/(N:ℝ) := by
  apply le_trans _ (arithmetic_reciprocal_count_second_moment P hP hN hL)
  rw [mul_sum]
  apply sum_le_sum
  intro n hn
  have hsq : ‖f n‖^2≤1 := by nlinarith [hf n,norm_nonneg (f n)]
  have hnrm : ‖(((P.filter (fun p => p∣n)).card:ℂ)+1)‖=
      (((P.filter (fun p => p∣n)).card:ℝ)+1) := by
    norm_cast
  rw [norm_div,hnrm,div_pow]
  have hh := div_le_div_of_nonneg_right hsq (by positivity :
    (0:ℝ)≤(((P.filter (fun p => p∣n)).card:ℝ)+1)^2)
  simpa only [one_div,div_eq_mul_inv,one_mul] using mul_le_mul_of_nonneg_left hh
    (by positivity : (0:ℝ)≤(N:ℝ)⁻¹)

end OrdinaryCofactorWeight

end

end OAI
