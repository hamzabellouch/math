import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.Count

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

lemma floor_intersection_error (N q : ℕ) (hN : 0<N) (hq : 0<q) :
    |((N/q:ℕ):ℝ)/N-(q:ℝ)⁻¹|≤(N:ℝ)⁻¹ := by
  have hNr : (0:ℝ)<N := by exact_mod_cast hN
  have hqr : (0:ℝ)<q := by exact_mod_cast hq
  have hl : (N:ℝ)/q-1≤((N/q:ℕ):ℝ) := by
    have he : (N:ℝ)<q*(((N/q:ℕ):ℝ)+1) := by exact_mod_cast Nat.lt_mul_div_succ N hq
    have hh : (N:ℝ)/q<((N/q:ℕ):ℝ)+1 := (div_lt_iff₀ hqr).mpr (by nlinarith [he])
    linarith
  have hu := Nat.cast_div_le (α:=ℝ) (m:=N) (n:=q)
  have he : (N:ℝ)/q/N=(q:ℝ)⁻¹ := by field_simp
  rw [abs_le]
  constructor
  · have hh := div_le_div_of_nonneg_right hl hNr.le
    rw [sub_div,he,one_div] at hh
    linarith
  · have hh := div_le_div_of_nonneg_right hu hNr.le
    rw [he] at hh
    have hi : (0:ℝ)≤(N:ℝ)⁻¹ := by positivity
    linarith

theorem arithmetic_generating_error (P : Finset ℕ) (hP : ∀p∈P,Nat.Prime p)
    {N : ℕ} (hN : 0<N) {z : ℝ} (hz : z∈Set.Icc (0:ℝ) 1) :
    |arithmeticGenerating P N z-∏p : ↥P,(1-(1-z)*(p:ℝ)⁻¹)|≤2^P.card/(N:ℝ) := by
  rw [arithmetic_expansion P hP,polynomial_expansion,←sum_sub_distrib]
  calc
    _ ≤ ∑t∈(univ : Finset ↥P).powerset,
        |(z-1)^t.card*(((N/(∏p∈t,(p:ℕ)):ℕ):ℝ)/N)-
          (z-1)^t.card*(∏p∈t,(p:ℝ)⁻¹)| := abs_sum_le_sum_abs _ _
    _ ≤ ∑t∈(univ : Finset ↥P).powerset,(N:ℝ)⁻¹ := by
      apply sum_le_sum
      intro t ht
      rw [←mul_sub,abs_mul,abs_pow]
      have he : (∏p∈t,(p:ℝ)⁻¹)=((∏p∈t,(p:ℕ):ℕ):ℝ)⁻¹ := by
        simp only [Nat.cast_prod,prod_inv_distrib]
      rw [he]
      have hc : |z-1|^t.card≤1 := by
        apply pow_le_one₀ (abs_nonneg _)
        rw [abs_le]
        constructor <;> linarith [hz.1,hz.2]
      have hq : 0<∏p∈t,(p:ℕ) := prod_pos (fun p _ => (hP p p.property).pos)
      calc
        _ ≤ 1*(N:ℝ)⁻¹ := mul_le_mul hc (floor_intersection_error N _ hN hq)
          (abs_nonneg _) (by norm_num)
        _ = _ := one_mul _
    _ = _ := by simp [div_eq_mul_inv]

end OrdinaryCofactorWeight

end

end OAI
