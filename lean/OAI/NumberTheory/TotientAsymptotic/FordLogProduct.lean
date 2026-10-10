import OAI.NumberTheory.TotientAsymptotic.FordBandExponent

namespace OAI

/-! Product-to-exponent identities for the logarithmic band costs. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma sum_predecessor_values {b : ℕ} (hb : 1 ≤ b) (v : ℕ → ℝ) :
    (∑ k ∈ Finset.Icc 2 b,v (k-1))=∑ j ∈ Finset.Icc 1 (b-1),v j := by
  induction b, hb using Nat.le_induction with
  | base => simp
  | succ b hb ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 2 ≤ b+1)]
    simp only [Nat.add_sub_cancel]
    rw [ih]
    conv_rhs => rw [← Nat.sub_add_cancel hb]
    rw [Finset.sum_Icc_succ_top (by omega)]
    simp only [Nat.sub_add_cancel hb]

lemma exp_two_B {U : ℝ} (hU : 1 < U) : Real.exp (2*B U)=(Real.log U)^2 := by
  simpa only [Nat.cast_ofNat,B,Real.exp_log (Real.log_pos hU)] using
    Real.exp_nat_mul (B U) 2

lemma ford_logarithmic_product {b : ℕ} (hb : 1 ≤ b)
    (y S : ℝ) (Y U : ℕ → ℝ) (hY : 1 < Y 1)
    (hU : ∀ j ∈ Finset.Icc 1 (b-1),1 < U j) :
    (Real.log (Y 1))⁻¹*
      (∏ k ∈ Finset.Icc 2 b,Real.exp (fordBandCap k y S Y*(Real.log k+1))/
        (Real.log (U (k-1)))^2)=
    Real.exp ((∑ k ∈ Finset.Icc 2 b,fordBandCap k y S Y*(Real.log k+1))-
      B (Y 1)-2*(∑ j ∈ Finset.Icc 1 (b-1),B (U j))) := by
  have he (k : ℕ) (hk : k ∈ Finset.Icc 2 b) :
      Real.exp (fordBandCap k y S Y*(Real.log k+1))/(Real.log (U (k-1)))^2=
      Real.exp (fordBandCap k y S Y*(Real.log k+1)-2*B (U (k-1))) := by
    rw [Real.exp_sub,exp_two_B (hU (k-1) (by obtain ⟨_,_⟩ := Finset.mem_Icc.mp hk; simp; omega))]
  rw [Finset.prod_congr rfl he,← Real.exp_sum]
  have hYexp : (Real.log (Y 1))⁻¹=Real.exp (-B (Y 1)) := by
    rw [Real.exp_neg,show Real.exp (B (Y 1))=Real.log (Y 1) by
      exact Real.exp_log (Real.log_pos hY)]
  rw [hYexp,← Real.exp_add,Finset.sum_sub_distrib,← Finset.mul_sum,
    sum_predecessor_values hb (fun j => B (U j))]
  congr 1
  ring

lemma ford_logarithmic_product_bound {b : ℕ} {y S : ℝ} (Y U : ℕ → ℝ)
    (hb : 1 ≤ b) (hy1 : 1 < y) (hy : 0 < B y) (hS : 0 ≤ B S) (hB : 0 ≤ B (Y b))
    (hY : 1 < Y 1) (hU : ∀ j ∈ Finset.Icc 1 (b-1),1 < U j) :
    (Real.log (Y 1))⁻¹*
      (∏ k ∈ Finset.Icc 2 b,Real.exp (fordBandCap k y S Y*(Real.log k+1))/
        (Real.log (U (k-1)))^2) ≤
    (Real.log y)^((∑ j ∈ Finset.Icc 1 (b-1),a j*(B (Y j)/B y))+
      comparisonError b y S Y U) := by
  have hlogy : 0 < Real.log y := Real.log_pos hy1
  rw [ford_logarithmic_product hb y S Y U hY hU,
    ford_band_exponent_identity hb y S Y U,Real.rpow_def_of_pos hlogy]
  apply Real.exp_le_exp.mpr
  have he : (∑ j ∈ Finset.Icc 1 (b-1),a j*(B (Y j)/B y))*B y=
      ∑ j ∈ Finset.Icc 1 (b-1),a j*B (Y j) := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    field_simp
  have herr := ford_comparison_error_mul hy hS Y U (b:=b)
  have hn := mul_nonneg (fordBandWeight_nonneg b) hB
  change _ ≤ B y*((∑ j ∈ Finset.Icc 1 (b-1),a j*(B (Y j)/B y))+
    comparisonError b y S Y U)
  nlinarith

end TotientAsymptotic

end

end OAI
