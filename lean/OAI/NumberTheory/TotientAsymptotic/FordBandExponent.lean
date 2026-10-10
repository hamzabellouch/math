import OAI.NumberTheory.TotientAsymptotic.FordStateIteration

namespace OAI

/-! Exact telescoping of the band exponents into Ford's coefficients. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

def fordBandWeight (k : ℕ) : ℝ := (k:ℝ)*Real.log k+k

lemma fordBandWeight_succ (k : ℕ) :
    fordBandWeight (k+1)-fordBandWeight k-2=a k := by
  simp only [fordBandWeight,a,Nat.cast_add,Nat.cast_one]
  ring

lemma fordBandWeight_nonneg (k : ℕ) : 0 ≤ fordBandWeight k := by
  by_cases hk : k=0
  · simp [fordBandWeight,hk]
  · have hk1 : (1:ℝ) ≤ k := by exact_mod_cast (show 1 ≤ k by omega)
    exact add_nonneg (mul_nonneg (by positivity) (Real.log_nonneg hk1)) (by positivity)

lemma ford_band_exponent_telescope {b : ℕ} (hb : 1 ≤ b) (v : ℕ → ℝ) :
    (∑ k ∈ Finset.Icc 2 b,fordBandWeight k*(v (k-1)-v k))-v 1-
      2*(∑ j ∈ Finset.Icc 1 (b-1),v j)=
    (∑ j ∈ Finset.Icc 1 (b-1),a j*v j)-fordBandWeight b*v b := by
  induction b, hb using Nat.le_induction with
  | base => simp [fordBandWeight]
  | succ b hb ih =>
    have hv : (∑ j ∈ Finset.Icc 1 b,v j)=
        (∑ j ∈ Finset.Icc 1 (b-1),v j)+v b := by
      conv_lhs => rw [← Nat.sub_add_cancel hb]
      rw [Finset.sum_Icc_succ_top (by omega)]
      simp only [Nat.sub_add_cancel hb]
    have ha : (∑ j ∈ Finset.Icc 1 b,a j*v j)=
        (∑ j ∈ Finset.Icc 1 (b-1),a j*v j)+a b*v b := by
      conv_lhs => rw [← Nat.sub_add_cancel hb]
      rw [Finset.sum_Icc_succ_top (by omega)]
      simp only [Nat.sub_add_cancel hb]
    rw [Finset.sum_Icc_succ_top (by omega : 2 ≤ b+1)]
    simp only [Nat.add_sub_cancel]
    rw [hv,ha]
    have hw := congrArg (fun z : ℝ => z*v b) (fordBandWeight_succ b)
    nlinarith

lemma ford_band_exponent_identity {b : ℕ} (hb : 1 ≤ b)
    (y S : ℝ) (Y U : ℕ → ℝ) :
    (∑ k ∈ Finset.Icc 2 b,fordBandCap k y S Y*(Real.log k+1))-
      B (Y 1)-2*(∑ j ∈ Finset.Icc 1 (b-1),B (U j))=
    (∑ j ∈ Finset.Icc 1 (b-1),a j*B (Y j))+
      2*(∑ j ∈ Finset.Icc 1 (b-1),(B (Y j)-B (U j)))+
      Real.sqrt (B S*B y)*(∑ k ∈ Finset.Icc 2 b,fordBandWeight k)-
      fordBandWeight b*B (Y b) := by
  have hsplit : (∑ k ∈ Finset.Icc 2 b,fordBandCap k y S Y*(Real.log k+1))=
      (∑ k ∈ Finset.Icc 2 b,fordBandWeight k*(B (Y (k-1))-B (Y k)))+
      Real.sqrt (B S*B y)*(∑ k ∈ Finset.Icc 2 b,fordBandWeight k) := by
    rw [Finset.mul_sum,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    dsimp [fordBandCap,fordBandWeight]
    ring
  rw [hsplit,Finset.sum_sub_distrib]
  have hh := ford_band_exponent_telescope hb (fun k => B (Y k))
  linarith

lemma ford_comparison_error_mul {b : ℕ} {y S : ℝ} (hy : 0 < B y) (hS : 0 ≤ B S)
    (Y U : ℕ → ℝ) :
    comparisonError b y S Y U*B y=
      2*(∑ j ∈ Finset.Icc 1 (b-1),(B (Y j)-B (U j)))+
      Real.sqrt (B S*B y)*(∑ k ∈ Finset.Icc 2 b,fordBandWeight k) := by
  have hs : Real.sqrt (B S/B y)*B y=Real.sqrt (B S*B y) := by
    rw [Real.sqrt_div hS,Real.sqrt_mul hS]
    have hyroot : Real.sqrt (B y) ≠ 0 := (Real.sqrt_pos.2 hy).ne'
    have hsq := Real.sq_sqrt hy.le
    field_simp
    rw [hsq]
  unfold comparisonError
  rw [add_mul,mul_assoc,Finset.sum_mul]
  have he : (∑ j ∈ Finset.Icc 1 (b-1),(B (Y j)/B y-B (U j)/B y)*B y)=
      ∑ j ∈ Finset.Icc 1 (b-1),(B (Y j)-B (U j)) := by
    apply Finset.sum_congr rfl
    intro j _
    field_simp
  rw [he]
  change _+Real.sqrt (B S/B y)*(∑ k ∈ Finset.Icc 2 b,fordBandWeight k)*B y=_
  rw [mul_right_comm _ _ (B y),hs]

end TotientAsymptotic

end

end OAI
