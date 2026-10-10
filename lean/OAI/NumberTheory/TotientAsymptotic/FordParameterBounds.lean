import OAI.NumberTheory.TotientAsymptotic.FordTerminalMass

namespace OAI

/-! Elementary quantitative consequences of Ford's separated cutoffs. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma sum_predecessor_diff {b : ℕ} (hb : 1 ≤ b) (v : ℕ → ℝ) :
    (∑ k ∈ Finset.Icc 2 b,(v (k-1)-v k))=v 1-v b := by
  induction b, hb using Nat.le_induction with
  | base => simp
  | succ b hb ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 2 ≤ b+1)]
    simp only [Nat.add_sub_cancel]
    rw [ih]
    ring

lemma ford_band_count_le {b D r : ℕ} {y S : ℝ} {Y U : ℕ → ℝ}
    (hp : FordComparisonParameters b y S D r Y U) : (b:ℝ) ≤ B y := by
  have hb := hp.1
  have hBy := ford_cutoff_B_one_le hp (k:=0) (by omega)
  rw [hp.2.1] at hBy
  have hS := (ford_scale_bounds hp).2
  have hroot : 1 ≤ Real.sqrt (B S/B y)*B y := by
    have he : Real.sqrt (B S/B y)*B y=Real.sqrt (B S*B y) := by
      rw [Real.sqrt_div (by linarith : 0 ≤ B S),Real.sqrt_mul (by linarith : 0 ≤ B S)]
      have hsq := Real.sq_sqrt (by linarith : 0 ≤ B y)
      have hpos : Real.sqrt (B y) ≠ 0 := (Real.sqrt_pos.2 (by linarith)).ne'
      field_simp
      rw [hsq]
    rw [he]
    exact Real.one_le_sqrt.mpr (by nlinarith)
  have hgap (k : ℕ) (hk : k ∈ Finset.Icc 2 b) : 1 ≤ B (Y (k-1))-B (Y k) := by
    have hh := hp.2.2.2.2.2.2.1 k hk
    have hh' := (mul_lt_mul_of_pos_right hh (by linarith : 0 < B y))
    have he : (B (Y (k-1))/B y-B (Y k)/B y)*B y=B (Y (k-1))-B (Y k) := by
      field_simp
    rw [he] at hh'
    nlinarith
  have hsum := Finset.sum_le_sum hgap
  have hcount : ((Finset.Icc 2 b).card:ℝ)=(b:ℝ)-1 := by
    simp only [Nat.card_Icc]
    rw [Nat.cast_sub (by omega)]
    push_cast
    ring
  have htotal : (b:ℝ)-1 ≤ B (Y 1)-B (Y b) := by
    simpa only [Finset.sum_const,nsmul_eq_mul,mul_one,hcount,sum_predecessor_diff hp.1 (fun j => B (Y j))]
      using hsum
  have hY : B (Y 1) ≤ B y := Real.log_le_log
    (Real.log_pos (by linarith [ford_cutoff_two_le hp hp.1]))
    (Real.log_le_log (by linarith [ford_cutoff_two_le hp hp.1]) (ford_cutoff_le_y hp hp.1))
  linarith [ford_cutoff_B_one_le hp (k:=b) le_rfl]

end TotientAsymptotic

end

end OAI
