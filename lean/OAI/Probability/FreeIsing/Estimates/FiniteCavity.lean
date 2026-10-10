import OAI.Probability.FreeIsing.Cavity.LogOdds

namespace OAI

noncomputable section

namespace Problem367

theorem binary_mean_eq_tanh_half_log {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (a - b) / (a + b) = Real.tanh ((Real.log a - Real.log b) / 2) := by
  have hab : 0 < a + b := add_pos ha hb
  have hmem : (a - b) / (a + b) ∈ Set.Ioo (-1 : ℝ) 1 := by
    constructor
    · apply (lt_div_iff₀ hab).2
      linarith
    · apply (div_lt_iff₀ hab).2
      linarith
  have hratio : (1 + (a - b) / (a + b)) / (1 - (a - b) / (a + b)) = a / b := by
    apply (div_eq_div_iff (by linarith [hmem.2]) hb.ne').2
    field_simp
    ring
  have hfield : Real.artanh ((a - b) / (a + b)) = (Real.log a - Real.log b) / 2 := by
    rw [Real.artanh_eq_half_log ⟨hmem.1.le, hmem.2.le⟩, hratio,
      Real.log_div ha.ne' hb.ne']
    ring
  rw [← hfield, Real.tanh_artanh hmem]

def finiteBranchWeight {I : Type*} (D : Finset I) (beta x : ℝ) (z : I → ℝ) (s : ℝ) : ℝ :=
  Real.exp (x * s) * ∏ i ∈ D, Real.cosh (z i + beta * s)

theorem finiteBranchWeight_pos {I : Type*} (D : Finset I) (beta x : ℝ)
    (z : I → ℝ) (s : ℝ) : 0 < finiteBranchWeight D beta x z s := by
  exact mul_pos (Real.exp_pos _) (Finset.prod_pos fun i _ => Real.cosh_pos _)

theorem log_finiteBranchWeight {I : Type*} (D : Finset I) (beta x : ℝ)
    (z : I → ℝ) (s : ℝ) :
    Real.log (finiteBranchWeight D beta x z s) =
      x * s + ∑ i ∈ D, Real.log (Real.cosh (z i + beta * s)) := by
  rw [finiteBranchWeight, Real.log_mul (Real.exp_pos _).ne'
    (Finset.prod_ne_zero_iff.mpr fun i _ => (Real.cosh_pos _).ne'), Real.log_exp,
    Real.log_prod (fun i _ => (Real.cosh_pos _).ne')]

theorem finiteBranchWeight_half_log_odds {I : Type*} (D : Finset I) (beta x : ℝ)
    (z : I → ℝ) :
    (Real.log (finiteBranchWeight D beta x z 1) -
      Real.log (finiteBranchWeight D beta x z (-1))) / 2 =
      x + ∑ i ∈ D, cavityMessage (Real.tanh beta) (z i) := by
  rw [log_finiteBranchWeight, log_finiteBranchWeight]
  simp only [mul_one, mul_neg_one, ← sub_eq_add_neg]
  have hsum : (∑ i ∈ D, Real.log (Real.cosh (z i + beta))) -
      (∑ i ∈ D, Real.log (Real.cosh (z i - beta))) =
      2 * ∑ i ∈ D, cavityMessage (Real.tanh beta) (z i) := by
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [cavityMessage_eq_log_cosh_sub beta (z i)]
    ring
  linarith

theorem finite_cavity_mean {I : Type*} (D : Finset I) (beta x : ℝ) (z : I → ℝ) :
    (finiteBranchWeight D beta x z 1 - finiteBranchWeight D beta x z (-1)) /
      (finiteBranchWeight D beta x z 1 + finiteBranchWeight D beta x z (-1)) =
      Real.tanh (x + ∑ i ∈ D, cavityMessage (Real.tanh beta) (z i)) := by
  rw [binary_mean_eq_tanh_half_log (finiteBranchWeight_pos D beta x z 1)
    (finiteBranchWeight_pos D beta x z (-1)), finiteBranchWeight_half_log_odds]

theorem finite_cavity_field {I : Type*} (D : Finset I) (beta x : ℝ) (z : I → ℝ) :
    Real.artanh ((finiteBranchWeight D beta x z 1 - finiteBranchWeight D beta x z (-1)) /
      (finiteBranchWeight D beta x z 1 + finiteBranchWeight D beta x z (-1))) =
      x + ∑ i ∈ D, cavityMessage (Real.tanh beta) (z i) := by
  rw [finite_cavity_mean, Real.artanh_tanh]

theorem finite_cavity_field_difference_bound {I : Type*} (D : Finset I)
    {beta : ℝ} (hbeta : 0 ≤ beta) (x : ℝ) (z : I → ℝ) :
    |Real.artanh ((finiteBranchWeight D beta x z 1 - finiteBranchWeight D beta x z (-1)) /
      (finiteBranchWeight D beta x z 1 + finiteBranchWeight D beta x z (-1))) - x| ≤
      (D.card : ℝ) * beta := by
  rw [finite_cavity_field, add_sub_cancel_left]
  calc
    |∑ i ∈ D, cavityMessage (Real.tanh beta) (z i)| ≤
        ∑ i ∈ D, |cavityMessage (Real.tanh beta) (z i)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ D, beta := Finset.sum_le_sum fun i _ => abs_cavityMessage_tanh_le hbeta (z i)
    _ = (D.card : ℝ) * beta := by simp

end Problem367

end

end OAI
