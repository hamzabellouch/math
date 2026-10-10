import OAI.NumberTheory.Ostmann.Arithmetic.ScaleBudget

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistoryGiantCompensationError
open Filter

def rawLogBudget (C L : ℝ) : ℝ :=
  C*(L+1)^2*Real.exp ((1/100:ℝ)*L)

theorem rawLogBudget_nonneg {C L : ℝ} (hC : 0 ≤ C) :
    0 ≤ rawLogBudget C L := by unfold rawLogBudget; positivity

theorem weighted_error_eventually (A C : ℝ) (hA : 0 ≤ A) (hC : 0 ≤ C) :
    ∀ᶠ L : ℝ in atTop, ∀ J F : ℝ,
      0 ≤ J → J ≤ Real.exp (rawLogBudget A L) →
      0 ≤ F → F ≤ Real.exp (rawLogBudget C L) →
      J*F*(30*Real.exp (-Real.exp (ScaleBudget.giant.target*L))) ≤
        Real.exp (-Real.exp ((21/2000:ℝ)*L)) := by
  have herr := ScaleBudget.eventually_double_exp_error (4*(A+C+30)) 2
    (a := (1/100:ℝ)) (b := (13/1000:ℝ)) (d := (21/2000:ℝ)) (c := 1)
    (by norm_num) (by norm_num) (by norm_num)
  filter_upwards [herr,eventually_ge_atTop (1:ℝ)] with L he hL
  intro J F hJ hJA hF hFC
  have heL : 1 ≤ Real.exp ((1/100:ℝ)*L) := Real.one_le_exp (by linarith)
  have hsq : 1 ≤ (L+1)^2 := by nlinarith
  have hsq' : (L+1)^2 ≤ 4*L^2 := by nlinarith
  have hunit : 1 ≤ (L+1)^2*Real.exp ((1/100:ℝ)*L) := one_le_mul_of_one_le_of_one_le hsq heL
  have h30 : (30:ℝ) ≤ Real.exp 30 := by linarith [Real.add_one_le_exp (30:ℝ)]
  have hbase : rawLogBudget A L+rawLogBudget C L+30 ≤
      4*(A+C+30)*L^2*Real.exp ((1/100:ℝ)*L) := by
    have hx := mul_le_mul_of_nonneg_left hsq' (by positivity : 0 ≤ A+C+30)
    have hy := mul_le_mul_of_nonneg_right hx (Real.exp_nonneg ((1/100:ℝ)*L))
    unfold rawLogBudget
    nlinarith
  calc
    _ ≤ Real.exp (rawLogBudget A L)*Real.exp (rawLogBudget C L)*
        (Real.exp 30*Real.exp (-Real.exp (ScaleBudget.giant.target*L))) :=
      mul_le_mul (mul_le_mul hJA hFC hF (Real.exp_nonneg _))
        (mul_le_mul_of_nonneg_right h30 (Real.exp_nonneg _)) (by positivity) (by positivity)
    _ = Real.exp (-Real.exp (ScaleBudget.giant.target*L)+
        (rawLogBudget A L+rawLogBudget C L+30)) := by
      rw [←Real.exp_add,←Real.exp_add,←Real.exp_add]
      congr 1
      ring
    _ ≤ Real.exp (-Real.exp ((13/1000:ℝ)*L)+
        4*(A+C+30)*L^2*Real.exp ((1/100:ℝ)*L)) := by
      apply Real.exp_le_exp.mpr
      simpa only [ScaleBudget.giant, add_comm] using add_le_add_left hbase
        (-Real.exp ((13/1000:ℝ)*L))
    _ ≤ _ := by simpa only [neg_one_mul] using he

end Ostmann.Arithmetic.HistoryGiantCompensationError

end

end OAI
