import OAI.NumberTheory.TotientAsymptotic.RowCutoffModel

namespace OAI

/-! The projected simplex factor absorbs the complete residual mass. -/
noncomputable section
namespace TotientAsymptotic

lemma projected_gaussian_bound {J r : ℝ} (hJ : 0 < J) (hr : 0 < r)
    (hsmall : r ≤ Real.exp (-3/5:ℝ)) (k : ℕ) :
    J^(k+1)*r^((k+1)*k/2)*Real.exp ((k:ℝ)^2/21) ≤
      Real.exp (105*(Real.log J)^2+Real.log J)*Real.exp (-(k:ℝ)^2/4) := by
  let n := (k+1)*k/2
  have hn : n*2=(k+1)*k := Nat.div_mul_cancel (by
    simpa only [Nat.mul_comm] using Nat.two_dvd_mul_add_one k)
  have hnR := congrArg (fun a : ℕ => (a:ℝ)) hn
  norm_num only [Nat.cast_mul,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat] at hnR
  have hlog := Real.log_le_log hr hsmall
  rw [Real.log_exp] at hlog
  have hlogn := mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg n : (0:ℝ)≤n)
  have hJexp : J^(k+1)=Real.exp (((k:ℝ)+1)*Real.log J) := by
    simpa only [Nat.cast_add,Nat.cast_one,Real.exp_log hJ] using
      (Real.exp_nat_mul (Real.log J) (k+1)).symm
  have hrexp : r^n=Real.exp ((n:ℝ)*Real.log r) := by
    simpa only [Real.exp_log hr] using (Real.exp_nat_mul (Real.log r) n).symm
  change J^(k+1)*r^n*Real.exp ((k:ℝ)^2/21) ≤ _
  rw [hJexp,hrexp,← Real.exp_add,← Real.exp_add,← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hy := sq_nonneg ((k:ℝ)-210*Real.log J)
  have hk : (0:ℝ) ≤ k := Nat.cast_nonneg k
  nlinarith only [hlogn,hnR,hy,hk]

lemma projected_row_mass_bound {J r F : ℝ} (hJ : 0 < J) (hr : 0 < r)
    (hsmall : r ≤ Real.exp (-3/5:ℝ)) (hF : 0 ≤ F) (k : ℕ) :
    J^(k+1)*r^((k+1)*k/2)*
      Real.exp (10*(Real.log (rowMassCutoffHeight F (rowModelDecay k)+4))^2) ≤
    Real.exp (210*(rowModelConstant F)^2+105*(Real.log J)^2+Real.log J)*
      Real.exp (-(k:ℝ)^2/4) := by
  have hb := Real.exp_le_exp.mpr (row_model_mass_exponent_bound hF (Nat.cast_nonneg k))
  have hfactor : 0 ≤ J^(k+1)*r^((k+1)*k/2) := by positivity
  calc
    _ ≤ J^(k+1)*r^((k+1)*k/2)*
        Real.exp ((k:ℝ)^2/21+210*(rowModelConstant F)^2) :=
      mul_le_mul_of_nonneg_left hb hfactor
    _ = Real.exp (210*(rowModelConstant F)^2)*
        (J^(k+1)*r^((k+1)*k/2)*Real.exp ((k:ℝ)^2/21)) := by
      rw [Real.exp_add]
      ring
    _ ≤ Real.exp (210*(rowModelConstant F)^2)*
        (Real.exp (105*(Real.log J)^2+Real.log J)*Real.exp (-(k:ℝ)^2/4)) :=
      mul_le_mul_of_nonneg_left (projected_gaussian_bound hJ hr hsmall k) (Real.exp_pos _).le
    _ = _ := by rw [← mul_assoc,← Real.exp_add]; congr 2; ring

end TotientAsymptotic

end

end OAI
