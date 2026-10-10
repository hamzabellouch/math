import OAI.NumberTheory.Ostmann.Arithmetic.PrimeCellFreezingLog

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistoryRepeatedSmoothPullback
open PrimeCellFreezing Characters.RationalHistory
open scoped BigOperators
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

omit [Fintype κ] in
theorem deriv_logCurve_comp_le (f : (ι → ℝ) → ℂ) (m : ι → κ)
    (x : κ → ℝ) (j : κ) (hx : ∀ i, 0 < x i) {D : ℝ} (hD : 0 ≤ D)
    (hf : DifferentiableAt ℝ (fun y => f (fun i => Real.exp (y i)))
      (fun i => Real.log (x (m i))))
    (hd : ∀ i, ‖deriv (fun t => f (Expr.logCurve (fun q => x (m q)) i t)) 0‖ ≤ D) :
    ‖deriv (fun t => f (fun i => Expr.logCurve x j t (m i))) 0‖ ≤ (Fintype.card ι:ℝ)*D := by
  classical
  let y : ι → ℝ := fun i => Real.log (x (m i))
  let v : ι → ℝ := fun i => if m i=j then 1 else 0
  let F : (ι → ℝ) → ℂ := fun z => f (fun i => Real.exp (z i))
  have hy : (fun i => Real.exp (y i)) = fun i => x (m i) := by
    funext i
    exact Real.exp_log (hx (m i))
  have hlin : ‖fderiv ℝ F y‖ ≤ (Fintype.card ι:ℝ)*D := by
    apply opNorm_le_card_mul _ hD
    intro i
    have he := logCurve_deriv_eq_fderiv f y i hf
    rw [hy] at he
    exact he ▸ hd i
  have hv : ‖v‖ ≤ 1 := (pi_norm_le_iff_of_nonneg zero_le_one).mpr (fun i => by
    dsimp only [v]
    split_ifs <;> norm_num)
  have hcurve := ((hasDerivAt_id (0:ℝ)).smul_const v).const_add y
  simp only [one_smul] at hcurve
  have hFy : HasFDerivAt F (fderiv ℝ F y) (y+(0:ℝ) • v) := by
    simpa only [zero_smul,add_zero] using hf.hasFDerivAt
  have hdF := (hFy.comp_hasDerivAt 0 hcurve).deriv
  simp only [Function.comp_def,id_eq] at hdF
  have heq : (fun t => f (fun i => Expr.logCurve x j t (m i))) =
      (fun t => F (y+t • v)) := by
    funext t
    congr 1
    funext i
    simp only [y,v,Expr.logCurve,Pi.add_apply,Pi.smul_apply,smul_eq_mul]
    split_ifs <;> simp [Real.exp_add,Real.exp_log (hx (m i))]
  rw [heq,hdF]
  exact ((fderiv ℝ F y).le_opNorm v).trans
    ((mul_le_mul hlin hv (norm_nonneg _) (by positivity)).trans_eq (mul_one _))

omit [DecidableEq ι] [Fintype κ] in
theorem differentiableAt_logCurve_comp (f : (ι → ℝ) → ℂ) (m : ι → κ)
    (x : κ → ℝ) (j : κ) (hx : ∀ i, 0 < x i)
    (hf : DifferentiableAt ℝ (fun y => f (fun i => Real.exp (y i)))
      (fun i => Real.log (x (m i)))) :
    DifferentiableAt ℝ (fun t => f (fun i => Expr.logCurve x j t (m i))) 0 := by
  let y : ι → ℝ := fun i => Real.log (x (m i))
  let v : ι → ℝ := fun i => if m i=j then 1 else 0
  have hcurve : DifferentiableAt ℝ (fun t : ℝ => y+t • v) 0 := by fun_prop
  have heq : (fun t => f (fun i => Expr.logCurve x j t (m i))) =
      (fun t => f (fun i => Real.exp ((y+t • v) i))) := by
    funext t
    congr 1
    funext i
    simp only [y,v,Expr.logCurve,Pi.add_apply,Pi.smul_apply,smul_eq_mul]
    split_ifs <;> simp [Real.exp_add,Real.exp_log (hx (m i))]
  rw [heq]
  have hf' : DifferentiableAt ℝ (fun z => f (fun i => Real.exp (z i))) (y+(0:ℝ) • v) := by
    simpa only [zero_smul,add_zero] using hf
  simpa only [Function.comp_def] using hf'.comp 0 hcurve

end Ostmann.Arithmetic.HistoryRepeatedSmoothPullback

end

end OAI
