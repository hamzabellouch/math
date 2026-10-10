import OAI.Analysis.FourierLLogL.Finite.Independent
/-! # Complex moments -/
open Function Set Filter
open scoped BigOperators ComplexConjugate
noncomputable section
namespace OAI

namespace FourierLLogL.Law
open Real
variable {α β γ I : Type} [Fintype α] [Fintype β] [Fintype γ] [Fintype I] [DecidableEq I]

def Cx (P : Law α) (f : α → ℂ) : ℂ := ∑ x, (P x:ℂ)*f x

lemma Cx_ofReal (P : Law α) (f : α → ℝ) : P.Cx (fun x => (f x:ℂ)) = ↑(P.Ex f) := by
  simp only [Cx,Ex, Complex.ofReal_sum, Complex.ofReal_mul]

lemma re_Cx (P : Law α) (f : α → ℂ) :
    (P.Cx f).re = P.Ex (fun x => (f x).re) := by
  simp [Cx,Ex,Complex.re_sum,Complex.mul_re]

lemma Cx_mul (P : Law α) (f : α → ℂ) (c : ℂ) : P.Cx (fun x => f x*c) = P.Cx f * c := by
  simp_rw [Cx, ← mul_assoc, Finset.sum_mul]

lemma Cx_lmul (P : Law α) (f : α → ℂ) (c : ℂ) : P.Cx (fun x => c*f x) = c*P.Cx f := by
  simpa only [mul_comm c] using P.Cx_mul f c

lemma Cx_conj (P : Law α) (f : α → ℂ) : P.Cx (fun x => conj (f x)) = conj (P.Cx f) := by
  simp only [Cx,map_sum,map_mul,Complex.conj_ofReal]

lemma Cx_norm (P : Law α) (f : α → ℂ) : ‖P.Cx f‖ ≤ P.Ex (fun x => ‖f x‖) := by
  unfold Cx
  refine (norm_sum_le _ _).trans ?_
  simp_rw [Ex,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (P.nonneg _)]
  exact le_rfl

lemma norm_Cx_unit (P : Law α) (f : α → ℂ) (h : ∀ x, ‖f x‖ ≤ 1) :
    ‖P.Cx f‖ ≤ 1 := (P.Cx_norm f).trans ((P.Ex_mono h).trans (P.Ex_const 1).le)

lemma Cx_swap (P : Law α) (Q : Law β) (f : α → β → ℂ) :
    P.Cx (fun x => Q.Cx (f x)) = Q.Cx (fun y => P.Cx (fun x => f x y)) := by
  unfold Cx
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro j _; ring

lemma Ex_swap (P : Law α) (Q : Law β) (f : α → β → ℝ) :
    P.Ex (fun x => Q.Ex (f x)) = Q.Ex (fun y => P.Ex (fun x => f x y)) := by
  unfold Ex
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [mul_left_comm (Q _)]

lemma Cx_prod (P : I → Law α) (f : I → α → ℂ) :
    (pack P).Cx (fun x => ∏ i, f i (x i)) = ∏ i, (P i).Cx (f i) := by
  simp_rw [Cx,pack_apply,Complex.ofReal_prod,← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun i x => (P i x:ℂ)*f i x)).symm

lemma sq_norm_Cx (P : Law α) (f : α → ℂ) :
    ‖P.Cx f‖^2 = P.Ex (fun x => P.Ex (fun y => (f x*conj (f y)).re)) := by
  have heq : P.Cx f * conj (P.Cx f) =
      P.Cx (fun x => P.Cx (fun y => f x*conj (f y))) := by
    simp_rw [Cx_lmul,Cx_conj,Cx_mul]
  rw [Complex.sq_norm, ← Complex.ofReal_re (Complex.normSq _),
    ← Complex.mul_conj, heq]
  simp_rw [re_Cx]

lemma Ex_exp (P : Law α) (f : α → ℝ) : exp (P.Ex f) ≤ P.Ex (fun x => exp (f x)) := by
  let C := P.Ex f
  have H (x : ℝ) : exp C * ((x-C)+1) ≤ exp x := by
    apply le_trans (mul_le_mul_of_nonneg_left (add_one_le_exp (x-C)) (exp_nonneg _))
    rw [← exp_add]; simp
  have H' := P.Ex_mono (f:=fun x => exp C*((f x-C)+1)) (g:=fun x => exp (f x))
    (fun x => H (f x))
  rw [Ex_lmul,Ex_add,Ex_sub,Ex_const,Ex_const,show P.Ex f=C from rfl] at H'
  simpa only [sub_self,zero_add,mul_one] using H'

end FourierLLogL.Law

end OAI
