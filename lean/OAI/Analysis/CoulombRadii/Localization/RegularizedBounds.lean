import Mathlib
import OAI.Analysis.CoulombRadii.Localization.HarmonicInterior

namespace OAI

section
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators ContDiff
noncomputable section
namespace NeutralAtom
lemma radial_rpow_partial {l:ℝ} (hl:l≠0) (p:ℝ) (x:Position) (b:Fin 3) :
    dirPartial (fun y:Position => (‖y‖^2+l^2)^p) (axis b) x =
      p*(‖x‖^2+l^2)^(p-1)*(2*x b) := by
  have hq:0<‖x‖^2+l^2:=add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_ne_zero hl)
  have H:=((hasStrictFDerivAt_norm_sq x).hasFDerivAt.add_const (l^2)).rpow_const (p:=p) (Or.inl hq.ne')
  unfold dirPartial
  rw [H.fderiv]
  simp [axis,EuclideanSpace.inner_single_right,mul_assoc]
lemma regularized_second_partial {l:ℝ} (hl:l≠0) (x:Position) (a b:Fin 3) :
    dirPartial (dirPartial (regularizedKernel l) (axis a)) (axis b) x=
      -(if a=b then (1:ℝ) else 0)*(‖x‖^2+l^2)^(-3/2:ℝ)+
        3*x a*x b*(‖x‖^2+l^2)^(-5/2:ℝ) := by
  have he:dirPartial (regularizedKernel l) (axis a)=fun x => -x a*(‖x‖^2+l^2)^(-3/2:ℝ):=
    funext fun x => dirPartial_regularizedKernel hl a x
  rw [he]
  have hcoord := ((EuclideanSpace.proj (𝕜:=ℝ) a).hasFDerivAt (x:=x)).neg
  change HasFDerivAt (fun y:Position => -y a) _ x at hcoord
  have hd: DifferentiableAt ℝ (fun y:Position => (‖y‖^2+l^2)^(-3/2:ℝ)) x := by
    exact (((hasStrictFDerivAt_norm_sq x).hasFDerivAt.add_const (l^2)).rpow_const
      (p:=(-3/2:ℝ)) (Or.inl (add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_ne_zero hl)).ne')).differentiableAt
  rw [dirPartial_mul hcoord.differentiableAt hd,radial_rpow_partial hl]
  have hc:dirPartial (fun y:Position => -y a) (axis b) x= -(if a=b then (1:ℝ) else 0) := by
    unfold dirPartial
    rw [hcoord.fderiv]
    simp [axis,PiLp.single_apply]
  rw [hc]
  norm_num
  ring
lemma regularizedKernel_uniform_bound {l:ℝ} (hl:l≠0) (x:Position) :
    |regularizedKernel l x|≤(l^2)^(-1/2:ℝ) := by
  unfold regularizedKernel
  rw [abs_of_nonneg (Real.rpow_nonneg (by positivity) _)]
  exact Real.rpow_le_rpow_of_nonpos (sq_pos_of_ne_zero hl) (by nlinarith [sq_nonneg ‖x‖]) (by norm_num)
lemma regularizedPartial_uniform_bound {l:ℝ} (hl:l≠0) (x:Position) (a:Fin 3) :
    |dirPartial (regularizedKernel l) (axis a) x|≤(l^2)^(-1/2:ℝ)+(l^2)^(-3/2:ℝ) := by
  let q:=‖x‖^2+l^2
  have hq:0<q:=add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_ne_zero hl)
  have hbase:l^2≤q:=by dsimp [q]; nlinarith [sq_nonneg ‖x‖]
  have ha:|x a|≤q+1 := by
    have H:|x a|≤‖x‖:=by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le x a
    dsimp [q]
    nlinarith [sq_nonneg (‖x‖-1),sq_nonneg l]
  have he:q*q^(-3/2:ℝ)=q^(-1/2:ℝ) := by
    rw [mul_comm,←Real.rpow_add_one hq.ne']
    norm_num
  rw [dirPartial_regularizedKernel hl,abs_mul,abs_neg,
    abs_of_nonneg (Real.rpow_nonneg hq.le _)]
  change |x a| *q^(-3/2:ℝ)≤_
  calc
    _≤(q+1)*q^(-3/2:ℝ):=mul_le_mul_of_nonneg_right ha (Real.rpow_nonneg hq.le _)
    _=q^(-1/2:ℝ)+q^(-3/2:ℝ):=by rw [add_mul,he,one_mul]
    _≤_:=add_le_add (Real.rpow_le_rpow_of_nonpos (sq_pos_of_ne_zero hl) hbase (by norm_num))
      (Real.rpow_le_rpow_of_nonpos (sq_pos_of_ne_zero hl) hbase (by norm_num))
lemma regularizedSecond_uniform_bound {l:ℝ} (hl:l≠0) (x:Position) (a b:Fin 3) :
    |dirPartial (dirPartial (regularizedKernel l) (axis a)) (axis b) x|≤4*(l^2)^(-3/2:ℝ) := by
  let q:=‖x‖^2+l^2
  have hq:0<q:=add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_ne_zero hl)
  have hbase:l^2≤q:=by dsimp [q]; nlinarith [sq_nonneg ‖x‖]
  have hab:|x a| * |x b|≤q := by
    have ha:|x a|≤‖x‖:=by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le x a
    have hb:|x b|≤‖x‖:=by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le x b
    have H:=mul_le_mul ha hb (abs_nonneg _) (norm_nonneg x)
    dsimp [q]
    nlinarith [sq_nonneg l]
  have he:q*q^(-5/2:ℝ)=q^(-3/2:ℝ) := by
    rw [mul_comm,←Real.rpow_add_one hq.ne']
    norm_num
  have hb:q^(-3/2:ℝ)≤(l^2)^(-3/2:ℝ):=
    Real.rpow_le_rpow_of_nonpos (sq_pos_of_ne_zero hl) hbase (by norm_num)
  rw [regularized_second_partial hl]
  calc
    _≤|-(if a=b then (1:ℝ) else 0)*q^(-3/2:ℝ)|+|3*x a*x b*q^(-5/2:ℝ)|:=abs_add_le _ _
    _≤q^(-3/2:ℝ)+3*q^(-3/2:ℝ) := by
      apply add_le_add
      · split_ifs <;> simp [abs_of_nonneg (Real.rpow_nonneg hq.le _),Real.rpow_nonneg hq.le]
      · simp only [abs_mul,abs_of_nonneg (Real.rpow_nonneg hq.le _)]
        rw [abs_of_pos (by norm_num : (0:ℝ)<3)]
        rw [show 3* |x a| * |x b|=3*(|x a| * |x b|) by ring, mul_assoc,←he]
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hab (Real.rpow_nonneg hq.le _)) (by norm_num)
    _≤_:=by nlinarith
end NeutralAtom
end

end

end OAI
