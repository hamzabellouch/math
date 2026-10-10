import OAI.Analysis.BernoulliCone.CapCalculus

namespace OAI

section
noncomputable section
open Set Filter
open scoped Topology ContDiff Laplacian
namespace Bernoulli.DeSilvaJerison

lemma capH_abs (s:ℝ) : capH |s|=capH s := by
  rcases le_total 0 s with h|h
  · rw [abs_of_nonneg h]
  · rw [abs_of_nonpos h,capH_even]
lemma capHP_sq_abs (s:ℝ) : (capHP |s|)^2=(capHP s)^2 := by
  rcases le_total 0 s with h|h
  · rw [abs_of_nonneg h]
  · rw [abs_of_nonpos h,capHP_odd,neg_sq]
lemma capH_boundary {s:ℝ} (hs:|s|=3/4) : capH s=0 := by
  rw [←capH_abs,hs,capH_end]
lemma capHP_sq_boundary {s:ℝ} (hs:|s|=3/4) : (capHP s)^2=(capHP (3/4))^2 := by
  rw [←capHP_sq_abs,hs]
lemma capC_pos : 0<capC := by unfold capC; positivity
lemma capC_sq : capC^2=1+9/16*capP^2 := Real.sq_sqrt (by positivity)
lemma cap_boundary_slope_bound : capC^2*(capHP (3/4))^2≤c7 := by
  have hp := capP_bounds
  have ha := capAmplitude_bounds
  have hs : capP^2≤(3886/10000:ℝ)^2 := by nlinarith [hp.1,hp.2]
  have hq : 0≤3125/768-capAmplitude/6 := by linarith [ha.2]
  have hq1 : (3125/768-capAmplitude/6)^2≤(3125/768-(289237/1000000)/6:ℝ)^2 := by
    nlinarith [ha.1]
  rw [capC_sq,capHP_end]
  have hprod := mul_le_mul (show 1+9/16*capP^2≤1+9/16*(3886/10000:ℝ)^2 by linarith)
    hq1 (sq_nonneg _) (by positivity : (0:ℝ)≤1+9/16*(3886/10000:ℝ)^2)
  nlinarith only [hprod,c7_lower]

lemma gradient_smoothCap {x:Space 7} (hx:Cylindrical.radiusSq axis x≤1) :
    let q := Cylindrical.radiusSq axis x
    let V := CapAlgebra.V q capB
    let s := Cylindrical.axis axis x/V
    gradient smoothCap x =
      (2*CapAlgebra.Y1 q capB capC*capH s) • Cylindrical.transverse axis x +
      (CapAlgebra.Y q capB capC*capHP s) •
        (V⁻¹ • axis+(-Cylindrical.axis axis x*CapAlgebra.D q capB/V^2) • Cylindrical.transverse axis x) := by
  dsimp only
  let q:=Cylindrical.radiusSq axis x
  let a:=Cylindrical.axis axis x
  have hq:=Cylindrical.radiusSq_nonneg axis x axis_norm
  have hh:0<CapAlgebra.H q capB:=CapAlgebra.H_pos (b:=capB) hq
  have hv:0<CapAlgebra.V q capB:= (CapAlgebra.V_bounds hq hx capB_bounds.1 capB_bounds.2).1
  have hg:=Cylindrical.gradient_lift (e:=axis) (x:=x)
    (CapAlgebra.Y_contDiffAt (C:=capC) (n:=1) hh |>.differentiableAt (by norm_num))
    (CapAlgebra.hasDerivAt_invV hv.ne').differentiableAt
    (hasDerivAt_capH _).differentiableAt
  change gradient smoothCap x= _ at hg
  change gradient smoothCap x=
    (2*deriv (fun q=>CapAlgebra.Y q capB capC) q*capH (a*(CapAlgebra.V q capB)⁻¹)) • Cylindrical.transverse axis x+
    (CapAlgebra.Y q capB capC*deriv capH (a*(CapAlgebra.V q capB)⁻¹)) •
      ((CapAlgebra.V q capB)⁻¹ • axis+(2*a*deriv (fun q=>(CapAlgebra.V q capB)⁻¹) q) • Cylindrical.transverse axis x) at hg
  rw [hg]
  simp only [CapAlgebra.deriv_Y hh,(CapAlgebra.hasDerivAt_invV hv.ne').deriv,
    (hasDerivAt_capH _).deriv,←div_eq_mul_inv]
  have he:2*a*(-CapAlgebra.D q capB/(2*CapAlgebra.V q capB^2)) = -a*CapAlgebra.D q capB/CapAlgebra.V q capB^2 := by ring
  rw [he]

/-- Constant free-boundary slope of the actual cylindrical cap, including the
transverse axis. The result is for the genuine Euclidean gradient. -/
theorem smoothCap_boundary_gradient {x:Space 7} (hx:Cylindrical.radiusSq axis x≤1)
    (hs:|Cylindrical.axis axis x/CapAlgebra.V (Cylindrical.radiusSq axis x) capB|=3/4) :
    ‖gradient smoothCap x‖^2=capC^2*(capHP (3/4))^2 := by
  let q:=Cylindrical.radiusSq axis x
  let a:=Cylindrical.axis axis x
  let V:=CapAlgebra.V q capB
  let H:=CapAlgebra.H q capB
  let s:=a/V
  have hq:0≤q:=Cylindrical.radiusSq_nonneg axis x axis_norm
  have hv:0<V:= (CapAlgebra.V_bounds hq hx capB_bounds.1 capB_bounds.2).1
  have hh:0<H:=CapAlgebra.H_pos hq
  have hs2 : s^2=9/16 := by nlinarith only [sq_abs s,hs]
  have hz : capH s=0 := capH_boundary hs
  have hp : (capHP s)^2=(capHP (3/4))^2 := capHP_sq_boundary hs
  have hg:=gradient_smoothCap hx
  dsimp only at hg
  change gradient smoothCap x=(2*CapAlgebra.Y1 q capB capC*capH s) • Cylindrical.transverse axis x+
    (CapAlgebra.Y q capB capC*capHP s) •
      (V⁻¹ • axis+(-a*CapAlgebra.D q capB/V^2) • Cylindrical.transverse axis x) at hg
  rw [hz] at hg
  simp only [mul_zero,zero_smul,zero_add] at hg
  have horth:inner ℝ axis (Cylindrical.transverse axis x)=0 := by
    rw [real_inner_comm,Cylindrical.transverse_inner axis x axis_norm]
  rw [hg,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs,norm_add_sq_real]
  simp only [norm_smul,Real.norm_eq_abs,mul_pow,sq_abs,axis_norm,mul_one,
    real_inner_smul_left,real_inner_smul_right,horth,mul_zero,add_zero,
    Cylindrical.transverse_sq axis x axis_norm]
  change (CapAlgebra.Y q capB capC)^2*(capHP s)^2*
    ((V⁻¹)^2+(-a*CapAlgebra.D q capB/V^2)^2*q)=_
  have he : ((V⁻¹)^2+(-a*CapAlgebra.D q capB/V^2)^2*q)=H/V^2 := by
    have hhdef : H=1+9/16*q*(CapAlgebra.D q capB)^2:=rfl
    have ha2 : a^2=9/16*V^2 := by
      dsimp only [s] at hs2
      field_simp at hs2
      nlinarith only [hs2]
    field_simp
    rw [ha2,hhdef]
    ring
  rw [he,hp]
  unfold CapAlgebra.Y
  change (capC*V/Real.sqrt H)^2*(capHP (3/4))^2*(H/V^2)=_
  rw [div_pow,mul_pow,Real.sq_sqrt hh.le]
  field_simp

 theorem smoothCap_boundary_slope {x:Space 7} (hx:Cylindrical.radiusSq axis x≤1)
    (hs:|Cylindrical.axis axis x/CapAlgebra.V (Cylindrical.radiusSq axis x) capB|=3/4) :
    ‖gradient smoothCap x‖^2≤c7 := by
  rw [smoothCap_boundary_gradient hx hs]
  exact cap_boundary_slope_bound
end Bernoulli.DeSilvaJerison

end
end

end OAI
