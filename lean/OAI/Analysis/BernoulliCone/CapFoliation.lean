import OAI.Analysis.BernoulliCone.CapGeometry

namespace OAI

section
noncomputable section
open Set Filter
open scoped Topology ContDiff Laplacian
namespace Bernoulli.DeSilvaJerison

lemma capHP_mul_nonpos (s:ℝ) : s*capHP s≤0 := by
  rcases le_total 0 s with h|h
  · exact mul_nonpos_of_nonneg_of_nonpos h (capHP_nonpos h)
  · have hh:=capHP_nonpos (s:= -s) (by linarith)
    rw [capHP_odd] at hh
    exact mul_nonpos_of_nonpos_of_nonneg h (by linarith)

lemma capHP_neg {s:ℝ} (hs:0<s) : capHP s<0 := by
  have hh:=capHP_le_linear hs.le
  have hn: -5+4*capAmplitude<0 := by linarith [capAmplitude_le]
  exact hh.trans_lt (mul_neg_of_neg_of_pos hn hs)

lemma capH_strictAnti : StrictAntiOn capH (Ici 0) := by
  apply strictAntiOn_of_deriv_neg (convex_Ici _)
  · intro x hx
    exact (hasDerivAt_capH x).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Ici] at hx
    rw [(hasDerivAt_capH x).deriv]
    exact capHP_neg hx

lemma capH_pos_iff (s:ℝ) : 0<capH s ↔ |s|<3/4 := by
  rw [←capH_abs]
  constructor
  · intro hh
    by_contra hn
    have hh1:=capH_antitone (show (3/4:ℝ)∈Ici 0 by norm_num)
      (abs_nonneg s) (le_of_not_gt hn)
    rw [capH_end] at hh1
    linarith
  · intro hs
    have hh:=capH_strictAnti (abs_nonneg s) (show (3/4:ℝ)∈Ici 0 by norm_num) hs
    rwa [capH_end] at hh

namespace CapAlgebra
lemma V_radial_pos {q b:ℝ} (_hq:0≤q) (hq1:q≤1) (hb:2242/10000≤b) (hb1:b≤2243/10000) :
    0<V q b-q*D q b := by
  have hmul:q*b≤b:=mul_le_of_le_one_left (by linarith) hq1
  unfold V D
  nlinarith [sq_nonneg q]
lemma D_pos {q b:ℝ} (hq1:q≤1) (hb:2242/10000≤b) :0<D q b := by
  unfold D; linarith
lemma E_pos {q b:ℝ} (hq1:q≤1) (hb:2242/10000≤b) :0<E q b := by
  unfold E; linarith
lemma Y_pos {q b C:ℝ} (hq:0≤q) (hv:0<V q b) (hc:0<C) :0<Y q b C := by
  unfold Y; exact div_pos (mul_pos hc hv) (Real.sqrt_pos.mpr (H_pos hq))
lemma Y1_eq {q b C:ℝ} (hh:0<H q b) (hv:V q b≠0) :
    2*Y1 q b C=Y q b C*(D q b/V q b-9/16*D q b*E q b/H q b) := by
  have hs:Real.sqrt (H q b)≠0:=(Real.sqrt_pos.mpr hh).ne'
  have hs2:=Real.sq_sqrt hh.le
  unfold Y1 Y
  generalize V q b=v at *
  generalize D q b=d at *
  generalize E q b=e at *
  generalize H q b=h at *
  field_simp
  rw [hs2]
  ring
end CapAlgebra

lemma smoothCap_radial_defect {x:Space 7} (hx:Cylindrical.radiusSq axis x≤1) :
    let q:=Cylindrical.radiusSq axis x
    let V:=CapAlgebra.V q capB
    let H:=CapAlgebra.H q capB
    let D:=CapAlgebra.D q capB
    let E:=CapAlgebra.E q capB
    let s:=Cylindrical.axis axis x/V
    smoothCap x-inner ℝ x (gradient smoothCap x)=
      CapAlgebra.Y q capB capC*((1-q*D/V+q*9/16*D*E/H)*capH s-
        s*capHP s*(1-q*D/V)) := by
  dsimp only
  let q:=Cylindrical.radiusSq axis x
  let a:=Cylindrical.axis axis x
  have hq:0≤q:=Cylindrical.radiusSq_nonneg axis x axis_norm
  have hv:0<CapAlgebra.V q capB:= (CapAlgebra.V_bounds hq hx capB_bounds.1 capB_bounds.2).1
  have hh:0<CapAlgebra.H q capB:=CapAlgebra.H_pos hq
  have ht:inner ℝ x (Cylindrical.transverse axis x)=q := by
    simp only [Cylindrical.transverse,inner_sub_right,real_inner_smul_right,
      real_inner_self_eq_norm_sq]
    change ‖x‖^2-a*a=‖x‖^2-a^2
    ring
  rw [gradient_smoothCap hx]
  simp only [inner_add_right,real_inner_smul_right,ht]
  change smoothCap x-(2*CapAlgebra.Y1 q capB capC*capH (a/CapAlgebra.V q capB)*q+
    CapAlgebra.Y q capB capC*capHP (a/CapAlgebra.V q capB)*
      ((CapAlgebra.V q capB)⁻¹*a+(-a*CapAlgebra.D q capB/(CapAlgebra.V q capB)^2)*q))=_
  rw [CapAlgebra.Y1_eq hh hv.ne']
  change CapAlgebra.Y q capB capC*capH (a*(CapAlgebra.V q capB)⁻¹)-_=_
  dsimp only [q,a] at *
  simp only [div_eq_mul_inv]
  field_simp
  ring

lemma smoothCap_radial_defect_pos {x:Space 7} (hx:Cylindrical.radiusSq axis x≤1)
    (hp:0<smoothCap x) : 0<smoothCap x-inner ℝ x (gradient smoothCap x) := by
  let q:=Cylindrical.radiusSq axis x
  let V:=CapAlgebra.V q capB
  let H:=CapAlgebra.H q capB
  let D:=CapAlgebra.D q capB
  let E:=CapAlgebra.E q capB
  let s:=Cylindrical.axis axis x/V
  have hq:0≤q:=Cylindrical.radiusSq_nonneg axis x axis_norm
  have hv:0<V:= (CapAlgebra.V_bounds hq hx capB_bounds.1 capB_bounds.2).1
  have hh:0<H:=CapAlgebra.H_pos hq
  have hd:0<D:=CapAlgebra.D_pos hx capB_bounds.1
  have he:0<E:=CapAlgebra.E_pos hx capB_bounds.1
  have hy:0<CapAlgebra.Y q capB capC:=CapAlgebra.Y_pos hq hv capC_pos
  have hhpos:0<capH s := by
    change 0<CapAlgebra.Y q capB capC*capH (Cylindrical.axis axis x*V⁻¹) at hp
    rw [←div_eq_mul_inv] at hp
    exact pos_of_mul_pos_right hp hy.le
  have hk:0<1-q*D/V := by
    have hl:=CapAlgebra.V_radial_pos hq hx capB_bounds.1 capB_bounds.2
    apply sub_pos.mpr
    apply (div_lt_iff₀ hv).mpr
    simpa only [one_mul] using (show q*D<V by linarith)
  have hk1:0≤q*9/16*D*E/H:=by positivity
  have hsprod:=capHP_mul_nonpos s
  rw [smoothCap_radial_defect hx]
  change 0<CapAlgebra.Y q capB capC*((1-q*D/V+q*9/16*D*E/H)*capH s-s*capHP s*(1-q*D/V))
  have ht:=mul_pos (show 0<1-q*D/V+q*9/16*D*E/H by linarith) hhpos
  have ht1:=mul_nonpos_of_nonpos_of_nonneg hsprod hk.le
  exact mul_pos hy (by linarith)
end Bernoulli.DeSilvaJerison

end
end

end OAI
