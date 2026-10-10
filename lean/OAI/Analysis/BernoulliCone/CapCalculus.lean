import OAI.Analysis.BernoulliCone.UpperSupport

namespace OAI

section
noncomputable section
open Set Filter
open scoped Topology ContDiff Laplacian
namespace Bernoulli.DeSilvaJerison
namespace CapAlgebra
lemma V_bounds {q b:ℝ} (hq:0≤q) (hq1:q≤1) (hb:2242/10000≤b) (hb1:b≤2243/10000) :
    0<V q b ∧ V q b≤1 := by
  have hqq : q^2≤q := by nlinarith
  have he : V q b=1-(1-q)*(b-3/200*(q+1)) := by unfold V; ring
  have hl : 0≤b*q := mul_nonneg (by linarith) hq
  constructor
  · unfold V
    nlinarith
  · rw [he]
    have hh : 0≤(1-q)*(b-3/200*(q+1)) := mul_nonneg (by linarith) (by linarith)
    linarith
lemma hasDerivAt_V (q b:ℝ) : HasDerivAt (fun q=>V q b) (D q b/2) q := by
  convert! (((hasDerivAt_const q (203/200-b)).add ((hasDerivAt_id q).const_mul b)).sub
    (((hasDerivAt_id q).pow 2).const_mul (3/200))) using 1
  dsimp [V,D]
  ring
lemma hasDerivAt_D (q b:ℝ) : HasDerivAt (fun q=>D q b) (-3/50) q := by
  convert! (hasDerivAt_const q (2*b)).sub ((hasDerivAt_id q).const_mul (3/50)) using 1
  ring
lemma hasDerivAt_E (q b:ℝ) : HasDerivAt (fun q=>E q b) (-9/50) q := by
  convert! (hasDerivAt_const q (2*b)).sub ((hasDerivAt_id q).const_mul (9/50)) using 1
  ring
lemma hasDerivAt_H (q b:ℝ) : HasDerivAt (fun q=>H q b) (9/16*D q b*E q b) q := by
  convert! (hasDerivAt_const q (1:ℝ)).add
    ((((hasDerivAt_id q).const_mul (9/16)).mul ((hasDerivAt_D q b).pow 2))) using 1
  dsimp [D,E]
  ring
lemma V_contDiff (b:ℝ) {n:WithTop ℕ∞} : ContDiff ℝ n (fun q=>V q b) := by
  exact (contDiff_const.add (contDiff_const.mul contDiff_id)).sub (contDiff_const.mul (contDiff_id.pow 2))
lemma H_contDiff (b:ℝ) {n:WithTop ℕ∞} : ContDiff ℝ n (fun q=>H q b) := by
  exact contDiff_const.add ((contDiff_const.mul contDiff_id).mul
    ((contDiff_const.sub (contDiff_const.mul contDiff_id)).pow 2))
/-- The cap prefactor in squared transverse coordinates. -/
def Y (q b C:ℝ) :ℝ := C*V q b/Real.sqrt (H q b)
def Y1 (q b C:ℝ) :ℝ :=
  C*(D q b/2/Real.sqrt (H q b)-V q b*(9/16*D q b*E q b)/(2*(Real.sqrt (H q b))^3))
def Y2 (q b C:ℝ) :ℝ :=
  C*((-3/100)/Real.sqrt (H q b)-D q b/2*(9/16*D q b*E q b)/(Real.sqrt (H q b))^3-
    V q b*(9/16*((-3/50)*E q b+D q b*(-9/50)))/(2*(Real.sqrt (H q b))^3)+
    3*V q b*(9/16*D q b*E q b)^2/(4*(Real.sqrt (H q b))^5))
lemma Y_contDiffAt {q b C:ℝ} (hH:0<H q b) {n:WithTop ℕ∞} : ContDiffAt ℝ n (fun q=>Y q b C) q :=
  (contDiffAt_const.mul (V_contDiff b (n:=n)).contDiffAt).div ((H_contDiff b (n:=n)).contDiffAt.sqrt hH.ne')
    (Real.sqrt_pos.mpr hH).ne'
lemma hasDerivAt_Y {q b C:ℝ} (hH:0<H q b) : HasDerivAt (fun q=>Y q b C) (Y1 q b C) q := by
  have hS:=Real.sqrt_pos.mpr hH
  have hSsq:=Real.sq_sqrt hH.le
  convert! ((hasDerivAt_V q b).const_mul C).div ((hasDerivAt_H q b).sqrt hH.ne') hS.ne' using 1
  simp only [Y1]
  field_simp
lemma hasDerivAt_Y1 {q b C:ℝ} (hH:0<H q b) : HasDerivAt (fun q=>Y1 q b C) (Y2 q b C) q := by
  have hS:=Real.sqrt_pos.mpr hH
  have hs := (hasDerivAt_H q b).sqrt hH.ne'
  have hd := hasDerivAt_D q b
  have he := hasDerivAt_E q b
  have hv := hasDerivAt_V q b
  convert! (((hd.div_const 2).div hs hS.ne').sub
    ((hv.mul ((hd.const_mul (9/16)).mul he)).div ((hs.pow 3).const_mul 2) (mul_ne_zero (by norm_num) (pow_ne_zero _ hS.ne')))).const_mul C using 1
  dsimp [Y1,Y2]
  field_simp
  ring
lemma deriv_Y {q b C:ℝ} (hH:0<H q b) : deriv (fun q=>Y q b C) q=Y1 q b C := (hasDerivAt_Y hH).deriv
lemma deriv2_Y {q b C:ℝ} (hH:0<H q b) : deriv (deriv (fun q=>Y q b C)) q=Y2 q b C := by
  have hh : deriv (fun q=>Y q b C)=ᶠ[𝓝 q] fun q=>Y1 q b C := by
    filter_upwards [(H_contDiff b (n:=∞)).continuous.continuousAt.eventually (Ioi_mem_nhds hH)] with t ht
    exact deriv_Y ht
  rw [hh.deriv_eq]
  exact (hasDerivAt_Y1 hH).deriv
lemma hasDerivAt_invV {q b:ℝ} (hv:V q b≠0) :
    HasDerivAt (fun q=>(V q b)⁻¹) (-D q b/(2*(V q b)^2)) q := by
  convert! (hasDerivAt_V q b).inv hv using 1
  ring
lemma deriv2_invV {q b:ℝ} (hv:V q b≠0) :
    deriv (deriv (fun q=>(V q b)⁻¹)) q= (D q b)^2/(2*(V q b)^3)+3/(100*(V q b)^2) := by
  have hh : deriv (fun q=>(V q b)⁻¹)=ᶠ[𝓝 q] fun q=>-D q b/(2*(V q b)^2) := by
    filter_upwards [((V_contDiff b (n:=∞)).continuous.continuousAt.eventually_ne hv)] with t ht
    exact (hasDerivAt_invV ht).deriv
  rw [hh.deriv_eq]
  have hd := ((hasDerivAt_D q b).neg.div (((hasDerivAt_V q b).pow 2).const_mul 2) (by positivity : 2*(V q b)^2≠0)).deriv
  change deriv (fun q=>-D q b/(2*(V q b)^2)) q = _ at hd
  rw [hd]
  simp only [Pi.pow_apply,Pi.neg_apply]
  field_simp
  ring
lemma lap_Y {q b C:ℝ} (hV:V q b≠0) (hH:0<H q b) :
    4*q*Y2 q b C+12*Y1 q b C = Y q b C/V q b*(NN q b/(H q b)^2) := by
  have hS := (Real.sqrt_pos.mpr hH).ne'
  have hSq := Real.sq_sqrt hH.le
  have hE : E q b=D q b-3/25*q := by unfold E D; ring
  unfold Y Y1 Y2 NN MN
  generalize hvv : V q b=v at *
  generalize hdd : D q b=z at *
  generalize hee : E q b=e at *
  generalize hhh : H q b=h at *
  have hdef : h=1+9/16*q*z^2 := by rw [←hhh, H, hdd]
  field_simp [hS,hV,hH.ne']
  ring_nf
  simp only [show Real.sqrt h^4=h^2 by calc
    _ = (Real.sqrt h^2)^2 := by ring
    _ = _ := by rw [hSq], hSq]
  rw [hE,hdef]
  ring

lemma invV_mixed {q b C:ℝ} (hV:V q b≠0) (hH:0<H q b) :
    Y q b C*(4*q*((D q b)^2/(2*(V q b)^3)+3/(100*(V q b)^2))+
      12*(-D q b/(2*(V q b)^2)))+8*q*Y1 q b C*(-D q b/(2*(V q b)^2)) =
      -Y q b C/(V q b)^2*(MN q b/H q b) := by
  have hS := (Real.sqrt_pos.mpr hH).ne'
  have hSq := Real.sq_sqrt hH.le
  have hE : E q b=D q b-3/25*q := by unfold E D; ring
  unfold Y Y1 MN
  generalize hvv : V q b=v at *
  generalize hdd : D q b=z at *
  generalize hee : E q b=e at *
  generalize hhh : H q b=h at *
  have hdef : h=1+9/16*q*z^2 := by rw [←hhh, H, hdd]
  field_simp [hS,hV,hH.ne']
  ring_nf
  rw [hSq,hE,hdef]
  ring

end CapAlgebra

lemma capH_contDiff : ContDiff ℝ ∞ capH := by
  have hr : ContDiff ℝ ∞ capRadius := by
    apply ContDiff.sqrt
    · exact contDiff_const.add (contDiff_id.pow 2)
    · intro x; positivity
  have ht : ContDiff ℝ ∞ capAngle := contDiff_id.div hr (fun x=>(capRadius_pos x).ne')
  have hf : ContDiff ℝ ∞ (fun s=>f (capAngle s)) := by
    apply contDiff_iff_contDiffAt.mpr
    intro s
    exact (contDiffAt_f (capAngle_mem s)).comp s ht.contDiffAt
  exact (hr.mul hf).add (contDiff_const.mul (contDiff_const.add (contDiff_const.mul (contDiff_id.pow 2))))

lemma deriv2_capH (s:ℝ) : deriv (deriv capH) s=-5*(capRadius s)^3+4*capAmplitude := by
  have hh : deriv capH=capHP := funext fun t=>(hasDerivAt_capH t).deriv
  rw [hh]
  exact (hasDerivAt_capHP s).deriv

def capC :ℝ := Real.sqrt (1+9/16*capP^2)
def smoothCap (x:Space 7) :ℝ := Cylindrical.lift axis (fun q=>CapAlgebra.Y q capB capC)
  (fun q=>(CapAlgebra.V q capB)⁻¹) capH x

lemma smoothCap_contDiffAt {x:Space 7} (hx:Cylindrical.radiusSq axis x≤1) :
    ContDiffAt ℝ ∞ smoothCap x := by
  have hq:=Cylindrical.radiusSq_nonneg axis x axis_norm
  have hv := (CapAlgebra.V_bounds hq hx capB_bounds.1 capB_bounds.2).1
  exact Cylindrical.contDiffAt_lift (CapAlgebra.Y_contDiffAt (CapAlgebra.H_pos hq))
    ((CapAlgebra.V_contDiff capB).contDiffAt.inv hv.ne') capH_contDiff.contDiffAt

lemma laplacian_smoothCap {x:Space 7} (hx:Cylindrical.radiusSq axis x≤1) :
    let q := Cylindrical.radiusSq axis x
    let V := CapAlgebra.V q capB
    let ξ := Cylindrical.axis axis x/V
    Δ smoothCap x = CapAlgebra.Y q capB capC/V^2 *
      ((-5*(capRadius ξ)^3+4*capAmplitude)*(1+q*ξ^2*(CapAlgebra.D q capB)^2)-
        ξ*capHP ξ*V*(CapAlgebra.MN q capB/CapAlgebra.H q capB)+
        capH ξ*V*(CapAlgebra.NN q capB/(CapAlgebra.H q capB)^2)) := by
  dsimp only
  let q := Cylindrical.radiusSq axis x
  let a := Cylindrical.axis axis x
  have hq : 0≤q := Cylindrical.radiusSq_nonneg axis x axis_norm
  have hv := (CapAlgebra.V_bounds hq hx capB_bounds.1 capB_bounds.2).1
  have hh := CapAlgebra.H_pos (b:=capB) hq
  have hc := Cylindrical.laplacian_lift axis_norm
    (CapAlgebra.Y_contDiffAt (C:=capC) (n:=2) hh)
    ((CapAlgebra.V_contDiff capB (n:=2)).contDiffAt.inv hv.ne')
    (capH_contDiff.of_le (by norm_cast : (2:WithTop ℕ∞)≤∞)).contDiffAt
  change Δ smoothCap x=_ at hc
  simp only [Space,finrank_euclideanSpace_fin,Nat.cast_ofNat] at hc
  norm_num only at hc
  change Δ smoothCap x =
    CapAlgebra.Y q capB capC * deriv (deriv capH) (a*(CapAlgebra.V q capB)⁻¹) *
      (((CapAlgebra.V q capB)⁻¹)^2+4*q*a^2*deriv (fun q=>(CapAlgebra.V q capB)⁻¹) q^2)+
    deriv capH (a*(CapAlgebra.V q capB)⁻¹)*
      (a*CapAlgebra.Y q capB capC*(4*q*deriv (deriv (fun q=>(CapAlgebra.V q capB)⁻¹)) q+
        12*deriv (fun q=>(CapAlgebra.V q capB)⁻¹) q)+
        8*q*a*deriv (fun q=>CapAlgebra.Y q capB capC) q*deriv (fun q=>(CapAlgebra.V q capB)⁻¹) q)+
    capH (a*(CapAlgebra.V q capB)⁻¹)*(4*q*deriv (deriv (fun q=>CapAlgebra.Y q capB capC)) q+
      12*deriv (fun q=>CapAlgebra.Y q capB capC) q) at hc
  rw [hc]
  simp only [CapAlgebra.deriv_Y hh, CapAlgebra.deriv2_Y hh,
    (CapAlgebra.hasDerivAt_invV hv.ne').deriv, CapAlgebra.deriv2_invV hv.ne',
    deriv2_capH,(hasDerivAt_capH _).deriv]
  change _ = CapAlgebra.Y q capB capC/(CapAlgebra.V q capB)^2 * _
  have hm:=CapAlgebra.invV_mixed (C:=capC) hv.ne' hh
  have hn:=CapAlgebra.lap_Y (C:=capC) hv.ne' hh
  have h1 : ((CapAlgebra.V q capB)⁻¹)^2+4*q*a^2*(-CapAlgebra.D q capB/(2*(CapAlgebra.V q capB)^2))^2 =
      (1+q*(a/CapAlgebra.V q capB)^2*(CapAlgebra.D q capB)^2)/(CapAlgebra.V q capB)^2 := by
    field_simp
    ring
  have h2 : a*CapAlgebra.Y q capB capC*
      (4*q*((CapAlgebra.D q capB)^2/(2*(CapAlgebra.V q capB)^3)+3/(100*(CapAlgebra.V q capB)^2))+
        12*(-CapAlgebra.D q capB/(2*(CapAlgebra.V q capB)^2)))+
      8*q*a*CapAlgebra.Y1 q capB capC*(-CapAlgebra.D q capB/(2*(CapAlgebra.V q capB)^2)) =
      -a*CapAlgebra.Y q capB capC/(CapAlgebra.V q capB)^2*(CapAlgebra.MN q capB/CapAlgebra.H q capB) := by
    calc
      _ = a*(CapAlgebra.Y q capB capC*
          (4*q*((CapAlgebra.D q capB)^2/(2*(CapAlgebra.V q capB)^3)+3/(100*(CapAlgebra.V q capB)^2))+
            12*(-CapAlgebra.D q capB/(2*(CapAlgebra.V q capB)^2)))+
          8*q*CapAlgebra.Y1 q capB capC*(-CapAlgebra.D q capB/(2*(CapAlgebra.V q capB)^2))) := by ring
      _ = _ := by rw [hm]; ring
  rw [h1,h2,hn]
  change _=CapAlgebra.Y q capB capC/(CapAlgebra.V q capB)^2 *
    ((-5*(capRadius (a/CapAlgebra.V q capB))^3+4*capAmplitude)*(1+q*(a/CapAlgebra.V q capB)^2*(CapAlgebra.D q capB)^2)-
      (a/CapAlgebra.V q capB)*capHP (a/CapAlgebra.V q capB)*CapAlgebra.V q capB*(CapAlgebra.MN q capB/CapAlgebra.H q capB)+
      capH (a/CapAlgebra.V q capB)*CapAlgebra.V q capB*(CapAlgebra.NN q capB/(CapAlgebra.H q capB)^2))
  simp only [← div_eq_mul_inv]
  field_simp
  ring
lemma cap_sHP_nonpos (s:ℝ) : s*capHP s≤0 := by
  rcases le_total 0 s with h|h
  · exact mul_nonpos_of_nonneg_of_nonpos h (capHP_nonpos h)
  · have hh:=mul_nonpos_of_nonneg_of_nonpos (neg_nonneg.mpr h) (capHP_nonpos (neg_nonneg.mpr h))
    simpa only [capHP_odd,neg_mul_neg] using hh

/-- The actual smooth cylindrical cap is superharmonic on its positive strip. -/
theorem smoothCap_laplacian_nonpos {x:Space 7} (hx:Cylindrical.radiusSq axis x≤1)
    (hs:|Cylindrical.axis axis x/CapAlgebra.V (Cylindrical.radiusSq axis x) capB|≤3/4) :
    Δ smoothCap x≤0 := by
  let q:=Cylindrical.radiusSq axis x
  let V:=CapAlgebra.V q capB
  let s:=Cylindrical.axis axis x/V
  have hq:0≤q:=Cylindrical.radiusSq_nonneg axis x axis_norm
  obtain ⟨hv,hv1⟩:=CapAlgebra.V_bounds hq hx capB_bounds.1 capB_bounds.2
  obtain ⟨hM,hM1,hN,hN1⟩:=CapAlgebra.coeff_bounds hq hx capB_bounds.1 capB_bounds.2
  have hh:=capH_nonneg hs
  have hph:=capHPP_nonpos s
  have hsp:=cap_sHP_nonpos s
  have hK:=cap_K_nonpos hs
  change -5*capRadius s^3+4*capAmplitude-(673/250)*s*capHP s+(431/200)*capH s≤0 at hK
  have hvm : V*(CapAlgebra.MN q capB/CapAlgebra.H q capB)≤673/250 :=
    (mul_le_mul_of_nonneg_right hv1 hM).trans (by simpa using hM1)
  have hvn : V*(CapAlgebra.NN q capB/(CapAlgebra.H q capB)^2)≤431/200 :=
    (mul_le_mul_of_nonneg_right hv1 hN).trans (by simpa using hN1)
  have h0:=mul_nonpos_of_nonpos_of_nonneg hph
    (show 0≤q*s^2*(CapAlgebra.D q capB)^2 by positivity)
  have h1:=mul_le_mul_of_nonneg_left hvm (neg_nonneg.mpr hsp)
  have h2:=mul_le_mul_of_nonneg_left hvn hh
  have hbr : (-5*capRadius s^3+4*capAmplitude)*(1+q*s^2*(CapAlgebra.D q capB)^2)-
      s*capHP s*V*(CapAlgebra.MN q capB/CapAlgebra.H q capB)+
      capH s*V*(CapAlgebra.NN q capB/(CapAlgebra.H q capB)^2)≤0 := by
    nlinarith only [h0,h1,h2,hK]
  rw [laplacian_smoothCap hx]
  have hY:0≤CapAlgebra.Y q capB capC := by unfold CapAlgebra.Y capC; positivity
  exact mul_nonpos_of_nonneg_of_nonpos (div_nonneg hY (sq_nonneg V)) hbr

end Bernoulli.DeSilvaJerison

end
end

end OAI
