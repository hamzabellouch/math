import Mathlib
import OAI.Probability.SKValue.Evolution.JetParity
import OAI.Probability.SKValue.Coercivity.ZeroFlux

namespace OAI

section
open MeasureTheory Set Filter
open scoped Topology
namespace SKValue.Certificate

lemma integrated_coercivity {r v w z s a d f:ℝ → ℝ}
    (hr:Measurable r) (hv:Measurable v) (hw:Measurable w) (hz:Measurable z)
    (hs:Measurable s) (ha:Measurable a) (hd:Measurable d)
    (hgv:ExpGrowth v) (hgw:ExpGrowth w) (hgz:ExpGrowth z)
    (hgr:ExpGrowth r) (hgs:ExpGrowth s) (hgd:ExpGrowth d)
    (hgb:ExpGrowth (fun x ↦ -w x/r x))
    (hgj:ExpGrowth (fun x ↦ a x-s x/r x*v x))
    (hint:∀ F:ℝ → ℝ,ExpGrowth F → Measurable F → Integrable (fun x ↦ F x*f x))
    (hf:∀ x,0≤f x) (hrn:∀ x,x≠0 → r x≠0)
    (hKv:∀ x,x≠0 → 0≤r x*s x ∧ 0≤v x ∧ 0≤ -w x/r x-2*v x ∧
      0≤a x-s x/r x*v x ∧ 0≤ -r x*d x ∧
      0≤z x+(-w x/r x)*v x-2*(r x^2)*(-w x/r x))
    (hzero:(∫ x,W₂ (r x^2) (r x*s x) (v x) (-w x/r x) (a x-s x/r x*v x)
      (z x) (-r x*d x)*f x)=0) :
    (1/1000:ℝ)*(∫ x,v x^4*f x)≤∫ x,(z x^2-12*v x*w x^2+6*v x^4)*f x := by
  let W:=fun x ↦ W₂ (r x^2) (r x*s x) (v x) (-w x/r x) (a x-s x/r x*v x)
      (z x) (-r x*d x)
  have hWg:ExpGrowth W := growth_W (hgr.pow 2) (hgr.mul hgs) hgv hgb hgj hgz (hgr.neg.mul hgd)
  have hWm:Measurable W := by dsimp [W,W₂,F₂];fun_prop
  have hWi:=hint _ hWg hWm
  have hvi:=hint _ (hgv.pow 4) (hv.pow_const 4)
  have hMi:=hint _ (((hgz.pow 2).sub (((ExpGrowth.const 12).mul hgv).mul (hgw.pow 2))).add
      ((ExpGrowth.const 6).mul (hgv.pow 4))) (by fun_prop)
  have hP:∀ᵐ x:ℝ,((1661507/1521000000:ℝ)*v x^4+W x)*f x≤
      (z x^2-12*v x*w x^2+6*v x^4)*f x := by
    filter_upwards [show ∀ᵐ x:ℝ,x≠0 from by rw [ae_iff]; simp] with x hx
    obtain ⟨hK,hv0,hB,hj,hL,hS⟩:=hKv x hx
    have hp:=pointwise_coercivity (sq_nonneg (r x)) hK hv0 hB hj hL (by
      simpa only [sub_add_cancel] using hS)
    simp only [sub_add_cancel] at hp
    have he:(r x^2)*v x*(-w x/r x)^2=v x*w x^2 := by
      field_simp [hrn x hx]
    have hp':(1661507/1521000000:ℝ)*v x^4+W x≤z x^2-12*v x*w x^2+6*v x^4 := by
      dsimp [W]
      nlinarith only [hp,he]
    exact mul_le_mul_of_nonneg_right hp' (hf x)
  have hsum:Integrable (fun x ↦ ((1661507/1521000000:ℝ)*v x^4+W x)*f x) := by
    convert! (hvi.const_mul (1661507/1521000000:ℝ)).add hWi using 1
    funext x; simp only [Pi.add_apply]; ring
  have hi:=integral_mono_ae hsum hMi hP
  have he:(∫ x,((1661507/1521000000:ℝ)*v x^4+W x)*f x)=
      (1661507/1521000000:ℝ)*(∫ x,v x^4*f x) := by
    simp_rw [add_mul,mul_assoc]
    rw [integral_add (hvi.const_mul _) hWi,integral_const_mul,hzero,add_zero]
  rw [he] at hi
  have hvnon:0≤∫ x,v x^4*f x := integral_nonneg (fun x ↦ mul_nonneg (by positivity) (hf x))
  nlinarith
end SKValue.Certificate

end

section

open Set Filter MeasureTheory
open scoped Topology
namespace SKValue
lemma BackwardShape.certificate_signs {A:ℝ → ℝ} {c:ℝ} (hA:SmoothTerminal A)
    (hB:BackwardShape c A) (hc:0<c) (D:ForwardDensityData)
    (hsl:∀ x,0≤D.jet 1 x) (hsc:∀ x,0≤x → D.jet 2 x≤0)
    (hJ:∀ x,0≤x → 0≤ spatialJet c A 0 x*D.jet 1 x-D.jet 0 x*spatialJet c A 1 x) :
    ∀ x,x≠0 →
    0≤ spatialJet c A 0 x*D.jet 0 x ∧ 0≤ spatialJet c A 1 x ∧
    0≤ -spatialJet c A 2 x/spatialJet c A 0 x-2*spatialJet c A 1 x ∧
    0≤D.jet 1 x-D.jet 0 x/spatialJet c A 0 x*spatialJet c A 1 x ∧
    0≤ -spatialJet c A 0 x*D.jet 2 x ∧
    0≤ spatialJet c A 3 x+(-spatialJet c A 2 x/spatialJet c A 0 x)*spatialJet c A 1 x-
      2*(spatialJet c A 0 x^2)*(-spatialJet c A 2 x/spatialJet c A 0 x) := by
  obtain ⟨hr,hv,hw,hz⟩:=hA.spatialJet_parity hB.even c
  obtain ⟨hs,ha,hd⟩:=D.jet_parity
  have hr0:spatialJet c A 0 0=0 := by have hh:=hr 0;simp only [neg_zero] at hh;linarith
  have hs0:D.jet 0 0=0 := by have he:=hs 0;simp only [neg_zero] at he;linarith
  have hvpos (x:ℝ):0<spatialJet c A 1 x := by
    simpa only [spatialJet,iteratedDeriv_one] using mul_pos hc (hB.convex x)
  have hrpos (x:ℝ) (hx:0<x):0<spatialJet c A 0 x := by
    have hm:=strictMono_of_deriv_pos (fun y ↦ by rw [(hA.spatialJet_space c 0 y).deriv];exact hvpos y)
    simpa only [hr0] using hm hx
  have hspos (x:ℝ) (hx:0≤x):0≤D.jet 0 x := by
    have hm:=monotone_of_deriv_nonneg (fun y ↦ (D.jet_space 0 y).differentiableAt)
      (fun y ↦ by rw [(D.jet_space 0 y).deriv];exact hsl y)
    simpa only [hs0] using hm hx
  have hpositive (x:ℝ) (hx:0<x) :
      0≤ spatialJet c A 0 x*D.jet 0 x ∧ 0≤ spatialJet c A 1 x ∧
      0≤ -spatialJet c A 2 x/spatialJet c A 0 x-2*spatialJet c A 1 x ∧
      0≤D.jet 1 x-D.jet 0 x/spatialJet c A 0 x*spatialJet c A 1 x ∧
      0≤ -spatialJet c A 0 x*D.jet 2 x ∧
      0≤ spatialJet c A 3 x+(-spatialJet c A 2 x/spatialJet c A 0 x)*spatialJet c A 1 x-
        2*(spatialJet c A 0 x^2)*(-spatialJet c A 2 x/spatialJet c A 0 x) := by
    have hrp:=hrpos x hx
    refine ⟨mul_nonneg hrp.le (hspos x hx.le),(hvpos x).le,?_,?_,?_,?_⟩
    · have hk:=hB.k x hx.le
      dsimp only [spatialK] at hk
      apply sub_nonneg.mpr
      apply (le_div_iff₀ hrp).mpr
      nlinarith
    · have hj:=hJ x hx.le
      apply (mul_nonneg_iff_of_pos_right hrp).mp
      field_simp
      nlinarith
    · exact mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.mpr hrp.le) (hsc x hx.le)
    · have hn:=hB.n x hx.le
      dsimp only [spatialN] at hn
      apply (mul_nonneg_iff_of_pos_right hrp).mp
      field_simp
      nlinarith
  intro x hx
  rcases lt_or_gt_of_ne hx with hn | hp
  · have hh:=hpositive (-x) (neg_pos.mpr hn)
    simpa only [hr,hv,hw,hz,hs,ha,hd,neg_mul_neg,neg_neg,div_neg,neg_div,neg_sq,neg_mul,mul_neg] using hh
  · exact hpositive x hp

lemma BackwardShape.integrated_certificate {A:ℝ → ℝ} {c:ℝ} (hA:SmoothTerminal A)
    (hB:BackwardShape c A) (hc:0<c) (D:ForwardDensityData)
    (hsl:∀ x,0≤D.jet 1 x) (hsc:∀ x,0≤x → D.jet 2 x≤0)
    (hJ:∀ x,0≤x → 0≤ spatialJet c A 0 x*D.jet 1 x-D.jet 0 x*spatialJet c A 1 x) :
    (1/1000:ℝ)*(∫ x,(spatialJet c A 1 x)^4*(Real.exp (c*A x)*D.weight x))≤
      ∫ x,((spatialJet c A 3 x)^2-12*spatialJet c A 1 x*(spatialJet c A 2 x)^2+
        6*(spatialJet c A 1 x)^4)*(Real.exp (c*A x)*D.weight x) := by
  let r:=spatialJet c A 0
  let v:=spatialJet c A 1
  let w:=spatialJet c A 2
  let z:=spatialJet c A 3
  let s:=D.jet 0
  let a:=D.jet 1
  let d:=D.jet 2
  let f:=fun x ↦ Real.exp (c*A x)*D.weight x
  obtain ⟨hr,hev,hw,hez⟩:=hA.spatialJet_parity hB.even c
  obtain ⟨hs,hea,hdd⟩:=D.jet_parity
  have hr0:r 0=0 := by have hh:=hr 0;change r (-0)= -r 0 at hh;simp only [neg_zero] at hh;linarith
  have hw0:w 0=0 := by have hh:=hw 0;change w (-0)= -w 0 at hh;simp only [neg_zero] at hh;linarith
  have hs0:s 0=0 := by have hh:=hs 0;change s (-0)= -s 0 at hh;simp only [neg_zero] at hh;linarith
  have hvpos (x:ℝ):0<v x := by
    simpa only [v,spatialJet,iteratedDeriv_one] using mul_pos hc (hB.convex x)
  have hrmono:StrictMono r := strictMono_of_deriv_pos (fun y ↦ by
    rw [(hA.spatialJet_space c 0 y).deriv];exact hvpos y)
  have hrpos:∀ x,0<x → 0<r x := fun x hx ↦ by simpa only [hr0] using hrmono hx
  have hrn:∀ x,x≠0 → r x≠0 := fun x hx he ↦ hx (hrmono.injective (he.trans hr0.symm))
  have hg (n:ℕ):ExpGrowth (spatialJet c A n) := hA.spatialJet_growth c n
  have hgb:ExpGrowth (fun x ↦ -w x/r x) :=
    (hg 2).neg.div_odd_monotone (by change -w 0=0;rw [hw0];ring) hr0 ((hA.spatialJet_space c 2 0).neg)
      (hA.spatialJet_space c 0 0) (hvpos 0) hr hrmono.monotone hrpos
  have hgsr:ExpGrowth (fun x ↦ s x/r x) :=
    (D.jet_growth 0).div_odd_monotone hs0 hr0 (D.jet_space 0 0)
      (hA.spatialJet_space c 0 0) (hvpos 0) hr hrmono.monotone hrpos
  have hgj:ExpGrowth (fun x ↦ a x-s x/r x*v x) := (D.jet_growth 1).sub (hgsr.mul (hg 1))
  have hm (n:ℕ):Measurable (spatialJet c A n) :=
    (continuous_iff_continuousAt.mpr (fun x ↦ (hA.spatialJet_space c n x).continuousAt)).measurable
  have hmd (n:ℕ):Measurable (D.jet n) := (D.jet_continuous n).measurable
  have hint:∀ F:ℝ → ℝ,ExpGrowth F → Measurable F → Integrable (fun x ↦ F x*f x) :=
    fun F hF hmF ↦ Certificate.ForwardDensityData.integrable_density_factor D hA hc.le hF hmF
  have hzero:=Certificate.integral_W_zero (hA.spatialJet_space c 0) (hA.spatialJet_space c 1)
    (hA.spatialJet_space c 2) (D.jet_space 0) (D.jet_space 1)
    (D.density_derivative hA) (hm 3) (hmd 2) hr0 hrn (hg 0) (hg 1) (hg 3)
    (D.jet_growth 0) (D.jet_growth 1) (D.jet_growth 2) hgb hgj hint
  exact Certificate.integrated_coercivity (hm 0) (hm 1) (hm 2) (hm 3) (hmd 0) (hmd 1) (hmd 2)
    (hg 1) (hg 2) (hg 3) (hg 0) (D.jet_growth 0) (D.jet_growth 2) hgb hgj hint
    (fun x ↦ mul_nonneg (Real.exp_pos _).le (D.weight_pos x).le) hrn
    (hB.certificate_signs hA hc D hsl hsc hJ) hzero
end SKValue

end

end OAI
