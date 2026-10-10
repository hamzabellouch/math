import Mathlib
import OAI.Probability.SKFluctuations.FinitePrefixRoot

namespace OAI

/-! Residual Root Moment. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology
open MeasureTheory Filter Set
open scoped Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus Scalar
open scoped Topology NNReal BigOperators

section
variable (α : NonnegativeMassProfile) (hα : ∀ s, α.mass s ≤ 1) (l : ℝ) (t : ℝ≥0)
    {m : ℝ} (hm : 0 < m) (hmα : m ≤ α.mass l) (r : ℝ≥0)

include hm hmα

theorem scalarClockProfile_residual_transversality {R : GaussianResidual} (hR : R.residual.Cone)
    (hzero : (∫ x, R.density x*Real.exp (m*scalarClockProfileJet α hα l t m r 0 x)*
      ((scalarClockProfileJet α hα l t m r 3 x)^2-
        2*m*(scalarClockProfileJet α hα l t m r 2 x)^3)) = 0) :
    0 < ∫ x, R.density x*Real.exp (m*scalarClockProfileJet α hα l t m r 0 x)*
      ((scalarClockProfileJet α hα l t m r 4 x)^2-
        12*m*scalarClockProfileJet α hα l t m r 2 x*(scalarClockProfileJet α hα l t m r 3 x)^2+
        6*m^2*(scalarClockProfileJet α hα l t m r 2 x)^4) := by
  let j := scalarClockProfileJet α hα l t m r
  let S := scalarClockProfileSlice α hα l t hm hmα r
  let E := fun x : ℝ => R.density x*Real.exp (m*j 0 x)
  let f := fun x : ℝ => E x*((j 3 x)^2-2*m*(j 2 x)^3)
  let g := fun x : ℝ => E x*((j 4 x)^2-12*m*j 2 x*(j 3 x)^2+6*m^2*(j 2 x)^4)
  have hj0 (x) : j 0 (-x) = j 0 x := by
    simpa only [pow_zero,one_mul] using scalarClockProfileJet_parity α hα l t hm r 0 x
  have hj2 (x) : j 2 (-x) = j 2 x := by
    simpa using scalarClockProfileJet_parity α hα l t hm r 2 x
  have hj3 (x) : j 3 (-x) = -j 3 x := by
    simpa only [show (-1:ℝ)^3 = -1 by norm_num,neg_one_mul] using scalarClockProfileJet_parity α hα l t hm r 3 x
  have hj4 (x) : j 4 (-x) = j 4 x := by
    simpa only [show (-1:ℝ)^4 = 1 by norm_num,one_mul] using scalarClockProfileJet_parity α hα l t hm r 4 x
  have hden (x : ℝ) : R.density (-x) = R.density x := by
    have he := GaussianResidual.potential_even hR x
    have hd (y : ℝ) : R.density y = Real.exp (-R.potential y) := by
      simp only [GaussianResidual.potential,neg_neg,Real.exp_log (R.density_pos y)]
    rw [hd,hd,he]
  have hE (x) : E (-x) = E x := by simp only [E,hj0,hden]
  have hf (x) : f (-x) = f x := by simp only [f,hE,hj2,hj3,neg_sq]
  have hg (x) : g (-x) = g x := by simp only [g,hE,hj2,hj3,hj4,neg_sq]
  have hfzero : (∫ x, f x) = 0 := hzero
  change 0 < ∫ x, g x
  have hfw (x : ℝ) : f x = 2*(R.rootWeight S (j 0) x*S.Φ x) := by
    dsimp only [f]
    rw [scalarClockProfileSlice_second α hα l t hm hmα r]
    rw [R.rootWeight_eq]
    dsimp only [E,S,j]
    ring
  have hgw (x : ℝ) : g x = R.rootWeight S (j 0) x*S.thirdTest x := by
    dsimp only [g]
    rw [scalarClockProfileSlice_third α hα l t hm hmα r]
    rw [R.rootWeight_eq]
    dsimp only [E,S,j]
    ring
  have hcenter : ∫ x in Ioi 0, R.rootWeight S (j 0) x*S.Φ x = 0 := by
    rw [integral_even_eq_two_Ioi hf] at hfzero
    simp_rw [hfw] at hfzero
    rw [integral_const_mul] at hfzero
    linarith
  have hroot := scalarClockProfileSlice_residual_root_pos α hα l t hm hmα r hR hcenter
  rw [integral_even_eq_two_Ioi hg]
  simp_rw [hgw]
  exact mul_pos (by norm_num) hroot

end
end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations.Scalar.PhysicalSlopeSlice
open Set Filter MeasureTheory
open scoped Topology

 theorem prefixGradient_lower {D E : ℝ → ℝ}
    (hD : ∀ x, HasDerivAt D (E x) x) (hD0 : D 0 = 0)
    {c : ℝ} (hE : ∀ x, c ≤ E x) {x : ℝ} (hx : 0 ≤ x) : c*x ≤ D x := by
  have hd (y : ℝ) : HasDerivAt (fun y => D y-c*y) (E y-c) y := by
    convert (hD y).sub ((hasDerivAt_id y).const_mul c) using 1 <;> first | rfl | simp only [mul_one]
  have hm : Monotone (fun y => D y-c*y) := monotone_of_deriv_nonneg
    (fun y => (hd y).differentiableAt) (fun y => by rw [(hd y).deriv]; exact sub_nonneg.mpr (hE y))
  have hh := hm hx
  simp only [hD0,mul_zero,sub_zero] at hh
  linarith

theorem potentialTerm_quadratic_monotone {D E H : ℝ → ℝ}
    (hD : ∀ x, HasDerivAt D (E x) x) (hE : ∀ x, HasDerivAt E (H x) x)
    (hD0 : D 0 = 0) {c : ℝ} (hc : 0 ≤ c) (hEc : ∀ x, c ≤ E x)
    (hHn : ∀ x, 0 ≤ x → H x ≤ 0) :
    MonotoneOn (fun x => potentialTerm D E x-c^2*x^2/2) (Ici 0) := by
  have hd (x : ℝ) : HasDerivAt (fun x => potentialTerm D E x-c^2*x^2/2)
      (D x*E x-H x/2-c^2*x) x := by
    convert (dpotentialTerm hD hE x).sub
      ((((hasDerivAt_id x).pow 2).const_mul (c^2)).div_const 2) using 1 <;> first | rfl | (simp only [id_eq]; ring)
  apply monotoneOn_of_deriv_nonneg (convex_Ici _)
    (continuous_iff_continuousAt.mpr fun x => (hd x).continuousAt).continuousOn
    (fun x _ => (hd x).differentiableAt.differentiableWithinAt)
  intro x hx
  rw [interior_Ici] at hx
  change 0 < x at hx
  rw [(hd x).deriv]
  have hl := prefixGradient_lower hD hD0 hEc hx.le
  have hp := mul_le_mul hl (hEc x) hc (le_trans (mul_nonneg hc hx.le) hl)
  nlinarith [hHn x hx.le]

end SKFluctuations.Scalar.PhysicalSlopeSlice

 

 

namespace SKFluctuations.Scalar
open Set Filter MeasureTheory
open scoped Topology

theorem onePeak_lower {g w L : ℝ → ℝ} {b v : ℝ}
    (hc : ContinuousOn g (Ici 0)) (hd : ∀ x, 0 < x → HasDerivAt g (w x*L x) x)
    (hw : ∀ x, 0 < x → 0 ≤ w x) (hL : AntitoneOn L (Ioi 0))
    (hzero : b ≤ g 0) (htop : Tendsto g atTop (𝓝 v)) (hv : b ≤ v)
    {x : ℝ} (hx : 0 ≤ x) : b ≤ g x := by
  rcases hx.eq_or_lt with rfl|hx
  · exact hzero
  by_cases hsign : 0 ≤ L x
  · have hm : MonotoneOn g (Icc 0 x) := monotoneOn_of_deriv_nonneg (convex_Icc ..)
      (hc.mono Icc_subset_Ici_self) (by
        intro y hy
        rw [interior_Icc] at hy
        exact (hd y hy.1).differentiableAt.differentiableWithinAt) (by
        intro y hy
        rw [interior_Icc] at hy
        rw [(hd y hy.1).deriv]
        exact mul_nonneg (hw y hy.1) (hsign.trans (hL hy.1 hx hy.2.le)))
    exact hzero.trans (hm ⟨le_rfl,hx.le⟩ ⟨hx.le,le_rfl⟩ hx.le)
  · have hm : AntitoneOn g (Ici x) := antitoneOn_of_deriv_nonpos (convex_Ici _)
      (hc.mono (Ici_subset_Ici.mpr hx.le)) (by
        intro y hy
        rw [interior_Ici] at hy
        exact (hd y (hx.trans hy)).differentiableAt.differentiableWithinAt) (by
        intro y hy
        rw [interior_Ici] at hy
        rw [(hd y (hx.trans hy)).deriv]
        exact mul_nonpos_of_nonneg_of_nonpos (hw y (hx.trans hy))
          ((hL hx (hx.trans hy) hy.le).trans (lt_of_not_ge hsign).le))
    apply hv.trans
    apply le_of_tendsto htop
    filter_upwards [eventually_ge_atTop x] with y hy
    exact hm (show x ∈ Ici x from Set.mem_Ici.mpr (le_refl x)) hy hy

theorem weight_mul_lower {w l φ v : ℝ → ℝ}
    (hwl : ∀ x, 0 < x → l x ≤ w x)
    (hφ : MonotoneOn φ (Ici 0)) (hv : MonotoneOn v (Ici 0))
    {a : ℝ} (ha : 0 ≤ a) (hφa : φ a=0)
    (hi : IntegrableOn (fun x => w x*φ x) (Ioi 0))
    (hiv : IntegrableOn (fun x => w x*φ x*v x) (Ioi 0))
    (hil : IntegrableOn (fun x => l x*φ x*(v x-v a)) (Ioi 0)) :
    (∫ x in Ioi 0, l x*φ x*(v x-v a))+v a*(∫ x in Ioi 0, w x*φ x) ≤
      ∫ x in Ioi 0, w x*φ x*v x := by
  have hiwv : IntegrableOn (fun x => w x*φ x*(v x-v a)) (Ioi 0) := by
    simp_rw [mul_sub]
    exact hiv.sub (hi.mul_const _)
  have hh : (∫ x in Ioi 0, l x*φ x*(v x-v a)) ≤ ∫ x in Ioi 0, w x*φ x*(v x-v a) :=
    integral_mono_ae hil hiwv (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      simp only [mul_assoc]
      exact mul_le_mul_of_nonneg_right (hwl x hx)
        (monotone_root_product_nonneg hφ hv ha hφa hx.le))
  have he : (fun x => w x*φ x*(v x-v a)) = fun x => w x*φ x*v x-(w x*φ x)*v a := by funext x; ring
  rw [he,integral_sub hiv (hi.mul_const _),integral_mul_const] at hh
  linarith

theorem weight_mul_ge_center {w φ v : ℝ → ℝ}
    (hw : ∀ x, 0 < x → 0 ≤ w x)
    (hφ : MonotoneOn φ (Ici 0)) (hv : MonotoneOn v (Ici 0))
    {a : ℝ} (ha : 0 ≤ a) (hφa : φ a=0)
    (hi : IntegrableOn (fun x => w x*φ x) (Ioi 0))
    (hiv : IntegrableOn (fun x => w x*φ x*v x) (Ioi 0)) :
    v a*(∫ x in Ioi 0, w x*φ x) ≤ ∫ x in Ioi 0, w x*φ x*v x := by
  have hh := weight_mul_lower (l:=fun _ => 0) hw hφ hv ha hφa hi hiv (by simp)
  simpa only [zero_mul,integral_zero,zero_add] using hh

namespace PhysicalSlopeSlice
variable {m : ℝ} (S : PhysicalSlopeSlice m)

theorem weighted_tail_bounds_near {D E : ℝ → ℝ} (hD : ∀ x, HasDerivAt D (E x) x)
    (hD0 : D 0 = 0) (hEp : ∀ x, 0 < E x) (hm : 0 < m)
    {w F : ℝ → ℝ} (hw : ∀ x, 0 ≤ w x)
    (hdw : ∀ x, HasDerivAt w (w x*(-D x-S.A x-3*S.z x)) x)
    (hF : ∀ x, HasDerivAt F (-w x*S.Φ x) x)
    (hFt : Tendsto F atTop (𝓝 0))
    (hwzt : Tendsto (fun x => w x*S.z x) atTop (𝓝 0))
    {x : ℝ} (hx : 0 ≤ x) : -|F 0| ≤ F x ∧ F x ≤ w x*S.z x+|F 0| := by
  have hFc : Continuous F := continuous_iff_continuousAt.mpr fun x => (hF x).continuousAt
  constructor
  · exact onePeak_lower hFc.continuousOn (by
      intro y _
      simpa only [neg_mul,mul_neg] using hF y) (fun y _ => hw y)
      (S.Φ_strictMono hm |>.monotoneOn.mono Ioi_subset_Ici_self |>.neg)
      (neg_abs_le _) hFt (neg_nonpos.mpr (abs_nonneg _)) hx
  · have hd : ∀ y, HasDerivAt (fun y => w y*S.z y-F y) (w y*S.generalL D y) y := by
      intro y
      convert ((hdw y).mul (S.dz y)).sub (hF y) using 1;
        first | rfl | (dsimp only [generalL,Φ]; ring)
    have hh := onePeak_lower
      ((continuous_iff_continuousAt.mpr fun y => (hd y).continuousAt).continuousOn)
      (fun y _ => hd y) (fun y _ => hw y)
      (S.generalL_strictAnti hD hD0 hEp hm |>.antitoneOn.mono Ioi_subset_Ici_self)
      (show -|F 0| ≤ w 0*S.z 0-F 0 by rw [S.zzero,mul_zero,zero_sub]; exact neg_le_neg (le_abs_self _))
      (by simpa only [sub_zero] using hwzt.sub hFt) (neg_nonpos.mpr (abs_nonneg (F 0))) hx
    linarith

theorem correction_near {w F : ℝ → ℝ} (hm : 0 < m) {x e : ℝ} (hx : 0 ≤ x) (heps : 0 ≤ e)
    (hF : -e ≤ F x) (hFz : F x ≤ w x*S.z x+e) :
    -(7*e*S.z x*S.κ x) ≤ F x*(2*S.lam x-5*S.z x*S.κ x)+w x*S.G x := by
  have hk := S.κnonneg x hx
  have hz := S.z_nonneg hm hx
  have hc := S.cone x hx
  have hl := S.lamnonneg x hx
  have h1 := mul_le_mul_of_nonneg_left hFz (show 0 ≤ 2*(3*S.z x*S.κ x-S.lam x) by nlinarith)
  have h2 := mul_le_mul_of_nonneg_left hF (mul_nonneg hz hk)
  have he : F x*(2*S.lam x-5*S.z x*S.κ x)+w x*S.G x =
      2*(3*S.z x*S.κ x-S.lam x)*(w x*S.z x-F x)+S.z x*S.κ x*F x := by
    dsimp only [G]; ring
  rw [he]
  nlinarith [mul_nonneg heps hl]

end PhysicalSlopeSlice
end SKFluctuations.Scalar

 

 

namespace SKFluctuations.Scalar.PhysicalSlopeSlice
open Set Filter MeasureTheory
open scoped Topology
variable {m : ℝ} (S : PhysicalSlopeSlice m)

theorem generalNearRootIntegral_lower {w F : ℝ → ℝ} (hm : 0 < m)
    {D E H : ℝ → ℝ} (hD : ∀ x, HasDerivAt D (E x) x)
    (hE : ∀ x, HasDerivAt E (H x) x) (hD0 : D 0 = 0)
    {c : ℝ} (hc : 0 < c) (hEc : ∀ x, c ≤ E x) (hHn : ∀ x, 0 ≤ x → H x ≤ 0)
    ( _hw : Continuous w) (hwp : ∀ x, 0 < w x)
    (hdw : ∀ x, HasDerivAt w (w x*(-D x-S.A x-3*S.z x)) x)
    (hi : IntegrableOn (fun x => w x*S.Φ x) (Ioi 0))
    (hiQ : IntegrableOn (fun x => w x*S.Φ x*x^2) (Ioi 0))
    (hi₂ : IntegrableOn (fun x => w x*S.Φ x*potentialTerm D E x) (Ioi 0))
    (hi₁ : IntegrableOn (fun x => w x*S.Φ x*S.generalR₁ D x) (Ioi 0))
    (hi₀ : IntegrableOn (fun x => w x*S.Φ x*S.R₀ x) (Ioi 0))
    (hiG : IntegrableOn (fun x => w x*S.G x) (Ioi 0))
    (hiT : IntegrableOn (fun x => w x*S.thirdTest x) (Ioi 0))
    (hF : ∀ x, HasDerivAt F (-w x*S.Φ x) x)
    (hF0 : F 0=∫ x in Ioi 0, w x*S.Φ x) (hFt : Tendsto F atTop (𝓝 0))
    (hiF : IntegrableOn (fun x => F x*(2*S.lam x-5*S.z x*S.κ x)) (Ioi 0))
    (hizk : IntegrableOn (fun x => S.z x*S.κ x) (Ioi 0))
    (htz : Tendsto (fun x => w x*S.z x) atTop (𝓝 0))
    (htF : Tendsto (fun x => F x*S.R₀ x) atTop (𝓝 0))
    (htFlux : Tendsto (fun x => w x*S.generalFlux D x) atTop (𝓝 0))
    {a : ℝ} (ha : 0 ≤ a) (hφa : S.Φ a=0) :
    c^2*(∫ x in Ioi 0, w x*S.Φ x*x^2)+
      2*(∫ x in Ioi 0, w x*S.Φ x)*
        (potentialTerm D E a-c^2*a^2/2+S.generalR₁ D a+S.R₀ 0)-
      14*|∫ x in Ioi 0, w x*S.Φ x| *(∫ x in Ioi 0, S.z x*S.κ x) ≤
      ∫ x in Ioi 0, w x*S.thirdTest x := by
  have hEp (x) : 0 < E x := hc.trans_le (hEc x)
  have hFb (x : ℝ) (hx : 0 ≤ x) :
      -|∫ y in Ioi 0, w y*S.Φ y| ≤ F x ∧
      F x ≤ w x*S.z x+|∫ y in Ioi 0, w y*S.Φ y| := by
    simpa only [hF0] using S.weighted_tail_bounds_near hD hD0 hEp hm
      (fun y => (hwp y).le) hdw hF hFt htz hx
  have hiRem : IntegrableOn (fun x => w x*S.Φ x*(potentialTerm D E x-c^2*x^2/2)) (Ioi 0) := by
    apply (hi₂.sub (hiQ.mul_const (c^2/2))).congr
    filter_upwards [] with x
    dsimp only [Pi.sub_apply]
    ring
  have hRem : (potentialTerm D E a-c^2*a^2/2)*(∫ x in Ioi 0, w x*S.Φ x) ≤
      ∫ x in Ioi 0, w x*S.Φ x*(potentialTerm D E x-c^2*x^2/2) :=
    weight_mul_ge_center (fun x _ => (hwp x).le) (S.Φ_strictMono hm).monotoneOn
      (potentialTerm_quadratic_monotone hD hE hD0 hc.le hEc hHn) ha hφa hi hiRem
  have h₂ : c^2/2*(∫ x in Ioi 0, w x*S.Φ x*x^2)+
      (potentialTerm D E a-c^2*a^2/2)*(∫ x in Ioi 0, w x*S.Φ x) ≤
      ∫ x in Ioi 0, w x*S.Φ x*potentialTerm D E x := by
    have he : (fun x => w x*S.Φ x*(potentialTerm D E x-c^2*x^2/2)) =
        fun x => w x*S.Φ x*potentialTerm D E x-(w x*S.Φ x*x^2)*(c^2/2) := by
      funext x; ring
    rw [he,integral_sub hi₂ (hiQ.mul_const _),integral_mul_const] at hRem
    linarith
  have h₁ : S.generalR₁ D a*(∫ x in Ioi 0, w x*S.Φ x) ≤
      ∫ x in Ioi 0, w x*S.Φ x*S.generalR₁ D x := weight_mul_ge_center
    (fun x _ => (hwp x).le) (S.Φ_strictMono hm).monotoneOn (S.generalR₁_monotone hD hD0 hEp)
    ha hφa hi hi₁
  have hFi : IntegrableOn (fun x => -w x*S.Φ x*S.R₀ x+F x*(2*S.lam x-5*S.z x*S.κ x)) (Ioi 0) := by
    apply (hi₀.neg.add hiF).congr
    filter_upwards [] with x
    simp only [Pi.add_apply,Pi.neg_apply,neg_mul]
  have hIBP := integral_Ioi_of_hasDerivAt_of_tendsto'
    (fun x _ => S.dweightedPrimitive hF x) hFi htF
  rw [hF0] at hIBP
  have hIBP' : (∫ x in Ioi 0, w x*S.Φ x*S.R₀ x) =
      (∫ x in Ioi 0, F x*(2*S.lam x-5*S.z x*S.κ x))+
        (∫ x in Ioi 0, w x*S.Φ x)*S.R₀ 0 := by
    simp_rw [neg_mul] at hIBP
    have hn : IntegrableOn (fun x => -(w x*S.Φ x*S.R₀ x)) (Ioi 0) := hi₀.neg
    rw [integral_add hn hiF,integral_neg] at hIBP
    linarith
  have hcint : -(7*|∫ x in Ioi 0, w x*S.Φ x| *(∫ x in Ioi 0, S.z x*S.κ x)) ≤
      (∫ x in Ioi 0, F x*(2*S.lam x-5*S.z x*S.κ x))+(∫ x in Ioi 0, w x*S.G x) := by
    have hh := integral_mono_ae ((hizk.const_mul (7*|∫ x in Ioi 0, w x*S.Φ x|)).neg)
      (hiF.add hiG) (by
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
        simp only [Pi.neg_apply,Pi.add_apply]
        simpa only [mul_assoc] using S.correction_near (w:=w) (F:=F) hm hx.le
          (abs_nonneg _) (hFb x hx.le).1 (hFb x hx.le).2)
    simpa only [Pi.neg_apply,Pi.add_apply,integral_neg,integral_const_mul,integral_add hiF hiG] using hh
  have hcor : (∫ x in Ioi 0, w x*S.Φ x)*S.R₀ 0-
      7*|∫ x in Ioi 0, w x*S.Φ x| *(∫ x in Ioi 0, S.z x*S.κ x) ≤
      (∫ x in Ioi 0, w x*S.Φ x*S.R₀ x)+(∫ x in Ioi 0, w x*S.G x) := by
    rw [hIBP']
    linarith
  have he : (fun x => w x*S.generalIntegrand D E x) = fun x =>
      (w x*S.Φ x*potentialTerm D E x+w x*S.Φ x*S.generalR₁ D x+w x*S.Φ x*S.R₀ x)+w x*S.G x := by
    funext x; dsimp only [generalIntegrand]; ring
  have hi21 : IntegrableOn (fun x => w x*S.Φ x*potentialTerm D E x+w x*S.Φ x*S.generalR₁ D x) (Ioi 0) := hi₂.add hi₁
  have hi210 : IntegrableOn (fun x => w x*S.Φ x*potentialTerm D E x+w x*S.Φ x*S.generalR₁ D x+w x*S.Φ x*S.R₀ x) (Ioi 0) := hi21.add hi₀
  have hroot : IntegrableOn (fun x => w x*S.generalIntegrand D E x) (Ioi 0) := by
    rw [he]
    exact hi210.add hiG
  have heq : (∫ x in Ioi 0, w x*S.generalIntegrand D E x) =
      (∫ x in Ioi 0, w x*S.Φ x*potentialTerm D E x)+
      (∫ x in Ioi 0, w x*S.Φ x*S.generalR₁ D x)+
      (∫ x in Ioi 0, w x*S.Φ x*S.R₀ x)+(∫ x in Ioi 0, w x*S.G x) := by
    rw [he,integral_add hi210 hiG,integral_add hi21 hi₀,integral_add hi₂ hi₁]
  have hrlower : c^2/2*(∫ x in Ioi 0, w x*S.Φ x*x^2)+
      (∫ x in Ioi 0, w x*S.Φ x)*(potentialTerm D E a-c^2*a^2/2+S.generalR₁ D a+S.R₀ 0)-
      7*|∫ x in Ioi 0, w x*S.Φ x| *(∫ x in Ioi 0, S.z x*S.κ x) ≤
      ∫ x in Ioi 0, w x*S.generalIntegrand D E x := by
    rw [heq]
    nlinarith
  have hfluxi : IntegrableOn (fun x => w x*(S.thirdTest x/2-S.generalIntegrand D E x)) (Ioi 0) := by
    apply ((hiT.mul_const (1/2)).sub hroot).congr
    filter_upwards [] with x
    simp only [Pi.sub_apply]; ring
  have hfint := integral_Ioi_of_hasDerivAt_of_tendsto'
    (fun x _ => S.dweightedGeneralFlux hD hdw x) hfluxi htFlux
  simp only [S.generalFlux_zero hD0,mul_zero,sub_zero] at hfint
  have he : (fun x => w x*(S.thirdTest x/2-S.generalIntegrand D E x)) =
      fun x => (w x*S.thirdTest x)*(1/2)-w x*S.generalIntegrand D E x := by funext x; ring
  rw [he,integral_sub (hiT.mul_const _) hroot,integral_mul_const] at hfint
  nlinarith

end SKFluctuations.Scalar.PhysicalSlopeSlice

 

 

namespace SKFluctuations.Hierarchy
open scoped NNReal

theorem AbsBounded.div_const {E : Type*} {f : E → ℝ} (hf : AbsBounded f) (c : ℝ) :
    AbsBounded (fun x => f x/c) := by
  simpa only [div_eq_mul_inv,mul_comm] using hf.const_mul c⁻¹

end SKFluctuations.Hierarchy
namespace SKFluctuations.Scalar
open Hierarchy
variable {m : ℝ} (j : ℕ → ℝ → ℝ)
  (hd : ∀ k x, HasDerivAt (j k) (j (k+1) x) x)
  (hp : ∀ x, 0 < j 2 x) (h1 : j 1 0 = 0) (h3 : j 3 0 = 0)
  (hs : PolynomialSigns m j)

theorem physicalSlopeOfJets_absBounded (hb : ∀ k, AbsBounded (j (k+1)))
    (hr : ∀ k, AbsBounded (fun x => j (k+2) x/j 2 x)) :
    let S := physicalSlopeOfJets j hd hp h1 h3 hs
    AbsBounded S.B ∧ AbsBounded S.C ∧ AbsBounded S.z ∧
      AbsBounded S.κ ∧ AbsBounded S.lam := by
  dsimp only
  have hC : AbsBounded (j 2) := hb 1
  have h3r : AbsBounded (fun x => j 3 x/j 2 x) := hr 1
  have h4r : AbsBounded (fun x => j 4 x/j 2 x) := hr 2
  have h5r : AbsBounded (fun x => j 5 x/j 2 x) := hr 3
  refine ⟨hb 0,hC,?_,?_,?_⟩
  · have he : (physicalSlopeOfJets j hd hp h1 h3 hs).z = fun x => -(j 3 x/j 2 x)/2 := by
      funext x; dsimp only [physicalSlopeOfJets]; ring
    rw [he]
    exact h3r.neg.div_const 2
  · have he : (physicalSlopeOfJets j hd hp h1 h3 hs).κ = fun x =>
        -m*j 2 x-j 4 x/j 2 x/2+(j 3 x/j 2 x)^2/2 := by
      funext x; dsimp only [physicalSlopeOfJets,invariantP]; field_simp [(hp x).ne']
    rw [he]
    exact ((hC.const_mul (-m)).sub (h4r.div_const 2)).add ((h3r.pow 2).div_const 2)
  · have he : (physicalSlopeOfJets j hd hp h1 h3 hs).lam = fun x =>
        -(j 5 x/j 2 x)/2+2*(j 3 x/j 2 x)*(j 4 x/j 2 x)-3*(j 3 x/j 2 x)^3/2 := by
      funext x; dsimp only [physicalSlopeOfJets,invariantQ]; field_simp [(hp x).ne']
    rw [he]
    exact ((h5r.neg.div_const 2).add ((h3r.const_mul 2).mul h4r)).sub
      (((h3r.pow 3).const_mul 3).div_const 2)

end SKFluctuations.Scalar
namespace SKFluctuations.Hierarchy
open scoped NNReal
open Scalar

theorem scalarClockProfileSlice_absBounded (α : NonnegativeMassProfile)
    (hα : ∀ s, α.mass s ≤ 1) (l : ℝ) (t : ℝ≥0)
    {m : ℝ} (hm : 0 < m) (hmα : m ≤ α.mass l) (r : ℝ≥0) :
    let S := scalarClockProfileSlice α hα l t hm hmα r
    AbsBounded S.B ∧ AbsBounded S.C ∧ AbsBounded S.z ∧ AbsBounded S.κ ∧ AbsBounded S.lam := by
  apply physicalSlopeOfJets_absBounded
  · exact scalarClockProfileJet_absBounded α hα l t hm r
  · intro k
    exact absBounded_ratio (scalarClockProfileJet_curvature_pos α hα l t hm hmα r)
      (by positivity : 0 ≤ (ReplicaTree.attachmentCount 1 (k+1):ℝ)/m)
      (scalarClockProfile_relative_curvature α hα l t hm hmα r k)

end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations.Scalar.PhysicalSlopeSlice
open MeasureTheory Filter Set Hierarchy
open scoped Topology
variable {m : ℝ} (S : PhysicalSlopeSlice m)

theorem A_monotone : MonotoneOn S.A (Ici 0) := by
  apply monotoneOn_of_deriv_nonneg (convex_Ici _)
    S.continuous_A.continuousOn (fun y _ => (S.dA y).differentiableAt.differentiableWithinAt)
  intro x hx
  rw [interior_Ici] at hx
  rw [(S.dA x).deriv]
  exact S.κnonneg x hx.le

theorem kappa_integrable (hB : AbsBounded S.B) (hz : AbsBounded S.z) :
    IntegrableOn S.κ (Ioi 0) := by
  have hA : AbsBounded S.A := hz.sub (hB.const_mul m)
  obtain ⟨K,_,hK⟩ := hA
  let f : ℝ → ℝ := fun x => S.A (max x 0)
  have hf : Monotone f := fun x y hxy => S.A_monotone
    (le_max_right x 0) (le_max_right y 0) (max_le_max_right 0 hxy)
  have hb : BddAbove (range f) := ⟨K,by rintro _ ⟨x,rfl⟩; exact (le_abs_self _).trans (hK _)⟩
  have ht : Tendsto S.A atTop (𝓝 (⨆ x, f x)) := (tendsto_atTop_ciSup hf hb).congr' (by
    filter_upwards [eventually_ge_atTop (0:ℝ)] with x hx
    exact congrArg S.A (max_eq_left hx))
  exact integrableOn_Ioi_deriv_of_nonneg' (fun x _ => S.dA x) (fun x hx => S.κnonneg x hx.le) ht

theorem z_kappa_integrable (hB : AbsBounded S.B) (hz : AbsBounded S.z) :
    IntegrableOn (fun x => S.z x*S.κ x) (Ioi 0) := by
  obtain ⟨K,hK,hb⟩ := hz
  apply ((S.kappa_integrable hB ⟨K,hK,hb⟩).abs.const_mul K).mono'
    (S.continuous_z.mul S.continuous_κ).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  simp only [Real.norm_eq_abs,Pi.mul_apply,abs_mul]
  exact mul_le_mul_of_nonneg_right (hb x) (abs_nonneg _)

theorem correction_rate_integrable (hm : 0 < m) (hB : AbsBounded S.B) (hz : AbsBounded S.z)
    (hl : Continuous S.lam) :
    IntegrableOn (fun x => 2*S.lam x-5*S.z x*S.κ x) (Ioi 0) := by
  have hi := (S.z_kappa_integrable hB hz).const_mul 5
  apply hi.mono' ((hl.const_mul 2).sub ((S.continuous_z.const_mul 5).mul S.continuous_κ)).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  rw [Real.norm_eq_abs]
  have hz0 := S.z_nonneg hm hx.le
  have hk0 := S.κnonneg x hx.le
  have hl0 := S.lamnonneg x hx.le
  have hc := S.cone x hx.le
  change |2*S.lam x-5*S.z x*S.κ x| ≤ 5*(S.z x*S.κ x)
  rw [abs_le]
  constructor <;> nlinarith [mul_nonneg hz0 hk0]

 theorem Rzero_absBounded (hC : AbsBounded S.C) (hz : AbsBounded S.z) (hk : AbsBounded S.κ) :
    AbsBounded S.R₀ := ((hk.const_mul 2).sub ((hC.const_mul m).div_const 2)).sub
      ((hz.pow 2).div_const 2)

end SKFluctuations.Scalar.PhysicalSlopeSlice

 

 

namespace SKFluctuations.Scalar.PhysicalSlopeSlice
open MeasureTheory Set Filter
open scoped Topology
variable {m : ℝ} (S : PhysicalSlopeSlice m)

theorem generalNearRootIntegral_lower_gaussian {w : ℝ → ℝ} (hm : 0 < m)
    {D E H : ℝ → ℝ} (hD : ∀ x, HasDerivAt D (E x) x)
    (hE : ∀ x, HasDerivAt E (H x) x) (hD0 : D 0 = 0)
    {c : ℝ} (hc : 0 < c) (hEc : ∀ x, c ≤ E x) (hHn : ∀ x, 0 ≤ x → H x ≤ 0)
    (hpD : PolyBounded D) (hpE : PolyBounded E)
    (hw : Continuous w) (hwp : ∀ x, 0 < w x)
    (hdw : ∀ x, HasDerivAt w (w x*(-D x-S.A x-3*S.z x)) x)
    (hGauss : GaussianDominated w) (hbB : Hierarchy.AbsBounded S.B) (hbC : Hierarchy.AbsBounded S.C)
    (hbz : Hierarchy.AbsBounded S.z) (hbκ : Hierarchy.AbsBounded S.κ) (hlam : PolyBounded S.lam)
    (hcLam : Continuous S.lam)
    {a : ℝ} (ha : 0 ≤ a) (hφa : S.Φ a=0) :
    c^2*(∫ x in Ioi 0, w x*S.Φ x*x^2)+
      2*(∫ x in Ioi 0, w x*S.Φ x)*
        (potentialTerm D E a-c^2*a^2/2+S.generalR₁ D a+S.R₀ 0)-
      14*|∫ x in Ioi 0, w x*S.Φ x| * (∫ x in Ioi 0, S.z x*S.κ x) ≤
      ∫ x in Ioi 0, w x*S.thirdTest x := by
  have hEp (x) : 0 < E x := hc.trans_le (hEc x)
  have hB := PolyBounded.of_absBounded hbB
  have hC := PolyBounded.of_absBounded hbC
  have hz := PolyBounded.of_absBounded hbz
  have hκ := PolyBounded.of_absBounded hbκ
  have hA : PolyBounded S.A := hz.sub (hB.const_mul m)
  have hΦ : PolyBounded S.Φ := ((hz.pow 2).const_mul 2).sub (hC.const_mul m)
  have hR₀ : PolyBounded S.R₀ := ((hκ.const_mul 2).sub ((hC.const_mul m).div_const 2)).sub
    ((hz.pow 2).div_const 2)
  have hR₁ : PolyBounded (S.generalR₁ D) := (hA.mul hpD).add ((hA.pow 2).div_const 2)
  have hRV : PolyBounded (potentialTerm D E) := ((hpD.pow 2).sub hpE).div_const 2
  have hG : PolyBounded S.G := (hz.const_mul 2).mul (((hz.const_mul 3).mul hκ).sub hlam)
  have hT : PolyBounded S.thirdTest :=
    (((((hz.pow 2).const_mul 4).sub (hC.const_mul (2*m))).sub (hκ.const_mul 2)).pow 2 |>.sub
      ((hC.const_mul (48*m)).mul (hz.pow 2))).add ((hC.pow 2).const_mul (6*m^2))
  have hRate : PolyBounded (fun x => 2*S.lam x-5*S.z x*S.κ x) :=
    (hlam.const_mul 2).sub ((hz.const_mul 5).mul hκ)
  have hFlux : PolyBounded (S.generalFlux D) :=
    (hz.mul ((hκ.const_mul 2).add (hC.const_mul (3*m)))).add
      ((((hpD.div_const 2).sub ((hz.const_mul 3).div_const 2)).add (hA.div_const 2)).mul hΦ)
  have hcD : Continuous D := continuous_iff_continuousAt.mpr fun x => (hD x).continuousAt
  have hcE : Continuous E := continuous_iff_continuousAt.mpr fun x => (hE x).continuousAt
  have hcRV : Continuous (potentialTerm D E) := ((hcD.pow 2).sub hcE).div_const 2
  have hcB := S.continuous_B
  have hcC := S.continuous_C
  have hcz := S.continuous_z
  have hcκ := S.continuous_κ
  have hcA := S.continuous_A
  have hcR₀ : Continuous S.R₀ := by unfold R₀; fun_prop
  have hcR₁ : Continuous (S.generalR₁ D) := by unfold generalR₁; fun_prop
  have hcG : Continuous S.G := by unfold G; fun_prop
  have hcT : Continuous S.thirdTest := by unfold thirdTest; fun_prop
  have hcRate : Continuous (fun x => 2*S.lam x-5*S.z x*S.κ x) := by fun_prop
  have hi : IntegrableOn (fun x => w x*S.Φ x) (Ioi 0) :=
    (hGauss.mul_poly_integrable hΦ (hw.mul S.continuous_Φ).aestronglyMeasurable).integrableOn
  have hiQ : IntegrableOn (fun x => w x*S.Φ x*x^2) (Ioi 0) := by
    have hh := hGauss.mul_poly_integrable (hΦ.mul (PolyBounded.id.pow 2))
      (hw.mul (S.continuous_Φ.mul (continuous_id.pow 2))).aestronglyMeasurable
    simpa only [mul_assoc] using hh.integrableOn (s := Ioi 0)
  have hi₂ : IntegrableOn (fun x => w x*S.Φ x*potentialTerm D E x) (Ioi 0) := by
    have hh := hGauss.mul_poly_integrable (hΦ.mul hRV)
      (hw.mul (S.continuous_Φ.mul hcRV)).aestronglyMeasurable
    simpa only [mul_assoc] using hh.integrableOn (s := Ioi 0)
  have hi₁ : IntegrableOn (fun x => w x*S.Φ x*S.generalR₁ D x) (Ioi 0) := by
    have hh := hGauss.mul_poly_integrable (hΦ.mul hR₁)
      (hw.mul (S.continuous_Φ.mul hcR₁)).aestronglyMeasurable
    simpa only [mul_assoc] using hh.integrableOn (s := Ioi 0)
  have hi₀ : IntegrableOn (fun x => w x*S.Φ x*S.R₀ x) (Ioi 0) := by
    have hh := hGauss.mul_poly_integrable (hΦ.mul hR₀)
      (hw.mul (S.continuous_Φ.mul hcR₀)).aestronglyMeasurable
    simpa only [mul_assoc] using hh.integrableOn (s := Ioi 0)
  have hiG := (hGauss.mul_poly_integrable hG (hw.mul hcG).aestronglyMeasurable).integrableOn (s := Ioi 0)
  have hiT := (hGauss.mul_poly_integrable hT (hw.mul hcT).aestronglyMeasurable).integrableOn (s := Ioi 0)
  have htz := hGauss.mul_poly_tendsto hz
  let M := ∫ x in Ioi 0, w x*S.Φ x
  let F := fun x => S.rootPrimitive w x+M
  have hdF (x) : HasDerivAt F (-w x*S.Φ x) x := (S.rootPrimitive_hasDerivAt hw x).add_const M
  have hF0 : F 0=M := by simp only [F,S.rootPrimitive_zero,zero_add]
  have hFt : Tendsto F atTop (𝓝 0) := by
    have hh := (intervalIntegral_tendsto_integral_Ioi 0 hi tendsto_id).neg.add_const M
    simpa only [F,rootPrimitive,id_eq,M,neg_add_cancel] using hh
  have hcF : Continuous F := continuous_iff_continuousAt.mpr fun x => (hdF x).continuousAt
  have hFb (x : ℝ) (hx : 0 ≤ x) : -|M| ≤ F x ∧ F x ≤ w x*S.z x+|M| := by
    simpa only [hF0] using S.weighted_tail_bounds_near hD hD0 hEp hm
      (fun y => (hwp y).le) hdw hdF hFt htz hx
  have hiF : IntegrableOn (fun x => F x*(2*S.lam x-5*S.z x*S.κ x)) (Ioi 0) := by
    have hh := (hGauss.mul_poly_integrable (hz.mul hRate)
      (hw.mul (S.continuous_z.mul hcRate)).aestronglyMeasurable).norm.integrableOn (s := Ioi 0)
    have hj := ((S.correction_rate_integrable hm hbB hbz hcLam).abs.const_mul |M|)
    apply (hh.add hj).mono' (hcF.mul hcRate).aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hfabs : |F x| ≤ w x*S.z x+|M| := abs_le.mpr ⟨by
      have hz0 := mul_nonneg (hwp x).le (S.z_nonneg hm hx.le)
      linarith [(hFb x hx.le).1],(hFb x hx.le).2⟩
    simp only [Pi.add_apply,Pi.mul_apply,Real.norm_eq_abs,abs_mul,abs_of_pos (hwp x),
      abs_of_nonneg (S.z_nonneg hm hx.le)]
    have hh := mul_le_mul_of_nonneg_right hfabs (abs_nonneg (2*S.lam x-5*S.z x*S.κ x))
    nlinarith
  have htF : Tendsto (fun x => F x*S.R₀ x) atTop (𝓝 0) := by
    obtain ⟨K,_,hK⟩ := S.Rzero_absBounded hbC hbz hbκ
    have ht := hFt.norm.mul_const K
    simp only [norm_zero,zero_mul] at ht
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) _ ht
    exact Eventually.of_forall fun x => by
      simp only [Real.norm_eq_abs,abs_mul]
      exact mul_le_mul_of_nonneg_left (hK x) (abs_nonneg _)
  exact S.generalNearRootIntegral_lower hm hD hE hD0 hc hEc hHn hw hwp hdw
    hi hiQ hi₂ hi₁ hi₀ hiG hiT hdF hF0 hFt hiF (S.z_kappa_integrable hbB hbz)
    htz htF (hGauss.mul_poly_tendsto hFlux) ha hφa

end SKFluctuations.Scalar.PhysicalSlopeSlice

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus Scalar
open scoped Topology NNReal BigOperators

section
variable (α : NonnegativeMassProfile) (hα : ∀ s, α.mass s ≤ 1) (l : ℝ) (t : ℝ≥0)
    {m : ℝ} (hm : 0 < m) (hmα : m ≤ α.mass l) (r : ℝ≥0)

theorem scalarClockProfileSlice_residual_near_root_lower {R : GaussianResidual} (hR : R.residual.Cone)
    {a : ℝ} (ha : 0 ≤ a) (hφa : (scalarClockProfileSlice α hα l t hm hmα r).Φ a=0) :
    let S := scalarClockProfileSlice α hα l t hm hmα r
    let w := R.rootWeight S (scalarClockProfileJet α hα l t m r 0)
    let D := deriv R.potential
    let E := deriv (deriv R.potential)
    (1/R.variance)^2*(∫ x in Ioi 0, w x*S.Φ x*x^2)+
      2*(∫ x in Ioi 0, w x*S.Φ x)*
        (PhysicalSlopeSlice.potentialTerm D E a-(1/R.variance)^2*a^2/2+S.generalR₁ D a+S.R₀ 0)-
      14*|∫ x in Ioi 0, w x*S.Φ x| * (∫ x in Ioi 0, S.z x*S.κ x) ≤
      ∫ x in Ioi 0, w x*S.thirdTest x := by
  let S := scalarClockProfileSlice α hα l t hm hmα r
  let U := scalarClockProfileJet α hα l t m r 0
  have hdU : ∀ x, HasDerivAt U (S.B x) x := scalarClockProfileJet_deriv α hα l t hm r 0
  have hdw := R.rootWeight_deriv S hdU
  obtain ⟨_,_,_,_,hlam⟩ := scalarClockProfileSlice_polyBounded α hα l t hm hmα r
  have hD (x : ℝ) : HasDerivAt (deriv R.potential) (deriv (deriv R.potential) x) x :=
    (R.potential_second_hasDerivAt x).differentiableAt.hasDerivAt
  have hE (x : ℝ) : HasDerivAt (deriv (deriv R.potential)) (deriv (deriv (deriv R.potential)) x) x :=
    (R.potential_third_hasDerivAt x).differentiableAt.hasDerivAt
  obtain ⟨hbB,hbC,hbz,hbκ,_⟩ := scalarClockProfileSlice_absBounded α hα l t hm hmα r
  exact S.generalNearRootIntegral_lower_gaussian hm hD hE (GaussianResidual.potential_gradient_zero hR)
    (one_div_pos.mpr R.positive) (GaussianResidual.potential_curvature_lower hR)
    (fun x hx => (GaussianResidual.potential_shape hR hx).2.2)
    R.potential_gradient_polyBounded R.potential_curvature_polyBounded
    (continuous_iff_continuousAt.mpr fun x => (hdw x).continuousAt)
    (R.rootWeight_pos S U) hdw
    (GaussianResidual.rootWeight_dominated hR S hm.le
      (scalarClockProfileJet_zero_upper α hα l t hm r)
      (scalarClockProfileJet_absBounded α hα l t hm r 1))
    hbB hbC hbz hbκ hlam (scalarClockProfileSlice_lam_continuous α hα l t hm hmα r) ha hφa

end
end SKFluctuations.Hierarchy

end

end OAI
