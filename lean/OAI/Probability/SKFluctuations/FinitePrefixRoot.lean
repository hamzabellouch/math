import Mathlib
import OAI.Probability.SKFluctuations.MassResponseJet
import OAI.Probability.SKFluctuations.ResidualGradientBound

namespace OAI

/-! Finite Prefix Root. -/

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

theorem scalarClockProfileSlice_residual_root_pos {R : GaussianResidual} (hR : R.residual.Cone)
    (hcenter : ∫ x in Ioi 0,
      R.rootWeight (scalarClockProfileSlice α hα l t hm hmα r)
        (scalarClockProfileJet α hα l t m r 0) x*
      (scalarClockProfileSlice α hα l t hm hmα r).Φ x = 0) :
    0 < ∫ x in Ioi 0,
      R.rootWeight (scalarClockProfileSlice α hα l t hm hmα r)
        (scalarClockProfileJet α hα l t m r 0) x*
      (scalarClockProfileSlice α hα l t hm hmα r).thirdTest x := by
  let S := scalarClockProfileSlice α hα l t hm hmα r
  let U := scalarClockProfileJet α hα l t m r 0
  have hdU : ∀ x, HasDerivAt U (S.B x) x := scalarClockProfileJet_deriv α hα l t hm r 0
  have hdw := R.rootWeight_deriv S hdU
  obtain ⟨hB,hC,hz,hκ,hlam⟩ := scalarClockProfileSlice_polyBounded α hα l t hm hmα r
  have hD (x : ℝ) : HasDerivAt (deriv R.potential) (deriv (deriv R.potential) x) x :=
    (R.potential_second_hasDerivAt x).differentiableAt.hasDerivAt
  have hE (x : ℝ) : HasDerivAt (deriv (deriv R.potential)) (deriv (deriv (deriv R.potential)) x) x :=
    (R.potential_third_hasDerivAt x).differentiableAt.hasDerivAt
  exact S.generalRootIntegral_pos_gaussian hm hD hE (GaussianResidual.potential_gradient_zero hR)
    (fun x => (one_div_pos.mpr R.positive).trans_le (GaussianResidual.potential_curvature_lower hR x))
    (fun x hx => (GaussianResidual.potential_shape hR hx).2.2)
    R.potential_gradient_polyBounded R.potential_curvature_polyBounded
    (continuous_iff_continuousAt.mpr fun x => (hdw x).continuousAt)
    (R.rootWeight_pos S U) hdw
    (GaussianResidual.rootWeight_dominated hR S hm.le
      (scalarClockProfileJet_zero_upper α hα l t hm r)
      (scalarClockProfileJet_absBounded α hα l t hm r 1))
    hB hC hz hκ hlam (scalarClockProfileSlice_lam_continuous α hα l t hm hmα r) hcenter

theorem scalarClockProfileSlice_finite_prefix_root_pos (s : ℝ) (hs : 0 < s) (b : ℝ)
    (steps : List DensityStep)
    (hcenter : ∫ x in Ioi 0,
       (finiteTransformedResidual s hs b steps).rootWeight (scalarClockProfileSlice α hα l t hm hmα r)
         (scalarClockProfileJet α hα l t m r 0) x*
       (scalarClockProfileSlice α hα l t hm hmα r).Φ x = 0) :
    0 < ∫ x in Ioi 0,
       (finiteTransformedResidual s hs b steps).rootWeight (scalarClockProfileSlice α hα l t hm hmα r)
         (scalarClockProfileJet α hα l t m r 0) x*
       (scalarClockProfileSlice α hα l t hm hmα r).thirdTest x :=
  scalarClockProfileSlice_residual_root_pos α hα l t hm hmα r
    (finiteTransformedResidual_cone s hs b steps) hcenter
end
end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus Scalar
open scoped Topology NNReal BigOperators

theorem ResidualJet.unit_lipschitz (J : ResidualJet)
    (hJ : ∀ x, |J.jet 1 x| ≤ 1) : LipschitzWith 1 (J.jet 0) := by
  apply lipschitzWith_of_nnnorm_deriv_le (fun x => (J.derivative 0 x).differentiableAt)
  intro x
  rw [(J.derivative 0 x).deriv]
  exact hJ x

theorem GaussianResidual.plantedDensity_envelope (R : GaussianResidual)
    (hR : ∀ x, |R.residual.jet 1 x| ≤ 1) {F : ℝ → ℝ} (hF : LipschitzWith 1 F)
    {m : ℝ} (hm : |m| ≤ 1) (hn : (∫ x, R.plantedDensity F m x)=1) (x : ℝ) :
    gaussianLinearEnvelope R.variance (-2) x/gaussianLinearEnvelopeMass R.variance 2 ≤
      R.plantedDensity F m x ∧
    R.plantedDensity F m x ≤
      gaussianLinearEnvelope R.variance 2 x/gaussianLinearEnvelopeMass R.variance (-2) := by
  let f := fun x => R.residual.jet 0 x+m*F x
  have he (y : ℝ) : R.plantedDensity F m y=realGaussianKernel R.variance y*Real.exp (f y) := by
    dsimp only [GaussianResidual.plantedDensity,GaussianResidual.density,f]
    rw [Real.exp_add,mul_assoc]
  have hf (y : ℝ) : |f y-f 0| ≤ 2*|y| := by
    have hres := (R.residual.unit_lipschitz hR).dist_le_mul y 0
    have hpot := hF.dist_le_mul y 0
    simp only [Real.dist_eq,sub_zero,NNReal.coe_one,one_mul] at hres hpot
    calc
      _ = |(R.residual.jet 0 y-R.residual.jet 0 0)+m*(F y-F 0)| := by congr 1; dsimp only [f]; ring
      _ ≤ |R.residual.jet 0 y-R.residual.jet 0 0|+|m*(F y-F 0)| := abs_add_le _ _
      _ ≤ |y|+|y| := by
        rw [abs_mul]
        exact add_le_add hres ((mul_le_mul hm hpot (abs_nonneg _) zero_le_one).trans_eq (one_mul _))
      _ = _ := by ring
  have hi := R.plantedDensity_integrable hF m
  change Integrable (fun x => R.plantedDensity F m x) at hi
  simp_rw [he] at hi hn ⊢
  exact gaussian_tilt_envelope R.positive hf hi hn x

 

theorem ScalarFinitePositivePrefix.uniform_density {T : ℝ} (hT : 0 < T)
    {α : boundedMassProfiles} {q m : ℝ} (h : ScalarFinitePositivePrefix α q m) :
    ∃ R : GaussianResidual, R.variance=T*q ∧ R.residual.Cone ∧
      ScalarPrefixDensity hT α q m R ∧
      (∀ x, |R.residual.jet 1 x| ≤ m) ∧
      (∀ x, gaussianLinearEnvelope (T*q) (-2) x/gaussianLinearEnvelopeMass (T*q) 2 ≤
        R.plantedDensity (fun y => (scalarTailJet hT α q).F (fun _ => y)) m x ∧
        R.plantedDensity (fun y => (scalarTailJet hT α q).F (fun _ => y)) m x ≤
        gaussianLinearEnvelope (T*q) 2 x/gaussianLinearEnvelopeMass (T*q) (-2)) := by
  obtain ⟨R,hv,hc,hr,hg⟩ := h.density_gradient_bound hT
  refine ⟨R,hv,hc,hr,hg,?_⟩
  intro x
  rw [← hv]
  exact R.plantedDensity_envelope (fun y => (hg y).trans h.bounds.2.2.2)
    (scalar_restrict_lipschitz (scalarTailJet hT α q).lipschitz)
    (by simpa only [abs_of_pos h.bounds.2.2.1] using h.bounds.2.2.2) (hr.integral hT) x

end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations.Scalar
open MeasureTheory Filter Set
open scoped Topology

section
variable {g d : ℝ → ℝ} {T : ℝ}
    (hc : ContinuousOn g (Icc 0 T))
    (hd : ∀ x ∈ Ioo 0 T, HasDerivAt g (d x) x)
    (hr : ∀ x ∈ Ioo 0 T, g x = 0 → 0 < d x)

include hc hd hr

theorem transverse_nonneg_after {a : ℝ} (ha : a ∈ Ioo 0 T) (hga : 0 ≤ g a)
    {x : ℝ} (hx : x ∈ Icc a T) : 0 ≤ g x := by
  have hh := image_le_of_deriv_right_lt_deriv_boundary
    (f := fun y => -g y) (f' := fun y => -d y)
    (a := a) (b := T) (B := fun _ => 0) (B' := fun _ => 0)
    ((hc.mono (Icc_subset_Icc ha.1.le le_rfl)).neg)
    (fun y hy => (hd y ⟨ha.1.trans_le hy.1,hy.2⟩).neg.hasDerivWithinAt)
    (neg_nonpos.mpr hga) (fun _ => hasDerivAt_const _ _) (by
      intro y hy he
      exact neg_neg_of_pos (hr y ⟨ha.1.trans_le hy.1,hy.2⟩ (neg_eq_zero.mp he))) hx
  exact neg_nonpos.mp hh

theorem transverse_pos_after {a : ℝ} (ha : a ∈ Ioo 0 T) (hga : 0 ≤ g a)
    {x : ℝ} (hx : x ∈ Ioo a T) : 0 < g x := by
  have hn := transverse_nonneg_after hc hd hr ha hga (show x ∈ Icc a T from ⟨hx.1.le,hx.2.le⟩)
  by_contra! he
  have hz : g x = 0 := le_antisymm he hn
  have hp := hr x ⟨ha.1.trans hx.1,hx.2⟩ hz
  have hevent : ∀ᶠ y in 𝓝[<] x, 0 < slope g x y :=
    ((hd x ⟨ha.1.trans hx.1,hx.2⟩).tendsto_slope.mono_left (nhdsLT_le_nhdsNE x)).eventually
      (Ioi_mem_nhds hp)
  have hnear : ∀ᶠ y in 𝓝[<] x, a < y :=
    nhdsWithin_le_nhds (Ioi_mem_nhds hx.1)
  obtain ⟨y,hy,hya,hyx⟩ := (hevent.and (hnear.and self_mem_nhdsWithin)).exists
  have hgy := transverse_nonneg_after hc hd hr ha hga
    (show y ∈ Icc a T from ⟨hya.le,(hyx.trans hx.2).le⟩)
  rw [slope_def_field,hz,sub_zero] at hy
  have hnq : g y/(y-x) ≤ 0 := div_nonpos_of_nonneg_of_nonpos hgy (sub_nonpos.mpr hyx.le)
  exact (not_lt_of_ge hnq hy)

theorem transverse_root_unique {a b : ℝ} (ha : a ∈ Ioo 0 T) (hb : b ∈ Ioo 0 T)
    (hga : g a = 0) (hgb : g b = 0) : a = b := by
  rcases lt_trichotomy a b with hab|he|hba
  · have hp := transverse_pos_after hc hd hr ha hga.ge ⟨hab,hb.2⟩
    exact False.elim (hp.ne' hgb)
  · exact he
  · have hp := transverse_pos_after hc hd hr hb hgb.ge ⟨hba,ha.2⟩
    exact False.elim (hp.ne' hga)

theorem transverse_neg_before (h0 : g 0 < 0) {a : ℝ}
    (ha : a ∈ Ioo 0 T) (hga : g a = 0) {x : ℝ} (hx : x ∈ Ico 0 a) : g x < 0 := by
  by_contra! h
  rcases hx.1.eq_or_lt with he|hp
  · subst x
    exact (not_le_of_gt h0 h)
  · have hh := transverse_pos_after hc hd hr ⟨hp,hx.2.trans ha.2⟩ h ⟨hx.2,ha.2⟩
    exact hh.ne' hga

omit hd hr in
 
theorem transverse_root_exists (hT : 0 < T) (h0 : g 0 < 0)
    (hc0 : ContinuousAt g 0)
    (hcenter : ∫ x in 0..T, x*(T-x)*g x = 0) :
    ∃ c ∈ Ioo 0 T, g c = 0 := by
  have hex : ∃ b ∈ Ioo 0 T, 0 < g b := by
    by_contra! h
    have hfn : ∀ x ∈ Ioc 0 T, 0 ≤ -(x*(T-x)*g x) := by
      intro x hx
      rcases hx.2.eq_or_lt with rfl|hxt
      · simp
      · exact neg_nonneg.mpr (mul_nonpos_of_nonneg_of_nonpos
          (mul_nonneg hx.1.le (sub_nonneg.mpr hxt.le)) (h x ⟨hx.1,hxt⟩))
    have hnear : ∀ᶠ x in 𝓝[>] (0:ℝ), g x < 0 ∧ x < T ∧ 0 < x :=
      ((hc0.eventually (Iio_mem_nhds h0)).filter_mono nhdsWithin_le_nhds).and
        (((eventually_lt_nhds hT).filter_mono nhdsWithin_le_nhds).and self_mem_nhdsWithin)
    obtain ⟨x,hgx,hxT,hx⟩ := hnear.exists
    have hpos := intervalIntegral.integral_pos hT
      ((continuousOn_id.mul (continuousOn_const.sub continuousOn_id)).mul hc |>.neg)
      hfn ⟨x,⟨hx.le,hxT.le⟩,neg_pos.mpr (mul_neg_of_pos_of_neg
        (mul_pos hx (sub_pos.mpr hxT)) hgx)⟩
    change 0 < ∫ x in 0..T, -(x*(T-x)*g x) at hpos
    rw [intervalIntegral.integral_neg,hcenter,neg_zero] at hpos
    exact (lt_irrefl 0 hpos)
  obtain ⟨b,hb,hgb⟩ := hex
  obtain ⟨c,hc',hgc⟩ := intermediate_value_Icc hb.1.le
    (hc.mono (Icc_subset_Icc le_rfl hb.2.le)) ⟨h0.le,hgb.le⟩
  refine ⟨c,⟨lt_of_le_of_ne hc'.1 ?_,lt_of_le_of_lt hc'.2 hb.2⟩,hgc⟩
  intro he
  subst c
  exact h0.ne hgc

 

theorem transverse_weighted_negative (hT : 0 < T) (h0 : g 0 < 0)
    (hc0 : ContinuousAt g 0)
    (hcenter : ∫ x in 0..T, x*(T-x)*g x = 0) :
    (∫ x in 0..T, (T-x)*g x) < 0 := by
  obtain ⟨c,hc',hgc⟩ := transverse_root_exists hc hT h0 hc0 hcenter
  have hprod : ∀ x ∈ Ioc 0 T, 0 ≤ (x-c)*(T-x)*g x := by
    intro x hx
    rcases hx.2.eq_or_lt with rfl|hxT
    · simp
    rcases le_total x c with hxc|hcx
    · rcases hxc.eq_or_lt with rfl|hxc
      · simp
      · have hgx := transverse_neg_before hc hd hr h0 hc' hgc ⟨hx.1.le,hxc⟩
        exact mul_nonneg_of_nonpos_of_nonpos
          (mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hxc.le) (sub_nonneg.mpr hxT.le)) hgx.le
    · have hgx : 0 ≤ g x := transverse_nonneg_after hc hd hr hc' hgc.ge ⟨hcx,hxT.le⟩
      exact mul_nonneg (mul_nonneg (sub_nonneg.mpr hcx) (sub_nonneg.mpr hxT.le)) hgx
  have hmid : c/2 ∈ Ioo 0 c := ⟨by linarith [hc'.1],by linarith [hc'.1]⟩
  have hgm := transverse_neg_before hc hd hr h0 hc' hgc ⟨hmid.1.le,hmid.2⟩
  have hp := intervalIntegral.integral_pos hT
    (((continuousOn_id.sub continuousOn_const).mul (continuousOn_const.sub continuousOn_id)).mul hc)
    hprod ⟨c/2,⟨hmid.1.le,(hmid.2.trans hc'.2).le⟩,
      mul_pos_of_neg_of_neg (mul_neg_of_neg_of_pos (sub_neg.mpr hmid.2)
        (sub_pos.mpr (hmid.2.trans hc'.2))) hgm⟩
  have hi : IntervalIntegrable (fun x => (T-x)*g x) volume 0 T :=
    ((continuousOn_const.sub continuousOn_id).mul hc).intervalIntegrable_of_Icc hT.le
  have hi2 : IntervalIntegrable (fun x => x*(T-x)*g x) volume 0 T :=
    ((continuousOn_id.mul (continuousOn_const.sub continuousOn_id)).mul hc).intervalIntegrable_of_Icc hT.le
  have hfun : (fun x => (x-c)*(T-x)*g x) =
      (fun x => x*(T-x)*g x-c*((T-x)*g x)) := by funext x; ring
  change 0 < ∫ x in 0..T, (x-c)*(T-x)*g x at hp
  rw [hfun,intervalIntegral.integral_sub hi2 (hi.const_mul c),
    intervalIntegral.integral_const_mul,hcenter,zero_sub] at hp
  by_contra! hn
  exact not_lt_of_ge (mul_nonneg hc'.1.le hn) (neg_pos.mp hp)
end
end SKFluctuations.Scalar

 

 
namespace SKFluctuations.Scalar
open MeasureTheory Set

section
variable {q e g : ℝ → ℝ} {T : ℝ} (hT : 0 < T)
    (hq : ContinuousOn q (Icc 0 T)) (he : ContinuousOn e (Icc 0 T))
    (hg : ContinuousOn g (Icc 0 T))
    (hq' : ∀ s ∈ Ioo 0 T, HasDerivAt q (e s) s)
    (he' : ∀ s ∈ Ioo 0 T, HasDerivAt e (g s) s)

include hT hq he hg hq' he'

theorem gap_area_first : (∫ s in 0..T, (T-s)*g s) = q T-q 0-T*e 0 := by
  have hh := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    (u := fun s => T-s) (u' := fun _ => -1) (v := e) (v' := g) (a := 0) (b := T)
    (by fun_prop)
    (by simpa only [uIcc_of_le hT.le] using he)
    (by
      intro s _
      convert (hasDerivAt_const s T).sub (hasDerivAt_id s) using 1 <;> first | rfl | norm_num)
    (by simpa only [min_eq_left hT.le,max_eq_right hT.le] using he')
    (intervalIntegrable_const) (hg.intervalIntegrable_of_Icc hT.le)
  have hf := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hT.le hq hq'
    (he.intervalIntegrable_of_Icc hT.le)
  simp only [sub_self,sub_zero,zero_mul,neg_one_mul,intervalIntegral.integral_neg,hf] at hh
  linarith

theorem gap_area_second : (∫ s in 0..T, s*(T-s)*g s) =
    T*q T+T*q 0-2*∫ s in 0..T, q s := by
  have h1 := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    (u := fun s => s*(T-s)) (u' := fun s => T-2*s) (v := e) (v' := g) (a := 0) (b := T)
    (by fun_prop)
    (by simpa only [uIcc_of_le hT.le] using he)
    (by
      intro s _
      convert (hasDerivAt_id s).mul ((hasDerivAt_const s T).sub (hasDerivAt_id s)) using 1 <;> first | rfl | (simp only [Pi.sub_apply,id_eq]; ring))
    (by simpa only [min_eq_left hT.le,max_eq_right hT.le] using he')
    ((continuous_const.sub (continuous_const.mul continuous_id)).intervalIntegrable _ _)
    (hg.intervalIntegrable_of_Icc hT.le)
  have h2 := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    (u := fun s => T-2*s) (u' := fun _ => -2) (v := q) (v' := e) (a := 0) (b := T)
    (by fun_prop)
    (by simpa only [uIcc_of_le hT.le] using hq)
    (by
      intro s _
      convert (hasDerivAt_const s T).sub ((hasDerivAt_id s).const_mul 2) using 1 <;> first | rfl | norm_num)
    (by simpa only [min_eq_left hT.le,max_eq_right hT.le] using hq')
    intervalIntegrable_const (he.intervalIntegrable_of_Icc hT.le)
  simp only [sub_self,sub_zero,zero_mul,mul_zero,zero_sub] at h1
  rw [h2,intervalIntegral.integral_const_mul] at h1
  linarith

 

theorem gap_strict_balance {d : ℝ → ℝ} (hg0 : ContinuousAt g 0)
    (hd : ∀ s ∈ Ioo 0 T, HasDerivAt g (d s) s)
    (hr : ∀ s ∈ Ioo 0 T, g s = 0 → 0 < d s)
    (h0 : g 0 < 0) (hq0 : q 0 = 0)
    (harea : 2*(∫ s in 0..T, q s) = T*q T) : q T < T*e 0 := by
  have hz : (∫ s in 0..T, s*(T-s)*g s) = 0 := by
    rw [gap_area_second hT hq he hg hq' he',hq0,mul_zero,add_zero,← harea,sub_self]
  have hn := transverse_weighted_negative hg hd hr hT h0 hg0 hz
  rw [gap_area_first hT hq he hg hq' he',hq0,sub_zero] at hn
  exact sub_neg.mp hn
end
end SKFluctuations.Scalar

 

 

namespace SKFluctuations.Scalar
open MeasureTheory Filter Set
open scoped Topology

section
variable {q e g d : ℝ → ℝ} {T : ℝ} (hT : 0 < T)
    (he : ContinuousOn e (Icc 0 T)) (hg : ContinuousOn g (Icc 0 T))
    (he' : ∀ s ∈ Ioo 0 T, HasDerivAt e (g s) s)
    (hg' : ∀ s ∈ Ioo 0 T, HasDerivAt g (d s) s)
    (hr : ∀ s ∈ Ioo 0 T, g s = 0 → 0 < d s)

include hT he hg he' hg' hr

theorem transverse_derivative_le_endpoints {x : ℝ} (hx : x ∈ Icc 0 T) :
    e x ≤ max (e 0) (e T) := by
  obtain ⟨c,hc,hmax⟩ := isCompact_Icc.exists_isMaxOn ⟨0,⟨le_rfl,hT.le⟩⟩ he
  rcases hc.1.eq_or_lt with hcz | hc0
  · subst c
    exact (hmax hx).trans (le_max_left _ _)
  rcases hc.2.eq_or_lt with hcT | hcT
  · subst c
    exact (hmax hx).trans (le_max_right _ _)
  have hl : IsLocalMax e c := by
    filter_upwards [Ioo_mem_nhds hc0 hcT] with y hy
    exact hmax ⟨hy.1.le,hy.2.le⟩
  have hgc : g c = 0 := hl.hasDerivAt_eq_zero (he' c ⟨hc0,hcT⟩)
  have hs : StrictMonoOn e (Icc c T) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc c T) (he.mono (Icc_subset_Icc hc0.le le_rfl))
    intro y hy
    rw [interior_Icc] at hy
    rw [(he' y ⟨hc0.trans hy.1,hy.2⟩).deriv]
    exact transverse_pos_after hg hg' hr ⟨hc0,hcT⟩ hgc.ge hy
  exact False.elim (not_lt_of_ge (hmax ⟨hT.le,le_rfl⟩)
    (hs ⟨le_rfl,hcT.le⟩ ⟨hcT.le,le_rfl⟩ hcT))

 

theorem transverse_no_stationary_gap
    (hq : ContinuousOn q (Icc 0 T))
    (hq' : ∀ s ∈ Ioo 0 T, HasDerivAt q (e s) s)
    (hqeq : q 0 = q T) (he0 : e 0 ≤ 0) (heT : e T ≤ 0) : False := by
  have hen (x : ℝ) (hx : x ∈ Icc 0 T) : e x ≤ 0 :=
    (transverse_derivative_le_endpoints hT he hg he' hg' hr hx).trans (max_le he0 heT)
  have hanti : AntitoneOn q (Icc 0 T) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc 0 T) hq
    · intro x hx
      rw [interior_Icc] at hx
      exact (hq' x hx).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      rw [(hq' x hx).deriv]
      exact hen x ⟨hx.1.le,hx.2.le⟩
  have hqc (x : ℝ) (hx : x ∈ Icc 0 T) : q x = q 0 := by
    apply le_antisymm (hanti ⟨le_rfl,hT.le⟩ hx hx.1)
    rw [hqeq]
    exact hanti hx ⟨hT.le,le_rfl⟩ hx.2
  have hez (x : ℝ) (hx : x ∈ Ioo 0 T) : e x = 0 := by
    have hd : HasDerivAt q 0 x := (hasDerivAt_const x (q 0)).congr_of_eventuallyEq (by
      filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
      exact hqc y ⟨hy.1.le,hy.2.le⟩)
    exact (hq' x hx).unique hd
  have hgz (x : ℝ) (hx : x ∈ Ioo 0 T) : g x = 0 := by
    have hd : HasDerivAt e 0 x := (hasDerivAt_const x (0:ℝ)).congr_of_eventuallyEq (by
      filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
      exact hez y hy)
    exact (he' x hx).unique hd
  have hx : T/2 ∈ Ioo (0:ℝ) T := ⟨by linarith,by linarith⟩
  have hd : HasDerivAt g 0 (T/2) := (hasDerivAt_const (T/2) (0:ℝ)).congr_of_eventuallyEq (by
    filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
    exact hgz y hy)
  have hz := (hg' (T/2) hx).unique hd
  have hp := hr (T/2) hx (hgz (T/2) hx)
  exact hp.ne' hz

end
end SKFluctuations.Scalar

 

 

namespace SKFluctuations.Scalar
open Set Filter MeasureTheory
open scoped Topology

theorem monotone_root_product_nonneg {φ v : ℝ → ℝ}
    (hφ : MonotoneOn φ (Ici 0)) (hv : MonotoneOn v (Ici 0))
    {a : ℝ} (ha : 0 ≤ a) (hφa : φ a=0) {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ φ x*(v x-v a) := by
  rcases le_total x a with hxa|hax
  · have h1 : φ x ≤ 0 := by simpa only [hφa] using hφ hx ha hxa
    exact mul_nonneg_of_nonpos_of_nonpos h1 (sub_nonpos.mpr (hv hx ha hxa))
  · have h1 : 0 ≤ φ x := by simpa only [hφa] using hφ ha hx hax
    exact mul_nonneg h1 (sub_nonneg.mpr (hv ha hx hax))

theorem centered_weight_mul_lower {w l φ v : ℝ → ℝ}
    (hwl : ∀ x, 0 < x → l x ≤ w x)
    (hφ : MonotoneOn φ (Ici 0)) (hv : MonotoneOn v (Ici 0))
    {a : ℝ} (ha : 0 ≤ a) (hφa : φ a=0)
    (hi : IntegrableOn (fun x => w x*φ x) (Ioi 0))
    (hiv : IntegrableOn (fun x => w x*φ x*v x) (Ioi 0))
    (hil : IntegrableOn (fun x => l x*φ x*(v x-v a)) (Ioi 0))
    (hcenter : ∫ x in Ioi 0, w x*φ x=0) :
    (∫ x in Ioi 0, l x*φ x*(v x-v a)) ≤ ∫ x in Ioi 0, w x*φ x*v x := by
  have hiwv : IntegrableOn (fun x => w x*φ x*(v x-v a)) (Ioi 0) := by
    simp_rw [mul_sub]
    exact hiv.sub (hi.mul_const _)
  calc
    _ ≤ ∫ x in Ioi 0, w x*φ x*(v x-v a) := integral_mono_ae hil hiwv (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      simp only [mul_assoc]
      exact mul_le_mul_of_nonneg_right (hwl x hx)
        (monotone_root_product_nonneg hφ hv ha hφa hx.le))
    _ = _ := by
      simp_rw [mul_sub]
      rw [integral_sub hiv (hi.mul_const _),integral_mul_const,hcenter,zero_mul,sub_zero]

theorem root_covariance_floor_pos {l φ v : ℝ → ℝ}
    (hlc : Continuous l) (hφc : Continuous φ) (hvc : Continuous v)
    (hl : ∀ x, 0 < x → 0 < l x) (hφ : StrictMonoOn φ (Ici 0))
    (hv : StrictMonoOn v (Ici 0)) {a : ℝ} (ha : 0 ≤ a) (hφa : φ a=0)
    (hi : IntegrableOn (fun x => l x*φ x*(v x-v a)) (Ioi 0)) :
    0 < ∫ x in Ioi 0, l x*φ x*(v x-v a) := by
  have hx : 0 < a+1 := by linarith
  apply halfLine_integral_pos ((hlc.mul hφc).mul (hvc.sub continuous_const)) hi
    (fun x hx => by
      rw [mul_assoc]
      exact mul_nonneg (hl x hx).le
        (monotone_root_product_nonneg hφ.monotoneOn hv.monotoneOn ha hφa hx.le)) hx
  have hp1 : 0 < φ (a+1) := by simpa only [hφa] using hφ ha hx.le (by linarith)
  have hp2 : 0 < v (a+1)-v a := sub_pos.mpr (hv ha hx.le (by linarith))
  exact mul_pos (mul_pos (hl _ hx) hp1) hp2

end SKFluctuations.Scalar

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus Scalar
open scoped Topology NNReal BigOperators

noncomputable def gaussianDensityFloor (s x : ℝ) : ℝ :=
  gaussianLinearEnvelope s (-2) x/gaussianLinearEnvelopeMass s 2

theorem gaussianDensityFloor_pos {s : ℝ} (hs : 0 < s) (x : ℝ) :
    0 < gaussianDensityFloor s x :=
  div_pos (mul_pos (realGaussianKernel_pos hs x) (Real.exp_pos _))
    (gaussianLinearEnvelopeMass_pos hs 2)

theorem gaussianDensityFloor_continuous (s : ℝ) : Continuous (gaussianDensityFloor s) := by
  unfold gaussianDensityFloor gaussianLinearEnvelope realGaussianKernel gaussianPDFReal
  fun_prop

theorem gaussianDensityFloor_dominated {s : ℝ} (hs : 0 < s) :
    GaussianDominated (gaussianDensityFloor s) := by
  let M := gaussianLinearEnvelopeMass s 2
  have hM : 0 < M := gaussianLinearEnvelopeMass_pos hs 2
  refine ⟨1/(2*s),(Real.sqrt (2*Real.pi*s))⁻¹/M,by positivity,by positivity,?_⟩
  intro x
  rw [abs_of_pos (gaussianDensityFloor_pos hs x)]
  calc
    _ ≤ realGaussianKernel s x/M := by
      apply div_le_div_of_nonneg_right _ hM.le
      exact mul_le_of_le_one_right (realGaussianKernel_pos hs x).le
        (Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (by norm_num) (abs_nonneg _)))
    _ = _ := by
      simp only [realGaussianKernel,gaussianPDFReal,Real.coe_toNNReal _ hs.le,sub_zero]
      rw [show -(1/(2*s))*x^2 = -x^2/(2*s) by ring]
      ring

noncomputable def rootCovarianceFloor {m : ℝ} (S : PhysicalSlopeSlice m)
    (s a : ℝ) : ℝ :=
  ∫ x in Ioi 0, gaussianDensityFloor s x*(S.C x)^2*S.Φ x*(x^2-a^2)

theorem rootCovarianceFloor_integrable {m : ℝ} (S : PhysicalSlopeSlice m)
    {s : ℝ} (hs : 0 < s) (a : ℝ) (hC : PolyBounded S.C) (hz : PolyBounded S.z) :
    IntegrableOn (fun x => gaussianDensityFloor s x*(S.C x)^2*S.Φ x*(x^2-a^2)) (Ioi 0) := by
  have hΦ : PolyBounded S.Φ := ((hz.pow 2).const_mul 2).sub (hC.const_mul m)
  have hp := ((hC.pow 2).mul hΦ).mul ((PolyBounded.id.pow 2).sub (PolyBounded.const (a^2)))
  have hc : Continuous (fun x => gaussianDensityFloor s x*((S.C x)^2*S.Φ x*(x^2-a^2))) :=
    (gaussianDensityFloor_continuous s).mul
      (((S.continuous_C.pow 2).mul S.continuous_Φ).mul ((continuous_id.pow 2).sub continuous_const))
  have hh := (gaussianDensityFloor_dominated hs).mul_poly_integrable hp hc.aestronglyMeasurable
  simpa only [mul_assoc] using hh.integrableOn (s := Ioi 0)

theorem rootCovarianceFloor_pos {m : ℝ} (S : PhysicalSlopeSlice m) (hm : 0 < m)
    {s a : ℝ} (hs : 0 < s) (ha : 0 ≤ a) (hzero : S.Φ a=0)
    (hC : PolyBounded S.C) (hz : PolyBounded S.z) : 0 < rootCovarianceFloor S s a := by
  exact root_covariance_floor_pos
    ((gaussianDensityFloor_continuous s).mul (S.continuous_C.pow 2))
    S.continuous_Φ (continuous_id.pow 2)
    (fun x _ => mul_pos (gaussianDensityFloor_pos hs x) (sq_pos_of_pos (S.Cpos x)))
    (S.Φ_strictMono hm)
    (by intro x hx y hy hxy; change 0 ≤ x at hx; change 0 ≤ y at hy; change x^2 < y^2; nlinarith)
    ha hzero (rootCovarianceFloor_integrable S hs a hC hz)

end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus Scalar
open scoped Topology NNReal BigOperators

section
variable (α : NonnegativeMassProfile) (hα : ∀ s, α.mass s ≤ 1) (l : ℝ) (t : ℝ≥0)
    {m : ℝ} (hm : 0 < m) (hmα : m ≤ α.mass l) (r : ℝ≥0)

include hm hmα

theorem scalarClockProfileSlice_second (x : ℝ) :
    (scalarClockProfileJet α hα l t m r 3 x)^2-2*m*(scalarClockProfileJet α hα l t m r 2 x)^3 =
      2*((scalarClockProfileSlice α hα l t hm hmα r).C x)^2*
        (scalarClockProfileSlice α hα l t hm hmα r).Φ x :=
  physicalSlopeOfJets_second ..

theorem scalarClockProfileSlice_third (x : ℝ) :
    (scalarClockProfileJet α hα l t m r 4 x)^2-
      12*m*scalarClockProfileJet α hα l t m r 2 x*(scalarClockProfileJet α hα l t m r 3 x)^2+
      6*m^2*(scalarClockProfileJet α hα l t m r 2 x)^4 =
      ((scalarClockProfileSlice α hα l t hm hmα r).C x)^2*
        (scalarClockProfileSlice α hα l t hm hmα r).thirdTest x :=
  physicalSlopeOfJets_third ..

theorem scalarClockProfile_transversality {s : ℝ} (hs : 0 < s)
    (hzero : clockTest m (fun y : Fin 1 → ℝ => scalarClockProfileJet α hα l t m r 0 (y 0))
      (fun y => (scalarClockProfileJet α hα l t m r 3 (y 0))^2-
        2*m*(scalarClockProfileJet α hα l t m r 2 (y 0))^3) s 0 = 0) :
    0 < clockTest m (fun y : Fin 1 → ℝ => scalarClockProfileJet α hα l t m r 0 (y 0))
      (fun y => (scalarClockProfileJet α hα l t m r 4 (y 0))^2-
        12*m*scalarClockProfileJet α hα l t m r 2 (y 0)*
          (scalarClockProfileJet α hα l t m r 3 (y 0))^2+
        6*m^2*(scalarClockProfileJet α hα l t m r 2 (y 0))^4) s 0 := by
  let j := scalarClockProfileJet α hα l t m r
  let S := scalarClockProfileSlice α hα l t hm hmα r
  let E := fun x : ℝ => Real.exp (m*j 0 x-x^2/(2*s))
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
  have hE (x) : E (-x) = E x := by simp only [E,hj0,neg_sq]
  have hf (x) : f (-x) = f x := by simp only [f,hE,hj2,hj3,neg_sq]
  have hg (x) : g (-x) = g x := by simp only [g,hE,hj2,hj3,hj4,neg_sq]
  have hFeq : (fun y : Fin 1 → ℝ => j 0 (y 0)) = ((scalarProfileHeatJet α hα l t).evolve hm r).F := by
    funext y
    change clockContinuation m (scalarProfileHeatJet α hα l t).F r (fun _ => y 0) = _
    congr 1
    funext i
    rw [Fin.eq_zero i]
  have hp : 0 < ∫ x, E x := by
    have hh := scalar_density_partition_pos ((scalarProfileHeatJet α hα l t).evolve hm r).lipschitz m hs
    rw [← hFeq] at hh
    exact hh
  rw [scalar_clockTest_density _ _ _ hs] at hzero ⊢
  change (∫ x, f x)/(∫ x, E x) = 0 at hzero
  change 0 < (∫ x, g x)/(∫ x, E x)
  have hfzero : (∫ x, f x) = 0 := (div_eq_zero_iff.mp hzero).resolve_right hp.ne'
  have hfw (x : ℝ) : f x = 2*(S.gaussianWeight (j 0) s x*S.Φ x) := by
    dsimp only [f]
    rw [scalarClockProfileSlice_second α hα l t hm hmα r]
    dsimp only [E,PhysicalSlopeSlice.gaussianWeight,S,j]
    ring
  have hgw (x : ℝ) : g x = S.gaussianWeight (j 0) s x*S.thirdTest x := by
    dsimp only [g]
    rw [scalarClockProfileSlice_third α hα l t hm hmα r]
    dsimp only [E,PhysicalSlopeSlice.gaussianWeight,S,j]
    ring
  have hcenter : ∫ x in Ioi 0, S.gaussianWeight (j 0) s x*S.Φ x = 0 := by
    rw [integral_even_eq_two_Ioi hf] at hfzero
    simp_rw [hfw] at hfzero
    rw [integral_const_mul] at hfzero
    linarith
  have hroot := scalarClockProfileSlice_root_pos α hα l t hm hmα r hs hcenter
  apply div_pos _ hp
  rw [integral_even_eq_two_Ioi hg]
  simp_rw [hgw]
  exact mul_pos (by norm_num) hroot

end

theorem scalarProfileGapCurvature_root {α : NonnegativeMassProfile} (hα : ∀ s, α.mass s ≤ 1)
    (l : ℝ) (t : ℝ≥0) {m T s : ℝ} (hm : 0 < m) (hmα : m ≤ α.mass l)
    (hs : s ∈ Ioo 0 T)
    (hzero : (scalarProfileHeatJet α hα l t).scalarGapCurvature m T s 0 = 0) :
    0 < (scalarProfileHeatJet α hα l t).scalarGapThird m T s 0 := by
  have hr : (Real.toNNReal (T-s):ℝ) = T-s := Real.coe_toNNReal _ (sub_nonneg.mpr hs.2.le)
  have hh := scalarClockProfile_transversality α hα l t hm hmα (Real.toNNReal (T-s)) hs.1
  dsimp only [scalarClockProfileJet,HeatJet.scalarClockJet,realSpatialJet] at hh
  rw [hr] at hh
  have hF : (fun y : Fin 1 → ℝ => (scalarProfileHeatJet α hα l t).scalarClockPlane m (T-s,y 0)) =
      clockContinuation m (scalarProfileHeatJet α hα l t).F (T-s) := by
    funext y
    change clockContinuation m (scalarProfileHeatJet α hα l t).F (T-s) (fun _ => y 0) = _
    congr 1
    funext i
    rw [Fin.eq_zero i]
  rw [hF] at hh
  simpa only [HeatJet.scalarGapThird,HeatJet.scalarClockJet,realSpatialJet,mul_assoc] using hh hzero
end SKFluctuations.Hierarchy

end

end OAI
