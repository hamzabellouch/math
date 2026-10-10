import Mathlib
import OAI.Geometry.CubicTorus.Profiles.NestingEndpointBound

namespace OAI

section
section
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem exists_smooth_seam_probability {L : ℝ} (hL : L∈Ioo 0 (1/2)) :
    ∃ β : ℝ →ℝ,ContDiff ℝ (⊤ : ℕ∞) β ∧Function.Periodic β 1 ∧
      (∀ t,0≤β t) ∧(∫ t in (0 : ℝ)..1,β t)=1 ∧
      (∀ t,|t|≤L →β t=0) ∧
      (∀ t : ℝ,β t≠0 →dist (t : AxisCircle) ((1/2 : ℝ) : AxisCircle)<1/2-L) := by
  let r : ℝ := 1/2-L
  have hr : 0<r := by dsimp only [r]; linarith [hL.2]
  let b : ContDiffBump (0 : ℝ) := ⟨r/2,r,half_pos hr,by linarith⟩
  let B : ℝ →ℝ := fun t ↦ b.normed volume (t-1/2)
  have hB : ContDiff ℝ (⊤ : ℕ∞) B := b.contDiff_normed.comp (contDiff_id.sub contDiff_const)
  have hBs : tsupport B ⊆ Ioo ((1/2 : ℝ)-1/2) (1/2+1/2) := by
    intro t ht
    have hh := tsupport_comp_subset_preimage (b.normed volume) (continuous_id.sub continuous_const) ht
    change t-1/2∈tsupport (b.normed volume) at hh
    rw [b.tsupport_normed_eq,Real.closedBall_eq_Icc] at hh
    change 0-r≤t-1/2 ∧ t-1/2≤0+r at hh
    dsimp only [r] at hh
    constructor <;> linarith [hh.1,hh.2,hL.1]
  have hBc : HasCompactSupport B := IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport B)
    (fun _ ht ↦ ⟨(hBs ht).1.le,(hBs ht).2.le⟩)
  let β := circlePeriodize B
  have hβ : ContDiff ℝ (⊤ : ℕ∞) β := circlePeriodize_contDiff hB hBc
  have pβ : Function.Periodic β 1 := circlePeriodize_periodic B
  have he (t : ℝ) (ht : t∈Icc (0 : ℝ) 1) : β t=B t :=
    (circlePeriodize_eventuallyEq hBc hBs (by convert ht using 1; norm_num)).eq_of_nhds
  have hnB (t : ℝ) (ht : B t≠0) : |t-1/2|<r := by
    have hh : t-1/2∈Metric.ball (0 : ℝ) r := by
      rw [←b.support_normed_eq (μ := volume)]
      exact ht
    simpa only [Metric.mem_ball,Real.dist_eq,sub_zero] using hh
  have hmean : (∫ t : AxisCircle,pβ.lift t)=1 := by
    rw [circlePeriodize_integral_short hBc hBs]
    exact (integral_sub_right_eq_self (b.normed volume) (1/2)).trans b.integral_normed
  refine ⟨β,hβ,pβ,fun t ↦ tsum_nonneg (fun n : ℤ ↦ b.nonneg_normed (t+n-1/2)),?_,?_,?_⟩
  · have hh := AddCircle.intervalIntegral_preimage (1 : ℝ) (0 : ℝ) pβ.lift
    simpa only [zero_add,pβ.lift_coe,hmean] using hh
  · intro t ht
    rcases le_total (0 : ℝ) t with ht0 | ht0
    · rw [he t ⟨ht0,by linarith [(abs_le.mp ht).2,hL.2]⟩]
      by_contra hh
      have hb := hnB t hh
      dsimp only [r] at hb
      have ha := (abs_lt.mp hb).1
      linarith [(abs_le.mp ht).2]
    · rw [←pβ t,he (t+1) ⟨by linarith [(abs_le.mp ht).1,hL.2],by linarith⟩]
      by_contra hh
      have hb := hnB (t+1) hh
      dsimp only [r] at hb
      have ha := (abs_lt.mp hb).2
      linarith [(abs_le.mp ht).1]
  · intro t ht
    let x : ℝ := ((AddCircle.equivIco (1 : ℝ) 0) (t : AxisCircle) : ℝ)
    have hx := ((AddCircle.equivIco (1 : ℝ) 0) (t : AxisCircle)).property
    change 0≤x ∧ x<0+1 at hx
    have hxt : (x : AxisCircle)=(t : AxisCircle) := (AddCircle.equivIco (1 : ℝ) 0).symm_apply_apply _
    have hβx : β x≠0 := by
      have heq : β x=β t := by rw [←pβ.lift_coe x,←pβ.lift_coe t,hxt]
      rwa [heq]
    rw [he x ⟨hx.1,by linarith [hx.2]⟩] at hβx
    have hnorm : dist (x : AxisCircle) ((1/2 : ℝ) : AxisCircle)≤|x-1/2| := by
      rw [dist_eq_norm,←QuotientAddGroup.mk_sub]
      exact QuotientAddGroup.norm_mk_le_norm
    rw [←hxt]
    exact hnorm.trans_lt (hnB x hβx)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem exists_smooth_saw_primitive {β : ℝ →ℝ}
    (hβ : ContDiff ℝ (⊤ : ℕ∞) β) (pβ : Function.Periodic β 1)
    (hβ0 : ∀ t,0≤β t) (hβ1 : (∫ t in (0 : ℝ)..1,β t)=1)
    {L k : ℝ} (hL : L∈Ioo 0 (1/2)) (hk : 0≤k)
    (hb : ∀ t,|t|≤L →β t=0) :
    ∃ v : ℝ →ℝ,ContDiff ℝ (⊤ : ℕ∞) v ∧Function.Periodic v 1 ∧
      (∀ t,deriv v t=2*k*(1-β t)) ∧
      (∀ t,|t|≤L →v t=2*k*t) ∧(∀ t,|v t|≤2*k*(1-L)) := by
  obtain ⟨ψ,hψ,pψ,hdψ⟩ := smooth_periodic_centered_primitive hβ pβ
  let v : ℝ →ℝ := fun t ↦ -2*k*(ψ t-ψ 0)
  have hv : ContDiff ℝ (⊤ : ℕ∞) v := contDiff_const.mul (hψ.sub contDiff_const)
  have pv : Function.Periodic v 1 := fun t ↦ by dsimp only [v]; rw [pψ t]
  have hd (t : ℝ) : deriv v t=2*k*(1-β t) := by
    dsimp only [v]
    rw [deriv_const_mul _ ((hψ.differentiable (by simp) t).sub_const _),deriv_sub_const,hdψ,hβ1]
    ring
  have hcentral (t : ℝ) (ht : |t|≤L) : v t=2*k*t := by
    have he : (∫ x in (0 : ℝ)..t,deriv v x)=2*k*t := by
      calc
        _=∫ x in (0 : ℝ)..t,(2*k : ℝ) := by
          apply intervalIntegral.integral_congr
          intro x hx
          have hxL : |x|≤L := by
            rcases le_total (0 : ℝ) t with ht0 | ht0
            · rw [uIcc_of_le ht0] at hx
              exact abs_le.mpr ⟨by linarith [hx.1,hL.1],hx.2.trans (le_trans (le_abs_self t) ht)⟩
            · rw [uIcc_of_ge ht0] at hx
              exact abs_le.mpr ⟨by linarith [(abs_le.mp ht).1,hx.1],by linarith [hx.2,hL.1]⟩
          rw [hd,hb x hxL]
          ring
        _=2*k*t := by rw [intervalIntegral.integral_const]; simp only [sub_zero,smul_eq_mul]; ring
    rw [intervalIntegral.integral_deriv_eq_sub (fun x _ ↦ hv.differentiable (by simp) x)
      ((hv.continuous_deriv (by simp)).intervalIntegrable _ _)] at he
    simpa only [v,sub_self,mul_zero,sub_zero] using he
  have hm : Antitone (fun t ↦ v t-2*k*t) := by
    apply antitone_of_deriv_nonpos (hv.differentiable (by simp) |>.sub (differentiable_id.const_mul (2*k)))
    intro t
    rw [deriv_sub (hv.differentiable (by simp) t) ((differentiable_id.const_mul (2*k)) t),
      hd,deriv_const_mul _ (differentiableAt_id),deriv_id,mul_one]
    nlinarith [hβ0 t,mul_nonneg hk (hβ0 t)]
  have hs (a b : ℝ) (hab : a≤b) : v b-v a≤2*k*(b-a) := by
    have hh := hm hab
    dsimp only at hh
    linarith
  refine ⟨v,hv,pv,hd,hcentral,fun t ↦ ?_⟩
  let x : ℝ := ((AddCircle.equivIco (1 : ℝ) (-L)) (t : AxisCircle) : ℝ)
  have hx := ((AddCircle.equivIco (1 : ℝ) (-L)) (t : AxisCircle)).property
  change -L≤x ∧ x< -L+1 at hx
  have hxt : (x : AxisCircle)=(t : AxisCircle) :=
    (AddCircle.equivIco (1 : ℝ) (-L)).symm_apply_apply _
  have hvt : v t=v x := by rw [←pv.lift_coe t,←pv.lift_coe x,hxt]
  rw [hvt]
  by_cases hxc : x≤L
  · rw [hcentral x (abs_le.mpr ⟨hx.1,hxc⟩),abs_mul,abs_of_nonneg (by positivity : 0≤2*k)]
    exact mul_le_mul_of_nonneg_left ((abs_le.mpr ⟨hx.1,hxc⟩).trans (by linarith [hL.2])) (by positivity)
  · have hvL : v L=2*k*L := hcentral L (by rw [abs_of_pos hL.1])
    have hvR : v (1-L)= -2*k*L := by
      rw [show 1-L= -L+1 by ring,pv (-L),hcentral (-L) (by rw [abs_neg,abs_of_pos hL.1])]
      ring
    have h1 := hs L x (le_of_not_ge hxc)
    have h2 := hs x (1-L) (by linarith [hx.2,hL.1])
    rw [hvL] at h1
    rw [hvR] at h2
    apply abs_le.mpr
    constructor
    · have h := mul_le_mul_of_nonneg_left (show L≤x from (le_of_not_ge hxc)) (show 0≤2*k by positivity)
      nlinarith
    · have h := mul_le_mul_of_nonneg_left (show x≤1-L by linarith [hx.2,hL.1]) (show 0≤2*k by positivity)
      nlinarith

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem planarTorusPerimeter_ge_strip_calibration
    {A : Set TransverseProduct} (hA : IsOpen A)
    (hin : ∀ y : TransverseProduct,y 0=0 →y∈A)
    (hout : ∀ y : TransverseProduct,y 0=((1/2 : ℝ) : AxisCircle) →y∉closure A)
    {e k : ℝ} (he : 0≤e) (hk : k∈Ico 0 1)
    (hedge : ∀ y∈closure A,y 1=((1/2 : ℝ) : AxisCircle) →2*‖y 0‖≤e) :
    ENNReal.ofReal (2*k*(volume.real A-e)+
      2*(∫ t in (-(1/2 : ℝ))..(1/2),Real.sqrt (1-(2*k*t)^2)))≤planarTorusPerimeter A := by
  let f : ℝ →ℝ := fun t ↦ Real.sqrt (1-(2*k*t)^2)
  have hf : Continuous f := (continuous_const.sub ((continuous_const.mul continuous_id).pow 2)).sqrt
  have hp : Continuous (fun z : ℝ ↦ ∫ t in (0 : ℝ)..z,f t) :=
    intervalIntegral.continuous_primitive (fun _ _ ↦ hf.intervalIntegrable _ _) 0
  have hI : Continuous (fun L : ℝ ↦ ∫ t in (-L)..L,f t) := by
    have heq (L : ℝ) : (∫ t in (-L)..L,f t)=(∫ t in (0 : ℝ)..L,f t)-(∫ t in (0 : ℝ)..(-L),f t) :=
      (intervalIntegral.integral_interval_sub_left (hf.intervalIntegrable _ _) (hf.intervalIntegrable _ _)).symm
    simp_rw [heq]
    exact hp.sub (hp.comp continuous_neg)
  have happrox (ε : ℝ) (hε : 0<ε) :
      ENNReal.ofReal (2*k*(volume.real A-(e+ε))+2*(∫ t in (-(1/2 : ℝ))..(1/2),f t))≤planarTorusPerimeter A := by
    obtain ⟨δ,hδ,hcollar⟩ := planar_closed_edge_collar hedge hε
    let U : Set ℝ := {L | 0<L ∧1/2-L<δ ∧2*k*(1-L)<1}
    have hU : IsOpen U := (isOpen_lt continuous_const continuous_id).inter
      ((isOpen_lt (continuous_const.sub continuous_id) continuous_const).inter
        (isOpen_lt (continuous_const.mul (continuous_const.sub continuous_id)) continuous_const))
    have hhalf : (1/2 : ℝ)∈U := by
      change 0<(1/2 : ℝ) ∧1/2-1/2<δ ∧2*k*(1-1/2)<1
      constructor
      · norm_num
      constructor
      · simpa using hδ
      · nlinarith [hk.2]
    obtain ⟨η,hη,hηU⟩ := Metric.isOpen_iff.mp hU _ hhalf
    have hfinite (L : ℝ) (hL : L∈Ioo (1/2-η) (1/2)) :
        ENNReal.ofReal (2*k*(volume.real A-(e+ε))+2*(∫ t in (-L)..L,f t))≤planarTorusPerimeter A := by
      have hLU : L∈U := hηU (show dist L (1/2 : ℝ)<η from by
        rw [Real.dist_eq,abs_of_neg (by linarith [hL.2])]; linarith [hL.1])
      have hLL : L∈Ioo 0 (1/2) := ⟨hLU.1,hL.2⟩
      obtain ⟨β,hβ,pβ,hβ0,hβ1,hβcentral,hβsupport⟩ := exists_smooth_seam_probability hLL
      obtain ⟨v,hv,pv,hd,hcentral,hbound⟩ := exists_smooth_saw_primitive hβ pβ hβ0 hβ1 hLL hk.1 hβcentral
      have hvb (t : ℝ) : |v t|<1 := (hbound t).trans_lt hLU.2.2
      have hpos (t : ℝ) : 0<1-(v t)^2 := by
        nlinarith [hvb t,sq_abs (v t),abs_nonneg (v t)]
      let u : ℝ →ℝ := fun t ↦ Real.sqrt (1-(v t)^2)
      have hu : ContDiff ℝ (⊤ : ℕ∞) u := (contDiff_const.sub (hv.pow 2)).sqrt (fun t ↦ (hpos t).ne')
      have pu : Function.Periodic u 1 := fun t ↦ by dsimp only [u]; rw [pv t]
      have huv (t : ℝ) : (u t)^2+(v t)^2≤1 := by
        dsimp only [u]
        rw [Real.sq_sqrt (hpos t).le]
        linarith
      have hβC : Continuous (pβ.lift : AxisCircle →ℝ) := continuous_periodic_lift pβ hβ.continuous
      have hβC0 (t : AxisCircle) : 0≤pβ.lift t := by
        induction t using Quotient.inductionOn with | h t => exact hβ0 t
      have hβC1 : (∫ t : AxisCircle,pβ.lift t)=1 := by
        rw [←AddCircle.intervalIntegral_preimage (1 : ℝ) (0 : ℝ)]
        simpa only [zero_add,pβ.lift_coe] using hβ1
      have hβCS (t : AxisCircle) (ht : pβ.lift t≠0) : dist t ((1/2 : ℝ) : AxisCircle)<δ := by
        induction t using Quotient.inductionOn with
        | h t => exact (hβsupport t ht).trans hLU.2.1
      have hcal := planarTorusPerimeter_ge_strip_seam_calibration hA (closedCentralArc_isCompact L)
        hu hv pu pv (fun t ↦ Real.sqrt_nonneg _) huv (fun y hy _ ↦ hin y hy) hout
        hβC hβC0 hβC1 hk.1 (show 0≤e+ε by linarith)
        (fun t ↦ hd t) (fun y hy hn ↦ (hcollar y (subset_closure hy) (hβCS (y 1) hn)).le)
      have hi : (∫ t in closedCentralArc L,pu.lift t)=∫ t in (-L)..L,f t := by
        rw [integral_closedCentralArc ⟨hLL.1.le,hLL.2⟩]
        apply intervalIntegral.integral_congr
        intro t ht
        rw [uIcc_of_le (by linarith [hLL.1])] at ht
        change Real.sqrt (1-(v t)^2)=Real.sqrt (1-(2*k*t)^2)
        rw [hcentral t (abs_le.mpr ht)]
      rwa [hi] at hcal
    have hc : Continuous (fun L : ℝ ↦ ENNReal.ofReal (2*k*(volume.real A-(e+ε))+2*(∫ t in (-L)..L,f t))) :=
      ENNReal.continuous_ofReal.comp (continuous_const.add (continuous_const.mul hI))
    have hs : IsClosed {L : ℝ | ENNReal.ofReal (2*k*(volume.real A-(e+ε))+2*(∫ t in (-L)..L,f t))≤planarTorusPerimeter A} :=
      isClosed_le hc continuous_const
    have hh : (1/2 : ℝ)∈closure (Ioo (1/2-η) (1/2)) := by
      rw [closure_Ioo (by linarith : (1/2 : ℝ)-η≠1/2)]
      exact ⟨by linarith,le_rfl⟩
    exact closure_minimal (fun L hL ↦ hfinite L hL) hs hh
  have hc : Continuous (fun ε : ℝ ↦ ENNReal.ofReal
      (2*k*(volume.real A-(e+ε))+2*(∫ t in (-(1/2 : ℝ))..(1/2),f t))) :=
    ENNReal.continuous_ofReal.comp
      ((continuous_const.mul (continuous_const.sub (continuous_const.add continuous_id))).add continuous_const)
  have hs : IsClosed {ε : ℝ | ENNReal.ofReal
      (2*k*(volume.real A-(e+ε))+2*(∫ t in (-(1/2 : ℝ))..(1/2),f t))≤planarTorusPerimeter A} :=
    isClosed_le hc continuous_const
  have h0 : (0 : ℝ)∈closure (Ioi (0 : ℝ)) := by rw [closure_Ioi]; exact (le_rfl : (0 : ℝ)≤0)
  have hh := closure_minimal (fun ε hε ↦ happrox ε hε) hs h0
  change ENNReal.ofReal (2*k*(volume.real A-(e+0))+2*(∫ t in (-(1/2 : ℝ))..(1/2),f t))≤planarTorusPerimeter A at hh
  simpa only [add_zero] using hh

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma strip_sqrt_polynomial_lower {w : ℝ} (hw : w∈Icc 0 ((21/40 : ℝ)^2)) :
    1-w/2-w^2/5≤Real.sqrt (1-w) := by
  have hw2 : w^2≤((21/40 : ℝ)^2)^2 := by nlinarith [mul_nonneg hw.1 (sub_nonneg.mpr hw.2)]
  have hc : -3/20+w/5+w^2/25≤0 := by nlinarith [hw.2,hw2]
  have hh := mul_nonpos_of_nonneg_of_nonpos (sq_nonneg w) hc
  apply Real.le_sqrt_of_sq_le
  nlinarith

lemma strip_round_integral_lower {k : ℝ} (hk : k∈Icc 0 (21/40 : ℝ)) :
    1-k^2/6-k^4/25≤∫ t in (-(1/2 : ℝ))..(1/2),Real.sqrt (1-(2*k*t)^2) := by
  let f : ℝ →ℝ := fun t ↦ 1-(2*k*t)^2/2-(2*k*t)^4/5
  have hf : Continuous f := (continuous_const.sub (((continuous_const.mul continuous_id).pow 2).div_const 2)).sub
    (((continuous_const.mul continuous_id).pow 4).div_const 5)
  have hg : Continuous (fun t : ℝ ↦ Real.sqrt (1-(2*k*t)^2)) :=
    (continuous_const.sub ((continuous_const.mul continuous_id).pow 2)).sqrt
  have hb := intervalIntegral.integral_mono_on (μ := volume) (show -(1/2 : ℝ)≤1/2 by norm_num)
    (hf.intervalIntegrable _ _) (hg.intervalIntegrable _ _) (fun t ht ↦ ?_)
  · have hpoly : f=(fun t : ℝ ↦ 1-(2*k^2)*t^2-((16/5)*k^4)*t^4) := by funext t; dsimp only [f]; ring
    have h2 : IntervalIntegrable (fun t : ℝ ↦ (2*k^2)*t^2) volume (-(1/2 : ℝ)) (1/2) :=
      (show Continuous (fun t : ℝ ↦ (2*k^2)*t^2) by fun_prop).intervalIntegrable _ _
    have h4 : IntervalIntegrable (fun t : ℝ ↦ ((16/5)*k^4)*t^4) volume (-(1/2 : ℝ)) (1/2) :=
      (show Continuous (fun t : ℝ ↦ ((16/5)*k^4)*t^4) by fun_prop).intervalIntegrable _ _
    rw [hpoly,intervalIntegral.integral_sub (intervalIntegrable_const.sub h2) h4,
      intervalIntegral.integral_sub intervalIntegrable_const h2,
      intervalIntegral.integral_const,intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul,
      integral_pow,integral_pow] at hb
    norm_num at hb
    nlinarith [hb]
  · have hm : |2*k*t|≤21/40 := by
      calc
        _=2*k*|t| := by rw [abs_mul,abs_mul,abs_of_nonneg (by norm_num : (0 : ℝ)≤2),abs_of_nonneg hk.1]
        _≤2*k*(1/2) := mul_le_mul_of_nonneg_left (abs_le.mpr ht) (mul_nonneg (by norm_num) hk.1)
        _≤21/40 := by linarith [hk.2]
    have hw : (2*k*t)^2∈Icc 0 ((21/40 : ℝ)^2) := ⟨sq_nonneg _,by nlinarith [sq_abs (2*k*t),abs_nonneg (2*k*t)]⟩
    have hh := strip_sqrt_polynomial_lower hw
    convert hh using 1
    dsimp only [f]
    ring

theorem planarTorusPerimeter_ge_strip_gain
    {A : Set TransverseProduct} (hA : IsOpen A)
    (hin : ∀ y : TransverseProduct,y 0=0 →y∈A)
    (hout : ∀ y : TransverseProduct,y 0=((1/2 : ℝ) : AxisCircle) →y∉closure A)
    {e j : ℝ} (he : 0≤e) (hj : j∈Icc 0 (21/100 : ℝ))
    (hedge : ∀ y∈closure A,y 1=((1/2 : ℝ) : AxisCircle) →2*‖y 0‖≤e)
    (hgap : j≤volume.real A-e) :
    ENNReal.ofReal (2*(1+(27/20)*j^2))≤planarTorusPerimeter A := by
  let k : ℝ := (5/2)*j
  have hk : k∈Icc 0 (21/40 : ℝ) := by dsimp only [k]; constructor <;> linarith [hj.1,hj.2]
  have hcal := planarTorusPerimeter_ge_strip_calibration hA hin hout he ⟨hk.1,by linarith [hk.2]⟩ hedge
  have hint := strip_round_integral_lower hk
  have hj2 : j^2≤(21/100 : ℝ)^2 := by nlinarith [mul_nonneg hj.1 (sub_nonneg.mpr hj.2)]
  have hq : 0≤13/120-(25/16)*j^2 := by nlinarith [hj2]
  have hqq := mul_nonneg (sq_nonneg j) hq
  have ha := mul_le_mul_of_nonneg_left hgap hk.1
  apply le_trans (ENNReal.ofReal_le_ofReal ?_) hcal
  dsimp only [k] at hint ha ⊢
  nlinarith

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma planar_radial_strip_gain_first {A : Set TransverseProduct} (hA : IsOpen A)
    (hd : PlanarRadialDownset A) (hin : planarAxisPoint (1/2)∈A)
    (hout : planarFirstAxisPoint (1/2)∉closure A)
    {e j : ℝ} (he : 0≤e) (hj : j∈Icc 0 (21/100 : ℝ))
    (hedge : ∀ y∈closure A,y 1=((1/2 : ℝ) : AxisCircle) →2*‖y 0‖≤e)
    (hgap : j≤volume.real A-e) :
    ENNReal.ofReal (2*(1+(27/20)*j^2))≤planarTorusPerimeter A := by
  apply planarTorusPerimeter_ge_strip_gain hA ?_ (planar_radial_empty_fiber hd hout) he hj hedge hgap
  intro y hy
  apply hd y (planarAxisPoint (1/2)) ?_ hin
  intro k
  fin_cases k
  · simp [hy,planarAxisPoint]
  · change ‖y 1‖≤‖((1/2 : ℝ) : AxisCircle)‖
    rw [axisCircle_norm_coe_small (by norm_num : |(1/2 : ℝ)|≤1/2),abs_of_pos (by norm_num : (0 : ℝ)<1/2)]
    exact axisCircle_norm_le_half (y 1)

lemma planar_radial_strip_gain_second {A : Set TransverseProduct} (hA : IsOpen A)
    (hd : PlanarRadialDownset A) (hin : planarFirstAxisPoint (1/2)∈A)
    (hout : planarAxisPoint (1/2)∉closure A)
    {e j : ℝ} (he : 0≤e) (hj : j∈Icc 0 (21/100 : ℝ))
    (hedge : ∀ y∈closure A,y 0=((1/2 : ℝ) : AxisCircle) →2*‖y 1‖≤e)
    (hgap : j≤volume.real A-e) :
    ENNReal.ofReal (2*(1+(27/20)*j^2))≤planarTorusPerimeter A := by
  have hi : planarAxisPoint (1/2)∈planarSwap ⁻¹' A := by simpa using hin
  have ho : planarFirstAxisPoint (1/2)∉closure (planarSwap ⁻¹' A) := by
    intro hh
    apply hout
    simpa only [mem_preimage,planarSwap_firstAxisPoint] using planarSwap_closure_subset A hh
  have hb : ∀ y∈closure (planarSwap ⁻¹' A),y 1=((1/2 : ℝ) : AxisCircle) →2*‖y 0‖≤e := by
    intro y hy hy1
    have hh := hedge (planarSwap y) (planarSwap_closure_subset A hy) (by simpa using hy1)
    simpa using hh
  have hh := planar_radial_strip_gain_first (hA.preimage planarSwap_continuous)
    (planarRadialDownset_swap hd) hi ho he hj hb (by simpa only [planar_volume_swap] using hgap)
  simpa only [planarTorusPerimeter_swap] using hh

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem isMinimizerAt_section_strip_gain {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hmin : IsMinimizerAt V E)
    (hR : ∀ i : Fin 3,E=ᵐ[torusVolume]((axisReflection i).torus ⁻¹' E))
    {b : Fin 3 →Bool}
    (hd : ∀ x∈upperOctant,∀ y∈upperOctant,OrientedCoordinateLE b x y →
      quotientMap y∈openRepresentative E →quotientMap x∈openRepresentative E)
    (i : Fin 3) (j : Fin 2) (t : ℝ)
    (hin : quotientMap (axialSectionCorner b i t (fun k ↦ if k=j then false else true))∈openRepresentative E)
    (hout : quotientMap (axialSectionCorner b i t (fun k ↦ if k=j then true else false))∉closure (openRepresentative E))
    {e r : ℝ} (he : 0≤e) (hr : r∈Icc 0 (21/100 : ℝ))
    (hedge : ∀ y∈closure (centeredAxialSlice (openRepresentative E) b i (t : AxisCircle)),
      (∀ k : Fin 2,k≠j →y k=((1/2 : ℝ) : AxisCircle)) →2*‖y j‖≤e)
    (hgap : r≤volume.real (axialSlice (openRepresentative E) i (t : AxisCircle))-e) :
    ENNReal.ofReal (2*(1+(27/20)*r^2))≤planarTorusPerimeter (axialSlice (openRepresentative E) i (t : AxisCircle)) := by
  let A := centeredAxialSlice (openRepresentative E) b i (t : AxisCircle)
  have hA : IsOpen A := centeredAxialSlice_isOpen (isOpen_openRepresentative E) b i _
  have hdA : PlanarRadialDownset A := isMinimizerAt_centered_section_radial hV hmin hR hd i _
  have hg : r≤volume.real A-e := by simpa only [A,centeredAxialSlice_volume] using hgap
  suffices hp : ENNReal.ofReal (2*(1+(27/20)*r^2))≤planarTorusPerimeter A by
    simpa only [A,centeredAxialSlice_perimeter] using hp
  fin_cases j
  · have hi : planarAxisPoint (1/2)∈A := by
      change (torusAxialSplit i).symm ((t : AxisCircle),planarAxisPoint (1/2)+axialSectionCenter b i)∈openRepresentative E
      rw [centered_section_second_axis]
      convert hin using 2
      congr 1
      funext k; fin_cases k <;> decide
    have ho : planarFirstAxisPoint (1/2)∉closure A := by
      intro hh
      apply hout
      have hc := centeredAxialSlice_closure_subset (openRepresentative E) b i (t : AxisCircle) hh
      change (torusAxialSplit i).symm ((t : AxisCircle),planarFirstAxisPoint (1/2)+axialSectionCenter b i)∈closure (openRepresentative E) at hc
      rw [centered_section_first_axis] at hc
      convert hc using 2
      congr 1
    apply planar_radial_strip_gain_first hA hdA hi ho he hr ?_ hg
    intro y hy hy1
    apply hedge y hy
    intro k hk
    fin_cases k
    · exact (hk rfl).elim
    · exact hy1
  · have hi : planarFirstAxisPoint (1/2)∈A := by
      change (torusAxialSplit i).symm ((t : AxisCircle),planarFirstAxisPoint (1/2)+axialSectionCenter b i)∈openRepresentative E
      rw [centered_section_first_axis]
      convert hin using 2
      congr 1
      funext k; fin_cases k <;> decide
    have ho : planarAxisPoint (1/2)∉closure A := by
      intro hh
      apply hout
      have hc := centeredAxialSlice_closure_subset (openRepresentative E) b i (t : AxisCircle) hh
      change (torusAxialSplit i).symm ((t : AxisCircle),planarAxisPoint (1/2)+axialSectionCenter b i)∈closure (openRepresentative E) at hc
      rw [centered_section_second_axis] at hc
      convert hc using 2
      congr 1
    apply planar_radial_strip_gain_second hA hdA hi ho he hr ?_ hg
    intro y hy hy0
    apply hedge y hy
    intro k hk
    fin_cases k
    · exact hy0
    · exact (hk rfl).elim

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma strip_gain_dominates_shape {δ q : ℝ} (_hδ : 0≤δ) (_hq : q∈Icc 0 1) :
    Real.sqrt (1+Shape.c*δ^2*Shape.shape q)≤1+(27/20)*(δ*q)^2 := by
  have hshape : Shape.shape q≤q^2 := min_le_left _ _
  have hmul := mul_le_mul_of_nonneg_left hshape (show 0≤(27/10 : ℝ)*δ^2 by positivity)
  apply (Real.sqrt_le_iff).mpr
  refine ⟨by positivity,?_⟩
  dsimp only [Shape.c] at *
  nlinarith [sq_nonneg ((27/20 : ℝ)*(δ*q)^2)]

lemma disk_gain_dominates_shape {δ q s : ℝ} (hδ : δ∈Icc 0 Shape.dm)
    (hq : q∈Icc 0 1) (hs : (38/100 : ℝ)<s) :
    Real.sqrt (1+Shape.c*δ^2*Shape.shape q)≤Real.sqrt (Real.pi*s) := by
  have hd2 : δ^2≤Shape.dm^2 := by nlinarith [mul_nonneg hδ.1 (sub_nonneg.mpr hδ.2)]
  have hh : δ^2*Shape.shape q≤Shape.dm^2 :=
    (mul_le_mul_of_nonneg_left (Shape.shape_le_one hq) (sq_nonneg δ)).trans (by simpa using hd2)
  have hs0 : 0<s := by linarith
  have hpi := mul_lt_mul_of_pos_right Real.pi_gt_three hs0
  apply Real.sqrt_le_sqrt
  dsimp only [Shape.dm,Shape.c] at *
  nlinarith

lemma complement_gain_dominates_shape {δ q s u : ℝ} (hδ : δ∈Icc 0 Shape.dm)
    (hq : q∈Icc 0 1) (hu : u≤1-1/Real.pi) (hs : s=u-δ+δ*q) :
    Real.sqrt (1+Shape.c*δ^2*Shape.shape q)≤Real.sqrt (Real.pi*(1-s)) := by
  have hc : 0<Shape.c*Shape.dm := by norm_num [Shape.c,Shape.dm]
  have hb : Shape.c*Shape.dm*Shape.shape q≤Real.pi*(1-q) := by
    have hh : Shape.shape q≤Real.pi*(1-q)/(Shape.c*Shape.dm) := min_le_right _ _
    have := (le_div_iff₀ hc).mp hh
    nlinarith
  have hscale := mul_le_mul_of_nonneg_left hb hδ.1
  have hremain := mul_nonneg (mul_nonneg hδ.1 (sub_nonneg.mpr hδ.2)) (Shape.shape_nonneg hq)
  have hu' := mul_le_mul_of_nonneg_left hu Real.pi_pos.le
  have hp : Real.pi*(1/Real.pi)=1 := by field_simp
  rw [hs]
  apply Real.sqrt_le_sqrt
  dsimp only [Shape.c,Shape.dm] at *
  nlinarith

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem isMinimizerAt_section_improved_profile {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hmin : IsMinimizerAt V E)
    (hR : ∀ i : Fin 3,E=ᵐ[torusVolume]((axisReflection i).torus ⁻¹' E))
    {b : Fin 3 →Bool}
    (hd : ∀ x∈upperOctant,∀ y∈upperOctant,OrientedCoordinateLE b x y →
      quotientMap y∈openRepresentative E →quotientMap x∈openRepresentative E)
    (i : Fin 3) {t : ℝ} (_ht : t∈Icc (1/2 : ℝ) 1)
    (hc : ∀ n : Fin 2 →Bool,quotientMap (axialSectionCorner b i t n)∉frontier (openRepresentative E))
    (hn : volume (axialSlice (frontier (openRepresentative E)) i (t : AxisCircle))=0)
    {e δ q u : ℝ} (he : 0≤e) (hδ : δ∈Icc 0 Shape.dm) (hq : q∈Icc 0 1)
    (hu : u≤1-1/Real.pi) (heq : e≤u-δ)
    (hs : volume.real (axialSlice (openRepresentative E) i (t : AxisCircle))=u-δ+δ*q)
    (hslo : (38/100 : ℝ)<volume.real (axialSlice (openRepresentative E) i (t : AxisCircle)))
    (hedge : ∀ j : Fin 2,∀ y∈closure (centeredAxialSlice (openRepresentative E) b i (t : AxisCircle)),
      (∀ k : Fin 2,k≠j →y k=((1/2 : ℝ) : AxisCircle)) →2*‖y j‖≤e) :
    ENNReal.ofReal (2*Real.sqrt (1+Shape.c*δ^2*Shape.shape q))≤
      planarTorusPerimeter (axialSlice (openRepresentative E) i (t : AxisCircle)) := by
  have hj : δ*q∈Icc 0 (21/100 : ℝ) := ⟨mul_nonneg hδ.1 hq.1,
    (mul_le_mul_of_nonneg_left hq.2 hδ.1).trans (by simpa only [mul_one,Shape.dm] using hδ.2)⟩
  have hgap : δ*q≤volume.real (axialSlice (openRepresentative E) i (t : AxisCircle))-e := by rw [hs]; linarith
  have hstrip : 2*Real.sqrt (1+Shape.c*δ^2*Shape.shape q)≤2*(1+(27/20)*(δ*q)^2) :=
    mul_le_mul_of_nonneg_left (strip_gain_dominates_shape hδ.1 hq) (by norm_num)
  have hdisk : 2*Real.sqrt (1+Shape.c*δ^2*Shape.shape q)≤2*Real.sqrt (Real.pi*volume.real (axialSlice (openRepresentative E) i (t : AxisCircle))) :=
    mul_le_mul_of_nonneg_left (disk_gain_dominates_shape hδ hq hslo) (by norm_num)
  have hcomp : 2*Real.sqrt (1+Shape.c*δ^2*Shape.shape q)≤2*Real.sqrt (Real.pi*(1-volume.real (axialSlice (openRepresentative E) i (t : AxisCircle)))) :=
    mul_le_mul_of_nonneg_left (complement_gain_dominates_shape hδ hq hu hs) (by norm_num)
  let A := centeredAxialSlice (openRepresentative E) b i (t : AxisCircle)
  have hr : PlanarRadialDownset A := isMinimizerAt_centered_section_radial hV hmin hR hd i _
  have hv : volume.real A=volume.real (axialSlice (openRepresentative E) i (t : AxisCircle)) :=
    centeredAxialSlice_volume _ b i _
  have hcorner (n : Fin 2 →Bool) : planarSquareCorner n∈A ↔
      quotientMap (axialSectionCorner b i t n)∈openRepresentative E := by
    change (torusAxialSplit i).symm ((t : AxisCircle),planarSquareCorner n+axialSectionCenter b i)∈openRepresentative E ↔ _
    rw [centered_section_corner]
  have hout (n : Fin 2 →Bool) (hn : quotientMap (axialSectionCorner b i t n)∉openRepresentative E) :
      quotientMap (axialSectionCorner b i t n)∉closure (openRepresentative E) :=
    open_outside_closure_of_not_frontier (isOpen_openRepresentative E) (hc n) hn
  by_cases hnear : quotientMap (axialSectionCorner b i t (fun _ ↦ false))∈openRepresentative E
  · by_cases hfar : quotientMap (axialSectionCorner b i t (fun _ ↦ true))∈openRepresentative E
    · have hAu : A=univ := by
        apply eq_univ_of_forall
        intro y
        apply hr _ _ (fun j ↦ ?_) ((hcorner _).mpr hfar)
        simp only [planarSquareCorner,ite_true]
        rw [axisCircle_norm_coe_small (by norm_num : |(1/2 : ℝ)|≤1/2)]
        simpa using axisCircle_norm_le_half (y j)
      have hs1 : volume.real (axialSlice (openRepresentative E) i (t : AxisCircle))=1 := by
        rw [←hv,hAu]; simp
      have hsle : volume.real (axialSlice (openRepresentative E) i (t : AxisCircle))≤u := by
        rw [hs]
        nlinarith [mul_le_mul_of_nonneg_left hq.2 hδ.1]
      have hp : 0<1/Real.pi := one_div_pos.mpr Real.pi_pos
      exfalso
      linarith
    · by_cases h0 : quotientMap (axialSectionCorner b i t (fun j ↦ j==0))∈openRepresentative E
      · by_cases h1 : quotientMap (axialSectionCorner b i t (fun j ↦ j==1))∈openRepresentative E
        · obtain ⟨L,hL,hband,hcal,hp⟩ := isMinimizerAt_section_complement_calibration hV hmin hR hd i t (hout _ hfar) h0 h1 hn
          exact (ENNReal.ofReal_le_ofReal hcomp).trans hp
        · have he0 : (fun k : Fin 2 ↦ if k=1 then false else true)=(fun k ↦ k==0) := by
            funext k; fin_cases k <;> decide
          have he1 : (fun k : Fin 2 ↦ if k=1 then true else false)=(fun k ↦ k==1) := by
            funext k; fin_cases k <;> decide
          have hp := isMinimizerAt_section_strip_gain hV hmin hR hd i 1 t (by rwa [he0]) (by rw [he1]; exact hout _ h1) he hj (hedge 1) hgap
          exact (ENNReal.ofReal_le_ofReal hstrip).trans hp
      · by_cases h1 : quotientMap (axialSectionCorner b i t (fun j ↦ j==1))∈openRepresentative E
        · have he0 : (fun k : Fin 2 ↦ if k=0 then false else true)=(fun k ↦ k==1) := by
            funext k; fin_cases k <;> decide
          have he1 : (fun k : Fin 2 ↦ if k=0 then true else false)=(fun k ↦ k==0) := by
            funext k; fin_cases k <;> decide
          have hp := isMinimizerAt_section_strip_gain hV hmin hR hd i 0 t (by rwa [he0]) (by rw [he1]; exact hout _ h0) he hj (hedge 0) hgap
          exact (ENNReal.ofReal_le_ofReal hstrip).trans hp
        · exact (ENNReal.ofReal_le_ofReal hdisk).trans
            (isMinimizerAt_section_disk_perimeter hV hmin hR hd i t hnear (hout _ h0) (hout _ h1))
  · have hAe : A=∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro y hy
      apply hnear
      apply (hcorner _).mp
      apply hr _ _ _ hy
      intro j
      simp only [planarSquareCorner,Bool.false_eq_true,ite_false,norm_zero]
      exact norm_nonneg _
    have hs0 : volume.real (axialSlice (openRepresentative E) i (t : AxisCircle))=0 := by
      rw [←hv,hAe]; simp
    exfalso
    linarith

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma isMinimizerAt_boundary_slice_null_ae {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E) (i : Fin 3) :
    ∀ᵐ t : AxisCircle,volume (axialSlice (frontier (openRepresentative E)) i t)=0 := by
  apply (lintegral_eq_zero_iff (axialSliceVolume_measurable isClosed_frontier.measurableSet i)).mp
  rw [axialSliceVolume_lintegral isClosed_frontier.measurableSet i]
  exact isMinimizerAt_volume_frontier_eq_zero hV hE hmin

theorem isMinimizerAt_planar_profile_ae {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    (hR : ∀ i : Fin 3,E=ᵐ[torusVolume]((axisReflection i).torus ⁻¹' E))
    {b : Fin 3 →Bool}
    (hd : ∀ x∈upperOctant,∀ y∈upperOctant,OrientedCoordinateLE b x y →
      quotientMap y∈openRepresentative E →quotientMap x∈openRepresentative E)
    (i : Fin 3) :
    ∀ᵐ t : ℝ ∂volume.restrict (Icc (1/2 : ℝ) 1),
      ENNReal.ofReal (unitPlanarProfile (volume.real (axialSlice (openRepresentative E) i (t : AxisCircle))))≤
        planarTorusPerimeter (axialSlice (openRepresentative E) i (t : AxisCircle)) := by
  have hc : ∀ᵐ t : ℝ,∀ n : Fin 2 →Bool,
      quotientMap (axialSectionCorner b i t n)∉frontier (openRepresentative E) := by
    rw [ae_all_iff]
    intro n
    exact (ae_iff.mpr (by simpa only [not_not] using isMinimizerAt_corner_boundary_heights_null hV hE hmin hR b i n))
  have hp : MeasurePreserving (fun t : ℝ ↦ (t : AxisCircle)) (volume.restrict (Ioc (0 : ℝ) 1)) volume := by
    simpa using AddCircle.measurePreserving_mk (1 : ℝ) 0
  have hn := hp.quasiMeasurePreserving.ae (isMinimizerAt_boundary_slice_null_ae hV hE hmin i)
  have hsub : Icc (1/2 : ℝ) 1⊆Ioc 0 1 := fun t ht ↦ ⟨by linarith [ht.1],ht.2⟩
  filter_upwards [ae_restrict_of_ae hc,ae_restrict_of_ae_restrict_of_subset hsub hn,
    ae_restrict_mem measurableSet_Icc] with t htc htn ht
  exact isMinimizerAt_section_planar_profile hV hmin hR hd i ht htc htn

theorem isMinimizerAt_nonstandard_planar_profile {V : ℝ} (hV : V∈Ioc 0 (1/2))
    {E : Set Torus} (hmin : IsMinimizerAt V E) (hstd : ¬StandardRegionAt V E)
    (hR : ∀ i : Fin 3,E=ᵐ[torusVolume]((axisReflection i).torus ⁻¹' E)) :
    ∃ b : Fin 3 →Bool,
      (∀ x∈upperOctant,∀ y∈upperOctant,OrientedCoordinateLE b x y →
        quotientMap y∈openRepresentative E →quotientMap x∈openRepresentative E) ∧
      ∀ i : Fin 3,∀ᵐ t : ℝ ∂volume.restrict (Icc (1/2 : ℝ) 1),
        ENNReal.ofReal (unitPlanarProfile (volume.real (axialSlice (openRepresentative E) i (t : AxisCircle))))≤
          planarTorusPerimeter (axialSlice (openRepresentative E) i (t : AxisCircle)) := by
  have hV' : V∈Ioo (0 : ℝ) 1 := ⟨hV.1,by linarith [hV.2]⟩
  have hc : IsPreconnected (frontier (openRepresentative E)) :=
    (Periodic.isMinimizerAt_connected_or_standard_slab hV' hmin).resolve_right (fun h ↦ hstd h.2.2)
  obtain ⟨b,hd⟩ := isMinimizerAt_octant_downset hV' hmin hc hR
  refine ⟨b,hd,fun i ↦ ?_⟩
  let F := toMeasurable torusVolume E
  have hF : MeasurableSet F := measurableSet_toMeasurable _ _
  have hFE : F=ᵐ[torusVolume]E := hmin.1.1.toMeasurable_ae_eq
  have hmF := (isMinimizerAt_congr_ae hFE).mpr hmin
  have ho := openRepresentative_congr_ae hFE
  have hRF (j : Fin 3) : F=ᵐ[torusVolume]((axisReflection j).torus ⁻¹' F) :=
    hFE.trans ((hR j).trans ((axisReflection j).measurePreserving.quasiMeasurePreserving.preimage_ae_eq hFE.symm))
  have hdF : ∀ x∈upperOctant,∀ y∈upperOctant,OrientedCoordinateLE b x y →
      quotientMap y∈openRepresentative F →quotientMap x∈openRepresentative F := by rwa [ho]
  have hp := isMinimizerAt_planar_profile_ae hV' hF hmF hRF hdF i
  rwa [ho] at hp

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma octantHeight_surjective_half (b : Fin 3 →Bool) (i : Fin 3) {t : ℝ}
    (ht : t∈Icc (1/2 : ℝ) 1) : ∃ z∈Icc (0 : ℝ) 1,octantHeight b i z=t := by
  cases hb : b i
  · refine ⟨2-2*t,⟨by linarith [ht.2],by linarith [ht.1]⟩,?_⟩
    simp only [octantHeight,hb,Bool.false_eq_true,ite_false]
    ring
  · refine ⟨2*t-1,⟨by linarith [ht.1],by linarith [ht.2]⟩,?_⟩
    simp only [octantHeight,hb,ite_true]
    ring

theorem isMinimizerAt_nesting_improved_profile_ae {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    (hR : ∀ i : Fin 3,E=ᵐ[torusVolume]((axisReflection i).torus ⁻¹' E))
    (b : Fin 3 →Bool)
    (hd : ∀ x∈upperOctant,∀ y∈upperOctant,OrientedCoordinateLE b x y →
      quotientMap y∈openRepresentative E →quotientMap x∈openRepresentative E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) {H : ℝ}
    (hCMC : ∀ F : Cover → Cover,ContDiff ℝ (⊤ : ℕ∞) F →
      (∀ m x,F (x+latticeVector m)=F x) →
      (∫ z,tangentialDivergence F z.1 z.2 ∂(μ : Measure NormalBundle))=
        H*(∫ z,⟪(z.2 : Cover),F z.1⟫ ∂(μ : Measure NormalBundle)))
    (i : Fin 3) (ha : (axialAreaMarginal μ i : Measure AxisCircle)≪volume)
    (hv : quotientMap (orientedUpperVertex b (fun j ↦ if j=i then true else false))∉openRepresentative E)
    (hout : quotientMap (axialSectionCorner b i (octantHeight b i 0) (fun _ ↦ true))∉closure (openRepresentative E))
    (hin0 : quotientMap (axialSectionCorner b i (octantHeight b i 0) (fun j ↦ j==0))∈openRepresentative E)
    (hin1 : quotientMap (axialSectionCorner b i (octantHeight b i 0) (fun j ↦ j==1))∈openRepresentative E)
    (hH : H/2∈Icc (51/50 : ℝ) (81/50 : ℝ)) :
    let s := volume.real (axialSlice (openRepresentative E) i (octantHeight b i 0 : AxisCircle))
    let δ := nestingDelta (H/2) s
    0<δ →∀ᵐ t : ℝ ∂volume.restrict (Icc (1/2 : ℝ) 1),
      let v := volume.real (axialSlice (openRepresentative E) i (t : AxisCircle))
      v∈Icc (Shape.u (H/2)-δ) (Shape.u (H/2)) →
      ENNReal.ofReal (2*Real.sqrt (1+Shape.c*δ^2*Shape.shape ((v-Shape.u (H/2)+δ)/δ)))≤
        planarTorusPerimeter (axialSlice (openRepresentative E) i (t : AxisCircle)) := by
  intro s δ hδpos
  have hδ : δ∈Icc 0 Shape.dm := nestingDelta_mem _ _
  have hh : 0<H/2 := by linarith [hH.1]
  obtain ⟨_,hdisc,_⟩ := isMinimizerAt_bottom_both_extents hV hE hmin hR b hd hμ hCMC i ha hv hout hin0 hin1
  have hbound := nestingEndpointBound_ge_exact hh (show 0 ≤ s from measureReal_nonneg) hdisc
  let e := max 0 (nestingEndpointBound (H/2) s)
  have he : 0≤e := le_max_left _ _
  have hegap : e≤Shape.u (H/2)-δ := nestingDelta_gap hH hδpos
  have hplace := Shape.interval_placement hH
  have hc : ∀ᵐ t : ℝ,∀ n : Fin 2 →Bool,
      quotientMap (axialSectionCorner b i t n)∉frontier (openRepresentative E) := by
    rw [ae_all_iff]
    intro n
    exact ae_iff.mpr (by simpa only [not_not] using isMinimizerAt_corner_boundary_heights_null hV hE hmin hR b i n)
  have hp : MeasurePreserving (fun t : ℝ ↦ (t : AxisCircle)) (volume.restrict (Ioc (0 : ℝ) 1)) volume := by
    simpa using AddCircle.measurePreserving_mk (1 : ℝ) 0
  have hn := hp.quasiMeasurePreserving.ae (isMinimizerAt_boundary_slice_null_ae hV hE hmin i)
  have hsub : Icc (1/2 : ℝ) 1⊆Ioc 0 1 := fun t ht ↦ ⟨by linarith [ht.1],ht.2⟩
  filter_upwards [ae_restrict_of_ae hc,ae_restrict_of_ae_restrict_of_subset hsub hn,
    ae_restrict_mem measurableSet_Icc] with t htc htn ht
  intro v hvrange
  let q := (v-Shape.u (H/2)+δ)/δ
  have hq : q∈Icc (0 : ℝ) 1 := ⟨div_nonneg (by linarith [hvrange.1]) hδpos.le,
    (div_le_one hδpos).mpr (by linarith [hvrange.2])⟩
  have hvrepr : v=Shape.u (H/2)-δ+δ*q := by dsimp only [q]; field_simp; ring
  have hvlo : (38/100 : ℝ)<v := by linarith [hplace.2.1,hδ.2,hvrange.1]
  apply isMinimizerAt_section_improved_profile hV hmin hR hd i ht htc htn he hδ hq hplace.2.2.2.1 hegap hvrepr hvlo
  intro j y hy hyedge
  obtain ⟨z,hz,hzt⟩ := octantHeight_surjective_half b i ht
  have hb := isMinimizerAt_bottom_nested_endpoint hV hE hmin hR b hd hμ hCMC i ha hv hout hin0 hin1 j z hz y (by rwa [hzt]) hyedge
  exact (hb.trans hbound).trans (le_max_right _ _)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma axialSliceIntegral_measurable {E : Set Torus} (hE : MeasurableSet E) (i : Fin 3)
    {f : Torus → ℝ} (hf : Measurable f) : Measurable (axialSliceIntegral E i f) := by
  have hh := ((hf.indicator hE).comp (torusAxialSplit i).symm.measurable).stronglyMeasurable.integral_prod_right' (ν := (volume : Measure TransverseProduct))
  simpa only [Function.comp_apply,←axialSliceIntegral_indicator hE] using hh.measurable

lemma axialTestPerimeter_countable (i : Fin 3) :
    ∃ S : Set C(Torus,ℝ),S⊆axialDivergenceClass i ∧ S.Countable ∧
      ∀ (E : Set Torus) (t : AxisCircle),axialTestPerimeter E i t=
        ⨆ f : S,ENNReal.ofReal (axialSliceFunctional E i t f) := by
  obtain ⟨S,hS,hSc,hSd⟩ := (TopologicalSpace.IsSeparable.of_separableSpace (axialDivergenceClass i)).exists_countable_dense_subset
  refine ⟨S,hS,hSc,?_⟩
  intro E t
  apply le_antisymm
  · refine iSup_le fun F ↦ iSup_le fun hF ↦ iSup_le fun hFi ↦ ?_
    let f : C(Torus,ℝ) := ⟨fun z ↦ divergence F (representative z),
      continuous_periodic_descent (continuous_divergence hF.1) (divergence_periodic hF.2.1)⟩
    have hf : f∈axialDivergenceClass i := ⟨F,hF,hFi,rfl⟩
    let r : ℝ≥0∞ := ⨆ f : S,ENNReal.ofReal (axialSliceFunctional E i t f)
    have hc : IsClosed {f : C(Torus,ℝ) | ENNReal.ofReal (axialSliceFunctional E i t f)≤r} :=
      isClosed_le (ENNReal.continuous_ofReal.comp (axialSliceFunctional E i t).continuous) continuous_const
    have hh : S⊆{f : C(Torus,ℝ) | ENNReal.ofReal (axialSliceFunctional E i t f)≤r} := by
      intro f hf
      exact le_iSup (fun f : S ↦ ENNReal.ofReal (axialSliceFunctional E i t f)) ⟨f,hf⟩
    exact (closure_minimal hh hc) (hSd hf)
  · apply iSup_le
    intro f
    obtain ⟨F,hF,hFi,hfe⟩ := hS f.property
    have he : axialSliceFunctional E i t f=
        axialSliceIntegral E i (fun z ↦ divergence F (representative z)) t := by
      change axialSliceIntegral E i f t=_
      rw [hfe]
      rfl
    rw [he]
    exact le_iSup_of_le F (le_iSup_of_le hF (le_iSup_of_le hFi le_rfl))

theorem planarTorusPerimeter_slice_measurable {E : Set Torus} (hE : MeasurableSet E) (i : Fin 3) :
    Measurable (fun t : AxisCircle ↦ planarTorusPerimeter (axialSlice E i t)) := by
  obtain ⟨S,hS,hSc,he⟩ := axialTestPerimeter_countable i
  have : Countable S := hSc.to_subtype
  have hh : Measurable (fun t : AxisCircle ↦ ⨆ f : S,ENNReal.ofReal (axialSliceFunctional E i t f)) := by
    apply Measurable.iSup
    intro f
    exact (axialSliceIntegral_measurable hE i f.1.continuous.measurable).ennreal_ofReal
  simpa only [←he,axialTestPerimeter_eq_planar] using hh

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma axisReflection_axialSplit (i : Fin 3) (t : AxisCircle) (y : TransverseProduct) :
    (axisReflection i).torus ((torusAxialSplit i).symm (t,y))=
      (torusAxialSplit i).symm (-t,y) := by
  ext j
  rw [axisReflection_torus_apply]
  by_cases hj : j=i
  · subst j; simp
  · obtain ⟨k,rfl⟩ := Fin.exists_succAbove_eq hj
    simp [Fin.succAbove_ne]

lemma axialSlice_neg_of_reflection {O : Set Torus}
    (hR : ∀ i : Fin 3,∀ z : Torus,(axisReflection i).torus z∈O ↔ z∈O)
    (i : Fin 3) (t : AxisCircle) : axialSlice O i (-t)=axialSlice O i t := by
  ext y
  change (torusAxialSplit i).symm (-t,y)∈O ↔ (torusAxialSplit i).symm (t,y)∈O
  rw [←axisReflection_axialSplit]
  exact hR i _

end CubicTorus
end
end
end

end OAI
