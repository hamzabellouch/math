import OAI.Analysis.NumericalRange.CauchyProjection

namespace OAI

noncomputable section

namespace CompleteCrouzeix

universe u_45

open Set Filter Metric Complex
open scoped Topology ComplexConjugate
open MeasureTheory Set Complex
open scoped Topology Real
open MeasureTheory Set Metric Complex Filter
open scoped Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal InnerProductSpace
open scoped ComplexConjugate InnerProductSpace
open Set Metric Filter Complex
open scoped Topology

section
open Set Metric Complex
open scoped ComplexConjugate

lemma analyticOnNhd_exteriorMap {a b : ℂ} {h : ℂ → ℂ} {R : ℝ}
    (hR : 0 < R) (hh : AnalyticOnNhd ℂ h (ball 0 R)) :
    AnalyticOnNhd ℂ (exteriorMap a b h) {t | R⁻¹ < ‖t‖} := by
  intro t ht
  change R⁻¹ < ‖t‖ at ht
  have ht0 : t ≠ 0 := by
    intro he; simp only [he, norm_zero] at ht
    exact (not_lt_of_ge (inv_nonneg.mpr hR.le)) ht
  have hi : t⁻¹ ∈ ball (0 : ℂ) R := by
    rw [mem_ball, dist_zero_right, norm_inv]
    exact (inv_lt_comm₀ (norm_pos_iff.mpr ht0) hR).mpr ht
  exact ((analyticAt_const.mul analyticAt_id).add analyticAt_const).add
    ((hh _ hi).comp (analyticAt_id.inv ht0))

def actualExteriorKernel {a b : ℂ} {h : ℂ → ℂ} {R : ℝ}
    (hR : 1 < R) (ha : a ≠ 0) (hh : AnalyticOnNhd ℂ h (ball 0 R))
    (hi : InjOn (exteriorMap a b h) {t | R⁻¹ < ‖t‖})
    (hd : ∀ t, R⁻¹ < ‖t‖ → deriv (exteriorMap a b h) t ≠ 0)
    (hsupport : ∀ w t : Circle,
      0 ≤ (conj ((t : ℂ)*deriv (exteriorMap a b h) t)*
        (exteriorMap a b h t-exteriorMap a b h w)).re) : AnalyticBidiskKernel := by
  have hR0 : 0 < R := lt_trans zero_lt_one hR
  have hn := dividedDifference_ne_zero ha hh hi hd hR0
  have hs : closedBall (0 : ℂ) 1 ⊆ ball 0 R := closedBall_subset_ball hR
  have hTU : ∀ t : Circle, R⁻¹ < ‖(t : ℂ)‖ := by
    intro t; rw [Circle.norm_coe]
    exact (inv_lt_one₀ hR0).mpr hR
  refine { B := reciprocalCorrection a h
           continuous := (reciprocalCorrection_continuousOn isOpen_ball hh hn).mono
             (prod_mono hs hs)
           left := fun y hy => (reciprocalCorrection_analytic_left isOpen_ball hh hn (hs hy)).mono hs
           right := fun x hx => (reciprocalCorrection_analytic_right isOpen_ball hh hn (hs hx)).mono hs
           zero_left := reciprocalCorrection_zero_left a h
           zero_right := reciprocalCorrection_zero_right a h
           positive := ?_ }
  intro w t
  have hw : (w : ℂ)⁻¹ ∈ ball (0 : ℂ) R := by
    simpa only [mem_ball, dist_zero_right, norm_inv, Circle.norm_coe, inv_one] using hR
  have ht : (t : ℂ)⁻¹ ∈ ball (0 : ℂ) R := by
    simpa only [mem_ball, dist_zero_right, norm_inv, Circle.norm_coe, inv_one] using hR
  have he := exteriorCorrection_eq_reciprocal (a := a) (b := b)
    (inv_ne_zero (Circle.coe_ne_zero w)) (inv_ne_zero (Circle.coe_ne_zero t))
    (hh _ hw).differentiableAt (hh _ ht).differentiableAt
    ((analyticOnNhd_dslope isOpen_ball hh hw) _ ht).differentiableAt
  simp only [inv_inv] at he
  rw [← he]
  exact exteriorMarkovKernel_nonneg (isOpen_lt continuous_const continuous_norm)
    (analyticOnNhd_exteriorMap hR0 hh) hi hd hTU hsupport w t

end

open MeasureTheory Set Complex
open scoped Topology
section

lemma interval_integral_swap_continuous {f : ℝ → ℝ → ℂ}
    (hf : ContinuousOn (Function.uncurry f) (Icc (0:ℝ) 1 ×ˢ Icc 0 1)) :
    (∫ s in (0:ℝ)..1, ∫ t in (0:ℝ)..1, f s t) =
      ∫ t in (0:ℝ)..1, ∫ s in (0:ℝ)..1, f s t := by
  simp_rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1),
    ← integral_Icc_eq_integral_Ioc]
  apply integral_integral_swap
  rw [Measure.prod_restrict]
  exact hf.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)

lemma analytic_segment_integral {U : Set ℂ} (hU : Convex ℝ U)
    {F : ℂ → ℂ} (hF : AnalyticOnNhd ℂ F U) {z w : ℂ} (hz : z ∈ U) (hw : w ∈ U) :
    (∫ r in (0:ℝ)..1, (w-z) * deriv F (z + (r:ℂ)*(w-z))) = F w - F z := by
  have hm : MapsTo (fun r : ℝ => z + (r:ℂ)*(w-z)) (Icc 0 1) U := by
    intro r hr
    simpa only [Complex.real_smul] using hU.add_smul_sub_mem hz hw hr
  have hc : ContinuousOn (fun r : ℝ => (w-z) * deriv F (z+(r:ℂ)*(w-z))) (Icc 0 1) :=
    continuousOn_const.mul (hF.deriv.continuousOn.comp (by fun_prop) hm)
  have hd : ∀ r ∈ Icc (0:ℝ) 1,
      HasDerivAt (fun r : ℝ => F (z+(r:ℂ)*(w-z)))
        ((w-z)*deriv F (z+(r:ℂ)*(w-z))) r := by
    intro r hr
    have hi := (((hasDerivAt_id r).ofReal_comp).mul_const (w-z)).const_add z
    simpa only [Function.comp_def, ofReal_one, one_mul, mul_one, id_eq, mul_comm] using
      ((hF _ (hm hr)).differentiableAt.hasDerivAt).comp r hi
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := (0:ℝ)) (b := 1)
    (fun r hr => hd r (by simpa using hr))
    (show ContinuousOn _ (uIcc (0:ℝ) 1) by simpa using hc).intervalIntegrable
  simpa using he

theorem convex_closed_curve_remainder {U : Set ℂ} (hU : Convex ℝ U)
    {F : ℂ → ℂ} (hF : AnalyticOnNhd ℂ F U)
    {γ γ' : ℝ → ℂ} (hγ : ∀ t ∈ Icc (0:ℝ) 1, HasDerivAt γ (γ' t) t)
    (hγ' : ContinuousOn γ' (Icc 0 1)) (hend : γ 1 = γ 0)
    (hcurve : MapsTo γ (Icc 0 1) U) {z : ℂ} (hz : z ∈ U)
    (hne : ∀ t ∈ Icc (0:ℝ) 1, γ t ≠ z) :
    (∫ t in (0:ℝ)..1, γ' t / (γ t-z) * (F (γ t)-F z)) = 0 := by
  have hcγ : ContinuousOn γ (Icc (0:ℝ) 1) := fun t ht =>
    (hγ t ht).continuousAt.continuousWithinAt
  have hm : MapsTo (fun p : ℝ × ℝ => z+(p.2:ℂ)*(γ p.1-z))
      (Icc 0 1 ×ˢ Icc 0 1) U := by
    intro p hp
    simpa only [Complex.real_smul] using hU.add_smul_sub_mem hz (hcurve hp.1) hp.2
  have hpath : ContinuousOn (fun p : ℝ × ℝ => z+(p.2:ℂ)*(γ p.1-z))
      (Icc 0 1 ×ˢ Icc 0 1) := by
    exact continuousOn_const.add
      ((continuous_ofReal.continuousOn.comp continuousOn_snd (fun _ hp => hp.2)).mul
        ((hcγ.comp continuousOn_fst (fun _ hp => hp.1)).sub continuousOn_const))
  have hc : ContinuousOn
      (fun p : ℝ × ℝ => γ' p.1 * deriv F (z+(p.2:ℂ)*(γ p.1-z)))
      (Icc 0 1 ×ˢ Icc 0 1) :=
    (hγ'.comp continuousOn_fst (fun _ hp => hp.1)).mul
      (hF.deriv.continuousOn.comp hpath hm)
  have hinner : ∀ r ∈ Icc (0:ℝ) 1,
      (∫ t in (0:ℝ)..1, γ' t * deriv F (z+(r:ℂ)*(γ t-z))) = 0 := by
    intro r hr
    have hct : ContinuousOn (fun t => γ' t * deriv F (z+(r:ℂ)*(γ t-z))) (Icc 0 1) :=
      hc.comp (continuousOn_id.prodMk continuousOn_const) (fun t ht => ⟨ht,hr⟩)
    by_cases hr0 : r = 0
    · subst r
      simp only [ofReal_zero, zero_mul, add_zero]
      rw [intervalIntegral.integral_mul_const]
      have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := (0:ℝ)) (b := 1)
        (fun t ht => hγ t (by simpa using ht)) (show ContinuousOn _ (uIcc (0:ℝ) 1) by simpa using hγ').intervalIntegrable
      rw [hi,hend,sub_self,zero_mul]
    · have hd : ∀ t ∈ Icc (0:ℝ) 1,
          HasDerivAt (fun t => F (z+(r:ℂ)*(γ t-z)))
            ((r:ℂ)*(γ' t*deriv F (z+(r:ℂ)*(γ t-z)))) t := by
        intro t ht
        have hi : HasDerivAt (fun t => z+(r:ℂ)*(γ t-z)) ((r:ℂ)*γ' t) t :=
          (((hγ t ht).sub_const z).const_mul (r:ℂ)).const_add z
        have he := ((hF (z+(r:ℂ)*(γ t-z)) (hm (x := (t,r)) ⟨ht,hr⟩)).differentiableAt.hasDerivAt).comp t hi
        simpa only [Function.comp_def, mul_left_comm, mul_comm, mul_assoc] using he
      have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := (0:ℝ)) (b := 1)
        (fun t ht => hd t (by simpa using ht))
        (show ContinuousOn (fun t => (r:ℂ)*(γ' t*deriv F (z+(r:ℂ)*(γ t-z)))) (uIcc (0:ℝ) 1) by
          simpa using continuousOn_const.fun_mul hct).intervalIntegrable
      rw [intervalIntegral.integral_const_mul,hend,sub_self] at hi
      exact (mul_eq_zero.mp hi).resolve_left (ofReal_ne_zero.mpr hr0)
  calc
    _ = ∫ t in (0:ℝ)..1, ∫ r in (0:ℝ)..1,
        γ' t * deriv F (z+(r:ℂ)*(γ t-z)) := by
      apply intervalIntegral.integral_congr
      intro t ht
      have ht' : t ∈ Icc (0:ℝ) 1 := by simpa using ht
      change γ' t / (γ t-z) * (F (γ t)-F z) = _
      rw [← analytic_segment_integral hU hF hz (hcurve ht'),
        ← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro r hr
      field_simp [sub_ne_zero.mpr (hne t ht')]
    _ = ∫ r in (0:ℝ)..1, ∫ t in (0:ℝ)..1,
        γ' t * deriv F (z+(r:ℂ)*(γ t-z)) := interval_integral_swap_continuous hc
    _ = ∫ r in (0:ℝ)..1, (0:ℂ) := by
      apply intervalIntegral.integral_congr
      intro r hr
      exact hinner r (by simpa using hr)
    _ = 0 := intervalIntegral.integral_zero

theorem convex_closed_curve_cauchy {U : Set ℂ} (hU : Convex ℝ U)
    {F : ℂ → ℂ} (hF : AnalyticOnNhd ℂ F U)
    {γ γ' : ℝ → ℂ} (hγ : ∀ t ∈ Icc (0:ℝ) 1, HasDerivAt γ (γ' t) t)
    (hγ' : ContinuousOn γ' (Icc 0 1)) (hend : γ 1 = γ 0)
    (hcurve : MapsTo γ (Icc 0 1) U) {z : ℂ} (hz : z ∈ U)
    (hne : ∀ t ∈ Icc (0:ℝ) 1, γ t ≠ z) :
    (∫ t in (0:ℝ)..1, γ' t / (γ t-z) * F (γ t)) =
      (∫ t in (0:ℝ)..1, γ' t / (γ t-z)) * F z := by
  have hcγ : ContinuousOn γ (Icc (0:ℝ) 1) := fun t ht =>
    (hγ t ht).continuousAt.continuousWithinAt
  have hquot : ContinuousOn (fun t => γ' t / (γ t-z)) (Icc (0:ℝ) 1) :=
    hγ'.div (hcγ.sub continuousOn_const) (fun t ht => sub_ne_zero.mpr (hne t ht))
  have h1 : IntervalIntegrable (fun t => γ' t / (γ t-z) * F (γ t)) volume 0 1 :=
    (show ContinuousOn _ (uIcc (0:ℝ) 1) by
      simpa only [uIcc_of_le (by norm_num : (0:ℝ) ≤ 1), Pi.mul_apply, Function.comp_def] using hquot.fun_mul (hF.continuousOn.comp hcγ hcurve)).intervalIntegrable
  have h2 : IntervalIntegrable (fun t => γ' t / (γ t-z) * F z) volume 0 1 :=
    (show ContinuousOn _ (uIcc (0:ℝ) 1) by
      simpa only [uIcc_of_le (by norm_num : (0:ℝ) ≤ 1), Pi.mul_apply] using hquot.fun_mul (continuousOn_const (c := F z))).intervalIntegrable
  have he := convex_closed_curve_remainder hU hF hγ hγ' hend hcurve hz hne
  simp_rw [mul_sub] at he
  rw [intervalIntegral.integral_sub h1 h2,
    intervalIntegral.integral_mul_const] at he
  exact sub_eq_zero.mp he

end

open MeasureTheory Set Complex Metric
open scoped Topology
section
local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

def reciprocalResolventDenom (a b : ℂ) (h : ℂ → ℂ) (z s : ℂ) : ℂ :=
  a+s*(b+h s-z)

def reciprocalResolvent (a b : ℂ) (h : ℂ → ℂ) (z s : ℂ) : ℂ :=
  (a-s^2*deriv h s) / reciprocalResolventDenom a b h z s

lemma reciprocalResolventDenom_ne_zero {a b : ℂ} {h : ℂ → ℂ} {z : ℂ}
    (ha : a ≠ 0) (hz : ∀ t : ℂ, 1 ≤ ‖t‖ → exteriorMap a b h t ≠ z)
    {s : ℂ} (hs : s ∈ closedBall 0 1) :
    reciprocalResolventDenom a b h z s ≠ 0 := by
  by_cases hs0 : s = 0
  · subst s; simpa [reciprocalResolventDenom] using ha
  have hsi : 1 ≤ ‖s⁻¹‖ := by
    rw [norm_inv]
    exact (one_le_inv₀ (norm_pos_iff.mpr hs0)).mpr (by simpa using hs)
  have he : reciprocalResolventDenom a b h z s = s*(exteriorMap a b h s⁻¹-z) := by
    simp only [reciprocalResolventDenom, exteriorMap, inv_inv]
    field_simp
    ring
  rw [he]
  exact mul_ne_zero hs0 (sub_ne_zero.mpr (hz _ hsi))

lemma reciprocalResolvent_analytic {a b : ℂ} {h : ℂ → ℂ} {z : ℂ}
    (ha : a ≠ 0) (hh : AnalyticOnNhd ℂ h (closedBall 0 1))
    (hz : ∀ t : ℂ, 1 ≤ ‖t‖ → exteriorMap a b h t ≠ z) :
    AnalyticOnNhd ℂ (reciprocalResolvent a b h z) (closedBall 0 1) := by
  intro s hs
  exact (analyticAt_const.sub ((analyticAt_id.pow 2).mul (hh.deriv s hs))).div
    (analyticAt_const.add (analyticAt_id.mul ((analyticAt_const.add (hh s hs)).sub
      analyticAt_const))) (reciprocalResolventDenom_ne_zero ha hz hs)

lemma reciprocalResolvent_eq {a b : ℂ} {h : ℂ → ℂ} {z t : ℂ}
    (ht : t ≠ 0) (hh : DifferentiableAt ℂ h t⁻¹) :
    reciprocalResolvent a b h z t⁻¹ =
      t*deriv (exteriorMap a b h) t / (exteriorMap a b h t-z) := by
  rw [(hasDerivAt_exteriorMap ht hh).deriv]
  simp only [reciprocalResolvent, reciprocalResolventDenom, exteriorMap]
  have he : a+t⁻¹*(b+h t⁻¹-z) = t⁻¹*(a*t+b+h t⁻¹-z) := by
    field_simp; ring
  rw [he, div_mul_eq_div_div, div_inv_eq_mul]
  congr 1
  field_simp

theorem exterior_cauchy_kernel_integral {a b : ℂ} {h : ℂ → ℂ} {z : ℂ}
    (ha : a ≠ 0) (hh : AnalyticOnNhd ℂ h (closedBall 0 1))
    (hz : ∀ t : ℂ, 1 ≤ ‖t‖ → exteriorMap a b h t ≠ z) :
    (∫ t : UnitAddCircle,
      (t.toCircle : ℂ)*deriv (exteriorMap a b h) (t.toCircle : ℂ) /
        (exteriorMap a b h (t.toCircle : ℂ)-z) ∂AddCircle.haarAddCircle) = 1 := by
  calc
    _ = ∫ t : UnitAddCircle, reciprocalResolvent a b h z (t.toCircle : ℂ)⁻¹
        ∂AddCircle.haarAddCircle := by
      apply integral_congr_ae
      filter_upwards [] with t
      apply (reciprocalResolvent_eq (Circle.coe_ne_zero _)
        (hh _ (by simp [mem_closedBall, dist_eq_norm, Circle.norm_coe])).differentiableAt).symm
    _ = reciprocalResolvent a b h z 0 :=
      integral_reciprocal_analytic (reciprocalResolvent_analytic ha hh hz)
    _ = 1 := by simp [reciprocalResolvent, reciprocalResolventDenom, ha]

lemma unitAddCircle_integral_eq_unitInterval {E : Type u_45}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (f : ℂ → E) :
    (∫ t : UnitAddCircle, f (t.toCircle : ℂ) ∂AddCircle.haarAddCircle) =
      ∫ r in (0:ℝ)..1, f (circleMap 0 1 (2*Real.pi*r)) := by
  rw [AddCircle.integral_haarAddCircle, ← AddCircle.intervalIntegral_preimage 1 0]
  simp only [inv_one, one_smul, zero_add]
  apply intervalIntegral.integral_congr
  intro r hr
  simp only [AddCircle.toCircle_apply_mk, Circle.coe_exp, circleMap,
    ofReal_one, one_mul, zero_add, div_one]

theorem circle_convex_cauchy {U : Set ℂ} (hU : Convex ℝ U)
    {F G : ℂ → ℂ} (hF : AnalyticOnNhd ℂ F U)
    (hG : AnalyticOnNhd ℂ G (sphere 0 1))
    (hcurve : MapsTo G (sphere 0 1) U) {z : ℂ} (hz : z ∈ U)
    (hne : ∀ t ∈ sphere (0:ℂ) 1, G t ≠ z)
    (hmass : (∫ t : UnitAddCircle,
      (t.toCircle : ℂ)*deriv G (t.toCircle : ℂ) / (G (t.toCircle : ℂ)-z)
        ∂AddCircle.haarAddCircle) = 1) :
    (∫ t : UnitAddCircle,
      ((t.toCircle : ℂ)*deriv G (t.toCircle : ℂ) / (G (t.toCircle : ℂ)-z)) *
        F (G (t.toCircle : ℂ)) ∂AddCircle.haarAddCircle) = F z := by
  let τ : ℝ → ℂ := fun r => circleMap 0 1 (2*Real.pi*r)
  let c : ℂ := (2*Real.pi:ℝ)*I
  have hc : c ≠ 0 := mul_ne_zero (ofReal_ne_zero.mpr (mul_ne_zero (by norm_num) Real.pi_ne_zero)) I_ne_zero
  have hτ (r : ℝ) : τ r ∈ sphere (0:ℂ) 1 := by
    exact circleMap_mem_sphere 0 (by norm_num) _
  have hτc : Continuous τ := by dsimp [τ]; fun_prop
  have hτd (r : ℝ) : HasDerivAt τ (c*τ r) r := by
    have he := (hasDerivAt_circleMap 0 1 (2*Real.pi*r)).scomp r
      ((hasDerivAt_id r).const_mul (2*Real.pi))
    simpa only [Function.comp_def, id_eq, mul_one, one_mul, Complex.real_smul, τ, c,
      mul_assoc, mul_left_comm, mul_comm] using he
  have hγ (r : ℝ) : HasDerivAt (fun r => G (τ r)) (c*(τ r*deriv G (τ r))) r := by
    simpa only [Function.comp_def, mul_assoc, mul_comm, mul_left_comm] using
      ((hG _ (hτ r)).differentiableAt.hasDerivAt).comp r (hτd r)
  have hγ' : ContinuousOn (fun r => c*(τ r*deriv G (τ r))) (Icc (0:ℝ) 1) := by
    exact continuousOn_const.fun_mul (hτc.continuousOn.fun_mul
      (hG.deriv.continuousOn.comp hτc.continuousOn (fun r _ => hτ r)))
  have hend : G (τ 1) = G (τ 0) := by
    congr 1
    simpa [τ] using (periodic_circleMap 0 1) 0
  have he := convex_closed_curve_cauchy hU hF (fun r _ => hγ r) hγ' hend
    (fun r _ => hcurve (hτ r)) hz (fun r _ => hne _ (hτ r))
  have h1 : (fun r => c*(τ r*deriv G (τ r)) / (G (τ r)-z) * F (G (τ r))) =
      (fun r => c*((τ r*deriv G (τ r) / (G (τ r)-z))*F (G (τ r)))) := by
    funext r; ring
  have h2 : (fun r => c*(τ r*deriv G (τ r)) / (G (τ r)-z)) =
      (fun r => c*(τ r*deriv G (τ r) / (G (τ r)-z))) := by
    funext r; ring
  rw [h1,h2,intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul] at he
  erw [unitAddCircle_integral_eq_unitInterval (fun t : ℂ => t*deriv G t/(G t-z))] at hmass
  erw [unitAddCircle_integral_eq_unitInterval (fun t : ℂ => (t*deriv G t/(G t-z))*F (G t))]
  change (∫ r in (0:ℝ)..1, (τ r*deriv G (τ r) / (G (τ r)-z))*F (G (τ r))) = F z
  change (∫ r in (0:ℝ)..1, τ r*deriv G (τ r) / (G (τ r)-z)) = 1 at hmass
  rw [hmass,mul_one] at he
  exact mul_left_cancel₀ hc he

end

open Set Metric Complex MeasureTheory
open scoped Topology
local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

lemma actualExteriorKernel_circleB {a b : ℂ} {h : ℂ → ℂ} {R : ℝ}
    (hR : 1 < R) (ha : a ≠ 0) (hh : AnalyticOnNhd ℂ h (ball 0 R))
    (hi : InjOn (exteriorMap a b h) {t | R⁻¹ < ‖t‖})
    (hd : ∀ t, R⁻¹ < ‖t‖ → deriv (exteriorMap a b h) t ≠ 0)
    (hsupport : ∀ w t : Circle,
      0 ≤ (conj ((t : ℂ)*deriv (exteriorMap a b h) t)*
        (exteriorMap a b h t-exteriorMap a b h w)).re)
    (w t : UnitAddCircle) :
    (actualExteriorKernel hR ha hh hi hd hsupport).circleB w t =
      exteriorCorrection (exteriorMap a b h) w.toCircle t.toCircle := by
  have hw : (w.toCircle : ℂ)⁻¹ ∈ ball (0 : ℂ) R := by
    simpa only [mem_ball, dist_zero_right, norm_inv, Circle.norm_coe, inv_one] using hR
  have ht : (t.toCircle : ℂ)⁻¹ ∈ ball (0 : ℂ) R := by
    simpa only [mem_ball, dist_zero_right, norm_inv, Circle.norm_coe, inv_one] using hR
  have he := exteriorCorrection_eq_reciprocal (a := a) (b := b)
    (inv_ne_zero (Circle.coe_ne_zero w.toCircle)) (inv_ne_zero (Circle.coe_ne_zero t.toCircle))
    (hh _ hw).differentiableAt (hh _ ht).differentiableAt
    ((analyticOnNhd_dslope isOpen_ball hh hw) _ ht).differentiableAt
  change reciprocalCorrection a h (w.toCircle : ℂ)⁻¹ (t.toCircle : ℂ)⁻¹ = _
  simpa only [inv_inv] using he.symm

theorem actualExteriorCauchy_fix_trace {a b : ℂ} {h : ℂ → ℂ} {R : ℝ}
    (hR : 1 < R) (ha : a ≠ 0) (hh : AnalyticOnNhd ℂ h (ball 0 R))
    (hi : InjOn (exteriorMap a b h) {t | R⁻¹ < ‖t‖})
    (hd : ∀ t, R⁻¹ < ‖t‖ → deriv (exteriorMap a b h) t ≠ 0)
    (hsupport : ∀ w t : Circle,
      0 ≤ (conj ((t : ℂ)*deriv (exteriorMap a b h) t)*
        (exteriorMap a b h t-exteriorMap a b h w)).re)
    {Ω : Set ℂ} (hΩ : Convex ℝ Ω)
    (hboundary : MapsTo (exteriorMap a b h) (sphere 0 1) Ω)
    (hinner : MapsTo (exteriorMap a b h) ({t | R⁻¹ < ‖t‖} ∩ ball 0 1) Ω)
    {v : ℂ → ℂ} (hv : AnalyticOnNhd ℂ v Ω)
    (u : C(UnitAddCircle,ℂ)) (hu : ∀ t, u t = v (exteriorMap a b h t.toCircle)) :
    scalarFourier.cauchy (actualExteriorKernel hR ha hh hi hd hsupport).scalarM
      (ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ u) =
        ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ u := by
  let G := exteriorMap a b h
  let U : Set ℂ := {t | R⁻¹ < ‖t‖}
  have hU : IsOpen U := isOpen_lt continuous_const continuous_norm
  have hG : AnalyticOnNhd ℂ G U := analyticOnNhd_exteriorMap (lt_trans zero_lt_one hR) hh
  have hTU : sphere (0:ℂ) 1 ⊆ U := by
    intro t ht
    change R⁻¹ < ‖t‖
    rw [mem_sphere_zero_iff_norm.mp ht]
    exact (inv_lt_one₀ (lt_trans zero_lt_one hR)).mpr hR
  let V := U ∩ {w | AnalyticAt ℂ (fun w => v (G w)) w}
  have hV : IsOpen V := hU.inter (isOpen_analyticAt ℂ _)
  have hTV : sphere (0:ℂ) 1 ⊆ V := by
    intro t ht
    exact ⟨hTU ht,(hv _ (hboundary ht)).comp (hG t (hTU ht))⟩
  have hvV : AnalyticOnNhd ℂ (fun w => v (G w)) V := fun _ hw => hw.2
  have hp := scalarCauchy_fix_physical_trace (actualExteriorKernel hR ha hh hi hd hsupport)
    hV (hG.mono inter_subset_left) (hi.mono inter_subset_left)
    (fun w hw => hd w hw.1) hTV hvV
    (actualExteriorKernel_circleB hR ha hh hi hd hsupport) (v := v) (by
      intro w hw
      have hne : ∀ t : ℂ, 1 ≤ ‖t‖ → G t ≠ G w := by
        intro t ht he
        have htU : t ∈ U := lt_of_lt_of_le
          ((inv_lt_one₀ (lt_trans zero_lt_one hR)).mpr hR) ht
        have htw := hi htU hw.1.1 he
        have hwi : ‖w‖ < 1 := mem_ball_zero_iff.mp hw.2
        exact (not_lt_of_ge (htw ▸ ht)) hwi
      have hm := exterior_cauchy_kernel_integral ha
        (hh.mono (closedBall_subset_ball hR)) hne
      have he := circle_convex_cauchy hΩ hv (hG.mono hTU) hboundary
        (hinner ⟨hw.1.1,hw.2⟩)
        (fun t ht => hne t (le_of_eq (mem_sphere_zero_iff_norm.mp ht).symm)) hm
      change (∫ t : UnitAddCircle, v (G t.toCircle) *
        ((t.toCircle : ℂ)*deriv G t.toCircle/(G t.toCircle-G w))
          ∂AddCircle.haarAddCircle) = v (G w)
      simpa only [mul_comm] using he)
  dsimp only at hp
  convert hp using 1 <;> congr 2 <;> ext t <;> exact hu t


end CompleteCrouzeix

end

end OAI
