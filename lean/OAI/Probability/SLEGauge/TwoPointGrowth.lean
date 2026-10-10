import Mathlib
import OAI.Probability.SLE.MomentGauge
import OAI.Probability.SLEGauge.StateBounds

namespace OAI

/-! Hausdorff gauges, Loewner evolution and trace measures. -/

section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
open scoped Topology
open Set
open MeasureTheory Filter
open scoped NNReal Topology
open MeasureTheory Filter Set Metric Function ODE
open MeasureTheory ProbabilityTheory Filter Set
open Filter
open Filter Set
namespace ExactSLEMain
open Set
theorem loewner_two_point_growth {A : ℝ} (hA : 0 < A)
    {b : ℝ≥0 → ℝ} (hb : Continuous b) {T : ℝ≥0} {z w : ℂ}
    (hz : alive A b T z) (hw : alive A b T w) (hzw : z ≠ w) :
    ‖z-w‖ ≤ (2 * (loewnerMap A b T z).im / ‖deriv (loewnerMap A b T) z‖) *
      (‖loewnerMap A b T z-loewnerMap A b T w‖ /
       ‖loewnerMap A b T z-star (loewnerMap A b T w)‖) /
      (1-‖loewnerMap A b T z-loewnerMap A b T w‖ /
       ‖loewnerMap A b T z-star (loewnerMap A b T w)‖)^2 := by
  obtain ⟨f,hf⟩ := hz
  obtain ⟨g,hg⟩ := hw
  have hz : alive A b T z := ⟨f,hf⟩
  have hw : alive A b T w := ⟨g,hg⟩
  have hyz : 0 < z.im := by simpa only [hf.1] using (hf.2 0 (by simp)).1
  have hyw : 0 < w.im := by simpa only [hg.1] using (hg.2 0 (by simp)).1
  let V : ℝ → ℝ := fun u => (f u).im/Complex.normSq (f u-(b u.toNNReal : ℂ))
  let W : ℝ → ℝ := fun u => (g u).im/Complex.normSq (g u-(b u.toNNReal : ℂ))
  have hVc : ContinuousOn V (Icc (0 : ℝ) T) :=
    (Complex.continuous_im.comp_continuousOn (odeUntil_continuousOn hf)).div
      (Complex.continuous_normSq.comp_continuousOn (odeUntil_center_continuousOn hb hf))
      (fun u hu => (Complex.normSq_pos.mpr (odeUntil_center_ne_zero hf hu)).ne')
  let v : ℝ → ℝ := fun u => V (projIcc (0 : ℝ) T T.coe_nonneg u)
  have hv : Continuous v := hVc.domRestrict.comp continuous_projIcc
  have hve (u : ℝ) (hu : u ∈ Icc (0 : ℝ) T) : v u = V u := by
    dsimp [v]; rw [projIcc_of_mem _ hu]
  let R : ℝ → ℝ := fun u => 2*z.im*Real.exp (-2*A*(∫ s in (0 : ℝ)..u, v s^2))
  let r : ℝ → ℝ := fun u => ‖f u-g u‖/‖f u-star (g u)‖
  have hR (u : ℝ) (hu : u ∈ Icc (0 : ℝ) T) :
      HasDerivWithinAt R (-2*A*(V u)^2*R u) (Icc (0 : ℝ) T) u := by
    have hi := intervalIntegral.integral_hasDerivAt_right ((hv.pow 2).intervalIntegrable 0 u)
      (hv.pow 2).aestronglyMeasurable.stronglyMeasurableAtFilter (hv.pow 2).continuousAt
    have hh := (((hi.const_mul (-2*A)).exp).const_mul (2*z.im)).hasDerivWithinAt (s := Icc (0 : ℝ) T)
    convert hh using 1
    try rfl
    dsimp only [R,Pi.pow_apply]
    rw [hve u hu]
    ring
  have hr (u : ℝ) (hu : u ∈ Icc (0 : ℝ) T) :
      HasDerivWithinAt r (2*A*V u*W u*r u) (Icc (0 : ℝ) T) u :=
    odeUntil_pair_ratio_deriv hb hf hg hzw hu
  have hl (u : ℝ) (hu : u ∈ Icc (0 : ℝ) T) : r u < 1 := by
    have hlt := upper_pair_norm_lt (hf.2 u hu).1 (hg.2 u hu).1
    exact (div_lt_one ((norm_nonneg _).trans_lt hlt)).mpr hlt
  have hH (u : ℝ) (hu : u ∈ Icc (0 : ℝ) T) :
      V u*(1-r u) ≤ W u*(1+r u) := by
    have hh := upper_velocity_harnack
      (z := f u-(b u.toNNReal : ℂ)) (w := g u-(b u.toNNReal : ℂ))
      (by simpa using (hf.2 u hu).1) (by simpa using (hg.2 u hu).1)
    have he : f u-(b u.toNNReal : ℂ)-(g u-(b u.toNNReal : ℂ)) = f u-g u := by ring
    have he' : f u-(b u.toNNReal : ℂ)-star (g u-(b u.toNNReal : ℂ)) = f u-star (g u) := by simp
    simp only [he,he',Complex.sub_im,Complex.ofReal_im,sub_zero] at hh
    have hD := (norm_nonneg _).trans_lt (upper_pair_norm_lt (hf.2 u hu).1 (hg.2 u hu).1)
    have hdiv := (div_le_div_iff_of_pos_right hD).mpr hh
    change V u*(‖f u-star (g u)‖-‖f u-g u‖)/‖f u-star (g u)‖ ≤
      W u*(‖f u-star (g u)‖+‖f u-g u‖)/‖f u-star (g u)‖ at hdiv
    calc
      V u*(1-r u) = V u*(‖f u-star (g u)‖-‖f u-g u‖)/‖f u-star (g u)‖ := by
        change _*(1-‖f u-g u‖/‖f u-star (g u)‖) = _
        simp only [mul_sub,sub_div,mul_div_assoc,div_self hD.ne',mul_one]
      _ ≤ _ := hdiv
      _ = W u*(1+r u) := by
        change _ = W u*(1+‖f u-g u‖/‖f u-star (g u)‖)
        simp only [mul_add,add_div,mul_div_assoc,div_self hD.ne',mul_one]
  let K : ℝ → ℝ := fun u => R u*r u/(1-r u)^2
  let K' : ℝ → ℝ := fun u => 2*A*R u*r u*V u/(1-r u)^3 *
    (W u*(1+r u)-V u*(1-r u))
  have hK (u : ℝ) (hu : u ∈ Icc (0 : ℝ) T) :
      HasDerivWithinAt K (K' u) (Icc (0 : ℝ) T) u :=
    growth_factor_deriv (hR u hu) (hr u hu) (ne_of_lt (hl u hu))
  have hpos (u : ℝ) (hu : u ∈ Icc (0 : ℝ) T) : 0 ≤ K' u := by
    have hRp : 0 < R u := by dsimp [R]; positivity
    have hrp : 0 ≤ r u := div_nonneg (norm_nonneg _) (norm_nonneg _)
    have hVp : 0 < V u := div_pos (hf.2 u hu).1
      (Complex.normSq_pos.mpr (odeUntil_center_ne_zero hf hu))
    have hlp : 0 < 1-r u := sub_pos.mpr (hl u hu)
    have hHp : 0 ≤ W u*(1+r u)-V u*(1-r u) := sub_nonneg.mpr (hH u hu)
    dsimp [K']; positivity
  have hmono : MonotoneOn K (Icc (0 : ℝ) T) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc _ _) (HasDerivWithinAt.continuousOn hK)
      (fun u hu => (hK u (interior_subset hu)).mono interior_subset)
      (fun u hu => hpos u (interior_subset hu))
  have hstart : ‖z-w‖ ≤ K 0 := by
    simpa [K,R,r,hf.1,hg.1] using upper_initial_growth hyz hyw
  have hstop := hstart.trans (hmono (by simp) (by simp) T.coe_nonneg)
  have heR : R T = 2*(loewnerMap A b T z).im/‖deriv (loewnerMap A b T) z‖ := by
    have hi : (∫ u in (0 : ℝ)..(T : ℝ), v u^2) = ∫ u in (0 : ℝ)..(T : ℝ),
      ((loewnerMap A b u.toNNReal z-(b u.toNNReal : ℂ)).im/
        Complex.normSq (loewnerMap A b u.toNNReal z-(b u.toNNReal : ℂ)))^2 := by
      apply intervalIntegral.integral_congr
      intro u hu
      have hu' : u ∈ Icc (0 : ℝ) T := by simpa only [uIcc_of_le T.coe_nonneg] using hu
      dsimp only
      rw [hve u hu',loewnerMap_eq_solution_time hf hu']
      simp [V]
    dsimp only [R]
    rw [hi]
    have hh := loewner_radius_ratio hb hz
    rw [show 2*(loewnerMap A b T z).im/‖deriv (loewnerMap A b T) z‖ =
      2*((loewnerMap A b T z).im/‖deriv (loewnerMap A b T) z‖) by ring,hh]
    ring
  dsimp only [K,r] at hstop
  rw [heR,← loewnerMap_eq hf,← loewnerMap_eq hg] at hstop
  exact hstop

end ExactSLEMain
open MeasureTheory Set
namespace ExactSLEMain

lemma interaction_integral_strong {a c S T : ℝ}
    (ha : 0 < a) (hc : 0 ≤ c) (hac : 2*c < a) (hST : S ≤ T)
    {L s V W : ℝ → ℝ}
    (hV : ContinuousOn V (Icc S T)) (hW : ContinuousOn W (Icc S T))
    (hL : ∀ t ∈ Icc S T, HasDerivWithinAt L (-2*a*V t*W t) (Icc S T) t)
    (hs : ∀ t ∈ Icc S T, HasDerivWithinAt s ((V t)^2+(W t)^2) (Icc S T) t)
    (hs0 : ∀ t ∈ Icc S T, 0 ≤ s t)
    (hL0 : ∀ t ∈ Icc S T, 0 ≤ L t)
    (hdecay : ∀ t ∈ Icc S T, L t ≤ Real.exp (-a*s t/2)) :
    (∫ t in S..T, Real.exp (c*s t)*V t*W t) ≤ 1/(2*(a-2*c)) := by
  let k := a/2-c
  have hk : 0 < k := by dsimp [k]; linarith
  have hsc := HasDerivWithinAt.continuousOn hs
  let q : ℝ → ℝ := fun t => Real.exp (c*s t)*V t*W t
  have hq : ContinuousOn q (Icc S T) :=
    ((Real.continuous_exp.comp_continuousOn (hsc.const_mul c)).mul hV).mul hW
  let q₀ : ℝ → ℝ := fun t => q (projIcc S T hST t)
  have hq₀ : Continuous q₀ := hq.domRestrict.comp continuous_projIcc
  have hqe (t : ℝ) (ht : t ∈ Icc S T) : q₀ t = q t := by
    dsimp [q₀]; rw [projIcc_of_mem _ ht]
  let F : ℝ → ℝ := fun t => Real.exp (c*s t)*L t + c/k*Real.exp (-k*s t) +
    2*a*(∫ v in S..t, q₀ v)
  let F' : ℝ → ℝ := fun t => c*((V t)^2+(W t)^2)*
    (Real.exp (c*s t)*L t-Real.exp (-k*s t))
  have hd (t : ℝ) (ht : t ∈ Icc S T) :
      HasDerivWithinAt F (F' t) (Icc S T) t := by
    have hi := intervalIntegral.integral_hasDerivAt_right (hq₀.intervalIntegrable S t)
      hq₀.aestronglyMeasurable.stronglyMeasurableAtFilter hq₀.continuousAt
    have hh := ((((hs t ht).const_mul c).exp.mul (hL t ht)).add
      ((((hs t ht).const_mul (-k)).exp).const_mul (c/k))).add
      (hi.const_mul (2*a)).hasDerivWithinAt
    convert hh using 1
    try rfl
    dsimp only [F',q]
    rw [hqe t ht]
    dsimp only [q]
    field_simp
    ring
  have hbound (t : ℝ) (ht : t ∈ Icc S T) :
      Real.exp (c*s t)*L t ≤ Real.exp (-k*s t) := by
    calc
      _ ≤ Real.exp (c*s t)*Real.exp (-a*s t/2) :=
        mul_le_mul_of_nonneg_left (hdecay t ht) (Real.exp_pos _).le
      _ = Real.exp (-k*s t) := by rw [←Real.exp_add]; congr 1; dsimp [k]; ring
  have hn (t : ℝ) (ht : t ∈ Icc S T) : F' t ≤ 0 := by
    exact mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hc (add_nonneg (sq_nonneg _) (sq_nonneg _)))
      (sub_nonpos.mpr (hbound t ht))
  have hanti : AntitoneOn F (Icc S T) :=
    antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc _ _) (HasDerivWithinAt.continuousOn hd)
      (fun t ht => (hd t (interior_subset ht)).mono interior_subset)
      (fun t ht => hn t (interior_subset ht))
  have htS : S ∈ Icc S T := ⟨le_rfl,hST⟩
  have htT : T ∈ Icc S T := ⟨hST,le_rfl⟩
  have hS : F S ≤ 1+c/k := by
    have hex : Real.exp (-k*s S) ≤ 1 :=
      Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hk.le) (hs0 S htS))
    have hb := hbound S htS
    have hc' := mul_le_mul_of_nonneg_left hex (div_nonneg hc hk.le)
    dsimp only [F]
    simp only [intervalIntegral.integral_same,mul_zero,add_zero]
    linarith
  have hT : 2*a*(∫ v in S..T, q₀ v) ≤ F T := by
    have h1 := mul_nonneg (Real.exp_pos (c*s T)).le (hL0 T htT)
    have h2 := mul_nonneg (div_nonneg hc hk.le) (Real.exp_pos (-k*s T)).le
    dsimp only [F]; linarith
  have hall := hT.trans ((hanti htS htT hST).trans hS)
  have hie : (∫ v in S..T, q₀ v) = ∫ v in S..T, Real.exp (c*s v)*V v*W v := by
    apply intervalIntegral.integral_congr
    intro t ht
    exact hqe t (by simpa only [uIcc_of_le hST] using ht)
  rw [hie] at hall
  have hdiv : (∫ v in S..T, Real.exp (c*s v)*V v*W v) ≤ (1+c/k)/(2*a) :=
    (le_div_iff₀ (show 0 < 2*a by positivity)).mpr (by convert hall using 1; ring)
  have he : (1+c/k)/(2*a) = 1/(2*(a-2*c)) := by
    have hh : a-2*c = 2*k := by dsimp [k]; ring
    rw [hh]
    field_simp
    dsimp [k]
    ring
  rwa [he] at hdiv

lemma interaction_constant_comparison {a c : ℝ} (ha : 0 < a) (hc : 0 ≤ c)
    (hac : 2*c < a) :
    1/(2*(a-2*c)) ≤ Real.exp (2*c)/(2*a*(1-Real.exp (2*c-a))) := by
  have hδ : 0 < a-2*c := sub_pos.mpr hac
  have he : 0 < 1-Real.exp (2*c-a) := sub_pos.mpr
    (Real.exp_lt_one_iff.mpr (sub_neg.mpr hac))
  have hp := Real.exp_pos (2*c-a)
  have h1 := Real.add_one_le_exp (2*c-a)
  have h2 := Real.add_one_le_exp (2*c)
  have h3 : (a-2*c)*(1-Real.exp (2*c-a)) ≤ a-2*c := by
    nlinarith [mul_pos hδ hp]
  have h4 : 2*c*(1-Real.exp (2*c-a)) ≤ 2*c*(a-2*c) := by
    exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have h5 := mul_le_mul_of_nonneg_left h2 hδ.le
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  nlinarith

theorem weighted_interaction_integral {a c S T : ℝ}
    (ha : 0 < a) (hc : 0 ≤ c) (hac : 2*c < a) (hST : S ≤ T)
    {L s V W : ℝ → ℝ}
    (hV : ContinuousOn V (Icc S T)) (hW : ContinuousOn W (Icc S T))
    (hL : ∀ t ∈ Icc S T, HasDerivWithinAt L (-2*a*V t*W t) (Icc S T) t)
    (hs : ∀ t ∈ Icc S T, HasDerivWithinAt s ((V t)^2+(W t)^2) (Icc S T) t)
    (hs0 : ∀ t ∈ Icc S T, 0 ≤ s t)
    (hL0 : ∀ t ∈ Icc S T, 0 ≤ L t)
    (hdecay : ∀ t ∈ Icc S T, L t ≤ Real.exp (-a*s t/2)) :
    (∫ t in S..T, Real.exp (c*s t)*V t*W t) ≤
      Real.exp (2*c)/(2*a*(1-Real.exp (2*c-a))) :=
  (interaction_integral_strong ha hc hac hST hV hW hL hs hs0 hL0 hdecay).trans
    (interaction_constant_comparison ha hc hac)

end ExactSLEMain

namespace ExactSLEMain
 

noncomputable def fullLoewnerRadius (A : ℝ) (b : ℝ≥0 → ℝ) (z : ℂ) (t : ℝ≥0) : ℝ :=
  2*(loewnerMap A b t z).im/‖deriv (loewnerMap A b t) z‖
 

noncomputable def odeSpeed (b : ℝ≥0 → ℝ) (T : ℝ≥0) (f : ℝ → ℂ) (t : ℝ) : ℝ :=
  let u : ℝ := projIcc (0:ℝ) T T.coe_nonneg t
  (f u).im/Complex.normSq (f u-(b u.toNNReal : ℂ))
noncomputable def activeODEClock (b : ℝ≥0 → ℝ) (T σ : ℝ≥0) (f : ℝ → ℂ) (t : ℝ) : ℝ :=
  ∫ u in (σ:ℝ)..t, odeSpeed b T f u^2
end ExactSLEMain
namespace ExactSLEMain
lemma odeSpeed_eq {b : ℝ≥0 → ℝ} {T : ℝ≥0} (f : ℝ → ℂ) {t : ℝ}
    (ht : t∈Icc (0:ℝ) T) :
    odeSpeed b T f t=(f t).im/Complex.normSq (f t-(b t.toNNReal : ℂ)) := by
  simp only [odeSpeed,projIcc_of_mem _ ht]
lemma odeSpeed_continuous {a : ℝ} {b : ℝ≥0 → ℝ} (hb : Continuous b)
    {z : ℂ} {T : ℝ≥0} {f : ℝ → ℂ} (hf : odeUntil a b z T f) :
    Continuous (odeSpeed b T f) := by
  have hv : ContinuousOn (fun t => (f t).im/Complex.normSq (f t-(b t.toNNReal : ℂ))) (Icc (0:ℝ) T) :=
    (Complex.continuous_im.comp_continuousOn (odeUntil_continuousOn hf)).div
      (Complex.continuous_normSq.comp_continuousOn (odeUntil_center_continuousOn hb hf))
      (fun t ht => (Complex.normSq_pos.mpr (odeUntil_center_ne_zero hf ht)).ne')
  exact hv.domRestrict.comp continuous_projIcc
lemma fullRadius_primitive {a : ℝ} {b : ℝ≥0 → ℝ} (hb : Continuous b)
    {z : ℂ} {T : ℝ≥0} {f : ℝ → ℂ} (hf : odeUntil a b z T f)
    {t : ℝ≥0} (ht : t≤T) :
    fullLoewnerRadius a b z t=2*z.im*Real.exp
      (-2*a*(∫ u in (0:ℝ)..(t:ℝ), odeSpeed b T f u^2)) := by
  have hz : alive a b t z := ⟨f,odeUntil_mono hf ht⟩
  have he : (∫ u in (0:ℝ)..(t:ℝ), odeSpeed b T f u^2) =
      ∫ u in (0:ℝ)..(t:ℝ),
        ((loewnerMap a b u.toNNReal z-(b u.toNNReal : ℂ)).im/
          Complex.normSq (loewnerMap a b u.toNNReal z-(b u.toNNReal : ℂ)))^2 := by
    apply intervalIntegral.integral_congr
    intro u hu
    have hu0 : u∈Icc (0:ℝ) t := by simpa only [uIcc_of_le t.coe_nonneg] using hu
    have hu' : u∈Icc (0:ℝ) T := ⟨hu0.1,hu0.2.trans (by exact_mod_cast ht)⟩
    dsimp only
    rw [odeSpeed_eq f hu',loewnerMap_eq_solution_time hf hu']
    simp
  unfold fullLoewnerRadius
  rw [show 2*(loewnerMap a b t z).im/‖deriv (loewnerMap a b t) z‖=
    2*((loewnerMap a b t z).im/‖deriv (loewnerMap a b t) z‖) by ring,
    loewner_radius_ratio hb hz,he]
  ring
lemma fullRadius_pos {a : ℝ} {b : ℝ≥0 → ℝ} (hb : Continuous b)
    {z : ℂ} {T : ℝ≥0} {f : ℝ → ℂ} (hf : odeUntil a b z T f)
    {t : ℝ≥0} (ht : t≤T) : 0<fullLoewnerRadius a b z t := by
  have hz : 0<z.im := by simpa only [hf.1] using (hf.2 0 (by simp)).1
  rw [fullRadius_primitive hb hf ht]
  positivity
lemma fullRadius_active_clock {a : ℝ} {b : ℝ≥0 → ℝ} (hb : Continuous b)
    {z : ℂ} {T : ℝ≥0} {f : ℝ → ℂ} (hf : odeUntil a b z T f)
    {σ t : ℝ≥0} (hσ : σ≤T) (ht : t≤T) :
    fullLoewnerRadius a b z t=fullLoewnerRadius a b z σ*
      Real.exp (-2*a*activeODEClock b T σ f t) := by
  have hc := (odeSpeed_continuous hb hf).pow 2
  have he := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hc.intervalIntegrable 0 (σ:ℝ)) (hc.intervalIntegrable (σ:ℝ) (t:ℝ))
  simp only [Pi.pow_apply] at he
  rw [fullRadius_primitive hb hf ht,fullRadius_primitive hb hf hσ]
  unfold activeODEClock
  rw [mul_assoc (2*z.im),← Real.exp_add,← mul_add,he]
lemma activeODEClock_deriv {a : ℝ} {b : ℝ≥0 → ℝ} (hb : Continuous b)
    {z : ℂ} {T : ℝ≥0} {f : ℝ → ℂ} (hf : odeUntil a b z T f)
    (σ : ℝ≥0) (t : ℝ) :
    HasDerivAt (activeODEClock b T σ f) (odeSpeed b T f t^2) t := by
  have hc := (odeSpeed_continuous hb hf).pow 2
  exact intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable (σ:ℝ) t)
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt
lemma activeODEClock_nonneg {b : ℝ≥0 → ℝ} {T σ : ℝ≥0} {f : ℝ → ℂ} {t : ℝ}
    (hσ : (σ:ℝ)≤t) : 0≤activeODEClock b T σ f t := by
  exact intervalIntegral.integral_nonneg hσ (fun _ _ => sq_nonneg _)
end ExactSLEMain
namespace ExactSLEMain
lemma neg_log_le_sqrt_ratio {r : ℝ} (hr : 0<r) (hr1 : r≤1) :
    -Real.log r≤(1-r)/Real.sqrt r := by
  have hl : 0≤-Real.log r/2 := by linarith [Real.log_nonpos hr.le hr1]
  have hs := Real.self_le_sinh_iff.mpr hl
  have he : Real.exp (Real.log r/2)=Real.sqrt r := by rw [Real.exp_half,Real.exp_log hr]
  have he' : Real.exp (-Real.log r/2)=(Real.sqrt r)⁻¹ := by
    rw [neg_div,Real.exp_neg,he]
  rw [Real.sinh_eq,he',show -(-Real.log r/2)=Real.log r/2 by ring,he] at hs
  have hsq := Real.sq_sqrt hr.le
  exact (le_div_iff₀ (Real.sqrt_pos.mpr hr)).mpr (by
    have hh := mul_le_mul_of_nonneg_right hs (Real.sqrt_nonneg r)
    field_simp at hh
    nlinarith)
lemma log_sq_mul_le {r : ℝ} (hr : 0<r) (hr1 : r≤1) :
    (Real.log r)^2*r≤(1-r)^2 := by
  have h := (le_div_iff₀ (Real.sqrt_pos.mpr hr)).mp (neg_log_le_sqrt_ratio hr hr1)
  have hl : 0≤-Real.log r := neg_nonneg.mpr (Real.log_nonpos hr.le hr1)
  have hprod := mul_nonneg hl (Real.sqrt_nonneg r)
  have hsq := mul_self_le_mul_self hprod h
  nlinarith [Real.sq_sqrt hr.le]
end ExactSLEMain
namespace ExactSLEMain
lemma ode_pair_ratio_pos_lt_one {a : ℝ} {b : ℝ≥0 → ℝ} (hb : Continuous b)
    {z w : ℂ} {T : ℝ≥0} {f g : ℝ → ℂ}
    (hf : odeUntil a b z T f) (hg : odeUntil a b w T g) (hzw : z≠w)
    {t : ℝ} (ht : t∈Icc (0:ℝ) T) :
    0<‖f t-g t‖/‖f t-star (g t)‖ ∧ ‖f t-g t‖/‖f t-star (g t)‖<1 := by
  have hlt := upper_pair_norm_lt (hf.2 t ht).1 (hg.2 t ht).1
  have hden : 0<‖f t-star (g t)‖ := (norm_nonneg _).trans_lt hlt
  exact ⟨div_pos (norm_pos_iff.mpr (odeUntil_pair_ne hb hf hg hzw ht)) hden,
    (div_lt_one hden).mpr hlt⟩
lemma actual_pair_clock_decay {a : ℝ} (ha : 0<a)
    {b : ℝ≥0 → ℝ} (hb : Continuous b) {z w : ℂ} {f g : ℝ → ℂ}
    {T σ t : ℝ≥0} (hσ : σ≤T) (ht : t≤T)
    (hf : odeUntil a b z T f) (hg : odeUntil a b w T g) (hzw : z≠w)
    (hcap : fullLoewnerRadius a b z σ≤‖z-w‖) :
    -Real.log (‖f t-g t‖/‖f t-star (g t)‖)≤
      Real.exp (-a*activeODEClock b T σ f t) := by
  let r := ‖f t-g t‖/‖f t-star (g t)‖
  have ht' : (t:ℝ)∈Icc (0:ℝ) T := ⟨t.coe_nonneg,by exact_mod_cast ht⟩
  have hr := ode_pair_ratio_pos_lt_one hb hf hg hzw ht'
  have hgrowth := loewner_two_point_growth ha hb
    (show alive a b t z from ⟨f,odeUntil_mono hf ht⟩)
    (show alive a b t w from ⟨g,odeUntil_mono hg ht⟩) hzw
  change ‖z-w‖ ≤ fullLoewnerRadius a b z t * _ / _ at hgrowth
  rw [loewnerMap_eq (odeUntil_mono hf ht),loewnerMap_eq (odeUntil_mono hg ht)] at hgrowth
  change ‖z-w‖≤fullLoewnerRadius a b z t*r/(1-r)^2 at hgrowth
  have hden : 0<(1-r)^2 := sq_pos_of_pos (sub_pos.mpr hr.2)
  have hgrowth' := (le_div_iff₀ hden).mp hgrowth
  rw [fullRadius_active_clock hb hf hσ ht] at hgrowth'
  have hR := fullRadius_pos hb hf hσ
  have hmul : fullLoewnerRadius a b z σ*(1-r)^2 ≤
      fullLoewnerRadius a b z σ*(Real.exp (-2*a*activeODEClock b T σ f t)*r) :=
    (mul_le_mul_of_nonneg_right hcap hden.le).trans (by simpa only [mul_assoc] using hgrowth')
  have hbound := (mul_le_mul_iff_right₀ hR).mp hmul
  have hsq : (Real.log r)^2≤Real.exp (-2*a*activeODEClock b T σ f t) :=
    (mul_le_mul_iff_left₀ hr.1).mp ((log_sq_mul_le hr.1 hr.2.le).trans hbound)
  have he : Real.exp (-2*a*activeODEClock b T σ f t) =
      (Real.exp (-a*activeODEClock b T σ f t))^2 := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [he] at hsq
  change -Real.log r≤_
  nlinarith [Real.exp_pos (-a*activeODEClock b T σ f t)]
lemma ode_pair_log_deriv {a : ℝ} {b : ℝ≥0 → ℝ} (hb : Continuous b)
    {z w : ℂ} {T : ℝ≥0} {f g : ℝ → ℂ}
    (hf : odeUntil a b z T f) (hg : odeUntil a b w T g) (hzw : z≠w)
    {t : ℝ} (ht : t∈Icc (0:ℝ) T) :
    HasDerivWithinAt (fun u => -Real.log (‖f u-g u‖/‖f u-star (g u)‖))
      (-2*a*odeSpeed b T f t*odeSpeed b T g t) (Icc (0:ℝ) T) t := by
  have hp := (ode_pair_ratio_pos_lt_one hb hf hg hzw ht).1
  have hd := ((odeUntil_pair_ratio_deriv hb hf hg hzw ht).log hp.ne').neg
  rw [mul_div_cancel_right₀ _ hp.ne'] at hd
  convert hd using 1
  try rfl
  rw [odeSpeed_eq f ht,odeSpeed_eq g ht]
  ring
end ExactSLEMain
namespace ExactSLEMain
 

theorem actual_pair_interaction {a c : ℝ} (ha : 0<a) (hc : 0≤c) (hac : 2*c<a)
    {b : ℝ≥0 → ℝ} (hb : Continuous b) {z w : ℂ} {f g : ℝ → ℂ}
    {T S σ τ : ℝ≥0} (hST : S≤T) (hσ : σ≤S) (hτ : τ≤S)
    (hf : odeUntil a b z T f) (hg : odeUntil a b w T g) (hzw : z≠w)
    (hcapz : fullLoewnerRadius a b z σ≤‖z-w‖)
    (hcapw : fullLoewnerRadius a b w τ≤‖z-w‖) :
    (∫ t in (S:ℝ)..(T:ℝ), Real.exp (c*(activeODEClock b T σ f t+
      activeODEClock b T τ g t))*odeSpeed b T f t*odeSpeed b T g t) ≤
      Real.exp (2*c)/(2*a*(1-Real.exp (2*c-a))) := by
  let L := fun t : ℝ => -Real.log (‖f t-g t‖/‖f t-star (g t)‖)
  let u := activeODEClock b T σ f
  let v := activeODEClock b T τ g
  have hST' : (S:ℝ)≤T := by exact_mod_cast hST
  have hsub : Icc (S:ℝ) T ⊆ Icc (0:ℝ) T := Icc_subset_Icc_left S.coe_nonneg
  have hnon (t : ℝ) (ht : t∈Icc (S:ℝ) T) : 0≤L t := by
    have hr := ode_pair_ratio_pos_lt_one hb hf hg hzw (hsub ht)
    exact neg_nonneg.mpr (Real.log_nonpos hr.1.le hr.2.le)
  have hdecay (t : ℝ) (ht : t∈Icc (S:ℝ) T) :
      L t≤Real.exp (-a*(u t+v t)/2) := by
    have ht0 : 0≤t := (hsub ht).1
    have htT : t.toNNReal≤T := by
      exact_mod_cast (show (t.toNNReal:ℝ)≤T by simpa only [Real.coe_toNNReal _ ht0] using ht.2)
    have hz := actual_pair_clock_decay ha hb (hσ.trans hST) htT hf hg hzw hcapz
    have hcapw' : fullLoewnerRadius a b w τ≤‖w-z‖ := by simpa only [norm_sub_rev] using hcapw
    have hw := actual_pair_clock_decay ha hb (hτ.trans hST) htT hg hf hzw.symm hcapw'
    rw [Real.coe_toNNReal _ ht0] at hz hw
    have hnorm : ‖g t-star (f t)‖=‖f t-star (g t)‖ := by
      calc
        _ = ‖star (g t-star (f t))‖ := (norm_star _).symm
        _ = ‖star (g t)-f t‖ := by rw [star_sub,star_star]
        _ = _ := norm_sub_rev _ _
    rw [hnorm,norm_sub_rev (g t) (f t)] at hw
    change L t≤Real.exp (-a*u t) at hz
    change L t≤Real.exp (-a*v t) at hw
    rcases le_total (u t) (v t) with h|h
    · exact hw.trans (Real.exp_le_exp.mpr (by nlinarith))
    · exact hz.trans (Real.exp_le_exp.mpr (by nlinarith))
  exact weighted_interaction_integral ha hc hac hST'
    (L:=L) (s:=fun t => u t+v t) (V:=odeSpeed b T f) (W:=odeSpeed b T g)
    (odeSpeed_continuous hb hf).continuousOn (odeSpeed_continuous hb hg).continuousOn
    (fun t ht => (ode_pair_log_deriv hb hf hg hzw (hsub ht)).mono hsub)
    (fun t _ => ((activeODEClock_deriv hb hf σ t).add
      (activeODEClock_deriv hb hg τ t)).hasDerivWithinAt)
    (fun t ht => add_nonneg (activeODEClock_nonneg ((by exact_mod_cast hσ : (σ:ℝ)≤S).trans ht.1))
      (activeODEClock_nonneg ((by exact_mod_cast hτ : (τ:ℝ)≤S).trans ht.1))) hnon hdecay
end ExactSLEMain
namespace ExactSLEGreen
open ExactSLEMain ExactSLEGenerator ExactSLEFiniteTilt
end ExactSLEGreen
end

end OAI
