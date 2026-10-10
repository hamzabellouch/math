import Mathlib
import OAI.Probability.ThreeState.RadialMoments

namespace OAI

/-! Fourth-moment resolvents and their lower bounds. -/

namespace ThreeState.Radial
open MeasureTheory

noncomputable def fourthResolvent (v : Fin 3 → ℝ) (t : ℝ) : ℝ := avg (fun i => (v i)^4/(1+t*v i))
noncomputable def doubleFourthResolvent (v : Fin 3 → ℝ) (lam t : ℝ) : ℝ :=
  avg (fun i => (v i)^4/((1+t*v i)*(1+lam*t*v i)))

lemma fourth_moment (v : Fin 3 → ℝ) (hv : avg v = 0) : avg (fun i => (v i)^4) = 6*(momentX v)^2 := by
  simp only [momentX, avg_expand, zero_sum_elim v hv]
  ring

lemma fourthResolvent_eq (v : Fin 3 → ℝ) (hv : avg v = 0) (hp : ∀ i, 0 < 1+v i)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    fourthResolvent v t = (6*(momentX v)^2-10*t*momentX v*momentY v+4*t^2*(momentY v)^2)/denom v t := by
  have h0 := ne_of_gt (message_segment_pos v hp t ht0 ht1 0)
  have h1 := ne_of_gt (message_segment_pos v hp t ht0 ht1 1)
  have h2 := ne_of_gt (message_segment_pos v hp t ht0 ht1 2)
  have h0c : 1+v 0*t ≠ 0 := by simpa [mul_comm] using h0
  have h1c : 1+v 1*t ≠ 0 := by simpa [mul_comm] using h1
  have h2c : 1+v 2*t ≠ 0 := by simpa [mul_comm] using h2
  rw [denom_product v hv t]
  simp only [fourthResolvent, momentX, momentY, avg_expand]
  field_simp [h0, h1, h2, h0c, h1c, h2c]
  rw [zero_sum_elim v hv]
  ring

lemma h_polynomial_bound (z : ℝ) (hz0 : 0 ≤ z) (hz1 : z < 1) :
    (1-3*z^2+2*z^3)*(4+(64/9:ℝ)*(z-1/2)^2) ≤ 6-10*z+4*z^2 := by
  rcases hz0.eq_or_lt with hzero | _
  · rw [← hzero]
    norm_num
  have hE : 1+z-2*z^2 ≤ (9/8:ℝ) := by nlinarith [sq_nonneg (z-1/4)]
  have hh : (1+z-2*z^2)*(4+(64/9:ℝ)*(z-1/2)^2) ≤ 6-4*z := by
    nlinarith [mul_nonneg (show 0 ≤ (9/8:ℝ)-(1+z-2*z^2) by linarith) (sq_nonneg (z-1/2))]
  have he := mul_le_mul_of_nonneg_left hh (show 0 ≤ 1-z by linarith)
  nlinarith only [he]

lemma momentY_sqrt_bound (v : Fin 3 → ℝ) (hv : avg v = 0) :
    -(Real.sqrt (momentX v))^3 ≤ momentY v ∧ momentY v ≤ (Real.sqrt (momentX v))^3 := by
  have h := discriminant_nonneg v hv
  have hs := Real.sq_sqrt (momentX_nonneg v)
  have he : (momentX v)^3 = ((Real.sqrt (momentX v))^3)^2 := by
    calc
      (momentX v)^3 = ((Real.sqrt (momentX v))^2)^3 := congrArg (fun x : ℝ => x^3) hs.symm
      _ = _ := by ring
  rw [he] at h
  have hr : 0 ≤ (Real.sqrt (momentX v))^3 := by positivity
  exact abs_le.mp ((sq_le_sq₀ (abs_nonneg (momentY v)) hr).mp (by simpa only [sq_abs] using h))

lemma fourthResolvent_lower (v : Fin 3 → ℝ) (hv : avg v = 0) (hp : ∀ i, 0 < 1+v i)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (momentX v)^2*(4+(64/9:ℝ)*(t*Real.sqrt (momentX v)-1/2)^2) ≤ fourthResolvent v t := by
  let r := Real.sqrt (momentX v)
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hr2 : r^2 = momentX v := Real.sq_sqrt (momentX_nonneg v)
  have hr1 : r < 1 := by nlinarith [momentX_lt_one v hv hp]
  have hy := momentY_sqrt_bound v hv
  change -r^3 ≤ momentY v ∧ momentY v ≤ r^3 at hy
  have hz0 : 0 ≤ t*r := mul_nonneg ht0 hr0
  have hz1 : t*r < 1 := lt_of_le_of_lt (mul_le_of_le_one_left hr0 ht1) hr1
  have hn : (momentX v)^2*(6-10*(t*r)+4*(t*r)^2) ≤
      6*(momentX v)^2-10*t*momentX v*momentY v+4*t^2*(momentY v)^2 := by
    have htr : t*r ≤ 1 := hz1.le
    have hfac : 0 ≤ 10*momentX v-4*t*(momentY v+r^3) := by
      have h1 := mul_le_mul_of_nonneg_left hy.2 (by positivity : 0 ≤ 4*t)
      have h2 := mul_le_mul_of_nonneg_left htr (by positivity : 0 ≤ 8*r^2)
      nlinarith only [h1,h2, sq_nonneg r,hr2]
    have hh := mul_nonneg (mul_nonneg ht0 (sub_nonneg.mpr hy.2)) hfac
    rw [← hr2] at hh ⊢
    nlinarith only [hh]
  have hd : denom v t ≤ 1-3*(t*r)^2+2*(t*r)^3 := by
    have hh := mul_le_mul_of_nonneg_left hy.2 (by positivity : 0 ≤ 2*t^3)
    dsimp only [denom]
    rw [← hr2]
    nlinarith only [hh]
  have hg : 0 ≤ (momentX v)^2*(4+(64/9:ℝ)*(t*r-1/2)^2) := by positivity
  have hh := mul_le_mul_of_nonneg_left hd hg
  have hpoly := mul_le_mul_of_nonneg_left (h_polynomial_bound (t*r) hz0 hz1) (sq_nonneg (momentX v))
  rw [fourthResolvent_eq v hv hp t ht0 ht1]
  apply (le_div_iff₀ (denom_pos v hv hp t ht0 ht1)).mpr
  dsimp only [r] at hh hpoly
  nlinarith only [hh,hpoly,hn]

lemma fourthResolvent_four (v : Fin 3 → ℝ) (hv : avg v = 0) (hp : ∀ i, 0 < 1+v i)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : 4*(momentX v)^2 ≤ fourthResolvent v t := by
  have hh := fourthResolvent_lower v hv hp t ht0 ht1
  nlinarith [mul_nonneg (sq_nonneg (momentX v)) (sq_nonneg (t*Real.sqrt (momentX v)-1/2))]

end ThreeState.Radial
namespace ThreeState.Radial
open MeasureTheory

lemma doubleFourthResolvent_lower (v : Fin 3 → ℝ) (hv : avg v = 0) (hp : ∀ i, 0 < 1+v i)
    (lam : ℝ) (hl0 : 0 ≤ lam) (hl1 : lam ≤ 1) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    2*fourthResolvent v t ≤ (2+lam)*doubleFourthResolvent v lam t := by
  let c := 1+lam/2
  have hc : 0 < c := by dsimp [c]; linarith
  have hlt0 : 0 ≤ lam*t := mul_nonneg hl0 ht0
  have hlt1 : lam*t ≤ 1 := (mul_le_of_le_one_left ht0 hl1).trans ht1
  have hi (i : Fin 3) : (2*c-1+lam)*(v i)^4/(1+t*v i)-lam*(v i)^4 ≤
      c^2*(v i)^4/((1+t*v i)*(1+lam*t*v i)) := by
    have hd := message_segment_pos v hp t ht0 ht1 i
    have he := message_segment_pos v hp (lam*t) hlt0 hlt1 i
    have hdc : 1+v i*t ≠ 0 := by simpa [mul_comm] using (ne_of_gt hd)
    have hec : 1+v i*t*lam ≠ 0 := by convert ne_of_gt he using 1; ring
    have hh : 0 ≤ (v i)^4*(c-(1+lam*t*v i))^2/((1+t*v i)*(1+lam*t*v i)) := by positivity
    have hid : c^2*(v i)^4/((1+t*v i)*(1+lam*t*v i))-
      ((2*c-1+lam)*(v i)^4/(1+t*v i)-lam*(v i)^4) =
      (v i)^4*(c-(1+lam*t*v i))^2/((1+t*v i)*(1+lam*t*v i)) := by
      field_simp [ne_of_gt hd, ne_of_gt he, hdc, hec]
      ring
    linarith
  have hh : (2*c-1+lam)*fourthResolvent v t-lam*(6*(momentX v)^2) ≤
      c^2*doubleFourthResolvent v lam t := by
    rw [← fourth_moment v hv]
    simp only [fourthResolvent, doubleFourthResolvent, avg_expand]
    have hi0 := hi 0
    have hi1 := hi 1
    have hi2 := hi 2
    simp only [mul_div_assoc] at hi0 hi1 hi2
    nlinarith only [hi0,hi1,hi2]
  have hw := fourthResolvent_four v hv hp t ht0 ht1
  have hnon := mul_nonneg hl0 (show 0 ≤ fourthResolvent v t-4*(momentX v)^2 by linarith)
  have hcW : c*fourthResolvent v t ≤ c^2*doubleFourthResolvent v lam t := by
    dsimp only [c] at *
    nlinarith only [hh,hnon]
  have hres : fourthResolvent v t ≤ c*doubleFourthResolvent v lam t := by
    apply (mul_le_mul_iff_right₀ hc).mp
    nlinarith only [hcW]
  dsimp only [c] at hres
  linarith

lemma continuousOn_fourthResolvent (v : Fin 3 → ℝ) (hp : ∀ i, 0 < 1+v i) :
    ContinuousOn (fourthResolvent v) (Set.Icc 0 1) := by
  have hi (i : Fin 3) : ContinuousOn (fun t : ℝ => (v i)^4/(1+t*v i)) (Set.Icc 0 1) :=
    continuousOn_const.div (by fun_prop) (fun t ht => ne_of_gt (message_segment_pos v hp t ht.1 ht.2 i))
  convert (((hi 0).add (hi 1)).add (hi 2)).div_const 3 using 1
  funext t
  exact avg_expand _

lemma continuousOn_doubleFourthResolvent (v : Fin 3 → ℝ) (hp : ∀ i, 0 < 1+v i)
    (lam : ℝ) (hl0 : 0 ≤ lam) (hl1 : lam ≤ 1) :
    ContinuousOn (doubleFourthResolvent v lam) (Set.Icc 0 1) := by
  have hi (i : Fin 3) : ContinuousOn (fun t : ℝ => (v i)^4/((1+t*v i)*(1+lam*t*v i))) (Set.Icc 0 1) :=
    continuousOn_const.div (by fun_prop) (fun t ht => ne_of_gt (mul_pos
      (message_segment_pos v hp t ht.1 ht.2 i)
      (message_segment_pos v hp (lam*t) (mul_nonneg hl0 ht.1) ((mul_le_of_le_one_left ht.1 hl1).trans ht.2) i)))
  convert (((hi 0).add (hi 1)).add (hi 2)).div_const 3 using 1
  funext t
  exact avg_expand _

noncomputable def resolventA (v : Fin 3 → ℝ) : ℝ := ∫ t in (0:ℝ)..1, t^2*fourthResolvent v t
noncomputable def resolventQ (v : Fin 3 → ℝ) (lam : ℝ) : ℝ := (∫ t in (0:ℝ)..1, t^2*doubleFourthResolvent v lam t)/2
noncomputable def functionJ (v : Fin 3 → ℝ) : ℝ := avg (fun i => v i*Real.log (1+v i))/2

lemma integral_h_lower (r : ℝ) :
    (∫ t in (0:ℝ)..1, t^2*(4+(64/9:ℝ)*(t*r-1/2)^2)) = (37/27:ℝ)+(64/45:ℝ)*(r-5/8)^2 := by
  let P := fun t : ℝ => (52/27:ℝ)*t^3-(16/9:ℝ)*r*t^4+(64/45:ℝ)*r^2*t^5
  have hd (t : ℝ) : HasDerivAt P (t^2*(4+(64/9:ℝ)*(t*r-1/2)^2)) t := by
    dsimp only [P]
    convert ((((hasDerivAt_id t).pow 3).const_mul (52/27:ℝ)).sub
      (((hasDerivAt_id t).pow 4).const_mul ((16/9:ℝ)*r))).add
      (((hasDerivAt_id t).pow 5).const_mul ((64/45:ℝ)*r^2)) using 1 <;> first | rfl | (norm_num; ring)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t)
    (Continuous.intervalIntegrable (by fun_prop) 0 1)]
  dsimp [P]
  ring

lemma resolventA_lower (v : Fin 3 → ℝ) (hv : avg v = 0) (hp : ∀ i, 0 < 1+v i) :
    (37/27:ℝ)*(momentX v)^2 ≤ resolventA v := by
  have hi : IntervalIntegrable (fun t : ℝ => (momentX v)^2*(t^2*(4+(64/9:ℝ)*(t*Real.sqrt (momentX v)-1/2)^2)))
      volume 0 1 := Continuous.intervalIntegrable (by fun_prop) 0 1
  have hj : IntervalIntegrable (fun t : ℝ => t^2*fourthResolvent v t) volume 0 1 :=
    ((by fun_prop : ContinuousOn (fun t : ℝ => t^2) (Set.Icc 0 1)).mul (continuousOn_fourthResolvent v hp)).intervalIntegrable_of_Icc (by norm_num)
  have hh := intervalIntegral.integral_mono_on (by norm_num : (0:ℝ) ≤ 1) hi hj (fun t ht => by
    have he := mul_le_mul_of_nonneg_left (fourthResolvent_lower v hv hp t ht.1 ht.2) (sq_nonneg t)
    nlinarith only [he])
  rw [intervalIntegral.integral_const_mul, integral_h_lower] at hh
  dsimp only [resolventA]
  nlinarith [mul_nonneg (sq_nonneg (momentX v)) (sq_nonneg (Real.sqrt (momentX v)-5/8))]

lemma resolventQ_lower (v : Fin 3 → ℝ) (hv : avg v = 0) (hp : ∀ i, 0 < 1+v i)
    (lam : ℝ) (hl0 : 0 ≤ lam) (hl1 : lam ≤ 1) : resolventA v/(2+lam) ≤ resolventQ v lam := by
  have hi : IntervalIntegrable (fun t : ℝ => 2*(t^2*fourthResolvent v t)) volume 0 1 :=
    (continuousOn_const.mul ((continuousOn_id.pow 2).mul (continuousOn_fourthResolvent v hp))).intervalIntegrable_of_Icc (by norm_num)
  have hj : IntervalIntegrable (fun t : ℝ => (2+lam)*(t^2*doubleFourthResolvent v lam t)) volume 0 1 :=
    (continuousOn_const.mul ((continuousOn_id.pow 2).mul (continuousOn_doubleFourthResolvent v hp lam hl0 hl1))).intervalIntegrable_of_Icc (by norm_num)
  have hh := intervalIntegral.integral_mono_on (by norm_num : (0:ℝ) ≤ 1) hi hj (fun t ht => by
    have he := mul_le_mul_of_nonneg_left (doubleFourthResolvent_lower v hv hp lam hl0 hl1 t ht.1 ht.2) (sq_nonneg t)
    nlinarith only [he])
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hh
  apply (div_le_iff₀ (by linarith : 0 < 2+lam)).mpr
  dsimp only [resolventQ, resolventA]
  linarith

lemma scalar_resolventA (a : ℝ) (ha : 0 < 1+a) :
    (∫ t in (0:ℝ)..1, t^2*a^4/(1+t*a)) = a^3/2-a^2+a*Real.log (1+a) := by
  have hp (t : ℝ) (ht : t ∈ Set.Icc (0:ℝ) 1) : 0 < 1+t*a := by
    rcases eq_or_lt_of_le ht.1 with hz | hz
    · rw [← hz]; norm_num
    · nlinarith [mul_pos hz ha, ht.2]
  have hc : ContinuousOn (fun t : ℝ => a/(1+t*a)) (Set.Icc 0 1) :=
    continuousOn_const.div (by fun_prop) (fun t ht => ne_of_gt (hp t ht))
  have hi : IntervalIntegrable (fun t : ℝ => a/(1+t*a)) volume 0 1 := hc.intervalIntegrable_of_Icc (by norm_num : (0:ℝ) ≤ 1)
  have he : (∫ t in (0:ℝ)..1, t^2*a^4/(1+t*a)) =
      ∫ t in (0:ℝ)..1, (a^3*t-a^2)+a*(a/(1+t*a)) := by
    apply intervalIntegral.integral_congr
    intro t ht
    have ht' : t ∈ Set.Icc (0:ℝ) 1 := by simpa using ht
    field_simp [ne_of_gt (hp t ht')]
    ring
  rw [he, intervalIntegral.integral_add (Continuous.intervalIntegrable (by fun_prop) 0 1) (hi.const_mul a),
    intervalIntegral.integral_sub (Continuous.intervalIntegrable (by fun_prop) 0 1) (intervalIntegrable_const),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, integral_id,
    intervalIntegral.integral_const, ← log_integral a ha]
  norm_num
  ring

lemma resolventA_identity (v : Fin 3 → ℝ) (hp : ∀ i, 0 < 1+v i) :
    resolventA v = 2*functionJ v-2*momentX v+momentY v := by
  have he (t : ℝ) : t^2*fourthResolvent v t = avg (fun i => t^2*(v i)^4/(1+t*v i)) := by
    simp only [fourthResolvent, avg_expand]; ring
  dsimp only [resolventA]
  simp_rw [he]
  rw [integral_avg]
  · simp_rw [scalar_resolventA _ (hp _)]
    simp only [functionJ, momentX, momentY, avg_expand]
    ring
  · intro i
    exact ((by fun_prop : ContinuousOn (fun t : ℝ => t^2*(v i)^4) (Set.Icc 0 1)).div
      (by fun_prop) (fun t ht => ne_of_gt (message_segment_pos v hp t ht.1 ht.2 i))).intervalIntegrable_of_Icc (by norm_num)

lemma resolvent_scaling (v : Fin 3 → ℝ) (hp : ∀ i, 0 < 1+v i)
    (lam : ℝ) (hl0 : 0 ≤ lam) (hl1 : lam ≤ 1) :
    lam^3*resolventA v-resolventA (fun i => lam*v i) = 2*lam^3*(1-lam)*resolventQ v lam := by
  have hpe (i : Fin 3) : 0 < 1+lam*v i := message_segment_pos v hp lam hl0 hl1 i
  have hvI : IntervalIntegrable (fun t : ℝ => t^2*fourthResolvent v t) volume 0 1 :=
    ((continuousOn_id.pow 2).mul (continuousOn_fourthResolvent v hp)).intervalIntegrable_of_Icc (by norm_num)
  have heI : IntervalIntegrable (fun t : ℝ => t^2*fourthResolvent (fun i => lam*v i) t) volume 0 1 :=
    ((continuousOn_id.pow 2).mul (continuousOn_fourthResolvent _ hpe)).intervalIntegrable_of_Icc (by norm_num)
  have he : (∫ t in (0:ℝ)..1, lam^3*(t^2*fourthResolvent v t)-t^2*fourthResolvent (fun i => lam*v i) t) =
      ∫ t in (0:ℝ)..1, (lam^3*(1-lam))*(t^2*doubleFourthResolvent v lam t) := by
    apply intervalIntegral.integral_congr
    intro t ht
    have ht' : t ∈ Set.Icc (0:ℝ) 1 := by simpa using ht
    have hi (i : Fin 3) : lam^3*((v i)^4/(1+t*v i))-(lam*v i)^4/(1+t*(lam*v i)) =
        lam^3*(1-lam)*((v i)^4/((1+t*v i)*(1+lam*t*v i))) := by
      have ha := ne_of_gt (message_segment_pos v hp t ht'.1 ht'.2 i)
      have hb := ne_of_gt (message_segment_pos _ hpe t ht'.1 ht'.2 i)
      have ha' : 1+v i*t ≠ 0 := by simpa [mul_comm] using ha
      have hb' : 1+v i*t*lam ≠ 0 := by convert hb using 1; ring
      have hb'' : 1+lam*v i*t ≠ 0 := by convert hb using 1; ring
      have hb''' : 1+lam*t*v i ≠ 0 := by convert hb using 1; ring
      field_simp [ha, hb, ha', hb', hb'', hb''']
      ring
    simp only [fourthResolvent, doubleFourthResolvent, avg_expand]
    linear_combination t^2/3*(hi 0)+t^2/3*(hi 1)+t^2/3*(hi 2)
  rw [intervalIntegral.integral_sub (hvI.const_mul _) heI,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at he
  dsimp only [resolventA, resolventQ]
  linarith only [he]

lemma momentX_scale (v : Fin 3 → ℝ) (lam : ℝ) : momentX (fun i => lam*v i) = lam^2*momentX v := by
  simp only [momentX, avg_expand]; ring

lemma momentY_scale (v : Fin 3 → ℝ) (lam : ℝ) : momentY (fun i => lam*v i) = lam^3*momentY v := by
  simp only [momentY, avg_expand]; ring

lemma resolventQ_identity (v : Fin 3 → ℝ) (hp : ∀ i, 0 < 1+v i)
    (lam : ℝ) (hl0 : 0 ≤ lam) (hl1 : lam ≤ 1) :
    lam^3*(1-lam)*resolventQ v lam = lam^3*functionJ v-functionJ (fun i => lam*v i)+lam^2*(1-lam)*momentX v := by
  have hh := resolvent_scaling v hp lam hl0 hl1
  rw [resolventA_identity v hp, resolventA_identity _ (fun i => message_segment_pos v hp lam hl0 hl1 i),
    momentX_scale, momentY_scale] at hh
  nlinarith only [hh]

end ThreeState.Radial

end OAI
