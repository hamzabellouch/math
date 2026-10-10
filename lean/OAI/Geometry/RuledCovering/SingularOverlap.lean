import OAI.Geometry.RuledCovering.SingularInverse

namespace OAI

noncomputable section

open Set MeasureTheory Filter Metric
open scoped Topology ContDiff Pointwise

namespace RuledApproximation

lemma ceiling_nonneg {p : ℝ} (hp : 0 ≤ p) (hp2 : p ≤ 2) (b : ℝ) :
    0 ≤ ceilingPolynomial p b := by
  unfold ceilingPolynomial
  have : 0 ≤ 2-p := sub_nonneg.mpr hp2
  positivity

lemma ceiling_P_identity (p x y : ℝ) :
    ceilingPolynomial p x + ceilingPolynomial p y -
      x^2*(p/4+(2-p)*y^2)-y^2*(p/4+(2-p)*x^2) = (2-p)*(x^2-y^2)^2 := by
  unfold ceilingPolynomial
  ring

lemma singular_region_estimates (p : ℝ) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ (z : Plane) (B : ℝ),
      |z 0| ≤ 2 → (1/2:ℝ) ≤ z 1 → z 1 ≤ 2 → |B| ≤ 2 →
      |singularField p z 0| ≤ K ∧
      |singularField p z 1-z 0| ≤ K*(z 1-1/2) ∧
      |singularField p z 0-(p/4+(2-p)*B^2)| ≤ K*(|z 0-B|+(z 1-1/2)) ∧
      |ceilingPolynomial p (z 0)-ceilingPolynomial p B| ≤ K*|z 0-B| := by
  let S : Set Plane := (EuclideanSpace.proj 0) ⁻¹' Icc (-2:ℝ) 2 ∩
    (EuclideanSpace.proj 1) ⁻¹' Icc (1/2:ℝ) 2
  have hSc : IsClosed S := (isClosed_Icc.preimage (by fun_prop)).inter
    (isClosed_Icc.preimage (by fun_prop))
  have hS : IsCompact S := (isCompact_closedBall (0:Plane) 4).of_isClosed_subset hSc (by
    intro z hz
    change z 0 ∈ Icc (-2:ℝ) 2 ∧ z 1 ∈ Icc (1/2:ℝ) 2 at hz
    rw [Metric.mem_closedBall,dist_zero_right]
    have ha : |z 0| ≤ 2 := abs_le.mpr hz.1
    have hb : |z 1| ≤ 2 := (abs_of_nonneg (by linarith [hz.2.1])).le.trans hz.2.2
    exact (plane_norm_le_sum z).trans (by linarith))
  have hconv : Convex ℝ S := ((convex_Icc (-2:ℝ) 2).linear_preimage (EuclideanSpace.proj 0).toLinearMap).inter
    ((convex_Icc (1/2:ℝ) 2).linear_preimage (EuclideanSpace.proj 1).toLinearMap)
  have hsmooth : ∀ z ∈ S, ContDiffAt ℝ ∞ (singularField p) z := by
    intro z hz
    apply singularField_contDiffAt
    have hz1 : (1/2:ℝ) ≤ z 1 := hz.2.1
    linarith
  obtain ⟨C₀,hC₀⟩ := hS.exists_bound_of_continuousOn
    (fun z hz => (hsmooth z hz).continuousAt.continuousWithinAt)
  obtain ⟨C₁,hC₁⟩ := hS.exists_bound_of_continuousOn
    (fun z hz => ((hsmooth z hz).continuousAt_fderiv (by norm_num)).continuousWithinAt)
  have hdelta : ContDiff ℝ ∞ (ceilingPolynomial p) := by unfold ceilingPolynomial; fun_prop
  obtain ⟨C₂,hC₂⟩ := (isCompact_Icc (a := (-2:ℝ)) (b := 2)).exists_bound_of_continuousOn
    (f := fderiv ℝ (ceilingPolynomial p))
    (fun _ _ => (hdelta.contDiffAt.continuousAt_fderiv (by norm_num)).continuousWithinAt)
  let K := max 1 (max C₀ (max C₁ C₂))
  have hK : 1 ≤ K := le_max_left _ _
  have hK₀ : C₀ ≤ K := (le_max_left _ _).trans (le_max_right _ _)
  have hK₁ : C₁ ≤ K := (le_max_left _ _).trans
    ((le_max_right _ _).trans (le_max_right _ _))
  have hK₂ : C₂ ≤ K := (le_max_right _ _).trans
    ((le_max_right _ _).trans (le_max_right _ _))
  have hKn : 0 ≤ K := by linarith
  have hlip : ∀ z ∈ S, ∀ w ∈ S, ‖singularField p z-singularField p w‖ ≤ K*‖z-w‖ := by
    intro z hz w hw
    exact Convex.norm_image_sub_le_of_norm_fderiv_le
      (fun q hq => (hsmooth q hq).differentiableAt (by norm_num))
      (fun q hq => (hC₁ q hq).trans hK₁) hconv hw hz
  have hdlip : ∀ b ∈ Icc (-2:ℝ) 2, ∀ B ∈ Icc (-2:ℝ) 2,
      |ceilingPolynomial p b-ceilingPolynomial p B| ≤ K*|b-B| := by
    intro b hb B hB
    simpa only [Real.norm_eq_abs] using Convex.norm_image_sub_le_of_norm_fderiv_le
      (f := ceilingPolynomial p) (fun _ _ => hdelta.differentiable (by norm_num) _)
      (fun q hq => (hC₂ q hq).trans hK₂) (convex_Icc _ _) hB hb
  refine ⟨K,hK,?_⟩
  intro z B hz0 hz1 hz2 hB
  have hz : z ∈ S := ⟨abs_le.mp hz0,⟨hz1,hz2⟩⟩
  have hw : vec2 (z 0) (1/2) ∈ S := ⟨abs_le.mp hz0,by norm_num [vec2]⟩
  have hwB : vec2 B (1/2) ∈ S := ⟨abs_le.mp hB,by norm_num [vec2]⟩
  refine ⟨(plane_coordinate_le _ 0).trans ((hC₀ z hz).trans hK₀),?_,?_,hdlip _ (abs_le.mp hz0) _ (abs_le.mp hB)⟩
  · have h := (plane_coordinate_le (singularField p z-singularField p (vec2 (z 0) (1/2))) 1).trans (hlip z hz _ hw)
    rw [singularField_level] at h
    change |singularField p z 1-z 0| ≤ K*‖z-vec2 (z 0) (1/2)‖ at h
    apply h.trans
    have he := plane_norm_le_sum (z-vec2 (z 0) (1/2))
    simpa only [PiLp.sub_apply,vec2_apply_zero,vec2_apply_one,sub_self,abs_zero,zero_add,
      abs_of_nonneg (sub_nonneg.mpr hz1)] using mul_le_mul_of_nonneg_left he hKn
  · have h := (plane_coordinate_le (singularField p z-singularField p (vec2 B (1/2))) 0).trans (hlip z hz _ hwB)
    rw [singularField_level] at h
    change |singularField p z 0-(p/4+(2-p)*B^2)| ≤ K*‖z-vec2 B (1/2)‖ at h
    apply h.trans
    have he := plane_norm_le_sum (z-vec2 B (1/2))
    simpa only [PiLp.sub_apply,vec2_apply_zero,vec2_apply_one,
      abs_of_nonneg (sub_nonneg.mpr hz1)] using mul_le_mul_of_nonneg_left he hKn

lemma abs_unit_mul_le {x A B : ℝ} (hx : |x| ≤ 1) (hA : |A| ≤ B) :
    |x*A| ≤ B := by
  rw [abs_mul]
  exact (mul_le_mul_of_nonneg_right hx (abs_nonneg A)).trans (by simpa using hA)

lemma singular_overlap_algebra {p K c x y bm bp rm rp Pm Pp Qm Qp : ℝ}
    (hp2 : p ≤ 2) (hK : 1 ≤ K) (hc : 0 ≤ c) (hc1 : c ≤ 1)
    (hcK : c*K ≤ 1/2) (hcsmall : 16*K^2*c^3 ≤ 2*c^(5/2:ℝ))
    (hx : |x| ≤ 1) (hy : |y| ≤ 1) (hrm : 1/2 ≤ rm) (hrp : 1/2 ≤ rp)
    (hPm : |Pm| ≤ K) (hPp : |Pp| ≤ K)
    (hQm : |Qm-bm| ≤ K*(rm-1/2)) (hQp : |Qp-bp| ≤ K*(rp-1/2))
    (hPmy : |Pm-(p/4+(2-p)*y^2)| ≤ K*(|bm-y|+(rm-1/2)))
    (hPpx : |Pp-(p/4+(2-p)*x^2)| ≤ K*(|bp-x|+(rp-1/2)))
    (hdm : |ceilingPolynomial p bm-ceilingPolynomial p y| ≤ K*|bm-y|)
    (hdp : |ceilingPolynomial p bp-ceilingPolynomial p x| ≤ K*|bp-x|)
    (hbm : bm=y-c*x*Pm) (hbp : bp=x+c*y*Pp)
    (hsum : rm+rp=1+c*(y*Qp-x*Qm)) :
    rm ≤ 1/2+c^2*ceilingPolynomial p bm+c^(5/2:ℝ) ∨
    rp ≤ 1/2+c^2*ceilingPolynomial p bp+c^(5/2:ℝ) := by
  have hKn : 0 ≤ K := by linarith
  have hxs : |x^2| ≤ 1 := by rw [abs_of_nonneg (sq_nonneg x)]; nlinarith only [(abs_le.mp hx).1,(abs_le.mp hx).2]
  have hys : |y^2| ≤ 1 := by rw [abs_of_nonneg (sq_nonneg y)]; nlinarith only [(abs_le.mp hy).1,(abs_le.mp hy).2]
  have hbm' : |bm-y| ≤ c*K := by
    rw [hbm,sub_sub_cancel_left,abs_neg,abs_mul,abs_mul,abs_of_nonneg hc]
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (by simpa only [abs_mul] using abs_unit_mul_le hx hPm) hc
  have hbp' : |bp-x| ≤ c*K := by
    rw [hbp,add_sub_cancel_left,abs_mul,abs_mul,abs_of_nonneg hc]
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (by simpa only [abs_mul] using abs_unit_mul_le hy hPp) hc
  let D := rm+rp-1
  have hD : 0 ≤ D := by dsimp [D]; linarith
  have hEd : |y*(Qp-bp)-x*(Qm-bm)| ≤ K*D := by
    calc
      _ ≤ |y*(Qp-bp)|+|x*(Qm-bm)| := abs_sub _ _
      _ ≤ K*(rp-1/2)+K*(rm-1/2) := add_le_add (abs_unit_mul_le hy hQp) (abs_unit_mul_le hx hQm)
      _ = _ := by dsimp [D]; ring
  have hPe : |y^2*Pp+x^2*Pm| ≤ 2*K := by
    calc
      _ ≤ |y^2*Pp|+|x^2*Pm| := abs_add_le _ _
      _ ≤ K+K := add_le_add (abs_unit_mul_le hys hPp) (abs_unit_mul_le hxs hPm)
      _ = _ := by ring
  have hDeq : D=c^2*(y^2*Pp+x^2*Pm)+c*(y*(Qp-bp)-x*(Qm-bm)) := by
    dsimp [D]
    rw [hsum,hbm,hbp]
    ring
  have hDb : D ≤ 4*K*c^2 := by
    have hu : D ≤ c^2*(2*K)+c*(K*D) := by
      calc
        D = c^2*(y^2*Pp+x^2*Pm)+c*(y*(Qp-bp)-x*(Qm-bm)) := hDeq
        _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left (le_trans (le_abs_self _) hPe) (sq_nonneg c))
          (mul_le_mul_of_nonneg_left (le_trans (le_abs_self _) hEd) hc)
    have hmul := mul_le_mul_of_nonneg_right hcK hD
    nlinarith only [hmul,hu]
  have hrmb : rm-1/2 ≤ 4*K*c^2 := by dsimp [D] at hDb; linarith
  have hrpb : rp-1/2 ≤ 4*K*c^2 := by dsimp [D] at hDb; linarith
  have hc2 : c^2 ≤ c := by nlinarith only [hc,hc1]
  have hPmy' : |Pm-(p/4+(2-p)*y^2)| ≤ 5*K^2*c := by
    apply hPmy.trans
    calc
      _ ≤ K*(c*K+4*K*c^2) := mul_le_mul_of_nonneg_left (add_le_add hbm' hrmb) hKn
      _ ≤ K*(c*K+4*K*c) := mul_le_mul_of_nonneg_left (add_le_add le_rfl (mul_le_mul_of_nonneg_left hc2 (by positivity : 0 ≤ 4*K))) hKn
      _ = _ := by ring
  have hPpx' : |Pp-(p/4+(2-p)*x^2)| ≤ 5*K^2*c := by
    apply hPpx.trans
    calc
      _ ≤ K*(c*K+4*K*c^2) := mul_le_mul_of_nonneg_left (add_le_add hbp' hrpb) hKn
      _ ≤ K*(c*K+4*K*c) := mul_le_mul_of_nonneg_left (add_le_add le_rfl (mul_le_mul_of_nonneg_left hc2 (by positivity : 0 ≤ 4*K))) hKn
      _ = _ := by ring
  let A := x^2*(p/4+(2-p)*y^2)+y^2*(p/4+(2-p)*x^2)
  have hAe : |y^2*Pp+x^2*Pm-A| ≤ 10*K^2*c := by
    calc
      _ = |y^2*(Pp-(p/4+(2-p)*x^2))+x^2*(Pm-(p/4+(2-p)*y^2))| := by dsimp [A]; congr 1; ring
      _ ≤ |y^2*(Pp-(p/4+(2-p)*x^2))|+|x^2*(Pm-(p/4+(2-p)*y^2))| := abs_add_le _ _
      _ ≤ 5*K^2*c+5*K^2*c := add_le_add (abs_unit_mul_le hys hPpx') (abs_unit_mul_le hxs hPmy')
      _ = _ := by ring
  have hDelta : D ≤ c^2*A+14*K^2*c^3 := by
    have hh : D-c^2*A ≤ c^2*(10*K^2*c)+c*(K*(4*K*c^2)) := by
      calc
        _ = c^2*(y^2*Pp+x^2*Pm-A)+c*(y*(Qp-bp)-x*(Qm-bm)) := by rw [hDeq]; ring
        _ ≤ c^2*(10*K^2*c)+c*(K*D) := add_le_add
          (mul_le_mul_of_nonneg_left ((le_abs_self _).trans hAe) (sq_nonneg c))
          (mul_le_mul_of_nonneg_left ((le_abs_self _).trans hEd) hc)
        _ ≤ _ := add_le_add le_rfl (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hDb hKn) hc)
    nlinarith only [hh]
  have hdm' : ceilingPolynomial p y-K^2*c ≤ ceilingPolynomial p bm := by
    have hh := hdm.trans (mul_le_mul_of_nonneg_left hbm' hKn)
    have hh' := (abs_le.mp hh).1
    nlinarith only [hh']
  have hdp' : ceilingPolynomial p x-K^2*c ≤ ceilingPolynomial p bp := by
    have hh := hdp.trans (mul_le_mul_of_nonneg_left hbp' hKn)
    have hh' := (abs_le.mp hh).1
    nlinarith only [hh']
  have hAid : A ≤ ceilingPolynomial p y+ceilingPolynomial p x := by
    have hh := ceiling_P_identity p x y
    have hz : 0 ≤ (2-p)*(x^2-y^2)^2 := mul_nonneg (by linarith) (sq_nonneg _)
    dsimp [A]
    linarith
  by_contra h
  push Not at h
  have hfail : c^2*(ceilingPolynomial p bm+ceilingPolynomial p bp)+2*c^(5/2:ℝ) < D := by
    dsimp [D]
    linarith [h.1,h.2]
  have hdlow : A-2*K^2*c ≤ ceilingPolynomial p bm+ceilingPolynomial p bp := by linarith
  have hh := mul_le_mul_of_nonneg_left hdlow (sq_nonneg c)
  nlinarith only [hh,hfail,hDelta,hcsmall]

lemma singular_overlap_small {p : ℝ} (hp : 0 ≤ p) (hp2 : p ≤ 2) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ (c x y : ℝ) (zm zp : Plane),
      0 ≤ c → c ≤ 1 → c*K ≤ 1/2 → 16*K^2*c^3 ≤ 2*c^(5/2:ℝ) →
      |x| ≤ 1 → |y| ≤ 1 → zm 1 ≤ 2 → zp 1 ≤ 2 →
      |zm 0| ≤ zm 1 → |zp 0| ≤ zp 1 →
      zm 0=y-c*x*singularField p zm 0 → zp 0=x+c*y*singularField p zp 0 →
      zm 1+zp 1=1+c*(y*singularField p zp 1-x*singularField p zm 1) →
      zm 1 ≤ 1/2+c^2*ceilingPolynomial p (zm 0)+c^(5/2:ℝ) ∨
      zp 1 ≤ 1/2+c^2*ceilingPolynomial p (zp 0)+c^(5/2:ℝ) := by
  obtain ⟨K,hK,he⟩ := singular_region_estimates p
  refine ⟨K,hK,?_⟩
  intro c x y zm zp hc hc1 hcK hsmall hx hy hzm hzp hbzm hbzp hezm hezp hesum
  by_cases hm : zm 1 ≤ 1/2+c^2*ceilingPolynomial p (zm 0)+c^(5/2:ℝ)
  · exact Or.inl hm
  by_cases hp' : zp 1 ≤ 1/2+c^2*ceilingPolynomial p (zp 0)+c^(5/2:ℝ)
  · exact Or.inr hp'
  have hrm : 1/2 ≤ zm 1 := by
    have hn := ceiling_nonneg hp hp2 (zm 0)
    have hn' : 0 ≤ c^2*ceilingPolynomial p (zm 0)+c^(5/2:ℝ) := by positivity
    linarith
  have hrp : 1/2 ≤ zp 1 := by
    have hn := ceiling_nonneg hp hp2 (zp 0)
    have hn' : 0 ≤ c^2*ceilingPolynomial p (zp 0)+c^(5/2:ℝ) := by positivity
    linarith
  obtain ⟨hPm,hQm,hPmy,hdm⟩ := he zm y (hbzm.trans hzm) hrm hzm (hy.trans (by norm_num))
  obtain ⟨hPp,hQp,hPpx,hdp⟩ := he zp x (hbzp.trans hzp) hrp hzp (hx.trans (by norm_num))
  exact singular_overlap_algebra hp2 hK hc hc1 hcK hsmall hx hy hrm hrp
    hPm hPp hQm hQp hPmy hPpx hdm hdp hezm hezp hesum

lemma right_rpow_tendsto_zero {q : ℝ} (hq : 0 < q) :
    Tendsto (fun c : ℝ => c^q) (𝓝[>] 0) (𝓝 0) := by
  have h : Tendsto (fun c : ℝ => c^q) (𝓝[>] 0) (𝓝 ((0:ℝ)^q)) :=
    ((Real.continuous_rpow_const hq.le).tendsto (0:ℝ)).mono_left nhdsWithin_le_nhds
  simpa only [Real.zero_rpow hq.ne'] using h

lemma overlap_error_eventually (K : ℝ) :
    ∀ᶠ c : ℝ in 𝓝[>] 0, 16*K^2*c^3 ≤ 2*c^(5/2:ℝ) := by
  have h : Tendsto (fun c : ℝ => 16*K^2*c^(1/2:ℝ)) (𝓝[>] 0) (𝓝 0) := by
    simpa using (right_rpow_tendsto_zero (q := (1/2:ℝ)) (by norm_num)).const_mul (16*K^2)
  filter_upwards [self_mem_nhdsWithin,h.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<2))] with c hc hb
  have hc : 0 < c := hc
  have he : c^3=c^(1/2:ℝ)*c^(5/2:ℝ) := by
    rw [← Real.rpow_add hc]
    norm_num
  rw [he]
  nlinarith only [mul_le_mul_of_nonneg_right hb.le (Real.rpow_nonneg hc.le (5/2:ℝ))]

end RuledApproximation

end

end OAI
