import OAI.Geometry.RuledCovering.Main
import OAI.Geometry.CylinderCovering.Singular.Cutoff
import OAI.Geometry.CylinderCovering.Singular.BasicDefinitions

namespace OAI

noncomputable section
open Set MeasureTheory Filter Topology Metric
open scoped ContDiff
namespace CylinderCovering.FlexibleSingular
open RuledApproximation

lemma labelDomain_isCompact (p c d q : ℝ) : IsCompact (labelDomain p c d q) := by
  have hb : Continuous (fun z : Plane => z 0) := by fun_prop
  have hr : Continuous (fun z : Plane => z 1) := by fun_prop
  have hcap : Continuous (fun z : Plane => (1/2:ℝ)+c^2*ceilingPolynomial p (z 0)+q) := by
    unfold ceilingPolynomial
    fun_prop
  have hclosed : IsClosed (labelDomain p c d q) :=
    (isClosed_le continuous_const hr).inter ((isClosed_le hr continuous_const).inter
      ((isClosed_le hb.abs hr).inter (isClosed_le hr hcap)))
  apply (isCompact_closedBall (0 : Plane) 4).of_isClosed_subset hclosed
  intro z hz
  have hz0 : |z 0| ≤ 2 := hz.2.2.1.trans hz.2.1
  have hz1 : |z 1| ≤ 2 := (abs_of_nonneg ((abs_nonneg _).trans hz.2.2.1)).le.trans hz.2.1
  rw [Metric.mem_closedBall,dist_zero_right]
  exact (plane_norm_le_sum z).trans (by linarith)

lemma labelDomain_smoothNear (p c q : ℝ) {d : ℝ} (hd : 0 < d) :
    SmoothNear ∞ (labelDomain p c d q) (singularField p) := by
  refine ⟨{z | 0 < z 1},isOpen_lt continuous_const (by fun_prop),?_,singularField_contDiffOn p⟩
  intro z hz
  exact hd.trans_le hz.1

lemma overlap_algebra {p K c q x y bm bp rm rp Pm Pp Qm Qp : ℝ}
    (hp2 : p ≤ 2) (hK : 1 ≤ K) (hc : 0 ≤ c) (hc1 : c ≤ 1)
    (hcK : c*K ≤ 1/2) (hcsmall : 16*K^2*c^3 ≤ 2*q)
    (hx : |x| ≤ 1) (hy : |y| ≤ 1) (hrm : 1/2 ≤ rm) (hrp : 1/2 ≤ rp)
    (hPm : |Pm| ≤ K) (hPp : |Pp| ≤ K)
    (hQm : |Qm-bm| ≤ K*(rm-1/2)) (hQp : |Qp-bp| ≤ K*(rp-1/2))
    (hPmy : |Pm-(p/4+(2-p)*y^2)| ≤ K*(|bm-y|+(rm-1/2)))
    (hPpx : |Pp-(p/4+(2-p)*x^2)| ≤ K*(|bp-x|+(rp-1/2)))
    (hdm : |ceilingPolynomial p bm-ceilingPolynomial p y| ≤ K*|bm-y|)
    (hdp : |ceilingPolynomial p bp-ceilingPolynomial p x| ≤ K*|bp-x|)
    (hbm : bm=y-c*x*Pm) (hbp : bp=x+c*y*Pp)
    (hsum : rm+rp=1+c*(y*Qp-x*Qm)) :
    rm ≤ 1/2+c^2*ceilingPolynomial p bm+q ∨
    rp ≤ 1/2+c^2*ceilingPolynomial p bp+q := by
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
  have hfail : c^2*(ceilingPolynomial p bm+ceilingPolynomial p bp)+2*q < D := by
    dsimp [D]
    linarith [h.1,h.2]
  have hdlow : A-2*K^2*c ≤ ceilingPolynomial p bm+ceilingPolynomial p bp := by linarith
  have hh := mul_le_mul_of_nonneg_left hdlow (sq_nonneg c)
  nlinarith only [hh,hfail,hDelta,hcsmall]

lemma overlap_small {p : ℝ} (hp : 0 ≤ p) (hp2 : p ≤ 2) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ (c q x y : ℝ) (zm zp : Plane),
      0 ≤ c → 0 ≤ q → c ≤ 1 → c*K ≤ 1/2 → 16*K^2*c^3 ≤ 2*q →
      |x| ≤ 1 → |y| ≤ 1 → zm 1 ≤ 2 → zp 1 ≤ 2 →
      |zm 0| ≤ zm 1 → |zp 0| ≤ zp 1 →
      zm 0=y-c*x*singularField p zm 0 → zp 0=x+c*y*singularField p zp 0 →
      zm 1+zp 1=1+c*(y*singularField p zp 1-x*singularField p zm 1) →
      zm 1 ≤ 1/2+c^2*ceilingPolynomial p (zm 0)+q ∨
      zp 1 ≤ 1/2+c^2*ceilingPolynomial p (zp 0)+q := by
  obtain ⟨K,hK,he⟩ := singular_region_estimates p
  refine ⟨K,hK,?_⟩
  intro c q x y zm zp hc hq hc1 hcK hsmall hx hy hzm hzp hbzm hbzp hezm hezp hesum
  by_cases hm : zm 1 ≤ 1/2+c^2*ceilingPolynomial p (zm 0)+q
  · exact Or.inl hm
  by_cases hp' : zp 1 ≤ 1/2+c^2*ceilingPolynomial p (zp 0)+q
  · exact Or.inr hp'
  have hrm : 1/2 ≤ zm 1 := by
    have hn := ceiling_nonneg hp hp2 (zm 0)
    have hn' : 0 ≤ c^2*ceilingPolynomial p (zm 0)+q := by positivity
    linarith
  have hrp : 1/2 ≤ zp 1 := by
    have hn := ceiling_nonneg hp hp2 (zp 0)
    have hn' : 0 ≤ c^2*ceilingPolynomial p (zp 0)+q := by positivity
    linarith
  obtain ⟨hPm,hQm,hPmy,hdm⟩ := he zm y (hbzm.trans hzm) hrm hzm (hy.trans (by norm_num))
  obtain ⟨hPp,hQp,hPpx,hdp⟩ := he zp x (hbzp.trans hzp) hrp hzp (hx.trans (by norm_num))
  exact overlap_algebra hp2 hK hc hc1 hcK hsmall hx hy hrm hrp
    hPm hPp hQm hQp hPmy hPpx hdm hdp hezm hezp hesum

theorem geometric_cover {p : ℝ} {ρ q : ℝ → ℝ} (hp : 1 < p) (hp2 : p < 2)
    (hadm : SingularCutoff.Admissible p ρ q) :
    ∀ᶠ c : ℝ in 𝓝[>] 0,
      tetrahedron ⊆ lowerFamily p c (ρ c) (q c) ∪ upperFamily p c (ρ c) (q c) ∪
        lowerTip (ρ c) ∪ upperTip (ρ c) := by
  obtain ⟨C,_,hinv⟩ := singular_inverse_small hp2
  obtain ⟨K,_,hover⟩ := overlap_small (by linarith : 0 ≤ p) hp2.le
  have h0 : Tendsto (fun c : ℝ => c) (𝓝[>] 0) (𝓝 0) := tendsto_id.mono_left nhdsWithin_le_nhds
  have hcut : Tendsto (fun c : ℝ => c*C*(ρ c)^(p-2)) (𝓝[>] 0) (𝓝 0) := by
    simpa only [mul_assoc,mul_left_comm,mul_zero] using (hadm.2.2.1).const_mul C
  have hKlim : Tendsto (fun c : ℝ => c*K) (𝓝[>] 0) (𝓝 0) := by simpa using h0.mul_const K
  filter_upwards [self_mem_nhdsWithin,h0.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1)),
    hcut.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1/8)),
    hKlim.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1/2)),SingularCutoff.overlap_error_eventually hadm K, hadm.1]
    with c hc hc1 hcut hcK herr hpos
  have hc : 0 < c := hc
  intro z hz
  obtain ⟨t,ht0,ht1,hx,hy,hz2⟩ := hz
  by_cases htip : t ≤ 2*ρ c
  · exact Or.inl (Or.inr ⟨t,ht0,htip,hy,hz2⟩)
  by_cases htip' : 1-t ≤ 2*ρ c
  · exact Or.inr ⟨1-t,by linarith,htip',hx,by rw [hz2]; congr 1; ring⟩
  have hx1 : |z 0| ≤ 1 := hx.trans (by linarith)
  have hy1 : |z 1| ≤ 1 := hy.trans ht1
  have hkx : |c*z 0| ≤ c := by simpa only [abs_mul,abs_of_pos hc,mul_one] using mul_le_mul_of_nonneg_left hx1 hc.le
  have hky : |-c*z 1| ≤ c := by simpa only [abs_mul,abs_neg,abs_of_pos hc,mul_one] using mul_le_mul_of_nonneg_left hy1 hc.le
  obtain ⟨zm,hm0,hm2,hmb,hem⟩ := hinv (ρ c) c (z 1) t (c*z 0)
    hpos.1 hc.le hcut.le (by linarith) ht1 hy hkx
  obtain ⟨zp,hp0,hp2',hpb,hep⟩ := hinv (ρ c) c (z 0) (1-t) (-c*z 1)
    hpos.1 hc.le hcut.le (by linarith) (by linarith) hx hky
  have hem0 := congrArg (fun w : Plane => w 0) hem
  have hem1 := congrArg (fun w : Plane => w 1) hem
  have hep0 := congrArg (fun w : Plane => w 0) hep
  have hep1 := congrArg (fun w : Plane => w 1) hep
  change z 1 = zm 0+(c*z 0)*singularField p zm 0 at hem0
  change t = zm 1+(c*z 0)*singularField p zm 1 at hem1
  change z 0 = zp 0+(-c*z 1)*singularField p zp 0 at hep0
  change 1-t = zp 1+(-c*z 1)*singularField p zp 1 at hep1
  have hceil := hover c (q c) (z 0) (z 1) zm zp hc.le hpos.2.le hc1.le hcK.le herr hx1 hy1 hm2 hp2' hmb hpb
    (by linarith only [hem0]) (by linarith only [hep0]) (by nlinarith only [hem1,hep1])
  rcases hceil with hm | hp'
  · apply Or.inl ∘ Or.inl ∘ Or.inl
    refine ⟨zm,⟨hm0,hm2,hmb,hm⟩,z 0,hx1,?_⟩
    ext i
    fin_cases i
    · rfl
    · change z 1 = zm 0+z 0*(c*singularField p zm 0)
      nlinarith only [hem0]
    · change z 2 = Real.sqrt 2*(zm 1+z 0*(c*singularField p zm 1))
      rw [hz2]
      congr 1
      nlinarith only [hem1]
  · apply Or.inl ∘ Or.inl ∘ Or.inr
    refine ⟨zp,⟨hp0,hp2',hpb,hp'⟩,z 1,hy1,?_⟩
    ext i
    fin_cases i
    · change z 0 = zp 0-c*z 1*singularField p zp 0
      nlinarith only [hep0]
    · rfl
    · change z 2 = Real.sqrt 2*(1-(zp 1-c*z 1*singularField p zp 1))
      rw [hz2]
      congr 1
      nlinarith only [hep1]

end CylinderCovering.FlexibleSingular

end

end OAI
