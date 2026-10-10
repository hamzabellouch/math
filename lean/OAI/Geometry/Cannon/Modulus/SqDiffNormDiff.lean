import Mathlib

namespace OAI

section
noncomputable section
noncomputable section
noncomputable section
namespace CannonRadialWitness
open Set Metric

lemma sq_diff_le_of_norm_diff {u v η : ℝ} (hu : 0≤u) (hv : 0≤v)
    (hlo : -η≤u-v) (hhi : u-v≤η) (hs : u+v≤3) :
    -3*η≤u^2-v^2 ∧ u^2-v^2≤3*η := by
  have he : 0≤η:=by linarith
  have hsum : 0≤u+v:=by linarith
  constructor
  · nlinarith [mul_nonneg (show 0≤u-v+η by linarith) hsum,
      mul_nonneg he (show 0≤3-(u+v) by linarith)]
  · nlinarith [mul_nonneg (show 0≤η-(u-v) by linarith) hsum,
      mul_nonneg he (show 0≤3-(u+v) by linarith)]

lemma norm_one_sq (z : ℂ) : ‖z-1‖^2=‖z‖^2-2*z.re+1 := by
  simp only [←Complex.normSq_eq_norm_sq,Complex.normSq_apply,Complex.sub_re,
    Complex.sub_im,Complex.one_re,Complex.one_im,sub_zero]
  ring

theorem two_center_small {E : Set ℂ} (hE : IsPreconnected E) {x y : ℂ}
    (hx : x∈E) (hy : y∈E) (hxn : ‖x‖≤1) {η : ℝ} (hη : 0≤η) (hη1 : η≤1)
    (h0 : ∀ z∈E,|‖z‖-‖x‖|≤η)
    (h1 : ∀ z∈E,|‖z-1‖-‖x-1‖|≤η) :
    dist x y^2≤102*η := by
  have hn (z : ℂ) (hz : z∈E) : ‖z‖≤2 := by
    have hh:=(abs_le.mp (h0 z hz)).2
    linarith
  have hns (z : ℂ) (hz : z∈E) :
      -3*η≤‖z‖^2-‖x‖^2 ∧ ‖z‖^2-‖x‖^2≤3*η :=
    sq_diff_le_of_norm_diff (norm_nonneg _) (norm_nonneg _)
      (abs_le.mp (h0 z hz)).1 (abs_le.mp (h0 z hz)).2 (by linarith [hn z hz])
  have hn1x : ‖x-1‖≤2 := by
    have ht:=norm_sub_le x (1:ℂ)
    norm_num at ht
    linarith
  have hn1 (z : ℂ) (hz : z∈E) : ‖z-1‖≤3 := by
    have ht:=norm_sub_le z (1:ℂ)
    norm_num at ht
    linarith [hn z hz]
  have hns1 (z : ℂ) (hz : z∈E) :
      -5*η≤‖z-1‖^2-‖x-1‖^2 ∧ ‖z-1‖^2-‖x-1‖^2≤5*η := by
    have hd:=abs_le.mp (h1 z hz)
    have hs : ‖z-1‖+‖x-1‖≤5:=by linarith [hn1 z hz]
    have hsum : 0≤‖z-1‖+‖x-1‖:=by positivity
    constructor
    · nlinarith [mul_nonneg (show 0≤‖z-1‖-‖x-1‖+η by linarith) hsum,
        mul_nonneg hη (show 0≤5-(‖z-1‖+‖x-1‖) by linarith)]
    · nlinarith [mul_nonneg (show 0≤η-(‖z-1‖-‖x-1‖) by linarith) hsum,
        mul_nonneg hη (show 0≤5-(‖z-1‖+‖x-1‖) by linarith)]
  have hre (z : ℂ) (hz : z∈E) : -(4*η)≤z.re-x.re ∧ z.re-x.re≤4*η := by
    have hh:=hns z hz
    have hh1:=hns1 z hz
    rw [norm_one_sq z,norm_one_sq x] at hh1
    constructor <;> linarith
  have hres (z : ℂ) (hz : z∈E) : -3≤z.re+x.re ∧ z.re+x.re≤3 := by
    have hz':=abs_le.mp (Complex.abs_re_le_norm z)
    have hx':=abs_le.mp (Complex.abs_re_le_norm x)
    constructor <;> linarith [hn z hz]
  have hre2 (z : ℂ) (hz : z∈E) : -12*η≤z.re^2-x.re^2 ∧ z.re^2-x.re^2≤12*η := by
    have habs : |z.re^2-x.re^2|≤12*η := by
      calc
        _ = |z.re-x.re| * |z.re+x.re| := by rw [←abs_mul]; congr 1; ring
        _ ≤ (4*η)*3 := mul_le_mul (abs_le.mpr (hre z hz))
          (abs_le.mpr (hres z hz)) (abs_nonneg _) (by positivity)
        _ = _ := by ring
    constructor <;> linarith [abs_le.mp habs]
  have him2 (z : ℂ) (hz : z∈E) : -15*η≤z.im^2-x.im^2 ∧ z.im^2-x.im^2≤15*η := by
    have hh:=hns z hz
    have hh':=hre2 z hz
    rw [←Complex.normSq_eq_norm_sq,←Complex.normSq_eq_norm_sq] at hh
    simp only [Complex.normSq_apply] at hh
    constructor <;> nlinarith
  have hw : ∃ w∈E,w.im=(x.im+y.im)/2 := by
    rcases le_total x.im y.im with hxy|hyx
    · exact hE.intermediate_value hx hy Complex.continuous_im.continuousOn
        (show (x.im+y.im)/2∈Icc x.im y.im by constructor <;> linarith)
    · exact hE.intermediate_value hy hx Complex.continuous_im.continuousOn
        (show (x.im+y.im)/2∈Icc y.im x.im by constructor <;> linarith)
  obtain ⟨w,hw,hwim⟩:=hw
  have himdiff : (x.im-y.im)^2≤90*η := by
    have hhy:=him2 y hy
    have hhw:=him2 w hw
    rw [hwim] at hhw
    nlinarith
  have hrediff : (x.re-y.re)^2≤12*η := by
    have hr:=hre y hy
    have hxre:=abs_le.mp (Complex.abs_re_le_norm x)
    have hyre:=abs_le.mp (Complex.abs_re_le_norm y)
    have hb : |y.re-x.re|≤3:=abs_le.mpr (by constructor <;> linarith [hn y hy])
    have hm:=mul_le_mul (abs_le.mpr hr) hb (abs_nonneg (y.re-x.re)) (by positivity : 0≤4*η)
    rw [←sq, sq_abs] at hm
    nlinarith
  rw [dist_eq_norm,←Complex.normSq_eq_norm_sq]
  simp only [Complex.normSq_apply,Complex.sub_re,Complex.sub_im]
  nlinarith

theorem two_center_band {E : Set ℂ} (hE : IsPreconnected E) {x y : ℂ}
    (hx : x∈E) (hy : y∈E) (hxn : ‖x‖≤1) {η : ℝ} (hη : 0≤η) (hη1 : η≤1)
    (hxy : 102*η<dist x y^2) :
    ∃ c : ℂ,(c=0 ∨ c=1) ∧ ∃ a b : ℝ,0≤a ∧ a≤b ∧ b≤3 ∧ b-a=η ∧
      ∃ u∈E,∃ v∈E,dist u c≤a ∧ b≤dist v c := by
  have hn : ¬((∀ z∈E,|‖z‖-‖x‖|≤η) ∧ (∀ z∈E,|‖z-1‖-‖x-1‖|≤η)) := by
    intro h
    exact (not_lt_of_ge (two_center_small hE hx hy hxn hη hη1 h.1 h.2)) hxy
  have hw : ∃ c : ℂ,(c=0 ∨ c=1) ∧ dist x c≤2 ∧ ∃ z∈E,η < |dist z c-dist x c| := by
    push Not at hn
    by_cases h0 : ∀ z∈E,|‖z‖-‖x‖|≤η
    · obtain ⟨z,hz,hh⟩:=hn h0
      refine ⟨1,Or.inr rfl,?_,z,hz,?_⟩
      · have hh:=norm_sub_le x (1:ℂ)
        norm_num at hh
        rw [dist_eq_norm]
        linarith
      · simpa only [dist_eq_norm] using hh
    · push Not at h0
      obtain ⟨z,hz,hh⟩:=h0
      exact ⟨0,Or.inl rfl,by simpa only [dist_zero_right] using hxn.trans (by norm_num),
        z,hz,by simpa only [dist_zero_right] using hh⟩
  obtain ⟨c,hc,hxc,z,hz,hh⟩:=hw
  refine ⟨c,hc,?_⟩
  rcases lt_abs.mp hh with hp|hm
  · exact ⟨dist x c,dist x c+η,dist_nonneg,by linarith,by linarith,by ring,
      x,hx,z,hz,le_rfl,by linarith⟩
  · exact ⟨dist x c-η,dist x c,by linarith [dist_nonneg (x:=z) (y:=c)],
      by linarith,by linarith,by ring,z,hz,x,hx,by linarith,le_rfl⟩

lemma normalized_dist (p q u v : ℂ) {R : ℝ} (hpq : dist p q=R) :
    dist ((u-p)/(q-p)) ((v-p)/(q-p))=dist u v/R := by
  rw [dist_eq_norm,←sub_div]
  have he : (u-p)-(v-p)=u-v:=by ring
  rw [he,norm_div,←dist_eq_norm,←dist_eq_norm,dist_comm q p,hpq]

theorem two_center_band_scaled {E : Set ℂ} (hE : IsPreconnected E) {x y p q : ℂ}
    (hx : x∈E) (hy : y∈E) {R η : ℝ} (hR : 0<R) (hpq : dist p q=R)
    (hxp : dist x p≤R) (hη : 0≤η) (hη1 : η≤1)
    (hxy : 102*η*R^2<dist x y^2) :
    ∃ c : ℂ,(c=p ∨ c=q) ∧ ∃ a b : ℝ,0≤a ∧ a≤b ∧ b≤3*R ∧ b-a=η*R ∧
      ∃ u∈E,∃ v∈E,dist u c≤a ∧ b≤dist v c := by
  let f : ℂ → ℂ:=fun z=>(z-p)/(q-p)
  have hf : Continuous f:=(continuous_id.sub continuous_const).div_const _
  have hfp : f p=0:=by simp [f]
  have hpq0 : q-p≠0:=by
    intro h
    have hh : q=p:=sub_eq_zero.mp h
    simp [hh] at hpq
    linarith
  have hfq : f q=1:=by simp [f,hpq0]
  have hfd (u v : ℂ) : dist (f u) (f v)=dist u v/R:=normalized_dist p q u v hpq
  have hxn : ‖f x‖≤1:=by
    rw [←dist_zero_right,←hfp,hfd]
    exact (div_le_one hR).mpr hxp
  have hxy' : 102*η<dist (f x) (f y)^2 := by
    rw [hfd,div_pow]
    exact (lt_div_iff₀ (sq_pos_of_pos hR)).mpr hxy
  obtain ⟨c,hc,a,b,ha,hab,hb,hw,u,⟨u',hu,rfl⟩,v,⟨v',hv,rfl⟩,huc,hvc⟩:=
    two_center_band (hE.image f hf.continuousOn) (mem_image_of_mem f hx)
      (mem_image_of_mem f hy) hxn hη hη1 hxy'
  have hband (c' : ℂ) (he : f c'=c) :
      ∃ a b : ℝ,0≤a ∧ a≤b ∧ b≤3*R ∧ b-a=η*R ∧
        ∃ u∈E,∃ v∈E,dist u c'≤a ∧ b≤dist v c' := by
    refine ⟨a*R,b*R,mul_nonneg ha hR.le,mul_le_mul_of_nonneg_right hab hR.le,
      mul_le_mul_of_nonneg_right hb hR.le,?_,u',hu,v',hv,?_,?_⟩
    · rw [←sub_mul,hw]
    · rw [←he,hfd] at huc
      exact (div_le_iff₀ hR).mp huc
    · rw [←he,hfd] at hvc
      exact (le_div_iff₀ hR).mp hvc
  rcases hc with rfl|rfl
  · exact ⟨p,Or.inl rfl,hband p hfp⟩
  · exact ⟨q,Or.inr rfl,hband q hfq⟩

end CannonRadialWitness

end
end
end
end

end OAI
