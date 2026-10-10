import Mathlib
import OAI.Probability.JammingConcavity.GaussianStepSlope

namespace OAI

/-! Gaussian Step Right. -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
open Set Filter
open scoped Topology
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory Filter Set
open scoped ENNReal NNReal BigOperators
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
open scoped NNReal ENNReal Topology
open scoped NNReal Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology

namespace MicroscopicJamming

 

def gaussianStepRightCoefficient : List (ℝ × ℝ) → ℝ → ℝ
  | [], _ => 0
  | (a,T)::rs,t => if t < T then a else gaussianStepRightCoefficient rs (t-T)

lemma gaussianStepRightCoefficient_bounds {rs : List (ℝ × ℝ)}
    (hrs : ∀ r ∈ rs, 0 ≤ r.1 ∧ r.1 ≤ 1 ∧ 0 ≤ r.2) (t : ℝ) :
    0 ≤ gaussianStepRightCoefficient rs t ∧ gaussianStepRightCoefficient rs t ≤ 1 := by
  induction rs generalizing t with
  | nil => simp [gaussianStepRightCoefficient]
  | cons r rs ih =>
    have hr := hrs r (by simp)
    have htail : ∀ v ∈ rs, 0 ≤ v.1 ∧ v.1 ≤ 1 ∧ 0 ≤ v.2 := fun v hv => hrs v (by simp [hv])
    by_cases h : t < r.2
    · simpa [gaussianStepRightCoefficient,h] using And.intro hr.1 hr.2.1
    · simpa [gaussianStepRightCoefficient,h] using ih htail (t-r.2)

lemma gaussianStepRightCoefficient_trace (rs : List (ℝ × ℝ)) (t : ℝ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ s ∈ Ioo t (t+ε),
      gaussianStepCoefficient rs s=gaussianStepRightCoefficient rs t := by
  induction rs generalizing t with
  | nil => exact ⟨1,by norm_num,fun _ _ => rfl⟩
  | cons r rs ih =>
    by_cases h : t < r.2
    · refine ⟨r.2-t,sub_pos.mpr h,?_⟩
      intro s hs
      have hsT : s ≤ r.2 := by linarith [hs.2]
      simp [gaussianStepCoefficient,gaussianStepRightCoefficient,h,hsT]
    · obtain ⟨ε,hε,he⟩ := ih (t-r.2)
      refine ⟨ε,hε,?_⟩
      intro s hs
      have hsT : ¬s ≤ r.2 := by linarith [hs.1,le_of_not_gt h]
      have hs' : s-r.2 ∈ Ioo (t-r.2) (t-r.2+ε) := by
        constructor <;> linarith [hs.1,hs.2]
      simpa [gaussianStepCoefficient,gaussianStepRightCoefficient,h,hsT] using he (s-r.2) hs'

lemma gaussianStepRightCoefficient_close {rs ss : List (ℝ × ℝ)} {Q δ : ℝ}
    (hδ : ∀ t ∈ Icc 0 Q, |gaussianStepCoefficient rs t-gaussianStepCoefficient ss t| ≤ δ)
    {t : ℝ} (ht : t ∈ Ico 0 Q) :
    |gaussianStepRightCoefficient rs t-gaussianStepRightCoefficient ss t| ≤ δ := by
  obtain ⟨r,hr,hrtrace⟩ := gaussianStepRightCoefficient_trace rs t
  obtain ⟨s,hs,hstrace⟩ := gaussianStepRightCoefficient_trace ss t
  let ε := min r (min s (Q-t))
  have hε : 0 < ε := lt_min hr (lt_min hs (sub_pos.mpr ht.2))
  have hεr : ε ≤ r := min_le_left _ _
  have hεs : ε ≤ s := (min_le_right _ _).trans (min_le_left _ _)
  have hεQ : ε ≤ Q-t := (min_le_right _ _).trans (min_le_right _ _)
  have hr' : t+ε/2 ∈ Ioo t (t+r) := by constructor <;> linarith
  have hs' : t+ε/2 ∈ Ioo t (t+s) := by constructor <;> linarith
  have ht' : t+ε/2 ∈ Icc 0 Q := by constructor <;> linarith [ht.1]
  have hh := hδ (t+ε/2) ht'
  rwa [hrtrace _ hr',hstrace _ hs'] at hh

lemma gaussianStepPath_cons_ge (r : ℝ × ℝ) (rs : List (ℝ × ℝ))
    (hrs : ∀ v ∈ rs, 0 ≤ v.2) (u : ℝ → ℝ) {t : ℝ} (ht : r.2 ≤ t) :
    gaussianStepPath (r::rs) u t=gaussianStepPath rs u (t-r.2) := by
  rcases ht.lt_or_eq with h | h
  · exact gaussianStepPath_cons_gt r rs u h
  · rw [← h,gaussianStepPath_cons_le r rs u le_rfl,sub_self,gaussianStepPath_zero hrs u]
    funext x
    exact gaussianRowOperator_zero _ _ _

 

lemma gaussianStepPath_right_pde {u : ℝ → ℝ} {A B C κ Q : ℝ}
    (hQ : 0 < Q) (hu : RowAnalyticTerminal u A B C κ Q)
    {rs : List (ℝ × ℝ)} (hrs : ∀ r ∈ rs, 0 ≤ r.1 ∧ r.1 ≤ 1 ∧ 0 ≤ r.2)
    (hsum : gaussianStepTime rs ≤ Q) {t : ℝ} (ht : t ∈ Ico 0 (gaussianStepTime rs)) (x : ℝ) :
    HasDerivWithinAt (fun s => gaussianStepPath rs u s x)
      (-(1/2:ℝ)*(deriv (deriv (gaussianStepPath rs u t)) x+
        gaussianStepRightCoefficient rs t*(deriv (gaussianStepPath rs u t) x)^2)) (Ici t) t := by
  induction rs generalizing t with
  | nil => simp [gaussianStepTime] at ht
  | cons r rs ih =>
    have hr := hrs r (by simp)
    have htail : ∀ v ∈ rs, 0 ≤ v.1 ∧ v.1 ≤ 1 ∧ 0 ≤ v.2 := fun v hv => hrs v (by simp [hv])
    have htailT : ∀ v ∈ rs, 0 ≤ v.2 := fun v hv => (htail v hv).2.2
    have htot : gaussianStepTime (r::rs)=r.2+gaussianStepTime rs := by simp [gaussianStepTime]
    have hR : gaussianStepTime rs ≤ Q := by rw [htot] at hsum; linarith
    by_cases h : t < r.2
    · have htw := gaussian_composition_twice hQ hu htail hR
      have hd0 := (Twice.gaussianRowOperator_calculus htw hr.1 (sub_pos.mpr h)).2.2 x
      have hd := hd0.comp_const_sub r.2 t
      have he : (fun s => gaussianStepPath (r::rs) u s x) =ᶠ[𝓝 t]
          (fun s => gaussianRowOperator r.1 (r.2-s) (gaussianRowComposition rs u) x) := by
        filter_upwards [eventually_lt_nhds h] with s hs
        exact congrFun (gaussianStepPath_cons_le r rs u hs.le) x
      have hh := hd.congr_of_eventuallyEq he
      rw [gaussianStepPath_cons_le r rs u h.le]
      simpa only [gaussianStepRightCoefficient,ite_eq_left h,neg_mul] using hh.hasDerivWithinAt (s := Ici t)
    · have hge : r.2 ≤ t := le_of_not_gt h
      have ht' : t-r.2 ∈ Ico 0 (gaussianStepTime rs) := by
        rw [htot] at ht
        constructor <;> linarith [ht.2]
      have hi := ih htail hR ht'
      have hdsub : HasDerivWithinAt (fun s : ℝ => s-r.2) 1 (Ici t) t :=
        ((hasDerivAt_id t).sub_const r.2).hasDerivWithinAt
      have hmap : MapsTo (fun s : ℝ => s-r.2) (Ici t) (Ici (t-r.2)) := by
        intro s hs
        exact sub_le_sub_right hs r.2
      have hd := hi.scomp t hdsub hmap
      have he : (fun s => gaussianStepPath (r::rs) u s x) =ᶠ[𝓝[Ici t] t]
          (fun s => gaussianStepPath rs u (s-r.2) x) := by
        filter_upwards [self_mem_nhdsWithin] with s hs
        exact congrFun (gaussianStepPath_cons_ge r rs htailT u (hge.trans hs)) x
      have hh := hd.congr_of_eventuallyEq_of_mem he (show t ∈ Ici t from by simp)
      rw [gaussianStepPath_cons_ge r rs htailT u hge]
      simpa only [Function.comp_def,one_smul,gaussianStepRightCoefficient,ite_eq_right h] using hh
end MicroscopicJamming

 
 

open Set Filter
open scoped Topology

namespace MicroscopicJamming

lemma localMax_second_deriv_nonpos {f : ℝ → ℝ} {x : ℝ}
    (hf : Differentiable ℝ f) (hm : IsLocalMax f x) : deriv (deriv f) x ≤ 0 := by
  by_contra hn
  have hp : 0 < deriv (deriv f) x := lt_of_not_ge hn
  have hzero : deriv f x=0 := hm.deriv_eq_zero
  have hsign := eventually_nhdsWithin_sign_eq_of_deriv_pos hp hzero
  have hright : ∀ᶠ y in 𝓝[>] x, 0 < deriv f y :=
    deriv_pos_right_of_sign_deriv (hsign.filter_mono nhdsWithin_le_nhds)
  obtain ⟨r,hr,hh⟩ := Metric.mem_nhdsWithin_iff.mp hright
  obtain ⟨s,hs,hmax⟩ := Metric.eventually_nhds_iff.mp hm
  let y := x+min r s/2
  have hry : x<y := by dsimp [y]; linarith [lt_min hr hs]
  have hdy : dist y x < r := by
    rw [Real.dist_eq,abs_of_pos (sub_pos.mpr hry)]
    dsimp [y]; linarith [min_le_left r s]
  have hsy : dist y x < s := by
    rw [Real.dist_eq,abs_of_pos (sub_pos.mpr hry)]
    dsimp [y]; linarith [min_le_right r s]
  have hmono : StrictMonoOn f (Icc x y) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc _ _) hf.continuous.continuousOn
    intro z hz
    rw [interior_Icc] at hz
    apply hh ⟨?_,hz.1⟩
    rw [Metric.mem_ball,Real.dist_eq,abs_of_pos (sub_pos.mpr hz.1)]
    have hd : y-x<r := by simpa [Real.dist_eq,abs_of_pos (sub_pos.mpr hry)] using hdy
    linarith [hz.2]
  exact (not_lt_of_ge (hmax hsy)) (hmono ⟨le_rfl,hry.le⟩ ⟨hry.le,le_rfl⟩ hry)

 

lemma backward_strict_compact {Q R : ℝ} (hQ : 0 < Q) (hR : 0 < R)
    {U b d : ℝ → ℝ → ℝ}
    (hc : ContinuousOn (fun p : ℝ × ℝ => U p.1 p.2) (Icc 0 Q ×ˢ Icc (-R) R))
    (hx : ∀ t ∈ Icc 0 Q, Differentiable ℝ (U t))
    (ht : ∀ t ∈ Ico 0 Q, ∀ x, HasDerivWithinAt (fun s => U s x) (d t x) (Ici t) t)
    (hp : ∀ t ∈ Ico 0 Q, ∀ x ∈ Ioo (-R) R,
      0 < d t x+(1/2:ℝ)*deriv (deriv (U t)) x+b t x*deriv (U t) x)
    (hterm : ∀ x ∈ Icc (-R) R, U Q x ≤ 0)
    (hleft : ∀ t ∈ Icc 0 Q, U t (-R) ≤ 0)
    (hright : ∀ t ∈ Icc 0 Q, U t R ≤ 0) :
    ∀ t ∈ Icc 0 Q, ∀ x ∈ Icc (-R) R, U t x ≤ 0 := by
  have hne : (Icc 0 Q ×ˢ Icc (-R) R).Nonempty :=
    ⟨(0,0),⟨le_rfl,hQ.le⟩,by constructor <;> linarith⟩
  obtain ⟨p,hpS,hmax⟩ := (isCompact_Icc.prod isCompact_Icc).exists_isMaxOn hne hc
  suffices h : U p.1 p.2 ≤ 0 by
    intro t ht' x hx'
    exact (hmax (show (t,x) ∈ Icc 0 Q ×ˢ Icc (-R) R from ⟨ht',hx'⟩)).trans h
  by_contra hn
  have hpos : 0 < U p.1 p.2 := lt_of_not_ge hn
  have htQ : p.1 < Q := lt_of_le_of_ne hpS.1.2 (by
    intro he
    have hh := hterm p.2 hpS.2
    rw [← he] at hh
    exact (not_le_of_gt hpos) hh)
  have hxl : -R < p.2 := lt_of_le_of_ne hpS.2.1 (by
    intro he
    have hh := hleft p.1 hpS.1
    rw [he] at hh
    exact (not_le_of_gt hpos) hh)
  have hxr : p.2 < R := lt_of_le_of_ne hpS.2.2 (by
    intro he
    have hh := hright p.1 hpS.1
    rw [← he] at hh
    exact (not_le_of_gt hpos) hh)
  have hxmax : IsMaxOn (U p.1) (Icc (-R) R) p.2 :=
    fun x hx' => hmax (show (p.1,x) ∈ Icc 0 Q ×ˢ Icc (-R) R from ⟨hpS.1,hx'⟩)
  have hxlocal : IsLocalMax (U p.1) p.2 :=
    hxmax.isLocalMax (Icc_mem_nhds hxl hxr)
  have hzero := hxlocal.deriv_eq_zero
  have hsecond := localMax_second_deriv_nonpos (hx p.1 hpS.1) hxlocal
  have htmax : IsMaxOn (fun t => U t p.2) (Icc p.1 Q) p.1 :=
    fun t ht' => hmax (show (t,p.2) ∈ Icc 0 Q ×ˢ Icc (-R) R from ⟨⟨hpS.1.1.trans ht'.1,ht'.2⟩,hpS.2⟩)
  have htan : Q-p.1 ∈ posTangentConeAt (Icc p.1 Q) p.1 :=
    sub_mem_posTangentConeAt_of_segment_subset (segment_eq_Icc htQ.le ▸ Subset.rfl)
  have hd := (ht p.1 ⟨hpS.1.1,htQ⟩ p.2).mono (show Icc p.1 Q ⊆ Ici p.1 from fun _ h => h.1)
  have hnonpos : (Q-p.1)*d p.1 p.2 ≤ 0 := by
    simpa only [ContinuousLinearMap.smulRight_apply,ContinuousLinearMap.toSpanSingleton_apply,one_apply_eq_self,smul_eq_mul] using
      htmax.isLocalMaxOn.hasFDerivWithinAt_nonpos hd htan
  have hdt : d p.1 p.2 ≤ 0 := by nlinarith [sub_pos.mpr htQ]
  have hstrict := hp p.1 ⟨hpS.1.1,htQ⟩ p.2 ⟨hxl,hxr⟩
  rw [hzero,mul_zero,add_zero] at hstrict
  linarith

def quarticBarrier (ε c Q t x : ℝ) : ℝ :=
  ε*Real.exp (c*(Q-t))*(1+x^2)^2

lemma quarticBarrier_space (ε c Q t x : ℝ) :
    HasDerivAt (quarticBarrier ε c Q t)
      (ε*Real.exp (c*(Q-t))*(4*x*(1+x^2))) x := by
  unfold quarticBarrier
  convert (((hasDerivAt_const x 1).add ((hasDerivAt_id x).pow 2)).pow 2).const_mul
    (ε*Real.exp (c*(Q-t))) using 1 <;> first | rfl | (simp only [Pi.add_apply,Pi.pow_apply,id_eq]; ring)

lemma quarticBarrier_space2 (ε c Q t x : ℝ) :
    HasDerivAt (deriv (quarticBarrier ε c Q t))
      (ε*Real.exp (c*(Q-t))*(4+12*x^2)) x := by
  have he : deriv (quarticBarrier ε c Q t)=
      fun y => ε*Real.exp (c*(Q-t))*(4*y*(1+y^2)) :=
    funext fun y => (quarticBarrier_space ε c Q t y).deriv
  rw [he]
  convert (((hasDerivAt_id x).const_mul 4).mul
    ((hasDerivAt_const x 1).add ((hasDerivAt_id x).pow 2))).const_mul
    (ε*Real.exp (c*(Q-t))) using 1 <;> first | rfl | (simp only [Pi.add_apply,Pi.pow_apply,id_eq]; ring)

lemma quarticBarrier_time (ε c Q t x : ℝ) :
    HasDerivAt (fun s => quarticBarrier ε c Q s x)
      (-c*quarticBarrier ε c Q t x) t := by
  unfold quarticBarrier
  convert ((((hasDerivAt_const t Q).sub (hasDerivAt_id t)).const_mul c).exp.const_mul ε).mul_const
    ((1+x^2)^2) using 1 <;> first | rfl | (simp only [Pi.sub_apply,id_eq]; ring)

lemma quartic_transport_neg {K b x : ℝ} (hK : 0 ≤ K)
    (hb : |b| ≤ K*(1+|x|)) :
    -(8*K+8)*(1+x^2)^2+(1/2:ℝ)*(4+12*x^2)+b*(4*x*(1+x^2)) < 0 := by
  have hnorm : (1+|x|)*|x| ≤ 2*(1+x^2) := by
    nlinarith [sq_abs x,sq_nonneg (|x|-1)]
  have hbx : b*x ≤ 2*K*(1+x^2) := calc
    b*x ≤ |b*x| := le_abs_self _
    _ = |b| * |x| := abs_mul _ _
    _ ≤ K*(1+|x|)*|x| := mul_le_mul_of_nonneg_right hb (abs_nonneg _)
    _ ≤ 2*K*(1+x^2) := by nlinarith [mul_le_mul_of_nonneg_left hnorm hK]
  have ht := mul_le_mul_of_nonneg_left hbx (show 0 ≤ 4*(1+x^2) by positivity)
  nlinarith [sq_nonneg x,sq_nonneg (x^2)]

lemma backward_quartic_bound {Q K C : ℝ} (hQ : 0 < Q) (hK : 0 ≤ K) (hC : 0 ≤ C)
    {U b d : ℝ → ℝ → ℝ}
    (hc : ContinuousOn (fun p : ℝ × ℝ => U p.1 p.2) (Icc 0 Q ×ˢ univ))
    (hx : ∀ t ∈ Icc 0 Q, Differentiable ℝ (U t) ∧ Differentiable ℝ (deriv (U t)))
    (ht : ∀ t ∈ Ico 0 Q, ∀ x, HasDerivWithinAt (fun s => U s x) (d t x) (Ici t) t)
    (hb : ∀ t ∈ Icc 0 Q, ∀ x, |b t x| ≤ K*(1+|x|))
    (hg : ∀ t ∈ Icc 0 Q, ∀ x, U t x ≤ C*(1+x^2))
    (hp : ∀ t ∈ Ico 0 Q, ∀ x,
      0 ≤ d t x+(1/2:ℝ)*deriv (deriv (U t)) x+b t x*deriv (U t) x)
    (hterm : ∀ x, U Q x ≤ 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ t ∈ Icc 0 Q, ∀ x, U t x ≤ quarticBarrier ε (8*K+8) Q t x := by
  let c := 8*K+8
  have hcpos : 0 ≤ c := by dsimp [c]; positivity
  let V : ℝ → ℝ → ℝ := fun t x => U t x-quarticBarrier ε c Q t x
  let vd : ℝ → ℝ → ℝ := fun t x => d t x+c*quarticBarrier ε c Q t x
  have hvx (t : ℝ) (ht' : t ∈ Icc 0 Q) (x : ℝ) :
      HasDerivAt (V t) (deriv (U t) x-ε*Real.exp (c*(Q-t))*(4*x*(1+x^2))) x :=
    ((hx t ht').1 x).hasDerivAt.sub (quarticBarrier_space ε c Q t x)
  have hvxx (t : ℝ) (ht' : t ∈ Icc 0 Q) (x : ℝ) :
      deriv (deriv (V t)) x=deriv (deriv (U t)) x-ε*Real.exp (c*(Q-t))*(4+12*x^2) := by
    have he : deriv (V t)=fun y => deriv (U t) y-deriv (quarticBarrier ε c Q t) y := by
      ext y
      rw [(hvx t ht' y).deriv,(quarticBarrier_space ε c Q t y).deriv]
    rw [he]
    exact (((hx t ht').2 x).hasDerivAt.sub (quarticBarrier_space2 ε c Q t x)).deriv
  have hvtime (t : ℝ) (ht' : t ∈ Ico 0 Q) (x : ℝ) :
      HasDerivWithinAt (fun s => V s x) (vd t x) (Ici t) t := by
    convert (ht t ht' x).sub (quarticBarrier_time ε c Q t x).hasDerivWithinAt using 1; first | rfl | (dsimp [V,vd]; ring)
  have hvp (t : ℝ) (ht' : t ∈ Ico 0 Q) (x : ℝ) :
      0 < vd t x+(1/2:ℝ)*deriv (deriv (V t)) x+b t x*deriv (V t) x := by
    have htcc : t ∈ Icc 0 Q := ⟨ht'.1,ht'.2.le⟩
    rw [hvxx t htcc x,(hvx t htcc x).deriv]
    have hneg := quartic_transport_neg hK (hb t htcc x)
    have hneg' := mul_neg_of_pos_of_neg (mul_pos hε (Real.exp_pos (c*(Q-t)))) hneg
    have hP := hp t ht' x
    dsimp [vd,quarticBarrier,c] at *
    nlinarith
  intro t ht' x
  let R := |x|+C/ε+1
  have hdiv : 0 ≤ C/ε := div_nonneg hC hε.le
  have hR1 : 1 ≤ R := by dsimp [R]; linarith [abs_nonneg x]
  have hR : 0 < R := by linarith
  have hxR : x ∈ Icc (-R) R := by
    dsimp [R]; constructor <;> linarith [le_abs_self x,neg_abs_le x]
  have hCR : C ≤ ε*(1+R^2) := by
    have hr : C/ε ≤ 1+R^2 := by dsimp [R] at hR1 ⊢; nlinarith [abs_nonneg x,sq_nonneg R]
    have hh := (div_le_iff₀ hε).mp hr
    nlinarith
  have hB (s : ℝ) (hs : s ∈ Icc 0 Q) :
      C*(1+R^2) ≤ quarticBarrier ε c Q s R := by
    have he : 1 ≤ Real.exp (c*(Q-s)) :=
      Real.one_le_exp_iff.mpr (mul_nonneg hcpos (sub_nonneg.mpr hs.2))
    have hh := mul_le_mul_of_nonneg_right hCR (show 0 ≤ 1+R^2 by positivity)
    have he' := mul_le_mul_of_nonneg_right he (show 0 ≤ ε*(1+R^2)^2 by positivity)
    dsimp [quarticBarrier]
    nlinarith
  have hVc : ContinuousOn (fun p : ℝ × ℝ => V p.1 p.2) (Icc 0 Q ×ˢ Icc (-R) R) := by
    apply (hc.mono (by intro p hp'; exact ⟨hp'.1,mem_univ _⟩)).sub
    have hh : Continuous (fun p : ℝ × ℝ => quarticBarrier ε c Q p.1 p.2) := by
      unfold quarticBarrier
      fun_prop
    exact hh.continuousOn
  have hcomp := backward_strict_compact (b := b) hQ hR hVc
    (fun s hs y => (hvx s hs y).differentiableAt) hvtime (fun s hs y _ => hvp s hs y)
    (fun y _ => by
      dsimp [V]
      have hn : 0 ≤ quarticBarrier ε c Q Q y := by unfold quarticBarrier; positivity
      linarith [hterm y])
    (fun s hs => by
      dsimp [V]
      have hh := hg s hs (-R)
      have hh' := hB s hs
      simp only [neg_sq] at hh
      have he : quarticBarrier ε c Q s (-R)=quarticBarrier ε c Q s R := by simp [quarticBarrier]
      rw [he]
      linarith)
    (fun s hs => by dsimp [V]; linarith [hg s hs R,hB s hs])
  have hh := hcomp t ht' x hxR
  dsimp [V] at hh
  linarith

def BackwardComparisonStatement : Prop :=
  ∀ (Q K C : ℝ), 0 < Q → 0 ≤ K → 0 ≤ C →
  ∀ (U b d : ℝ → ℝ → ℝ),
  ContinuousOn (fun p : ℝ × ℝ => U p.1 p.2) (Icc 0 Q ×ˢ univ) →
  (∀ t ∈ Icc 0 Q, Differentiable ℝ (U t) ∧ Differentiable ℝ (deriv (U t))) →
  (∀ t ∈ Ico 0 Q, ∀ x, HasDerivWithinAt (fun s => U s x) (d t x) (Ici t) t) →
  (∀ t ∈ Icc 0 Q, ∀ x, |b t x| ≤ K*(1+|x|)) →
  (∀ t ∈ Icc 0 Q, ∀ x, U t x ≤ C*(1+x^2)) →
  (∀ t ∈ Ico 0 Q, ∀ x,
    0 ≤ d t x+(1/2:ℝ)*deriv (deriv (U t)) x+b t x*deriv (U t) x) →
  (∀ x, U Q x ≤ 0) →
  ∀ t ∈ Icc 0 Q, ∀ x, U t x ≤ 0

theorem backward_comparison : BackwardComparisonStatement := by
  intro Q K C hQ hK hC U b d hc hx ht hb hg hp hterm t ht' x
  by_contra hn
  have hpos : 0 < U t x := lt_of_not_ge hn
  let M := Real.exp ((8*K+8)*(Q-t))*(1+x^2)^2
  have hM : 0 < M := by dsimp [M]; positivity
  let ε := U t x/(2*M)
  have hε : 0 < ε := div_pos hpos (by positivity)
  have hh := backward_quartic_bound hQ hK hC hc hx ht hb hg hp hterm hε t ht' x
  have he : quarticBarrier ε (8*K+8) Q t x=U t x/2 := by
    dsimp only [quarticBarrier]
    rw [mul_assoc]
    change (U t x/(2*M))*M=U t x/2
    field_simp
  rw [he] at hh
  linarith

end MicroscopicJamming

 
open Set Filter
open scoped Topology

namespace MicroscopicJamming

 

def quadraticSourceBarrier (D c Q t x : ℝ) : ℝ :=
  D*(Q-t)*Real.exp (c*(Q-t))*(1+x^2)

lemma quadraticSourceBarrier_space (D c Q t x : ℝ) :
    HasDerivAt (quadraticSourceBarrier D c Q t)
      (D*(Q-t)*Real.exp (c*(Q-t))*(2*x)) x := by
  unfold quadraticSourceBarrier
  convert ((hasDerivAt_const x 1).add ((hasDerivAt_id x).pow 2)).const_mul
    (D*(Q-t)*Real.exp (c*(Q-t))) using 1 <;>
    first | rfl | (simp only [id_eq]; ring)

lemma quadraticSourceBarrier_space2 (D c Q t x : ℝ) :
    HasDerivAt (deriv (quadraticSourceBarrier D c Q t))
      (2*D*(Q-t)*Real.exp (c*(Q-t))) x := by
  have he : deriv (quadraticSourceBarrier D c Q t)=
      fun y => D*(Q-t)*Real.exp (c*(Q-t))*(2*y) :=
    funext fun y => (quadraticSourceBarrier_space D c Q t y).deriv
  rw [he]
  convert ((hasDerivAt_id x).const_mul 2).const_mul
    (D*(Q-t)*Real.exp (c*(Q-t))) using 1 <;> first | rfl | ring

lemma quadraticSourceBarrier_time (D c Q t x : ℝ) :
    HasDerivAt (fun s => quadraticSourceBarrier D c Q s x)
      (-D*Real.exp (c*(Q-t))*(1+c*(Q-t))*(1+x^2)) t := by
  unfold quadraticSourceBarrier
  have hs := (hasDerivAt_const t Q).sub (hasDerivAt_id t)
  convert (((hs.const_mul D).mul (hs.const_mul c).exp).mul_const (1+x^2)) using 1 <;>
    first | rfl | (simp only [Pi.sub_apply,id_eq]; ring)

lemma quadratic_transport_bound {D K Q t x b : ℝ}
    (hD : 0 ≤ D) (hK : 0 ≤ K) (ht : t ≤ Q) (hb : |b| ≤ K*(1+|x|)) :
    -D*Real.exp ((4*K+2)*(Q-t))*(1+(4*K+2)*(Q-t))*(1+x^2)+
      (1/2:ℝ)*(2*D*(Q-t)*Real.exp ((4*K+2)*(Q-t)))+
      b*(D*(Q-t)*Real.exp ((4*K+2)*(Q-t))*(2*x)) ≤ -D*(1+x^2) := by
  have hnorm : (1+|x|)*|x| ≤ 2*(1+x^2) := by
    nlinarith [sq_abs x,sq_nonneg (|x|-1)]
  have hbx : b*x ≤ 2*K*(1+x^2) := calc
    b*x ≤ |b*x| := le_abs_self _
    _ = |b| * |x| := abs_mul _ _
    _ ≤ K*(1+|x|)*|x| := mul_le_mul_of_nonneg_right hb (abs_nonneg _)
    _ ≤ 2*K*(1+x^2) := by nlinarith [mul_le_mul_of_nonneg_left hnorm hK]
  have hpoly : 1+2*b*x-(4*K+2)*(1+x^2) ≤ 0 := by nlinarith [sq_nonneg x]
  have he : 1 ≤ Real.exp ((4*K+2)*(Q-t)) :=
    Real.one_le_exp_iff.mpr (mul_nonneg (by positivity) (sub_nonneg.mpr ht))
  have hx : 0 ≤ 1+x^2 := by positivity
  have h1 := mul_nonpos_of_nonneg_of_nonpos
    (show 0 ≤ D*(Q-t)*Real.exp ((4*K+2)*(Q-t)) by positivity) hpoly
  have h2 := mul_le_mul_of_nonneg_left he (mul_nonneg hD hx)
  nlinarith

def BackwardSourceComparisonStatement : Prop :=
  ∀ (Q K C D : ℝ), 0 < Q → 0 ≤ K → 0 ≤ C → 0 ≤ D →
  ∀ (U b d : ℝ → ℝ → ℝ),
  ContinuousOn (fun p : ℝ × ℝ => U p.1 p.2) (Icc 0 Q ×ˢ univ) →
  (∀ t ∈ Icc 0 Q, Differentiable ℝ (U t) ∧ Differentiable ℝ (deriv (U t))) →
  (∀ t ∈ Ico 0 Q, ∀ x, HasDerivWithinAt (fun s => U s x) (d t x) (Ici t) t) →
  (∀ t ∈ Icc 0 Q, ∀ x, |b t x| ≤ K*(1+|x|)) →
  (∀ t ∈ Icc 0 Q, ∀ x, U t x ≤ C*(1+x^2)) →
  (∀ t ∈ Ico 0 Q, ∀ x,
    -D*(1+x^2) ≤ d t x+(1/2:ℝ)*deriv (deriv (U t)) x+b t x*deriv (U t) x) →
  (∀ x, U Q x ≤ 0) →
  ∀ t ∈ Icc 0 Q, ∀ x, U t x ≤ quadraticSourceBarrier D (4*K+2) Q t x

theorem backward_source_comparison : BackwardSourceComparisonStatement := by
  intro Q K C D hQ hK hC hD U b d hc hx ht hb hg hp hterm
  let c := 4*K+2
  let V : ℝ → ℝ → ℝ := fun t x => U t x-quadraticSourceBarrier D c Q t x
  let vd : ℝ → ℝ → ℝ := fun t x => d t x+
    D*Real.exp (c*(Q-t))*(1+c*(Q-t))*(1+x^2)
  have hvx (t : ℝ) (ht' : t ∈ Icc 0 Q) (x : ℝ) :
      HasDerivAt (V t) (deriv (U t) x-D*(Q-t)*Real.exp (c*(Q-t))*(2*x)) x :=
    ((hx t ht').1 x).hasDerivAt.sub (quadraticSourceBarrier_space D c Q t x)
  have hvxx (t : ℝ) (ht' : t ∈ Icc 0 Q) (x : ℝ) :
      HasDerivAt (deriv (V t)) (deriv (deriv (U t)) x-2*D*(Q-t)*Real.exp (c*(Q-t))) x := by
    have he : deriv (V t)=fun y => deriv (U t) y-deriv (quadraticSourceBarrier D c Q t) y := by
      ext y
      rw [(hvx t ht' y).deriv,(quadraticSourceBarrier_space D c Q t y).deriv]
    rw [he]
    exact ((hx t ht').2 x).hasDerivAt.sub (quadraticSourceBarrier_space2 D c Q t x)
  have hvtime (t : ℝ) (ht' : t ∈ Ico 0 Q) (x : ℝ) :
      HasDerivWithinAt (fun s => V s x) (vd t x) (Ici t) t := by
    convert (ht t ht' x).sub (quadraticSourceBarrier_time D c Q t x).hasDerivWithinAt using 1;
      first | rfl | (dsimp [V,vd]; ring)
  have hvp (t : ℝ) (ht' : t ∈ Ico 0 Q) (x : ℝ) :
      0 ≤ vd t x+(1/2:ℝ)*deriv (deriv (V t)) x+b t x*deriv (V t) x := by
    have htcc : t ∈ Icc 0 Q := ⟨ht'.1,ht'.2.le⟩
    rw [(hvxx t htcc x).deriv,(hvx t htcc x).deriv]
    have hneg := quadratic_transport_bound hD hK htcc.2 (hb t htcc x)
    have hP := hp t ht' x
    dsimp [vd,c] at *
    linarith
  have hVc : ContinuousOn (fun p : ℝ × ℝ => V p.1 p.2) (Icc 0 Q ×ˢ univ) := by
    apply hc.sub
    have hh : Continuous (fun p : ℝ × ℝ => quadraticSourceBarrier D c Q p.1 p.2) := by
      unfold quadraticSourceBarrier
      fun_prop
    exact hh.continuousOn
  have hVg (t : ℝ) (ht' : t ∈ Icc 0 Q) (x : ℝ) : V t x ≤ C*(1+x^2) := by
    have hn : 0 ≤ quadraticSourceBarrier D c Q t x := by
      unfold quadraticSourceBarrier
      exact mul_nonneg (mul_nonneg (mul_nonneg hD (sub_nonneg.mpr ht'.2))
        (Real.exp_pos _).le) (by positivity)
    dsimp [V]
    linarith [hg t ht' x]
  have hVterm (x : ℝ) : V Q x ≤ 0 := by
    simpa [V,quadraticSourceBarrier] using hterm x
  have hcomp := backward_comparison Q K C hQ hK hC V b vd hVc
    (fun t ht' => ⟨fun x => (hvx t ht' x).differentiableAt,
      fun x => (hvxx t ht' x).differentiableAt⟩) hvtime hb hVg hvp hVterm
  intro t ht' x
  have hh := hcomp t ht' x
  dsimp [V,c] at hh
  linarith
end MicroscopicJamming

 
open Set Filter
open scoped Topology

namespace MicroscopicJamming

 

lemma variance_difference_le {Q C L δ : ℝ} (hQ : 0 < Q) (hC : 0 ≤ C)
    (hL : 0 ≤ L) (hδ : 0 ≤ δ) {F G : ℝ → ℝ → ℝ} {m n : ℝ → ℝ}
    (hcF : ContinuousOn (fun p : ℝ × ℝ => F p.1 p.2) (Icc 0 Q ×ˢ univ))
    (hcG : ContinuousOn (fun p : ℝ × ℝ => G p.1 p.2) (Icc 0 Q ×ˢ univ))
    (hxF : ∀ t ∈ Icc 0 Q, Differentiable ℝ (F t) ∧ Differentiable ℝ (deriv (F t)))
    (hxG : ∀ t ∈ Icc 0 Q, Differentiable ℝ (G t) ∧ Differentiable ℝ (deriv (G t)))
    (htF : ∀ t ∈ Ico 0 Q, ∀ x, HasDerivWithinAt (fun s => F s x)
      (-(1/2:ℝ)*(deriv (deriv (F t)) x+m t*(deriv (F t) x)^2)) (Ici t) t)
    (htG : ∀ t ∈ Ico 0 Q, ∀ x, HasDerivWithinAt (fun s => G s x)
      (-(1/2:ℝ)*(deriv (deriv (G t)) x+n t*(deriv (G t) x)^2)) (Ici t) t)
    (hm : ∀ t ∈ Icc 0 Q, 0 ≤ m t ∧ m t ≤ 1)
    (hclose : ∀ t ∈ Ico 0 Q, |m t-n t| ≤ δ)
    (hboundF : ∀ t ∈ Icc 0 Q, ∀ x, |F t x| ≤ C*(1+x^2))
    (hboundG : ∀ t ∈ Icc 0 Q, ∀ x, |G t x| ≤ C*(1+x^2))
    (hgradF : ∀ t ∈ Icc 0 Q, ∀ x, |deriv (F t) x| ≤ L*(1+|x|))
    (hgradG : ∀ t ∈ Icc 0 Q, ∀ x, |deriv (G t) x| ≤ L*(1+|x|))
    (hterm : ∀ x, F Q x=G Q x) :
    ∀ t ∈ Icc 0 Q, ∀ x,
      F t x-G t x ≤ quadraticSourceBarrier (δ*L^2) (4*L+2) Q t x := by
  let U : ℝ → ℝ → ℝ := fun t x => F t x-G t x
  let b : ℝ → ℝ → ℝ := fun t x => m t*(deriv (F t) x+deriv (G t) x)/2
  let d : ℝ → ℝ → ℝ := fun t x =>
    -(1/2:ℝ)*(deriv (deriv (F t)) x+m t*(deriv (F t) x)^2)-
    (-(1/2:ℝ)*(deriv (deriv (G t)) x+n t*(deriv (G t) x)^2))
  have hdx (t : ℝ) (ht : t ∈ Icc 0 Q) (x : ℝ) :
      HasDerivAt (U t) (deriv (F t) x-deriv (G t) x) x :=
    ((hxF t ht).1 x).hasDerivAt.sub ((hxG t ht).1 x).hasDerivAt
  have hdx2 (t : ℝ) (ht : t ∈ Icc 0 Q) (x : ℝ) :
      HasDerivAt (deriv (U t)) (deriv (deriv (F t)) x-deriv (deriv (G t)) x) x := by
    have he : deriv (U t)=fun y => deriv (F t) y-deriv (G t) y :=
      funext fun y => (hdx t ht y).deriv
    rw [he]
    exact ((hxF t ht).2 x).hasDerivAt.sub ((hxG t ht).2 x).hasDerivAt
  have hc : ContinuousOn (fun p : ℝ × ℝ => U p.1 p.2) (Icc 0 Q ×ˢ univ) := hcF.sub hcG
  have hx (t : ℝ) (ht : t ∈ Icc 0 Q) :
      Differentiable ℝ (U t) ∧ Differentiable ℝ (deriv (U t)) :=
    ⟨fun x => (hdx t ht x).differentiableAt,fun x => (hdx2 t ht x).differentiableAt⟩
  have htime (t : ℝ) (ht : t ∈ Ico 0 Q) (x : ℝ) :
      HasDerivWithinAt (fun s => U s x) (d t x) (Ici t) t := (htF t ht x).sub (htG t ht x)
  have hb (t : ℝ) (ht : t ∈ Icc 0 Q) (x : ℝ) : |b t x| ≤ L*(1+|x|) := by
    have hsum : |deriv (F t) x+deriv (G t) x| ≤ 2*L*(1+|x|) := by
      calc
        _ ≤ |deriv (F t) x|+|deriv (G t) x| := abs_add_le _ _
        _ ≤ L*(1+|x|)+L*(1+|x|) := add_le_add (hgradF t ht x) (hgradG t ht x)
        _ = _ := by ring
    have hmul := mul_le_mul_of_nonneg_left hsum (hm t ht).1
    have hmul' := mul_le_mul_of_nonneg_right (hm t ht).2 (show 0 ≤ 2*L*(1+|x|) by positivity)
    dsimp [b]
    rw [abs_div,abs_mul,abs_of_nonneg (hm t ht).1,abs_of_pos (by norm_num : (0:ℝ)<2)]
    linarith
  have hg (t : ℝ) (ht : t ∈ Icc 0 Q) (x : ℝ) : U t x ≤ (2*C)*(1+x^2) := by
    dsimp [U]
    have h1 := hboundF t ht x
    have h2 := hboundG t ht x
    nlinarith [le_abs_self (F t x),neg_abs_le (G t x)]
  have hp (t : ℝ) (ht : t ∈ Ico 0 Q) (x : ℝ) :
      -(δ*L^2)*(1+x^2) ≤ d t x+(1/2:ℝ)*deriv (deriv (U t)) x+b t x*deriv (U t) x := by
    have htcc : t ∈ Icc 0 Q := ⟨ht.1,ht.2.le⟩
    rw [(hdx2 t htcc x).deriv,(hdx t htcc x).deriv]
    have he : d t x+(1/2:ℝ)*(deriv (deriv (F t)) x-deriv (deriv (G t)) x)+
        b t x*(deriv (F t) x-deriv (G t) x)=
        -(m t-n t)*(deriv (G t) x)^2/2 := by dsimp [d,b]; ring
    rw [he]
    have hsquare : (deriv (G t) x)^2 ≤ 2*L^2*(1+x^2) := by
      have hs := pow_le_pow_left₀ (abs_nonneg (deriv (G t) x)) (hgradG t htcc x) 2
      rw [sq_abs] at hs
      have hab : (1+|x|)^2 ≤ 2*(1+x^2) := by nlinarith [sq_abs x,sq_nonneg (|x|-1)]
      have hh := mul_le_mul_of_nonneg_left hab (sq_nonneg L)
      nlinarith
    have h1 := mul_le_mul_of_nonneg_right (abs_le.mp (hclose t ht)).2 (sq_nonneg (deriv (G t) x))
    have h2 := mul_le_mul_of_nonneg_left hsquare hδ
    nlinarith
  have hterm' (x : ℝ) : U Q x ≤ 0 := by simp [U,hterm x]
  exact backward_source_comparison Q L (2*C) (δ*L^2) hQ hL (by positivity) (by positivity)
    U b d hc hx htime hb hg hp hterm'
end MicroscopicJamming

 
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology

namespace MicroscopicJamming
 

def GaussianStepStabilityStatement : Prop :=
  ∀ A B C κ Q : ℝ, 0 < Q → 0 ≤ A → 0 ≤ C → 0 ≤ κ → κ*Q < 1 →
  ∃ L : ℝ, 0 ≤ L ∧ ∀ u : ℝ → ℝ, RowAnalyticTerminal u A B C κ Q →
  ∀ rs ss : List (ℝ × ℝ),
    (∀ r ∈ rs, 0 ≤ r.1 ∧ r.1 ≤ 1 ∧ 0 ≤ r.2) →
    (∀ r ∈ ss, 0 ≤ r.1 ∧ r.1 ≤ 1 ∧ 0 ≤ r.2) →
    gaussianStepTime rs=Q → gaussianStepTime ss=Q →
    ∀ δ : ℝ, 0 ≤ δ →
      (∀ t ∈ Icc 0 Q, |gaussianStepCoefficient rs t-gaussianStepCoefficient ss t| ≤ δ) →
      ∀ t ∈ Icc 0 Q, ∀ x,
        |gaussianStepPath rs u t x-gaussianStepPath ss u t x| ≤ δ*L*(1+x^2)

theorem gaussian_step_stability : GaussianStepStabilityStatement := by
  intro A B C κ Q hQ hA hC hκ hκQ
  obtain ⟨D,L,hD,hL,hpath⟩ := gaussian_step_path A B C κ Q hQ hA hC hκ hκQ
  refine ⟨L^2*Q*Real.exp ((4*L+2)*Q),by positivity,?_⟩
  intro u hu rs ss hrs hss hTr hTs δ hδ hclose
  obtain ⟨_,htermR,htimeR,hspaceR⟩ := hpath u hu rs hrs hTr.le
  obtain ⟨_,htermS,htimeS,hspaceS⟩ := hpath u hu ss hss hTs.le
  have hxr (t : ℝ) (ht : t ∈ Icc 0 Q) :
      Differentiable ℝ (gaussianStepPath rs u t) ∧ Differentiable ℝ (deriv (gaussianStepPath rs u t)) := by
    have hh := hspaceR t ht.1 (hTr ▸ ht.2)
    exact ⟨hh.1,hh.2.1⟩
  have hxs (t : ℝ) (ht : t ∈ Icc 0 Q) :
      Differentiable ℝ (gaussianStepPath ss u t) ∧ Differentiable ℝ (deriv (gaussianStepPath ss u t)) := by
    have hh := hspaceS t ht.1 (hTs ▸ ht.2)
    exact ⟨hh.1,hh.2.1⟩
  have hgr (t : ℝ) (ht : t ∈ Icc 0 Q) (x : ℝ) :
      |deriv (gaussianStepPath rs u t) x| ≤ L*(1+|x|) :=
    ((hspaceR t ht.1 (hTr ▸ ht.2)).2.2 x).1
  have hgs (t : ℝ) (ht : t ∈ Icc 0 Q) (x : ℝ) :
      |deriv (gaussianStepPath ss u t) x| ≤ L*(1+|x|) :=
    ((hspaceS t ht.1 (hTs ▸ ht.2)).2.2 x).1
  have hcr := gaussianStepPath_jointly_continuous hD hL hTr htimeR
    (fun t ht htR => ⟨(hspaceR t ht htR).1,fun x => ((hspaceR t ht htR).2.2 x).1⟩)
  have hcs := gaussianStepPath_jointly_continuous hD hL hTs htimeS
    (fun t ht htS => ⟨(hspaceS t ht htS).1,fun x => ((hspaceS t ht htS).2.2 x).1⟩)
  have hpr (t : ℝ) (ht : t ∈ Ico 0 Q) (x : ℝ) :=
    gaussianStepPath_right_pde hQ hu hrs hTr.le (hTr ▸ ht) x
  have hps (t : ℝ) (ht : t ∈ Ico 0 Q) (x : ℝ) :=
    gaussianStepPath_right_pde hQ hu hss hTs.le (hTs ▸ ht) x
  have hb : 0 ≤ |B|+A*(1+Q) := by positivity
  have hvr (t : ℝ) (ht : t ∈ Icc 0 Q) (x : ℝ) :=
    gaussianStepPath_global_value_bound hQ hu hrs hTr ht x
  have hvs (t : ℝ) (ht : t ∈ Icc 0 Q) (x : ℝ) :=
    gaussianStepPath_global_value_bound hQ hu hss hTs ht x
  have hmr (t : ℝ) (_ : t ∈ Icc 0 Q) := gaussianStepRightCoefficient_bounds hrs t
  have hms (t : ℝ) (_ : t ∈ Icc 0 Q) := gaussianStepRightCoefficient_bounds hss t
  have hδr (t : ℝ) (ht : t ∈ Ico 0 Q) := gaussianStepRightCoefficient_close hclose ht
  have hδs (t : ℝ) (ht : t ∈ Ico 0 Q) :
      |gaussianStepRightCoefficient ss t-gaussianStepRightCoefficient rs t| ≤ δ := by
    rw [abs_sub_comm]
    exact hδr t ht
  have hterm (x : ℝ) : gaussianStepPath rs u Q x=gaussianStepPath ss u Q x := by
    simpa only [hTr,hTs] using (htermR x).trans (htermS x).symm
  have hr := variance_difference_le hQ hb hL hδ hcr hcs hxr hxs hpr hps hmr hδr hvr hvs hgr hgs hterm
  have hs := variance_difference_le hQ hb hL hδ hcs hcr hxs hxr hps hpr hms hδs hvs hvr hgs hgr
    (fun x => (hterm x).symm)
  intro t ht x
  have hab : |gaussianStepPath rs u t x-gaussianStepPath ss u t x| ≤
      quadraticSourceBarrier (δ*L^2) (4*L+2) Q t x := by
    rw [abs_le]
    constructor
    · linarith [hs t ht x]
    · exact hr t ht x
  have he : Real.exp ((4*L+2)*(Q-t)) ≤ Real.exp ((4*L+2)*Q) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (by linarith [ht.1]) (by positivity))
  have htq : (Q-t)*Real.exp ((4*L+2)*(Q-t)) ≤ Q*Real.exp ((4*L+2)*Q) :=
    mul_le_mul (by linarith [ht.1]) he (Real.exp_pos _).le hQ.le
  calc
    _ ≤ quadraticSourceBarrier (δ*L^2) (4*L+2) Q t x := hab
    _ = (δ*L^2)*((Q-t)*Real.exp ((4*L+2)*(Q-t)))*(1+x^2) := by
      unfold quadraticSourceBarrier
      ring
    _ ≤ (δ*L^2)*(Q*Real.exp ((4*L+2)*Q))*(1+x^2) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left htq (by positivity)) (by positivity)
    _ = δ*(L^2*Q*Real.exp ((4*L+2)*Q))*(1+x^2) := by ring
end MicroscopicJamming

 
 

namespace MicroscopicJamming

def GaussianStepThirdStatement : Prop :=
  ∀ (u : ℝ → ℝ) (A B C κ Q : ℝ), 0 < Q → RowAnalyticTerminal u A B C κ Q →
  ∃ H : ℝ, 0 ≤ H ∧
  ∀ rs : List (ℝ × ℝ), (∀ r ∈ rs, 0 ≤ r.1 ∧ r.1 ≤ 1 ∧ 0 ≤ r.2) →
    gaussianStepTime rs ≤ Q → ∀ t : ℝ, 0 ≤ t → t ≤ gaussianStepTime rs →
    Differentiable ℝ (deriv (deriv (gaussianStepPath rs u t))) ∧
    ∀ x, |deriv (deriv (deriv (gaussianStepPath rs u t))) x| ≤ H
end MicroscopicJamming

end

end OAI
