import Mathlib
import OAI.Analysis.PathSelection.InverseAsymptotics
import OAI.Analysis.PathSelection.PhaseSectors
import OAI.Analysis.PathSelection.RelativeStrips

namespace OAI

/-! Exponential sector charts, phase contraction and inward equal-exponent maps. -/

noncomputable section
open Set Filter Topology Metric Polynomial
open scoped BigOperators NNReal ENNReal

open Set Filter Topology Complex
namespace DegeneratingTrees.Clock

theorem strict_exponential_chart {F H : ℂ → ℂ} {a b : ℝ}
    (ha : 0≤a) (hab : a<b)
    (hFa : ∀ᶠ z in stripInfinity,AnalyticAt ℂ F z)
    (hHa : ∀ᶠ z in stripInfinity,AnalyticAt ℂ H z)
    (hF0 : ∀ᶠ z in stripInfinity,F z≠0)
    (hH0 : ∀ᶠ z in stripInfinity,H z≠0)
    (hFr : ∀ᶠ t : ℝ in atTop,(F (t:ℂ)).im=0 ∧ 0<(F (t:ℂ)).re)
    (hHr : ∀ᶠ t : ℝ in atTop,(H (t:ℂ)).im=0 ∧ 0<(H (t:ℂ)).re)
    (hFt : Tendsto (fun t : ℝ => (F (t:ℂ)).re) atTop atTop)
    (hHt : Tendsto (fun t : ℝ => (H (t:ℂ)).re) atTop atTop)
    (hFd : Tendsto (fun z => deriv F z/F z) stripInfinity (𝓝 (a:ℂ)))
    (hHd : Tendsto (fun z => deriv H z/H z) stripInfinity (𝓝 (b:ℂ))) :
    ∃ (T : ℝ) (x : ℂ → ℂ),0<T ∧
      AnalyticOnNhd ℂ x {w | 0<w.re ∧ T<‖w‖} ∧
      (∀ w : ℂ,0<w.re → T<‖w‖ → H (x w)=w) ∧
      (∀ᶠ t : ℝ in atTop,x (H (t:ℂ))=(t:ℂ)) ∧
      Tendsto x sectorInfinity stripInfinity ∧
      (∀ᶠ r : ℝ in atTop,(x (r:ℂ)).im=0 ∧ (F (x (r:ℂ))).im=0 ∧ 0<(F (x (r:ℂ))).re) ∧
      Tendsto (fun r : ℝ => (F (x (r:ℂ))).re) atTop atTop ∧
      (∀ᶠ w in sectorInfinity,AnalyticAt ℂ (fun z => F (x z)) w) ∧
      ∀ (ω : ℝ → ℝ) (S : ℝ),AdmissibleAngularLoss ω →
        ∃ (η : ℝ → ℝ) (R : ℝ),AdmissibleAngularLoss η ∧
          (∀ w∈lossSector η R,F (x w)∈lossSector ω S) ∧
          (∀ w∈lossSector η R,(F (x (‖w‖:ℂ))).re/2≤‖F (x w)‖ ∧
            ‖F (x w)‖≤2*(F (x (‖w‖:ℂ))).re) ∧
          (∀ ε : ℝ,0<ε → ∃ U : ℝ,∀ w∈lossSector η U,|(F (x w)).re|≤ε*w.re) := by
  have hb : 0<b := ha.trans_lt hab
  obtain ⟨T,hT,x,hxa,hleft,hright,hxr,hxt,hxto,hinc,hxd⟩ :=
    positive_exponential_inverse_asymptotic hb hHa hH0 hHr hHt hHd
  have hreal : ∀ᶠ r : ℝ in atTop,x (r:ℂ)=((x (r:ℂ)).re:ℂ) := by
    filter_upwards [eventually_gt_atTop T] with r hr
    exact Complex.ext rfl (by simpa using hxr r hr)
  have hFrx : ∀ᶠ r : ℝ in atTop,(F (x (r:ℂ))).im=0 ∧ 0<(F (x (r:ℂ))).re := by
    filter_upwards [hxt.eventually hFr,hreal] with r hr he
    rwa [←he] at hr
  have hFxt : Tendsto (fun r : ℝ => (F (x (r:ℂ))).re) atTop atTop :=
    (hFt.comp hxt).congr' (hreal.mono fun r hr => congrArg (fun z => (F z).re) hr.symm)
  have hdom : ∀ᶠ w in sectorInfinity,0<w.re ∧ T<‖w‖ :=
    SectorEventually.realpart_pos.and (tendsto_norm_sectorInfinity.eventually (eventually_gt_atTop T))
  have hFaX : ∀ᶠ w in sectorInfinity,AnalyticAt ℂ (fun z => F (x z)) w := by
    filter_upwards [hdom,hxto.eventually hFa] with w hw hF
    exact hF.comp (hxa w hw)
  have hi : ∀ ε : ℝ,0<ε → ∀ᶠ w in sectorInfinity,
      ‖x w-x (‖w‖:ℂ)-Complex.I*(w.arg/b:ℝ)‖≤ε*|w.arg| := by
    intro ε hε
    obtain ⟨U,hU⟩ := hinc ε hε
    filter_upwards [SectorEventually.realpart_pos,tendsto_norm_sectorInfinity.eventually (eventually_gt_atTop U)] with w hw hUw
    exact hU w hw hUw
  have hratio := inverse_clock_ratio_tendsto hb hFa hF0 hFd
    (tendsto_re_stripInfinity.comp hxto) hxt
    ((eventually_gt_atTop T).mono fun r hr => hxr r hr) hi
  let f : ℝ → ℝ := fun r => (F (x (r:ℂ))).re
  have hphase : Tendsto (fun w => Complex.exp (-Complex.I*((a/b)*w.arg:ℝ)) * (F (x w)/(f ‖w‖:ℂ)))
      sectorInfinity (𝓝 1) := by
    apply hratio.congr'
    filter_upwards [tendsto_norm_sectorInfinity.eventually hFrx] with w hw
    have he : F (x (‖w‖:ℂ))=(f ‖w‖:ℂ) := Complex.ext rfl (by simpa using hw.1)
    rw [he]
    congr 2
    push_cast
    ring
  have hq0 : 0≤a/b := div_nonneg ha hb.le
  have hq1 : a/b<1 := (div_lt_one hb).mpr hab
  let q := (a/b+1)/2
  have hq : q<1 := by dsimp [q]; linarith
  have hqab : a<q*b := by
    have hh : a/b<q := by dsimp [q]; linarith
    exact (div_lt_iff₀ hb).mp hh
  obtain ⟨C,hC,hpow⟩ := complex_log_derivative_power_bound hqab
    (tendsto_real_stripInfinity.eventually hFa) (tendsto_real_stripInfinity.eventually hHa)
    hFr hHr (hFd.comp tendsto_real_stripInfinity) (hHd.comp tendsto_real_stripInfinity)
  have hpowx : ∀ᶠ r : ℝ in atTop,f r≤C*r^q := by
    filter_upwards [hxt.eventually hpow,hreal,eventually_gt_atTop T] with r hr he hrT
    have hn : ‖(r:ℂ)‖=r := Complex.norm_of_nonneg ((hT.trans hrT).le)
    have hH := hleft (r:ℂ) (by simpa using hT.trans hrT) (by simpa only [hn] using hrT)
    rw [←he,hH,Complex.ofReal_re] at hr
    exact hr
  obtain ⟨κ,K,hκ,hmap,hmod⟩ := strict_phase_sector_mapping hq0 hq1 hFxt hphase baseLoss 0 admissible_baseLoss
  have hbound : ∀ᶠ w in sectorInfinity,‖F (x w)‖≤(2*C)*‖w‖^q := by
    have hh : ∀ᶠ w in sectorInfinity,‖F (x w)‖≤2*f ‖w‖ := ⟨κ,K,hκ,fun z hz => (hmod z hz).2⟩
    filter_upwards [hh,tendsto_norm_sectorInfinity.eventually hpowx] with w hw hp
    nlinarith
  obtain ⟨θ,hθ,hsmall⟩ := sector_sublinear_realpart hq (show 0<2*C by positivity) hbound
  refine ⟨T,x,hT,hxa,hleft,hright,hxto,?_,hFxt,hFaX,?_⟩
  · filter_upwards [hFrx,eventually_gt_atTop T] with r hr ht
    exact ⟨hxr r ht,hr⟩
  · intro ω S hω
    obtain ⟨η,R,hη,hmap,hmod⟩ := strict_phase_sector_mapping hq0 hq1 hFxt hphase ω S hω
    refine ⟨fun r => max (η r) (θ r),R,hη.max hθ,?_,?_,?_⟩
    · intro w hw
      exact hmap w ⟨hw.1,hw.2.trans_le (sub_le_sub_left (le_max_left _ _) _)⟩
    · intro w hw
      exact hmod w ⟨hw.1,hw.2.trans_le (sub_le_sub_left (le_max_left _ _) _)⟩
    · intro ε hε
      obtain ⟨U,hU⟩ := hsmall ε hε
      exact ⟨U,fun w hw => hU w ⟨hw.1,hw.2.trans_le (sub_le_sub_left (le_max_right _ _) _)⟩⟩

end DegeneratingTrees.Clock

 

 

 

open Set Filter Topology Complex
namespace DegeneratingTrees.Clock

theorem inverse_halfplane_strip {x : ℂ → ℂ} {b : ℝ} (hb : 0<b)
    (hr : ∀ᶠ r : ℝ in atTop,(x (r:ℂ)).im=0)
    (ht : Tendsto (fun r : ℝ => (x (r:ℂ)).re) atTop atTop)
    (hi : ∃ U : ℝ,∀ w : ℂ,0<w.re → U<‖w‖ →
      ‖x w-x (‖w‖:ℂ)-Complex.I*(w.arg/b:ℝ)‖≤|w.arg|) :
    ∃ R B : ℝ,0<R ∧ 0<B ∧ ∀ A : ℝ,∃ U : ℝ,0<U ∧
      ∀ w : ℂ,0<w.re → U<‖w‖ →
        A<(x (‖w‖:ℂ)).re ∧ x w∈horizontalTail A R ∧
        ‖x w-((x (‖w‖:ℂ)).re:ℂ)‖≤B := by
  obtain ⟨U₀,hU₀⟩ := hi
  let B := Real.pi+Real.pi/b+1
  have hB : 0<B := by dsimp [B]; positivity
  refine ⟨B+1,B,by linarith,hB,?_⟩
  intro A
  obtain ⟨U₁,hU₁⟩ := eventually_atTop.mp (hr.and (ht.eventually (eventually_gt_atTop (A+B))))
  refine ⟨max 1 (max U₀ U₁),lt_of_lt_of_le zero_lt_one (le_max_left _ _),?_⟩
  intro w hw hwU
  have hw₀ : U₀<‖w‖ := lt_of_le_of_lt ((le_max_left _ _).trans (le_max_right _ _)) hwU
  have hw₁ : U₁≤‖w‖ := ((le_max_right _ _).trans (le_max_right _ _)).trans hwU.le
  obtain ⟨hrw,htw⟩ := hU₁ ‖w‖ hw₁
  have he : x (‖w‖:ℂ)=((x (‖w‖:ℂ)).re:ℂ) := Complex.ext rfl (by simpa using hrw)
  have hd : ‖x w-x (‖w‖:ℂ)‖≤B := by
    have hn : ‖Complex.I*(w.arg/b:ℝ)‖=|w.arg|/b := by
      rw [norm_mul,Complex.norm_I,one_mul,Complex.norm_real,Real.norm_eq_abs,abs_div,abs_of_pos hb]
    calc
      ‖x w-x (‖w‖:ℂ)‖ ≤ ‖x w-x (‖w‖:ℂ)-Complex.I*(w.arg/b:ℝ)‖+‖Complex.I*(w.arg/b:ℝ)‖ := norm_le_norm_sub_add _ _
      _ ≤ |w.arg|+|w.arg|/b := by rw [hn]; exact add_le_add (hU₀ w hw hw₀) le_rfl
      _ ≤ B := by
        have hp := Complex.abs_arg_le_pi w
        have hh := div_le_div_of_nonneg_right hp hb.le
        dsimp [B]; linarith
  have hre := (Complex.abs_re_le_norm (x w-x (‖w‖:ℂ))).trans hd
  have him := (Complex.abs_im_le_norm (x w-x (‖w‖:ℂ))).trans hd
  simp only [Complex.sub_re] at hre
  simp only [Complex.sub_im,hrw,sub_zero] at him
  refine ⟨by linarith,⟨by linarith [(abs_le.mp hre).1],by linarith⟩,?_⟩
  rwa [he] at hd

lemma exp_horizontalTail_right {A : ℝ} {w : ℂ}
    (hw : w∈horizontalTail A (Real.pi/2)) : 0<(Complex.exp w).re := by
  rw [Complex.exp_re]
  exact mul_pos (Real.exp_pos _) (Real.cos_pos_of_mem_Ioo (abs_lt.mp hw.2))

lemma exp_horizontalTail_norm {A U : ℝ} (hU : 0<U) {w : ℂ}
    (hw : w∈horizontalTail (max A (Real.log U)) (Real.pi/2)) : U<‖Complex.exp w‖ := by
  rw [Complex.norm_exp,←Real.exp_log hU]
  exact Real.exp_strictMono (lt_of_le_of_lt (le_max_right _ _) hw.1)

end DegeneratingTrees.Clock

 

 

 

open Set Filter Topology Complex
namespace DegeneratingTrees.Clock

lemma imaginary_derivative_of_complex {f : ℂ → ℂ} {f' : ℂ} {t : ℝ}
    (h : HasDerivAt f f' (t:ℂ)) :
    HasDerivAt (fun s : ℝ => (f (s:ℂ)).im) f'.im t := by
  simpa only [Function.comp_def,Complex.imCLM_apply] using
    Complex.imCLM.hasFDerivAt.comp_hasDerivAt t h.comp_ofReal

lemma vertical_phase_derivative {G : ℂ → ℂ} {x t : ℝ}
    (hG : AnalyticAt ℂ G ((x:ℂ)+Complex.I*(t:ℂ))) :
    HasDerivAt (fun s : ℝ => s+(G ((x:ℂ)+Complex.I*(s:ℂ))).im)
      (1+(deriv G ((x:ℂ)+Complex.I*(t:ℂ))).re) t := by
  have hv : HasDerivAt (fun z : ℂ => (x:ℂ)+Complex.I*z) Complex.I (t:ℂ) := by
    simpa only [mul_one,id_eq] using (hasDerivAt_id (t:ℂ)).const_mul Complex.I |>.const_add (x:ℂ)
  have hcomp : HasDerivAt (fun z : ℂ => G ((x:ℂ)+Complex.I*z))
      (deriv G ((x:ℂ)+Complex.I*(t:ℂ))*Complex.I) (t:ℂ) :=
    hG.differentiableAt.hasDerivAt.comp (t:ℂ) hv
  have hh := imaginary_derivative_of_complex hcomp
  simpa only [Pi.add_def,id_eq,Complex.mul_im,Complex.I_re,Complex.I_im,mul_zero,mul_one,add_zero] using
    (hasDerivAt_id t).add hh

theorem vertical_phase_contraction {G : ℂ → ℂ} {x θ : ℝ}
    (hG : ∀ t∈uIcc (0:ℝ) θ,AnalyticAt ℂ G ((x:ℂ)+Complex.I*(t:ℂ)))
    (hr : (G (x:ℂ)).im=0)
    (hder : ∀ t∈uIcc (0:ℝ) θ,-1 ≤ (deriv G ((x:ℂ)+Complex.I*(t:ℂ))).re ∧
      (deriv G ((x:ℂ)+Complex.I*(t:ℂ))).re ≤ 0) :
    |θ+(G ((x:ℂ)+Complex.I*(θ:ℂ))).im| ≤ |θ| := by
  let f : ℝ → ℝ := fun t => t+(G ((x:ℂ)+Complex.I*(t:ℂ))).im
  have hd (t : ℝ) (ht : t∈uIcc (0:ℝ) θ) := vertical_phase_derivative (hG t ht)
  have hf : ContinuousOn f (uIcc (0:ℝ) θ) := fun t ht => (hd t ht).continuousAt.continuousWithinAt
  have hf' : DifferentiableOn ℝ f (interior (uIcc (0:ℝ) θ)) :=
    fun t ht => (hd t (interior_subset ht)).differentiableAt.differentiableWithinAt
  have h0 : f 0=0 := by simp [f,hr]
  have hlo := (convex_uIcc (0:ℝ) θ).mul_sub_le_image_sub_of_le_deriv hf hf'
    (C := 0) (fun t ht => by rw [(hd t (interior_subset ht)).deriv]; linarith [(hder t (interior_subset ht)).1])
  have hup := (convex_uIcc (0:ℝ) θ).image_sub_le_mul_sub_of_deriv_le hf hf'
    (C := 1) (fun t ht => by rw [(hd t (interior_subset ht)).deriv]; linarith [(hder t (interior_subset ht)).2])
  change |f θ| ≤ |θ|
  by_cases hθ : 0 ≤ θ
  · have hl := hlo 0 left_mem_uIcc θ right_mem_uIcc hθ
    have hu := hup 0 left_mem_uIcc θ right_mem_uIcc hθ
    rw [h0] at hl hu
    rw [abs_of_nonneg hθ,abs_le]
    constructor <;> linarith
  · have hl := hlo θ right_mem_uIcc 0 left_mem_uIcc (le_of_not_ge hθ)
    have hu := hup θ right_mem_uIcc 0 left_mem_uIcc (le_of_not_ge hθ)
    rw [h0] at hl hu
    rw [abs_of_neg (lt_of_not_ge hθ),abs_le]
    constructor <;> linarith

end DegeneratingTrees.Clock

 

 

 

open Set Filter Topology Complex
namespace DegeneratingTrees.Clock

lemma positive_quotient_neighborhood {b : ℝ} (hb : 0 < b) :
    ∃ δ : ℝ,0 < δ ∧ ∀ u v : ℂ,‖u-1‖ < δ → ‖v-(b:ℂ)‖ < δ →
      0 < (u/v).re ∧ ‖u/v‖ < 2/b := by
  have hbn : (b:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hb.ne'
  have hc : ContinuousAt (fun p : ℂ × ℂ => p.1/p.2) (1,(b:ℂ)) :=
    continuousAt_fst.div continuousAt_snd hbn
  have hr : (1/(b:ℂ)).re=1/b := by simp
  have hn : ‖(1:ℂ)/(b:ℂ)‖=1/b := by simp [abs_of_pos hb]
  have he : ∀ᶠ p : ℂ × ℂ in 𝓝 (1,(b:ℂ)),0 < (p.1/p.2).re ∧ ‖p.1/p.2‖ < 2/b := by
    apply hc.eventually (p := fun z : ℂ => 0 < z.re ∧ ‖z‖ < 2/b)
    filter_upwards [(show IsOpen {z : ℂ | (0:ℝ) < z.re} from isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by change 0 < (1/(b:ℂ)).re; rw [hr]; positivity),
      Metric.isOpen_ball.mem_nhds (show (1:ℂ)/(b:ℂ)∈Metric.ball 0 (2/b) by
        simp only [Metric.mem_ball,dist_zero_right,hn]
        exact (div_lt_div_iff_of_pos_right hb).mpr (by norm_num))] with z hz hzn
    exact ⟨hz,by simpa only [Metric.mem_ball,dist_zero_right] using hzn⟩
  obtain ⟨δ,hδ,hδs⟩ := Metric.mem_nhds_iff.mp he
  refine ⟨δ,hδ,?_⟩
  intro u v hu hv
  apply hδs (a := (u,v))
  simpa only [Metric.mem_ball,Prod.dist_eq,dist_eq_norm,Prod.norm_def,Prod.fst_sub,Prod.snd_sub,max_lt_iff] using And.intro hu hv

theorem negative_log_quotient_on_strip {q D : ℂ → ℂ} {b : ℝ} (hb : 0 < b)
    (ha : ∀ᶠ z in stripInfinity,AnalyticAt ℂ q z)
    (hz : ∀ᶠ z in stripInfinity,q z≠0)
    (hd : Tendsto (fun z => deriv q z/q z) stripInfinity (𝓝 0))
    (hD : Tendsto D stripInfinity (𝓝 (b:ℂ)))
    (hqr : ∀ᶠ t : ℝ in atTop,(q (t:ℂ)).im=0 ∧ (q (t:ℂ)).re < 0)
    (hq0 : Tendsto (fun t : ℝ => q (t:ℂ)) atTop (𝓝 0))
    {R B : ℝ} (hR : 0 < R) (hB : 0 < B) :
    ∃ A : ℝ,∀ t : ℝ,A < t → ∀ z∈horizontalTail A R,‖z-(t:ℂ)‖ ≤ B →
      -1 ≤ (q z/D z).re ∧ (q z/D z).re < 0 := by
  obtain ⟨δ,hδ,hnear⟩ := positive_quotient_neighborhood hb
  obtain ⟨A₁,hA₁⟩ := relative_strip_pair_estimate ha hz hd hR hB
    (show 0 < δ/(2*B) by positivity)
  have heD : ∀ᶠ z in stripInfinity,‖D z-(b:ℂ)‖ < δ := by
    simpa only [dist_eq_norm] using (Metric.tendsto_nhds.mp hD) δ hδ
  obtain ⟨A₂,hA₂⟩ := eventually_stripInfinity.mp heD R
  have heq : ∀ᶠ t : ℝ in atTop,‖q (t:ℂ)‖ < b/2 := by
    simpa only [dist_zero_right] using (Metric.tendsto_nhds.mp hq0) (b/2) (by positivity)
  obtain ⟨A₃,hA₃⟩ := eventually_atTop.mp (hqr.and heq)
  let A := max (max A₁ A₂) A₃
  refine ⟨A,?_⟩
  intro t ht z hzA hdist
  have ht₁ : A₁ < t := lt_of_le_of_lt ((le_max_left A₁ A₂).trans (le_max_left _ _)) ht
  have ht₃ : A₃ ≤ t := (le_max_right _ _).trans ht.le
  have hz₁ : z∈horizontalTail A₁ R :=
    ⟨lt_of_le_of_lt ((le_max_left A₁ A₂).trans (le_max_left _ _)) hzA.1,hzA.2⟩
  have hz₂ : z∈horizontalTail A₂ R :=
    ⟨lt_of_le_of_lt ((le_max_right A₁ A₂).trans (le_max_left _ _)) hzA.1,hzA.2⟩
  obtain ⟨hqtn,hratio⟩ := hA₁ z hz₁ (t:ℂ) ⟨ht₁,by simpa using hR⟩ hdist
  have hratio' : ‖q z/q (t:ℂ)-1‖ < δ := by
    have hh := mul_le_mul_of_nonneg_left hdist (by positivity : 0 ≤ δ/(2*B))
    have he : δ/(2*B)*B=δ/2 := by field_simp
    rw [he] at hh
    exact (hratio.trans hh).trans_lt (by linarith)
  obtain ⟨hpos,hbn⟩ := hnear (q z/q (t:ℂ)) (D z) hratio' (hA₂ z hz₂)
  have hqt := hA₃ t ht₃
  have heq : q z/D z=q (t:ℂ)*((q z/q (t:ℂ))/D z) := by field_simp
  have hneg : (q z/D z).re < 0 := by
    rw [heq,Complex.mul_re,hqt.1.1,zero_mul,sub_zero]
    exact mul_neg_of_neg_of_pos hqt.1.2 hpos
  have hn : ‖q z/D z‖ < 1 := by
    rw [heq,norm_mul]
    have hh' := mul_lt_mul_of_pos_right hqt.2 (by positivity : 0 < 2/b)
    have hid : (b/2)*(2/b)=(1:ℝ) := by field_simp
    rw [hid] at hh'
    exact (mul_le_mul_of_nonneg_left hbn.le (norm_nonneg _)).trans_lt hh'
  exact ⟨by have hh := (Complex.abs_re_le_norm (q z/D z)).trans hn.le
            exact (abs_le.mp hh).1,hneg⟩

end DegeneratingTrees.Clock

 

 

 

open Set Filter Topology Complex
namespace DegeneratingTrees.Clock

lemma arg_exp_eq_im_of_abs_lt_pi {w : ℂ} (hw : |w.im| < Real.pi) :
    (Complex.exp w).arg=w.im := by
  rw [Complex.arg_exp]
  apply (toIocMod_eq_self Real.two_pi_pos).mpr
  constructor
  · exact (abs_lt.mp hw).1
  · linarith [(abs_lt.mp hw).2]

 

theorem log_clock_phase_contraction {G : ℂ → ℂ} {A : ℝ}
    (hG : AnalyticOnNhd ℂ G (horizontalTail A (Real.pi/2)))
    (hr : ∀ t : ℝ,A<t → (G (t:ℂ)).im=0)
    (hder : ∀ w∈horizontalTail A (Real.pi/2),-1 ≤ (deriv G w).re ∧ (deriv G w).re ≤ 0)
    {w : ℂ} (hw : w∈horizontalTail A (Real.pi/2)) :
    |(Complex.exp (w+G w)).arg| ≤ |w.im| := by
  have hθ (t : ℝ) (ht : t∈uIcc (0:ℝ) w.im) :
      (w.re:ℂ)+Complex.I*(t:ℂ)∈horizontalTail A (Real.pi/2) := by
    refine ⟨by simpa using hw.1,?_⟩
    have hab : |t| ≤ |w.im| := by
      rcases le_total (0:ℝ) w.im with h | h
      · rw [uIcc_of_le h] at ht
        rw [abs_of_nonneg ht.1,abs_of_nonneg h]; exact ht.2
      · rw [uIcc_of_ge h] at ht
        rw [abs_of_nonpos ht.2,abs_of_nonpos h]; linarith [ht.1]
    simpa using hab.trans_lt hw.2
  have hphase := vertical_phase_contraction (fun t ht => hG _ (hθ t ht))
    (hr _ hw.1) (fun t ht => hder _ (hθ t ht))
  have hwform : (w.re:ℂ)+Complex.I*(w.im:ℂ)=w := by
    simpa only [mul_comm] using Complex.re_add_im w
  rw [hwform] at hphase
  have hpi : |(w+G w).im| < Real.pi := by
    simp only [Complex.add_im]
    exact hphase.trans_lt (hw.2.trans (by linarith [Real.pi_pos]))
  rw [arg_exp_eq_im_of_abs_lt_pi hpi,Complex.add_im]
  exact hphase

 

lemma log_inverse_ratio_derivative {H J Q X : ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) {w : ℂ} (hw : w∈U)
    (hX : AnalyticAt ℂ X w) (hH : AnalyticAt ℂ H (X w))
    (hQ : AnalyticAt ℂ Q (X w))
    (he : ∀ v∈U,H (X v)=Complex.exp v)
    (hQd : deriv Q (X w)=deriv J (X w)/J (X w))
    (hHne : deriv H (X w)≠0) :
    deriv (fun v => Q (X v)) w =
      (deriv J (X w)/J (X w))/(deriv H (X w)/H (X w)) := by
  have hd := hH.differentiableAt.hasDerivAt.comp w hX.differentiableAt.hasDerivAt
  have heq : (fun v => H (X v)) =ᶠ[𝓝 w] Complex.exp :=
    Filter.Eventually.mono (hU.mem_nhds hw) (fun v hv => he v hv)
  have hh := (hd.congr_of_eventuallyEq heq.symm).unique (Complex.hasDerivAt_exp w)
  have hXd : deriv X w=Complex.exp w/deriv H (X w) := by
    apply (eq_div_iff hHne).mpr
    simpa only [mul_comm] using hh
  change deriv (Q ∘ X) w = _
  rw [(hQ.differentiableAt.hasDerivAt.comp w hX.differentiableAt.hasDerivAt).deriv,hQd,hXd,←he w hw]
  field_simp [hHne,show H (X w)≠0 by rw [he w hw]; exact Complex.exp_ne_zero w]

end DegeneratingTrees.Clock

 

 

 

open Set Filter Topology Complex
namespace DegeneratingTrees.Clock

theorem equal_exponent_inward {H J : ℂ → ℂ} {b : ℝ} (hb : 0<b)
    (hHa : ∀ᶠ z in stripInfinity,AnalyticAt ℂ H z)
    (hH0 : ∀ᶠ z in stripInfinity,H z≠0)
    (hHr : ∀ᶠ t : ℝ in atTop,(H (t:ℂ)).im=0 ∧ 0<(H (t:ℂ)).re)
    (hHt : Tendsto (fun t : ℝ => (H (t:ℂ)).re) atTop atTop)
    (hHd : Tendsto (fun z => deriv H z/H z) stripInfinity (𝓝 (b:ℂ)))
    (hJa : ∀ᶠ z in stripInfinity,AnalyticAt ℂ J z)
    (hJ0 : ∀ᶠ z in stripInfinity,J z≠0)
    (hJr : ∀ᶠ t : ℝ in atTop,(J (t:ℂ)).im=0 ∧ 0<(J (t:ℂ)).re)
    (hqa : ∀ᶠ z in stripInfinity,AnalyticAt ℂ (fun z => deriv J z/J z) z)
    (hqne : ∀ᶠ z in stripInfinity,deriv J z/J z≠0)
    (hqd : Tendsto (fun z => deriv (fun z => deriv J z/J z) z/(deriv J z/J z)) stripInfinity (𝓝 0))
    (hqr : ∀ᶠ t : ℝ in atTop,(deriv J (t:ℂ)/J (t:ℂ)).im=0 ∧ (deriv J (t:ℂ)/J (t:ℂ)).re<0)
    (hq0 : Tendsto (fun t : ℝ => deriv J (t:ℂ)/J (t:ℂ)) atTop (𝓝 0)) :
    ∃ (T : ℝ) (x : ℂ → ℂ),0<T ∧
      AnalyticOnNhd ℂ x {w | 0<w.re ∧ T<‖w‖} ∧
      (∀ w : ℂ,0<w.re → T<‖w‖ → H (x w)=w) ∧
      (∀ᶠ t : ℝ in atTop,x (H (t:ℂ))=(t:ℂ)) ∧
      (∀ r : ℝ,T<r → (x (r:ℂ)).im=0) ∧
      Tendsto (fun r : ℝ => (x (r:ℂ)).re) atTop atTop ∧
      Tendsto x sectorInfinity stripInfinity ∧
      (∀ ε : ℝ,0<ε → ∃ U : ℝ,∀ w : ℂ,0<w.re → U<‖w‖ →
        ‖x w-x (‖w‖:ℂ)-Complex.I*(w.arg/b:ℝ)‖≤ε*|w.arg|) ∧
      Tendsto (fun w => w*deriv x w) sectorInfinity (𝓝 ((b:ℂ)⁻¹)) ∧
      ∃ U : ℝ,∀ w : ℂ,0<w.re → U<‖w‖ → |(w*J (x w)).arg|≤|w.arg| := by
  obtain ⟨T,hT,x,hxa,hleft,hright,hxr,hxt,hxto,hinc,hxd⟩ :=
    positive_exponential_inverse_asymptotic hb hHa hH0 hHr hHt hHd
  obtain ⟨R,B,hR,hB,hfull⟩ := inverse_halfplane_strip hb
    ((eventually_gt_atTop T).mono fun r hr => hxr r hr) hxt (by simpa only [one_mul] using hinc 1 zero_lt_one)
  obtain ⟨A₁,hA₁⟩ := negative_log_quotient_on_strip hb hqa hqne hqd hHd hqr hq0 hR hB
  obtain ⟨A₂,hA₂⟩ := eventually_stripInfinity.mp ((hJa.and hJ0).and hHa) R
  obtain ⟨A₃,hA₃⟩ := eventually_atTop.mp hJr
  let A := max A₁ (max A₂ A₃)
  have hAA₁ : A₁≤A := le_max_left _ _
  have hAA₂ : A₂≤A := (le_max_left _ _).trans (le_max_right _ _)
  have hAA₃ : A₃≤A := (le_max_right _ _).trans (le_max_right _ _)
  have hJ (z : ℂ) (hz : z∈horizontalTail A R) : AnalyticAt ℂ J z ∧ J z≠0 :=
    (hA₂ z ⟨lt_of_le_of_lt hAA₂ hz.1,hz.2⟩).1
  obtain ⟨Q,hQa,hQe,hQd,hQr⟩ := analytic_real_log_on_strip hR
    (fun z hz => (hJ z hz).1) (fun z hz => (hJ z hz).2)
    (fun t ht => hA₃ t (hAA₃.trans ht.le))
  obtain ⟨U,hU,hUf⟩ := hfull A
  let V := max T U
  have hV : 0<V := hT.trans_le (le_max_left _ _)
  let C := Real.log V
  let X : ℂ → ℂ := fun w => x (Complex.exp w)
  have hexp (w : ℂ) (hw : w∈horizontalTail C (Real.pi/2)) :
      0<(Complex.exp w).re ∧ V<‖Complex.exp w‖ := by
    refine ⟨exp_horizontalTail_right hw,?_⟩
    rw [Complex.norm_exp,←Real.exp_log hV]
    exact Real.exp_strictMono hw.1
  have hXmap (w : ℂ) (hw : w∈horizontalTail C (Real.pi/2)) :
      A<(x (‖Complex.exp w‖:ℂ)).re ∧ X w∈horizontalTail A R ∧
      ‖X w-((x (‖Complex.exp w‖:ℂ)).re:ℂ)‖≤B := by
    exact hUf _ (hexp w hw).1 (lt_of_le_of_lt (le_max_right _ _) (hexp w hw).2)
  have hXa : AnalyticOnNhd ℂ X (horizontalTail C (Real.pi/2)) := by
    intro w hw
    exact (hxa _ ⟨(hexp w hw).1,lt_of_le_of_lt (le_max_left _ _) (hexp w hw).2⟩).comp analyticAt_cexp
  have hXe (w : ℂ) (hw : w∈horizontalTail C (Real.pi/2)) : H (X w)=Complex.exp w :=
    hleft _ (hexp w hw).1 (lt_of_le_of_lt (le_max_left _ _) (hexp w hw).2)
  have hXr (t : ℝ) (ht : C<t) : X (t:ℂ)=((X (t:ℂ)).re:ℂ) := by
    have hw : (t:ℂ)∈horizontalTail C (Real.pi/2) := ⟨ht,by simp; positivity⟩
    have hnorm : ‖Complex.exp (t:ℂ)‖=Real.exp t := by rw [Complex.norm_exp,Complex.ofReal_re]
    have htT : T<Real.exp t := (le_max_left T U).trans_lt (by simpa only [hnorm] using (hexp _ hw).2)
    refine Complex.ext rfl ?_
    change (x (Complex.exp (t:ℂ))).im=0
    rw [←Complex.ofReal_exp]
    exact hxr _ htT
  have hGa : AnalyticOnNhd ℂ (fun w => Q (X w)) (horizontalTail C (Real.pi/2)) :=
    fun w hw => (hQa _ (hXmap w hw).2.1).comp (hXa w hw)
  have hGr (t : ℝ) (ht : C<t) : (Q (X (t:ℂ))).im=0 := by
    have hw : (t:ℂ)∈horizontalTail C (Real.pi/2) := ⟨ht,by simp; positivity⟩
    have hxA := (hXmap _ hw).2.1.1
    rw [hXr t ht,hQr _ hxA]
    rfl
  have hGd (w : ℂ) (hw : w∈horizontalTail C (Real.pi/2)) :
      -1≤(deriv (fun w => Q (X w)) w).re ∧ (deriv (fun w => Q (X w)) w).re≤0 := by
    have hmap := hXmap w hw
    have hHaw : AnalyticAt ℂ H (X w) := (hA₂ _ ⟨hAA₂.trans_lt hmap.2.1.1,hmap.2.1.2⟩).2
    have hHne : deriv H (X w)≠0 := by
      have heq : (fun v => H (X v)) =ᶠ[𝓝 w] Complex.exp :=
        Filter.Eventually.mono ((horizontalTail_open C (Real.pi/2)).mem_nhds hw) (fun v hv => hXe v hv)
      have hd := hHaw.differentiableAt.hasDerivAt.comp w (hXa w hw).differentiableAt.hasDerivAt
      have he := (hd.congr_of_eventuallyEq heq.symm).unique (Complex.hasDerivAt_exp w)
      intro hh
      have hh' := Complex.exp_ne_zero w
      simp only [hh,zero_mul] at he
      exact hh' he.symm
    rw [log_inverse_ratio_derivative (horizontalTail_open C (Real.pi/2)) hw (hXa w hw)
      hHaw (hQa _ hmap.2.1) hXe (hQd _ hmap.2.1) hHne]
    have hh := hA₁ _ (hAA₁.trans_lt hmap.1) _
      ⟨hAA₁.trans_lt hmap.2.1.1,hmap.2.1.2⟩ hmap.2.2
    exact ⟨hh.1,hh.2.le⟩
  refine ⟨T,x,hT,hxa,hleft,hright,hxr,hxt,hxto,hinc,hxd,V,?_⟩
  intro w hw hwV
  have hw0 : w≠0 := by intro he; simp [he] at hw
  have hwlog : Complex.log w∈horizontalTail C (Real.pi/2) := by
    constructor
    · rw [Complex.log_re]
      exact Real.log_lt_log hV hwV
    · rw [Complex.log_im]
      exact Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hw)
  have hh := log_clock_phase_contraction hGa hGr hGd hwlog
  rw [Complex.exp_add,hQe _ (hXmap _ hwlog).2.1,Complex.exp_log hw0] at hh
  simpa only [X,Complex.exp_log hw0,Complex.log_im] using hh

end DegeneratingTrees.Clock
end

end OAI
