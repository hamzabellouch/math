import Mathlib
import OAI.Analysis.PathSelection.ClockInverses

namespace OAI

/-! Strip and exponential inverse asymptotics and logarithmic radii. -/

noncomputable section
open Set Filter Topology Metric Polynomial
open scoped BigOperators NNReal ENNReal

open Set Filter Topology Complex
open scoped NNReal
namespace DegeneratingTrees.Clock

lemma inverse_strip_tail {A R T d : ℝ} {f g : ℂ → ℂ}
    (hd : 0<d) (hdR : 2*d<R)
    (hf : AnalyticOnNhd ℂ f (horizontalTail A R))
    (hder : ∀ z∈horizontalTail A R,‖deriv f z-1‖≤(1/2:ℝ))
    (hgb : ∀ w∈horizontalTail T d,∃ t : ℝ,A+2*d<t ∧
      (f (t:ℂ)).re=w.re ∧ ‖g w-(t:ℂ)‖≤2*|w.im|) (B : ℝ) :
    ∃ U : ℝ,T≤U ∧ ∀ w∈horizontalTail U d,
      B<(g w).re ∧ ∃ t : ℝ,B<t ∧ A<t ∧ (f (t:ℂ)).re=w.re ∧
        ‖g w-(t:ℂ)‖≤2*|w.im| := by
  let a := A+d
  have ha : A<a := by dsimp [a]; linarith
  have hR : 0<R := lt_trans (by positivity) hdR
  have haS : (a:ℂ)∈horizontalTail A R := ⟨ha,by simpa using hR⟩
  have happ := approximates_identity_of_deriv (horizontalTail_convex A R) hf
    (c := (1/2:ℝ≥0)) (by simpa using hder)
  have hupper (t : ℝ) (ht : A+2*d<t) : (f (t:ℂ)).re≤(f (a:ℂ)).re+2*(t-a) := by
    have hat : a<t := by dsimp [a]; linarith
    have htS : (t:ℂ)∈horizontalTail A R := ⟨by change A<t; linarith,by simpa using hR⟩
    have hh := happ (t:ℂ) htS (a:ℂ) haS
    change ‖f (t:ℂ)-f (a:ℂ)-((t:ℂ)-(a:ℂ))‖≤(1/2:ℝ)*‖(t:ℂ)-(a:ℂ)‖ at hh
    have hn : ‖(t:ℂ)-(a:ℂ)‖=t-a := by rw [←Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (sub_pos.mpr hat)]
    rw [hn] at hh
    have hnorm : ‖f (t:ℂ)-f (a:ℂ)‖≤(1/2:ℝ)*(t-a)+(t-a) := by
      calc
        ‖f (t:ℂ)-f (a:ℂ)‖ = ‖(f (t:ℂ)-f (a:ℂ)-((t:ℂ)-(a:ℂ)))+((t:ℂ)-(a:ℂ))‖ := by congr 1; ring
        _ ≤ ‖f (t:ℂ)-f (a:ℂ)-((t:ℂ)-(a:ℂ))‖+‖(t:ℂ)-(a:ℂ)‖ := norm_add_le _ _
        _ ≤ (1/2:ℝ)*(t-a)+(t-a) := by rw [hn]; exact add_le_add hh le_rfl
    have hr := (le_abs_self (f (t:ℂ)-f (a:ℂ)).re).trans
      ((Complex.abs_re_le_norm _).trans hnorm)
    simp only [Complex.sub_re] at hr
    linarith
  let U := max T ((f (a:ℂ)).re+2*(B+2*d-a))
  refine ⟨U,le_max_left _ _,?_⟩
  intro w hw
  have hwT : w∈horizontalTail T d := ⟨(le_max_left _ _).trans_lt hw.1,hw.2⟩
  obtain ⟨t,ht,hft,hgt⟩ := hgb w hwT
  have hbt : B+2*d<t := by
    have hl := hupper t ht
    rw [hft] at hl
    have := (le_max_right T ((f (a:ℂ)).re+2*(B+2*d-a))).trans_lt hw.1
    linarith
  have hgre : B<(g w).re := by
    have hh := (Complex.abs_re_le_norm (g w-(t:ℂ))).trans hgt
    rw [Complex.sub_re,Complex.ofReal_re] at hh
    have hl := (abs_le.mp hh).1
    linarith [hw.2]
  exact ⟨hgre,t,by linarith,by linarith,hft,hgt⟩

 

theorem inverse_strip_asymptotic {A R T d : ℝ} {f g : ℂ → ℂ}
    (hd : 0<d) (hdR : 2*d<R)
    (hf : AnalyticOnNhd ℂ f (horizontalTail A R))
    (hder : ∀ z∈horizontalTail A R,‖deriv f z-1‖≤(1/2:ℝ))
    (hlim : ∀ ε : ℝ,0<ε → ∃ B : ℝ,∀ z∈horizontalTail B R,‖deriv f z-1‖≤ε)
    (hreal : ∀ t : ℝ,A<t → (f (t:ℂ)).im=0)
    (hgf : ∀ w∈horizontalTail T d,g w∈horizontalTail A R ∧ f (g w)=w)
    (hfg : ∀ t : ℝ,A<t → f (t:ℂ)∈horizontalTail T d → g (f (t:ℂ))=(t:ℂ))
    (hgb : ∀ w∈horizontalTail T d,∃ t : ℝ,A+2*d<t ∧
      (f (t:ℂ)).re=w.re ∧ ‖g w-(t:ℂ)‖≤2*|w.im|) :
    ∀ ε : ℝ,0<ε → ∃ U : ℝ,T≤U ∧ ∀ w∈horizontalTail U d,
      ‖g w-g (w.re:ℂ)-Complex.I*(w.im:ℂ)‖≤ε*|w.im| := by
  intro ε hε
  obtain ⟨B,hB⟩ := hlim (ε/2) (by positivity)
  let C := max A B
  obtain ⟨U,hUT,hU⟩ := inverse_strip_tail hd hdR hf hder hgb C
  refine ⟨U,hUT,?_⟩
  intro w hw
  obtain ⟨hgw,t,htC,htA,hft,hgt⟩ := hU w hw
  have hwT : w∈horizontalTail T d := ⟨hUT.trans_lt hw.1,hw.2⟩
  have htS : (t:ℂ)∈horizontalTail C R := ⟨htC,by simpa using (show 0<R by linarith)⟩
  have hgS : g w∈horizontalTail C R := ⟨hgw,(hgf w hwT).1.2⟩
  have hsub : horizontalTail C R ⊆ horizontalTail A R :=
    fun z hz => ⟨(le_max_left _ _).trans_lt hz.1,hz.2⟩
  have hdb (z : ℂ) (hz : z∈horizontalTail C R) : ‖deriv f z-1‖≤ε/2 :=
    hB z ⟨(le_max_right _ _).trans_lt hz.1,hz.2⟩
  have happ := approximates_identity_of_deriv (horizontalTail_convex C R) (hf.mono hsub)
    (c := ⟨ε/2,by positivity⟩) hdb
  have hh := happ (g w) hgS (t:ℂ) htS
  change ‖f (g w)-f (t:ℂ)-(g w-(t:ℂ))‖≤(ε/2)*‖g w-(t:ℂ)‖ at hh
  have hft' : f (t:ℂ)=(w.re:ℂ) := Complex.ext hft (by simpa using hreal t htA)
  have hwreal : (w.re:ℂ)∈horizontalTail T d := ⟨hwT.1,by simpa using hd⟩
  have hgr : g (w.re:ℂ)=(t:ℂ) := by rw [←hft']; exact hfg t htA (by rwa [hft'])
  rw [(hgf w hwT).2,hft'] at hh
  have he : w-(w.re:ℂ)=Complex.I*(w.im:ℂ) := by apply Complex.ext <;> simp
  rw [he] at hh
  rw [hgr,show g w-(t:ℂ)-Complex.I*(w.im:ℂ)=-(Complex.I*(w.im:ℂ)-(g w-(t:ℂ))) by ring,norm_neg]
  calc
    ‖Complex.I*(w.im:ℂ)-(g w-(t:ℂ))‖ ≤ (ε/2)*‖g w-(t:ℂ)‖ := hh
    _ ≤ (ε/2)*(2*|w.im|) := mul_le_mul_of_nonneg_left hgt (by positivity)
    _ = ε*|w.im| := by ring

end DegeneratingTrees.Clock

 

 

 

open Set Filter Topology Complex
namespace DegeneratingTrees.Clock

lemma tendsto_stripInfinity_of_re_and_bounded_im {ι : Type*} {l : Filter ι}
    {x : ι → ℂ} (hre : Tendsto (fun t => (x t).re) l atTop)
    {C : ℝ} (him : ∀ᶠ t in l,|(x t).im|<C) : Tendsto x l stripInfinity := by
  apply Filter.tendsto_def.mpr
  intro s hs
  obtain ⟨A,hA⟩ := hs C
  filter_upwards [hre.eventually (eventually_gt_atTop A),him] with t ht hi
  exact hA ⟨ht,hi⟩

 

theorem positive_exponential_inverse_asymptotic {H : ℂ → ℂ} {b : ℝ} (hb : 0<b)
    (ha : ∀ᶠ z in stripInfinity,AnalyticAt ℂ H z)
    (h0 : ∀ᶠ z in stripInfinity,H z≠0)
    (hr : ∀ᶠ t : ℝ in atTop,(H (t:ℂ)).im=0 ∧ 0<(H (t:ℂ)).re)
    (hlim : Tendsto (fun t : ℝ => (H (t:ℂ)).re) atTop atTop)
    (hq : Tendsto (fun z => deriv H z/H z) stripInfinity (𝓝 (b:ℂ))) :
    ∃ T : ℝ,0<T ∧ ∃ x : ℂ → ℂ,
      AnalyticOnNhd ℂ x {w | 0<w.re ∧ T<‖w‖} ∧
      (∀ w : ℂ,0<w.re → T<‖w‖ → H (x w)=w) ∧
      (∀ᶠ t : ℝ in atTop,x (H (t:ℂ))=(t:ℂ)) ∧
      (∀ r : ℝ,T<r → (x (r:ℂ)).im=0) ∧
      Tendsto (fun r : ℝ => (x (r:ℂ)).re) atTop atTop ∧
      Tendsto x sectorInfinity stripInfinity ∧
      (∀ ε : ℝ,0<ε → ∃ U : ℝ,∀ w : ℂ,0<w.re → U<‖w‖ →
        ‖x w-x (‖w‖:ℂ)-Complex.I*(w.arg/b:ℝ)‖≤ε*|w.arg|) ∧
      Tendsto (fun w => w*deriv x w) sectorInfinity (𝓝 ((b:ℂ)⁻¹)) := by
  let d := Real.pi/b+1
  let R := 2*d+1
  have hd : 0<d := by dsimp [d]; positivity
  have hdR : 2*d<R := by dsimp [R]; linarith
  have hR : 0<R := by linarith
  have hb0 : (b:ℂ)≠0 := by exact_mod_cast hb.ne'
  obtain ⟨A,T₀,f,g,hfa,hfe,hfn,hfd,hfr,hga,hgf,hfg,hgb⟩ :=
    normalized_log_inverse hb hd hdR ha h0 hr hlim hq
  let T := Real.exp (b*T₀)
  let x : ℂ → ℂ := fun w => g (Complex.log w/(b:ℂ))
  have hmap (U : ℝ) (w : ℂ) (hT : Real.exp (b*U)<‖w‖) :
      Complex.log w/(b:ℂ)∈horizontalTail U d := by
    constructor
    · rw [Complex.div_ofReal_re,Complex.log_re]
      apply (lt_div_iff₀ hb).mpr
      have hh := Real.log_lt_log (Real.exp_pos (b*U)) hT
      rw [Real.log_exp] at hh
      simpa only [mul_comm] using hh
    · rw [Complex.div_ofReal_im,Complex.log_im,abs_div,abs_of_pos hb]
      have hh := div_le_div_of_nonneg_right (Complex.abs_arg_le_pi w) hb.le
      dsimp [d]
      linarith
  have hxa : AnalyticOnNhd ℂ x {w | 0<w.re ∧ T<‖w‖} := by
    intro w hw
    exact (hga _ (hmap T₀ w hw.2)).comp (f := fun w => Complex.log w/(b:ℂ))
      ((analyticAt_clog (Complex.mem_slitPlane_iff.mpr (Or.inl hw.1))).div_const)
  have hxe (w : ℂ) (hw : 0<w.re) (hT : T<‖w‖) : H (x w)=w := by
    have hh := hgf _ (hmap T₀ w hT)
    rw [show H (x w)=Complex.exp ((b:ℂ)*f (x w)) from (hfe _ hh.1).symm,
      hh.2,mul_div_cancel₀ _ hb0]
    exact Complex.exp_log (by intro he; simp [he] at hw)
  have hright : ∀ᶠ t : ℝ in atTop,x (H (t:ℂ))=(t:ℂ) := by
    have htlim : Tendsto (fun t : ℝ => (f (t:ℂ)).re) atTop atTop := by
      apply ((Real.tendsto_log_atTop.comp hlim).atTop_div_const hb).congr'
      filter_upwards [eventually_gt_atTop A] with t ht
      rw [hfr t ht,Complex.ofReal_re]
      rfl
    filter_upwards [eventually_gt_atTop A,hr,htlim.eventually (eventually_gt_atTop T₀)] with t ht hrt hft
    have hfstrip : f (t:ℂ)∈horizontalTail T₀ d := ⟨hft,by rw [hfr t ht]; simpa using hd⟩
    have hHreal : H (t:ℂ)=((H (t:ℂ)).re:ℂ) := Complex.ext (by simp) (by simp [hrt.1])
    have hh : Complex.log (H (t:ℂ))/(b:ℂ)=f (t:ℂ) := by
      rw [hHreal,←Complex.ofReal_log hrt.2.le,hfr t ht,Complex.ofReal_div]
    dsimp [x]; rw [hh]; exact hfg t ht hfstrip
  have hdom : ∀ᶠ w in sectorInfinity,0<w.re ∧ T<‖w‖ :=
    SectorEventually.realpart_pos.and (tendsto_norm_sectorInfinity.eventually (eventually_gt_atTop T))
  have hxre : Tendsto (fun w => (x w).re) sectorInfinity atTop := by
    apply Filter.tendsto_atTop.mpr
    intro B
    obtain ⟨U,hUT,hU⟩ := inverse_strip_tail hd hdR hfa hfn hgb B
    filter_upwards [tendsto_norm_sectorInfinity.eventually (eventually_gt_atTop (Real.exp (b*U)))] with w hw
    exact (hU _ (hmap U w hw)).1.le
  have hxto : Tendsto x sectorInfinity stripInfinity := by
    apply tendsto_stripInfinity_of_re_and_bounded_im hxre (C := R)
    filter_upwards [hdom] with w hw
    exact (hgf _ (hmap T₀ w hw.2)).1.2
  have hreal (r : ℝ) (hTr : T<r) : (x (r:ℂ)).im=0 := by
    have hrpos : 0<r := (Real.exp_pos _).trans hTr
    have hnorm : ‖(r:ℂ)‖=r := by simp only [Complex.norm_real,Real.norm_eq_abs,abs_of_pos hrpos]
    obtain ⟨t,ht,htr,htb⟩ := hgb _ (hmap T₀ (r:ℂ) (by simpa only [hnorm] using hTr))
    have him : (Complex.log (r:ℂ)/(b:ℂ)).im=0 := by
      rw [←Complex.ofReal_log hrpos.le,Complex.div_ofReal_im,Complex.ofReal_im,zero_div]
    rw [him,abs_zero,mul_zero] at htb
    have he : x (r:ℂ)=(t:ℂ) := sub_eq_zero.mp (norm_le_zero_iff.mp htb)
    simp only [he,Complex.ofReal_im]
  refine ⟨T,Real.exp_pos _,x,hxa,hxe,hright,hreal,hxre.comp tendsto_real_sectorInfinity,hxto,?_,?_⟩
  · intro ε hε
    have hdf : ∀ δ : ℝ,0<δ → ∃ B : ℝ,∀ z∈horizontalTail B R,‖deriv f z-1‖≤δ := by
      intro δ hδ
      have hl : ∀ᶠ z in stripInfinity,‖deriv H z/H z-(b:ℂ)‖<δ*b := by
        simpa only [dist_eq_norm] using Metric.tendsto_nhds.mp hq (δ*b) (mul_pos hδ hb)
      obtain ⟨B,hB⟩ := eventually_stripInfinity.mp hl R
      refine ⟨max A B,?_⟩
      intro z hz
      have hzA : z∈horizontalTail A R := ⟨(le_max_left _ _).trans_lt hz.1,hz.2⟩
      have hzB : z∈horizontalTail B R := ⟨(le_max_right _ _).trans_lt hz.1,hz.2⟩
      rw [hfd z hzA,show (deriv H z/H z)/(b:ℂ)-1=(deriv H z/H z-(b:ℂ))/(b:ℂ) by field_simp]
      rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hb]
      exact (div_le_iff₀ hb).mpr (hB z hzB).le
    obtain ⟨U,hUT,hU⟩ := inverse_strip_asymptotic hd hdR hfa hfn hdf
      (fun t ht => by rw [hfr t ht]; simp) hgf hfg hgb (ε*b) (mul_pos hε hb)
    refine ⟨Real.exp (b*U),?_⟩
    intro w hw hwU
    have hn : 0<‖w‖ := (Real.exp_pos _).trans hwU
    have he : Complex.log (‖w‖:ℂ)/(b:ℂ)=((Complex.log w/(b:ℂ)).re:ℂ) := by
      rw [←Complex.ofReal_log hn.le,Complex.div_ofReal_re,Complex.log_re,Complex.ofReal_div]
    have hh := hU _ (hmap U w hwU)
    change ‖g (Complex.log w/(b:ℂ))-g ((Complex.log w/(b:ℂ)).re:ℂ)-
      Complex.I*((Complex.log w/(b:ℂ)).im:ℂ)‖≤_ at hh
    simp only [Complex.div_ofReal_im,Complex.log_im,abs_div,abs_of_pos hb] at hh
    have hc : ε*b*(|w.arg|/b)=ε*|w.arg| := by field_simp
    rw [hc] at hh
    simpa only [x,he] using hh
  · have heq : (fun w => w*deriv x w) =ᶠ[sectorInfinity] (fun w => (deriv H (x w)/H (x w))⁻¹) := by
      filter_upwards [hdom,hxto.eventually ha,hxto.eventually h0] with w hw hHa hH0
      have hopen : IsOpen {v : ℂ | 0<v.re ∧ T<‖v‖} :=
        (isOpen_lt continuous_const Complex.continuous_re).inter (isOpen_lt continuous_const continuous_norm)
      have hident : (fun v => H (x v)) =ᶠ[𝓝 w] id :=
        Filter.Eventually.mono (hopen.mem_nhds hw) (fun v hv => hxe v hv.1 hv.2)
      have hh := ((hHa.differentiableAt.hasDerivAt).comp w (hxa w hw).differentiableAt.hasDerivAt)
      have hmul : deriv H (x w)*deriv x w=1 := (hh.congr_of_eventuallyEq hident.symm).unique (hasDerivAt_id w)
      have hderne : deriv H (x w)≠0 := by intro hz; simp [hz] at hmul
      rw [div_eq_mul_inv,mul_inv_rev,inv_inv,hxe w hw.1 hw.2]
      congr 1
      apply (mul_left_cancel₀ hderne)
      rw [hmul,mul_inv_cancel₀ hderne]
    exact (((hq.comp hxto).inv₀ hb0)).congr' heq.symm

end DegeneratingTrees.Clock

 

 

 

open Set Filter Topology Complex
namespace DegeneratingTrees.Clock

lemma complex_real_limit {G : ℝ → ℂ} {c : ℝ}
    (hr : ∀ᶠ r : ℝ in atTop,(G r).im=0)
    (ht : Tendsto (fun r => (G r).re) atTop (𝓝 c)) : Tendsto G atTop (𝓝 (c:ℂ)) := by
  apply (Complex.continuous_ofReal.tendsto c |>.comp ht).congr'
  exact hr.mono (fun r hr => Complex.ext (by simp) (by simpa using hr.symm))

theorem logarithmic_radius_derivative {G : ℂ → ℂ} {a : ℝ}
    (ha : ∀ᶠ r : ℝ in atTop,AnalyticAt ℂ G (r:ℂ))
    (hr : ∀ᶠ r : ℝ in atTop,(G (r:ℂ)).im=0 ∧ 0<(G (r:ℂ)).re)
    (hd : Tendsto (fun r : ℝ => (r:ℂ)*deriv G (r:ℂ)/G (r:ℂ)) atTop (𝓝 (a:ℂ))) :
    (∀ᶠ s : ℝ in atTop,DifferentiableAt ℝ (fun s => Real.logb 2 (G (((2:ℝ)^s:ℝ):ℂ)).re) s) ∧
    Tendsto (deriv (fun s : ℝ => Real.logb 2 (G (((2:ℝ)^s:ℝ):ℂ)).re)) atTop (𝓝 a) ∧
    (∀ᶠ r : ℝ in atTop,(G (r:ℂ)).re=(2:ℝ)^(Real.logb 2 (G (((2:ℝ)^(Real.logb 2 r):ℝ):ℂ)).re)) := by
  have h2 : Tendsto (fun s : ℝ => (2:ℝ)^s) atTop atTop :=
    tendsto_rpow_atTop_of_base_gt_one 2 (by norm_num)
  have hlog : Real.log 2≠0 := ne_of_gt (Real.log_pos (by norm_num))
  have hder : ∀ᶠ s : ℝ in atTop,
      HasDerivAt (fun s : ℝ => Real.logb 2 (G (((2:ℝ)^s:ℝ):ℂ)).re)
        ((((2:ℝ)^s:ℝ):ℂ)*deriv G (((2:ℝ)^s:ℝ):ℂ)/G (((2:ℝ)^s:ℝ):ℂ)).re s := by
    filter_upwards [h2.eventually ha,h2.eventually hr] with s ha hr
    have hg : HasDerivAt (fun r : ℝ => (G (r:ℂ)).re) (deriv G (((2:ℝ)^s:ℝ):ℂ)).re ((2:ℝ)^s) :=
      Complex.reCLM.hasFDerivAt.comp_hasDerivAt ((2:ℝ)^s) ha.differentiableAt.hasDerivAt.comp_ofReal
    have hp : HasDerivAt (fun s : ℝ => (2:ℝ)^s) (Real.log 2*(2:ℝ)^s) s := by
      simpa using (hasDerivAt_id s).const_rpow (by norm_num : (0:ℝ)<2)
    have hh : HasDerivAt (fun s : ℝ => Real.logb 2 (G (((2:ℝ)^s:ℝ):ℂ)).re)
        ((G (((2:ℝ)^s:ℝ):ℂ)).re⁻¹*((deriv G (((2:ℝ)^s:ℝ):ℂ)).re*(Real.log 2*(2:ℝ)^s))/Real.log 2) s := by
      simpa only [Real.logb,Function.comp_def] using
        ((Real.hasDerivAt_log hr.2.ne').comp s (hg.comp s hp)).div_const (Real.log 2)
    have hreal : G (((2:ℝ)^s:ℝ):ℂ)=((G (((2:ℝ)^s:ℝ):ℂ)).re:ℂ) := Complex.ext rfl (by simpa using hr.1)
    convert hh using 1
    rw [hreal,Complex.div_ofReal_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
    simp only [Complex.ofReal_re]
    field_simp
  refine ⟨hder.mono (fun _ h => h.differentiableAt),?_,?_⟩
  · have hh := (Complex.continuous_re.tendsto (a:ℂ)).comp (hd.comp h2)
    apply hh.congr'
    exact hder.mono (fun s h => h.deriv.symm)
  · filter_upwards [hr,eventually_gt_atTop (0:ℝ)] with r hr hpos
    rw [Real.rpow_logb (by norm_num : (0:ℝ)<2) (by norm_num) hpos,
      Real.rpow_logb (by norm_num : (0:ℝ)<2) (by norm_num) hr.2]

theorem inverse_radial_logarithmic_derivative {x : ℂ → ℂ} {a : ℝ}
    (ha : ∀ᶠ r : ℝ in atTop,AnalyticAt ℂ x (r:ℂ))
    (hd : Tendsto (fun r : ℝ => (r:ℂ)*deriv x (r:ℂ)) atTop (𝓝 (a:ℂ))) :
    (∀ᶠ s : ℝ in atTop,DifferentiableAt ℝ (fun s => (x (((2:ℝ)^s:ℝ):ℂ)).re) s) ∧
    Tendsto (deriv (fun s : ℝ => (x (((2:ℝ)^s:ℝ):ℂ)).re)) atTop (𝓝 (Real.log 2*a)) := by
  have h2 : Tendsto (fun s : ℝ => (2:ℝ)^s) atTop atTop :=
    tendsto_rpow_atTop_of_base_gt_one 2 (by norm_num)
  have hder : ∀ᶠ s : ℝ in atTop,HasDerivAt (fun s : ℝ => (x (((2:ℝ)^s:ℝ):ℂ)).re)
      (Real.log 2*((((2:ℝ)^s:ℝ):ℂ)*deriv x (((2:ℝ)^s:ℝ):ℂ)).re) s := by
    filter_upwards [h2.eventually ha] with s ha
    have hg : HasDerivAt (fun r : ℝ => (x (r:ℂ)).re) (deriv x (((2:ℝ)^s:ℝ):ℂ)).re ((2:ℝ)^s) :=
      Complex.reCLM.hasFDerivAt.comp_hasDerivAt ((2:ℝ)^s) ha.differentiableAt.hasDerivAt.comp_ofReal
    have hp : HasDerivAt (fun s : ℝ => (2:ℝ)^s) (Real.log 2*(2:ℝ)^s) s := by
      simpa using (hasDerivAt_id s).const_rpow (by norm_num : (0:ℝ)<2)
    have hh : HasDerivAt (fun s : ℝ => (x (((2:ℝ)^s:ℝ):ℂ)).re)
        ((deriv x (((2:ℝ)^s:ℝ):ℂ)).re*(Real.log 2*(2:ℝ)^s)) s := hg.comp s hp
    convert hh using 1
    simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
    ring
  refine ⟨hder.mono (fun _ h => h.differentiableAt),?_⟩
  have hh := ((Complex.continuous_re.tendsto (a:ℂ)).comp (hd.comp h2)).const_mul (Real.log 2)
  apply hh.congr'
  exact hder.mono (fun s h => h.deriv.symm)

theorem inverse_composition_logarithmic_slope {F x : ℂ → ℂ} {a b : ℂ}
    (hxa : ∀ᶠ w in sectorInfinity,AnalyticAt ℂ x w)
    (hFa : ∀ᶠ z in stripInfinity,AnalyticAt ℂ F z)
    (hxto : Tendsto x sectorInfinity stripInfinity)
    (hFd : Tendsto (fun z => deriv F z/F z) stripInfinity (𝓝 a))
    (hxd : Tendsto (fun w => w*deriv x w) sectorInfinity (𝓝 b)) :
    Tendsto (fun w => w*deriv (fun w => F (x w)) w/F (x w)) sectorInfinity (𝓝 (a*b)) := by
  apply ((hFd.comp hxto).mul hxd).congr'
  filter_upwards [hxa,hxto.eventually hFa] with w hxa hFa
  have hh : HasDerivAt (fun w => F (x w)) (deriv F (x w)*deriv x w) w :=
    hFa.differentiableAt.hasDerivAt.comp w hxa.differentiableAt.hasDerivAt
  rw [hh.deriv]
  dsimp only [Function.comp_apply]
  ring

end DegeneratingTrees.Clock

 

 

 

open Set Filter Topology Complex
namespace DegeneratingTrees.Clock

theorem strip_derivative_zero_constant {J : ℂ → ℂ} {c : ℝ}
    (ha : ∀ᶠ z in stripInfinity,AnalyticAt ℂ J z)
    (hd : ∀ᶠ z in stripInfinity,deriv J z=0)
    (hr : ∀ᶠ t : ℝ in atTop,(J (t:ℂ)).im=0)
    (ht : Tendsto (fun t : ℝ => (J (t:ℂ)).re) atTop (𝓝 c)) :
    ∀ᶠ z in stripInfinity,J z=(c:ℂ) := by
  have hlim := complex_real_limit hr ht
  apply eventually_stripInfinity.mpr
  intro R
  obtain ⟨A,hA⟩ := eventually_stripInfinity.mp (ha.and hd) (max R 1)
  refine ⟨A,fun z hz => ?_⟩
  have hz' : z∈horizontalTail A (max R 1) := ⟨hz.1,hz.2.trans_le (le_max_left _ _)⟩
  have heq : ∀ᶠ t : ℝ in atTop,J (t:ℂ)=J z := by
    filter_upwards [eventually_gt_atTop A] with t ht
    exact (horizontalTail_open A (max R 1)).is_const_of_deriv_eq_zero
      (horizontalTail_convex A (max R 1)).isPreconnected
      (fun w hw => (hA w hw).1.differentiableAt.differentiableWithinAt)
      (fun w hw => (hA w hw).2)
      (show (t:ℂ)∈horizontalTail A (max R 1) from
        ⟨ht,by simp⟩) hz'
  exact tendsto_nhds_unique (tendsto_const_nhds.congr' (heq.mono (fun _ h => h.symm))) hlim

end DegeneratingTrees.Clock
end

end OAI
