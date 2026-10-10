import Mathlib
import OAI.Analysis.PathSelection.DerivativeEstimates
import OAI.Analysis.PathSelection.LossPullbacks

namespace OAI

/-! Inverse derivative absorption, exponential decay and comparable inverse charts. -/

noncomputable section
open Set Filter Topology Metric Polynomial
open scoped BigOperators NNReal ENNReal

open Set Filter Topology Complex
namespace DegeneratingTrees.Clock

lemma summable_abs_variation {a : ℕ → ℝ} {M : ℝ}
    (hb : ∀ n,|a n|≤M) (hm : Monotone a ∨ Antitone a) :
    Summable (fun n => |a (n+1)-a n|) := by
  apply summable_of_sum_range_le (fun n => abs_nonneg _) (c := 2*M)
  intro n
  rcases hm with hm | hm
  · have he : ∀ i:ℕ,|a (i+1)-a i|=a (i+1)-a i := fun i =>
      abs_of_nonneg (sub_nonneg.mpr (hm (by omega)))
    simp_rw [he]
    rw [Finset.sum_range_sub]
    linarith [(abs_le.mp (hb n)).2,(abs_le.mp (hb 0)).1]
  · have he : ∀ i:ℕ,|a (i+1)-a i|=a i-a (i+1) := fun i => by
      rw [abs_of_nonpos (sub_nonpos.mpr (hm (by omega)))]; ring
    simp_rw [he]
    rw [Finset.sum_range_sub']
    linarith [(abs_le.mp (hb 0)).2,(abs_le.mp (hb n)).1]

theorem derivative_summable_unit_shells {F : ℂ → ℂ}
    (ha : ∀ᶠ z in stripInfinity,AnalyticAt ℂ F z)
    (hr : ∀ᶠ t : ℝ in atTop,(F (t:ℂ)).im=0)
    (hz : ∀ᶠ z in stripInfinity,deriv F z≠0)
    (hd : Tendsto (fun z => deriv (deriv F) z/deriv F z) stripInfinity (𝓝 0))
    {c : ℝ} (hl : Tendsto (fun t : ℝ => (F (t:ℂ)).re) atTop (𝓝 c))
    (hm : ∃ A : ℝ,MonotoneOn (fun t : ℝ => (F (t:ℂ)).re) (Ici A) ∨
      AntitoneOn (fun t : ℝ => (F (t:ℂ)).re) (Ici A)) :
    ∃ N : ℕ,∃ w : ℕ → ℝ,(∀ n,0≤w n) ∧ Summable w ∧
      ∀ n : ℕ,∀ t : ℝ,((n+N:ℕ):ℝ)≤t → t≤((n+N:ℕ):ℝ)+2 →
        ‖deriv F (t:ℂ)‖≤w n := by
  obtain ⟨A₁,hA₁⟩ := relative_strip_pair_estimate
    (ha.mono (fun z h => h.deriv)) hz hd (show (0:ℝ)<1 by norm_num)
    (show (0:ℝ)<2 by norm_num) (show (0:ℝ)<1/2 by norm_num)
  obtain ⟨A₂,hA₂⟩ := eventually_stripInfinity.mp ha 1
  have hbound : ∀ᶠ t : ℝ in atTop,(F (t:ℂ)).im=0 ∧ |(F (t:ℂ)).re|≤|c|+1 := by
    filter_upwards [hr,(Metric.tendsto_nhds.mp hl) 1 (by norm_num)] with t ht hb
    refine ⟨ht,?_⟩
    have hh : |(F (t:ℂ)).re-c|<1 := by simpa only [Real.dist_eq] using hb
    calc
      |(F (t:ℂ)).re| = |((F (t:ℂ)).re-c)+c| := by congr 1; ring
      _ ≤ |(F (t:ℂ)).re-c|+|c| := abs_add_le _ _
      _ ≤ |c|+1 := by linarith
  obtain ⟨A₃,hA₃⟩ := eventually_atTop.mp hbound
  obtain ⟨A₄,hA₄⟩ := hm
  let A := max A₁ (max A₂ (max A₃ A₄))
  have hAA₁ : A₁≤A := le_max_left _ _
  have hAA₂ : A₂≤A := (le_max_left _ _).trans (le_max_right _ _)
  have hAA₃ : A₃≤A := (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hAA₄ : A₄≤A := (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hFa (t : ℝ) (ht : A<t) : AnalyticAt ℂ F (t:ℂ) :=
    hA₂ _ ⟨hAA₂.trans_lt ht,by simp⟩
  have hFr (t : ℝ) (ht : A<t) : (F (t:ℂ)).im=0 := (hA₃ t (hAA₃.trans ht.le)).1
  have hFd (t : ℝ) (ht : A<t) :
      HasDerivAt (fun t : ℝ => (F (t:ℂ)).re) (deriv F (t:ℂ)).re t :=
    Complex.reCLM.hasFDerivAt.comp_hasDerivAt t (hFa t ht).differentiableAt.hasDerivAt.comp_ofReal
  obtain ⟨N,hN⟩ := exists_nat_gt A
  let a : ℕ → ℝ := fun n => (F (↑(((n+N:ℕ):ℝ)+1) : ℂ)).re
  have hab (n : ℕ) : |a n|≤|c|+1 := by
    apply (hA₃ _ ?_).2
    have hh : (N:ℝ)≤((n+N:ℕ):ℝ) := by norm_num
    exact hAA₃.trans (by linarith)
  have ham : Monotone a ∨ Antitone a := by
    rcases hA₄ with hh | hh
    · left
      intro i j hij
      apply hh
      · change A₄≤((i+N:ℕ):ℝ)+1
        apply hAA₄.trans
        have hh : (N:ℝ)≤((i+N:ℕ):ℝ) := by norm_num
        linarith
      · change A₄≤((j+N:ℕ):ℝ)+1
        apply hAA₄.trans
        have hh : (N:ℝ)≤((j+N:ℕ):ℝ) := by norm_num
        linarith
      · exact_mod_cast Nat.add_le_add_right (Nat.add_le_add_right hij N) 1
    · right
      intro i j hij
      apply hh
      · change A₄≤((i+N:ℕ):ℝ)+1
        apply hAA₄.trans
        have hh : (N:ℝ)≤((i+N:ℕ):ℝ) := by norm_num
        linarith
      · change A₄≤((j+N:ℕ):ℝ)+1
        apply hAA₄.trans
        have hh : (N:ℝ)≤((j+N:ℕ):ℝ) := by norm_num
        linarith
      · exact_mod_cast Nat.add_le_add_right (Nat.add_le_add_right hij N) 1
  let w : ℕ → ℝ := fun n => 2*|a (n+1)-a n|
  refine ⟨N,w,fun n => by dsimp [w]; positivity,(summable_abs_variation hab ham).mul_left 2,?_⟩
  intro n t htl htu
  let u : ℝ := ((n+N:ℕ):ℝ)+1
  have huA : A<u := by
    have hh : (N:ℝ)≤((n+N:ℕ):ℝ) := by norm_num
    dsimp [u]; linarith
  have hun : u+1-u=1 := by ring
  obtain ⟨s,hs,hds⟩ := exists_hasDerivAt_eq_slope (fun t : ℝ => (F (t:ℂ)).re)
    (fun t : ℝ => (deriv F (t:ℂ)).re) (show u<u+1 by linarith)
    (fun x hx => (hFd x (huA.trans_le hx.1)).continuousAt.continuousWithinAt)
    (fun x hx => hFd x (huA.trans hx.1))
  rw [hun,div_one] at hds
  have hsA : A<s := huA.trans hs.1
  have htA : A<t := by
    have hh : (N:ℝ)≤((n+N:ℕ):ℝ) := by norm_num
    linarith
  have hts : ‖(t:ℂ)-(s:ℂ)‖≤2 := by
    rw [←Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs,abs_le]
    dsimp [u] at hs
    constructor <;> linarith [hs.1,hs.2]
  obtain ⟨hs0,hrat⟩ := hA₁ (t:ℂ) ⟨hAA₁.trans_lt htA,by simp⟩
    (s:ℂ) ⟨hAA₁.trans_lt hsA,by simp⟩ hts
  have hrat1 : ‖deriv F (t:ℂ)/deriv F (s:ℂ)-1‖≤1 := by linarith
  have hcomp : ‖deriv F (t:ℂ)‖≤2*‖deriv F (s:ℂ)‖ := by
    have he : deriv F (t:ℂ)=(deriv F (t:ℂ)/deriv F (s:ℂ)-1)*deriv F (s:ℂ)+deriv F (s:ℂ) := by
      field_simp [hs0]
      ring
    calc
      ‖deriv F (t:ℂ)‖ = ‖(deriv F (t:ℂ)/deriv F (s:ℂ)-1)*deriv F (s:ℂ)+deriv F (s:ℂ)‖ := congrArg norm he
      _ ≤ ‖(deriv F (t:ℂ)/deriv F (s:ℂ)-1)*deriv F (s:ℂ)‖+‖deriv F (s:ℂ)‖ := norm_add_le _ _
      _ ≤ 2*‖deriv F (s:ℂ)‖ := by rw [norm_mul]; nlinarith [norm_nonneg (deriv F (s:ℂ))]
  have him : (deriv F (s:ℂ)).im=0 := analytic_ray_deriv_im_zero hsA (hFa s hsA) hFr
  have heq : deriv F (s:ℂ)=((a (n+1)-a n:ℝ):ℂ) := by
    apply Complex.ext
    · change (deriv F (s:ℂ)).re=a (n+1)-a n
      rw [hds]
      dsimp [a,u]
      congr 2
      push_cast
      ring_nf
    · simpa using him
  rw [heq,Complex.norm_real,Real.norm_eq_abs] at hcomp
  exact hcomp

end DegeneratingTrees.Clock

 

 

 

open Set Filter Topology Complex
namespace DegeneratingTrees.Clock

theorem inverse_derivative_loss_absorption {J x : ℂ → ℂ} {b c : ℝ} (hb : 0<b)
    (hJa : ∀ᶠ z in stripInfinity,AnalyticAt ℂ J z)
    (hJr : ∀ᶠ t : ℝ in atTop,(J (t:ℂ)).im=0)
    (hJd0 : ∀ᶠ z in stripInfinity,deriv J z≠0)
    (hJdd : Tendsto (fun z => deriv (deriv J) z/deriv J z) stripInfinity (𝓝 0))
    (hJl : Tendsto (fun t : ℝ => (J (t:ℂ)).re) atTop (𝓝 c))
    (hJm : ∃ A : ℝ,MonotoneOn (fun t : ℝ => (J (t:ℂ)).re) (Ici A) ∨
      AntitoneOn (fun t : ℝ => (J (t:ℂ)).re) (Ici A))
    (hxa : ∀ᶠ r : ℝ in atTop,AnalyticAt ℂ x (r:ℂ))
    (hxd : Tendsto (fun r : ℝ => (r:ℂ)*deriv x (r:ℂ)) atTop (𝓝 ((b:ℂ)⁻¹))) :
    ∃ ω : ℝ → ℝ,AdmissibleAngularLoss ω ∧
      ∀ ε : ℝ,0<ε → ∀ᶠ r : ℝ in atTop,‖deriv J ((x (r:ℂ)).re:ℂ)‖≤ε*ω r := by
  obtain ⟨N,w,hw,hs,hbound⟩ := derivative_summable_unit_shells hJa hJr hJd0 hJdd hJl hJm
  have hxda : Tendsto (fun r : ℝ => (r:ℂ)*deriv x (r:ℂ)) atTop (𝓝 ((b⁻¹:ℝ):ℂ)) := by
    simpa only [Complex.ofReal_inv] using hxd
  obtain ⟨hψa,hψd⟩ := inverse_radial_logarithmic_derivative hxa hxda
  have hbp : 0<Real.log 2*b⁻¹ := mul_pos (Real.log_pos (by norm_num)) (inv_pos.mpr hb)
  obtain ⟨ω,hω,hsmall⟩ := strict_loss_from_unit_shells (e := fun t => ‖deriv J (t:ℂ)‖)
    hw hs (fun n t htl htu => by simpa only [abs_norm] using hbound n t htl htu) hbp hψa hψd
  refine ⟨ω,hω,?_⟩
  intro ε hε
  filter_upwards [hsmall ε hε,eventually_gt_atTop (0:ℝ)] with r hr hr0
  simpa only [Real.rpow_logb (by norm_num : (0:ℝ)<2) (by norm_num : (2:ℝ)≠1) hr0,abs_norm] using hr

end DegeneratingTrees.Clock

 

 

 

open Set Filter Topology Complex
namespace DegeneratingTrees.Clock

theorem inverse_exponential_decay {H : ℂ → ℂ} {t : ℝ → ℝ} {b ε : ℝ}
    (hb : 0<b) (hε : 0<ε)
    (hHa : ∀ᶠ s : ℝ in atTop,AnalyticAt ℂ H (s:ℂ))
    (hHr : ∀ᶠ s : ℝ in atTop,(H (s:ℂ)).im=0 ∧ 0<(H (s:ℂ)).re)
    (hHd : Tendsto (fun s : ℝ => deriv H (s:ℂ)/H (s:ℂ)) atTop (𝓝 (b:ℂ)))
    (ht : Tendsto t atTop atTop)
    (hinv : ∀ᶠ r : ℝ in atTop,H (t r:ℂ)=(r:ℂ)) :
    ∃ C : ℝ,0<C ∧ ∀ᶠ r : ℝ in atTop,Real.exp (-ε*t r)≤C*r^(-(ε/(2*b))) := by
  let F : ℂ → ℂ := fun z => Complex.exp ((-ε:ℝ)*z)
  have hFval (s : ℝ) : F (s:ℂ)=(Real.exp (-ε*s):ℂ) := by
    dsimp [F]
    rw [←Complex.ofReal_mul,←Complex.ofReal_exp]
  have hFder (z : ℂ) : deriv F z/F z=(-ε:ℝ) := by
    have hd := (Complex.hasDerivAt_exp ((-ε:ℝ)*z)).comp z ((hasDerivAt_id z).const_mul ((-ε:ℝ):ℂ))
    change HasDerivAt F _ z at hd
    rw [hd.deriv]
    simp only [mul_one,F]
    exact mul_div_cancel_left₀ _ (Complex.exp_ne_zero _)
  have hgap : -ε<(-(ε/(2*b)))*b := by
    have he : (-(ε/(2*b)))*b= -ε/2 := by field_simp
    rw [he]; linarith
  obtain ⟨C,hC,hbound⟩ := complex_log_derivative_power_bound (F := F) (H := H) hgap
    (Eventually.of_forall fun s => (analyticAt_const.mul analyticAt_id).cexp) hHa
    (Eventually.of_forall fun s => by rw [hFval]; exact ⟨rfl,Real.exp_pos _⟩)
    hHr ((tendsto_const_nhds (x := ((-ε:ℝ):ℂ))).congr' (Eventually.of_forall fun s => (hFder _).symm)) hHd
  refine ⟨C,hC,?_⟩
  filter_upwards [ht.eventually hbound,hinv] with r hr hi
  simpa only [hFval,hi,Complex.ofReal_re] using hr

theorem inverse_exponential_loss_absorption {H : ℂ → ℂ} {t : ℝ → ℝ} {b ε : ℝ}
    (hb : 0<b) (hε : 0<ε)
    (hHa : ∀ᶠ s : ℝ in atTop,AnalyticAt ℂ H (s:ℂ))
    (hHr : ∀ᶠ s : ℝ in atTop,(H (s:ℂ)).im=0 ∧ 0<(H (s:ℂ)).re)
    (hHd : Tendsto (fun s : ℝ => deriv H (s:ℂ)/H (s:ℂ)) atTop (𝓝 (b:ℂ)))
    (ht : Tendsto t atTop atTop)
    (hinv : ∀ᶠ r : ℝ in atTop,H (t r:ℂ)=(r:ℂ))
    {ω : ℝ → ℝ} (hω : AdmissibleAngularLoss ω) (M : ℝ) :
    ∀ δ : ℝ,0<δ → ∀ᶠ r : ℝ in atTop,M*Real.exp (-ε*t r)≤δ*ω r := by
  obtain ⟨C,hC,hpow⟩ := inverse_exponential_decay hb hε hHa hHr hHd ht hinv
  intro δ hδ
  have ha : 0<ε/(2*b) := by positivity
  filter_upwards [hpow,hω.power_absorption ha (max M 0*C/δ)] with r hr hbound
  have h₁ := mul_le_mul_of_nonneg_left hr (show 0≤ max M 0 from le_max_right _ _)
  have h₂ := mul_le_mul_of_nonneg_left hbound hδ.le
  have he : δ*(max M 0*C/δ*r^(-(ε/(2*b))))=max M 0*C*r^(-(ε/(2*b))) := by field_simp
  rw [he] at h₂
  have h₃ := mul_le_mul_of_nonneg_right (le_max_left M 0) (Real.exp_pos (-ε*t r)).le
  exact h₃.trans (h₁.trans (by nlinarith [h₂]))

end DegeneratingTrees.Clock

 

 

 

open Set Filter Topology Complex
namespace DegeneratingTrees.Clock

lemma realpart_of_ratio_error {F z : ℂ} {a e : ℝ} (hz : z≠0) (hr : 0 ≤ z.re)
    (h : ‖F/z-(a:ℂ)‖ ≤ e) : |F.re| ≤ |a| *z.re+e*‖z‖ := by
  have he : F=z*(a:ℂ)+z*(F/z-(a:ℂ)) := by field_simp; ring
  rw [he,Complex.add_re]
  calc
    |(z*(a:ℂ)).re+(z*(F/z-(a:ℂ))).re| ≤ |(z*(a:ℂ)).re|+|(z*(F/z-(a:ℂ))).re| := abs_add_le _ _
    _ ≤ |a| *z.re+‖z*(F/z-(a:ℂ))‖ := by
      have he : |(z*(a:ℂ)).re|=|a| *z.re := by
        simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero,abs_mul,abs_of_nonneg hr]
        ring
      rw [he]
      exact add_le_add le_rfl (Complex.abs_re_le_norm _)
    _ ≤ |a| *z.re+e*‖z‖ := by rw [norm_mul]; nlinarith [norm_nonneg z]

theorem strict_loss_realpart_separation {F : ℂ → ℂ} {a e : ℝ → ℝ}
    {η ω : ℝ → ℝ} (hη : AdmissibleAngularLoss η) (hω : AdmissibleAngularLoss ω)
    (ha : Tendsto a atTop (𝓝 0))
    (he : ∀ ε : ℝ,0 < ε → ∀ᶠ r in atTop,|e r| ≤ ε*ω r)
    (happrox : ∃ A : ℝ,∀ z∈lossSector η A,‖F z/z-(a ‖z‖:ℂ)‖ ≤ |e ‖z‖|) :
    ∀ ε : ℝ,0 < ε → ∃ R : ℝ,∀ z∈lossSector (fun r => max (η r) (ω r)) R,
      |(F z).re| ≤ ε*z.re := by
  intro ε hε
  obtain ⟨A,hA⟩ := happrox
  let θ : ℝ → ℝ := fun r => max (η r) (ω r)
  have hθ : AdmissibleAngularLoss θ := hη.max hω
  have has : ∀ᶠ r in atTop,|a r| ≤ ε/2 := by
    filter_upwards [(Metric.tendsto_nhds.mp ha) (ε/2) (by positivity)] with r hr
    exact le_of_lt (by simpa only [dist_zero_right,Real.norm_eq_abs] using hr)
  have hθs := hθ.tendsto_zero.eventually (eventually_lt_nhds (show (0:ℝ) < Real.pi/2 by linarith [Real.pi_pos]))
  obtain ⟨R,hR⟩ := eventually_atTop.mp (has.and ((he (ε/4) (by positivity)).and
    (hθ.1.and (hθs.and (eventually_gt_atTop (max A 1))))))
  refine ⟨R,?_⟩
  intro z hz
  obtain ⟨haz,hez,hθz,hθsmall,hzlarge⟩ := hR ‖z‖ hz.1.le
  have hrz : 0 < ‖z‖ := lt_of_lt_of_le (by norm_num : (0:ℝ) < 1) ((le_max_right A 1).trans hzlarge.le)
  have hre := half_loss_norm_le_re hθz.1.le hθsmall.le hz.2
  have hre0 : 0 ≤ z.re := (mul_nonneg (by linarith [hθz.1] : 0 ≤ θ ‖z‖/2) hrz.le).trans hre
  have hzη : z∈lossSector η A := ⟨(le_max_left _ _).trans_lt hzlarge,
    hz.2.trans_le (sub_le_sub_left (le_max_left _ _) _)⟩
  have hmain := realpart_of_ratio_error (norm_ne_zero_iff.mp hrz.ne') hre0 (hA z hzη)
  have heθ : |e ‖z‖| ≤ (ε/4)*θ ‖z‖ :=
    hez.trans (mul_le_mul_of_nonneg_left (le_max_right _ _) (by positivity))
  have hh := mul_le_mul_of_nonneg_right heθ hrz.le
  have hh' := mul_le_mul_of_nonneg_left hre (show 0 ≤ ε/2 by positivity)
  have hh'' := mul_le_mul_of_nonneg_right haz hre0
  nlinarith

end DegeneratingTrees.Clock

 

 

 

open Set Filter Topology Complex
namespace DegeneratingTrees.Clock

theorem equal_exponent_realpart_separation {F H J E x : ℂ → ℂ} {b ε C T : ℝ}
    (hb : 0<b) (hε : 0<ε) (hC : 0≤C)
    (hxr : ∀ᶠ r : ℝ in atTop,(x (r:ℂ)).im=0)
    (hxt : Tendsto (fun r : ℝ => (x (r:ℂ)).re) atTop atTop)
    (hxi : ∃ U : ℝ,∀ w : ℂ,0<w.re → U<‖w‖ →
      ‖x w-x (‖w‖:ℂ)-Complex.I*(w.arg/b:ℝ)‖≤|w.arg|)
    (hinv : ∀ w : ℂ,0<w.re → T<‖w‖ → H (x w)=w)
    (hxa : ∀ᶠ r : ℝ in atTop,AnalyticAt ℂ x (r:ℂ))
    (hxd : Tendsto (fun r : ℝ => (r:ℂ)*deriv x (r:ℂ)) atTop (𝓝 ((b:ℂ)⁻¹)))
    (hHa : ∀ᶠ s : ℝ in atTop,AnalyticAt ℂ H (s:ℂ))
    (hHr : ∀ᶠ s : ℝ in atTop,(H (s:ℂ)).im=0 ∧ 0<(H (s:ℂ)).re)
    (hHd : Tendsto (fun s : ℝ => deriv H (s:ℂ)/H (s:ℂ)) atTop (𝓝 (b:ℂ)))
    (hJa : ∀ᶠ z in stripInfinity,AnalyticAt ℂ J z)
    (hJ0 : ∀ᶠ z in stripInfinity,J z≠0)
    (hJd : Tendsto (fun z => deriv J z/J z) stripInfinity (𝓝 0))
    (hJr : ∀ᶠ t : ℝ in atTop,(J (t:ℂ)).im=0)
    (hJl : Tendsto (fun t : ℝ => (J (t:ℂ)).re) atTop (𝓝 0))
    (hJd0 : ∀ᶠ z in stripInfinity,deriv J z≠0)
    (hJdd : Tendsto (fun z => deriv (deriv J) z/deriv J z) stripInfinity (𝓝 0))
    (hJm : ∃ A : ℝ,MonotoneOn (fun t : ℝ => (J (t:ℂ)).re) (Ici A) ∨
      AntitoneOn (fun t : ℝ => (J (t:ℂ)).re) (Ici A))
    (he : ∀ᶠ z in stripInfinity,‖E z‖≤C*Real.exp (-ε*z.re))
    (hfactor : ∀ᶠ z in stripInfinity,F z/H z=J z*(1+E z)) :
    ∃ η : ℝ → ℝ,AdmissibleAngularLoss η ∧
      ∀ δ : ℝ,0<δ → ∃ R : ℝ,∀ w∈lossSector η R,|(F (x w)).re|≤δ*w.re := by
  obtain ⟨K,U,hK,herr⟩ := equal_exponent_ratio_error hb hε hC hxr hxt hxi hinv
    hJa hJ0 hJd hJr hJl hJd0 hJdd he hfactor
  obtain ⟨ω,hω,hds⟩ := inverse_derivative_loss_absorption hb hJa hJr hJd0 hJdd hJl hJm hxa hxd
  have hri : ∀ᶠ r : ℝ in atTop,H ((x (r:ℂ)).re:ℂ)=(r:ℂ) := by
    filter_upwards [hxr,eventually_gt_atTop (max T 0)] with r hr hrt
    have hreal : x (r:ℂ)=((x (r:ℂ)).re:ℂ) := Complex.ext rfl (by simpa using hr)
    rw [←hreal]
    exact hinv (r:ℂ) (by simpa using (le_max_right T 0).trans_lt hrt)
      (by simpa only [Complex.norm_real,Real.norm_eq_abs,abs_of_pos ((le_max_right T 0).trans_lt hrt)] using (le_max_left T 0).trans_lt hrt)
  have hes := inverse_exponential_loss_absorption hb hε hHa hHr hHd hxt hri hω K
  let e : ℝ → ℝ := fun r => K*(‖deriv J ((x (r:ℂ)).re:ℂ)‖+Real.exp (-ε*(x (r:ℂ)).re))
  have hepos (r : ℝ) : 0≤e r := by dsimp [e]; positivity
  have hsmall : ∀ δ : ℝ,0<δ → ∀ᶠ r : ℝ in atTop,|e r|≤δ*ω r := by
    intro δ hδ
    filter_upwards [hds (δ/(2*K)) (by positivity),hes (δ/2) (by positivity)] with r hd he
    rw [abs_of_nonneg (hepos r)]
    have hh := mul_le_mul_of_nonneg_left hd hK.le
    have hkeq : K*(δ/(2*K)*ω r)=δ/2*ω r := by field_simp
    rw [hkeq] at hh
    dsimp [e]
    nlinarith only [hh,he]
  obtain ⟨κ,S,hκ,hdata⟩ := SectorEventually.realpart_pos.and
    (tendsto_norm_sectorInfinity.eventually (eventually_gt_atTop U))
  refine ⟨fun r => max (κ r) (ω r),hκ.max hω,?_⟩
  apply strict_loss_realpart_separation hκ hω (hJl.comp hxt) hsmall
  refine ⟨S,?_⟩
  intro w hw
  rw [abs_of_nonneg (hepos ‖w‖)]
  exact herr w (hdata w hw).1 (hdata w hw).2

end DegeneratingTrees.Clock

 

 

 

open Set Filter Topology Complex
namespace DegeneratingTrees.Clock

theorem inverse_chart_data {F x : ℂ → ℂ} {b : ℝ} (hb : 0<b)
    (hFa : ∀ᶠ z in stripInfinity,AnalyticAt ℂ F z)
    (hF0 : ∀ᶠ z in stripInfinity,F z≠0)
    (hFr : ∀ᶠ t : ℝ in atTop,(F (t:ℂ)).im=0 ∧ 0<(F (t:ℂ)).re)
    (hFt : Tendsto (fun t : ℝ => (F (t:ℂ)).re) atTop atTop)
    (hFd : Tendsto (fun z => deriv F z/F z) stripInfinity (𝓝 (b:ℂ)))
    (hxa : ∀ᶠ w in sectorInfinity,AnalyticAt ℂ x w)
    (hxr : ∀ᶠ r : ℝ in atTop,(x (r:ℂ)).im=0)
    (hxt : Tendsto (fun r : ℝ => (x (r:ℂ)).re) atTop atTop)
    (hxto : Tendsto x sectorInfinity stripInfinity)
    (hi : ∀ ε : ℝ,0<ε → ∀ᶠ w in sectorInfinity,
      ‖x w-x (‖w‖:ℂ)-Complex.I*(w.arg/b:ℝ)‖≤ε*|w.arg|)
    (hxd : Tendsto (fun w => w*deriv x w) sectorInfinity (𝓝 ((b:ℂ)⁻¹))) :
    (∀ᶠ r : ℝ in atTop,(F (x (r:ℂ))).im=0 ∧ 0<(F (x (r:ℂ))).re) ∧
    Tendsto (fun r : ℝ => (F (x (r:ℂ))).re) atTop atTop ∧
    (∀ᶠ w in sectorInfinity,AnalyticAt ℂ (fun w => F (x w)) w) ∧
    (∀ᶠ w in sectorInfinity,(F (x (‖w‖:ℂ))).re/2≤‖F (x w)‖ ∧
      ‖F (x w)‖≤2*(F (x (‖w‖:ℂ))).re) ∧
    ∃ ψ : ℝ → ℝ,
      (∀ᶠ s : ℝ in atTop,DifferentiableAt ℝ ψ s) ∧ Tendsto (deriv ψ) atTop (𝓝 1) ∧
      (∀ᶠ r : ℝ in atTop,(F (x (r:ℂ))).re=(2:ℝ)^(ψ (Real.logb 2 r))) := by
  have hreal : ∀ᶠ r : ℝ in atTop,x (r:ℂ)=((x (r:ℂ)).re:ℂ) :=
    hxr.mono (fun r hr => Complex.ext rfl (by simpa using hr))
  have hGreal : ∀ᶠ r : ℝ in atTop,(F (x (r:ℂ))).im=0 ∧ 0<(F (x (r:ℂ))).re := by
    filter_upwards [hxt.eventually hFr,hreal] with r hr he
    rwa [←he] at hr
  have hGft : Tendsto (fun r : ℝ => (F (x (r:ℂ))).re) atTop atTop :=
    (hFt.comp hxt).congr' (hreal.mono fun r hr => congrArg (fun z => (F z).re) hr.symm)
  have hGa : ∀ᶠ w in sectorInfinity,AnalyticAt ℂ (fun w => F (x w)) w := by
    filter_upwards [hxa,hxto.eventually hFa] with w hx hF
    exact hF.comp hx
  have hGrd : Tendsto (fun w => w*deriv (fun w => F (x w)) w/F (x w)) sectorInfinity (𝓝 (1:ℂ)) := by
    have hh := inverse_composition_logarithmic_slope hxa hFa hxto hFd hxd
    simpa only [mul_inv_cancel₀ (show (b:ℂ)≠0 by exact_mod_cast hb.ne')] using hh
  have hratio := inverse_clock_ratio_tendsto hb hFa hF0 hFd
    (tendsto_re_stripInfinity.comp hxto) hxt hxr hi
  have hmod := inverse_clock_modulus_tendsto hratio
  refine ⟨hGreal,hGft,hGa,?_,?_⟩
  · have hs := (Metric.tendsto_nhds.mp hmod) (1/2) (by norm_num)
    filter_upwards [hs,tendsto_norm_sectorInfinity.eventually hGreal] with w hs hr
    have he : F (x (‖w‖:ℂ))=((F (x (‖w‖:ℂ))).re:ℂ) := Complex.ext rfl (by simpa using hr.1)
    rw [he,Complex.norm_of_nonneg hr.2.le,Real.dist_eq] at hs
    have hl : (1:ℝ)/2<‖F (x w)‖/(F (x (‖w‖:ℂ))).re := by linarith [(abs_lt.mp hs).1]
    have hu : ‖F (x w)‖/(F (x (‖w‖:ℂ))).re<2 := by linarith [(abs_lt.mp hs).2]
    exact ⟨by linarith [(lt_div_iff₀ hr.2).mp hl],by linarith [(div_lt_iff₀ hr.2).mp hu]⟩
  · obtain ⟨ha,hd,he⟩ := logarithmic_radius_derivative (tendsto_real_sectorInfinity.eventually hGa)
      hGreal (hGrd.comp tendsto_real_sectorInfinity)
    exact ⟨_,ha,hd,he⟩

end DegeneratingTrees.Clock

 

 

 

open Set Filter Topology Complex
namespace DegeneratingTrees.Clock

theorem inverse_strip_exponential_error {E x : ℂ → ℂ} {b ε C : ℝ}
    (hb : 0<b) (hε : 0<ε) (hC : 0≤C)
    (hxr : ∀ᶠ r : ℝ in atTop,(x (r:ℂ)).im=0)
    (hxt : Tendsto (fun r : ℝ => (x (r:ℂ)).re) atTop atTop)
    (hi : ∃ U : ℝ,∀ w : ℂ,0<w.re → U<‖w‖ →
      ‖x w-x (‖w‖:ℂ)-Complex.I*(w.arg/b:ℝ)‖≤|w.arg|)
    (he : ∀ᶠ z in stripInfinity,‖E z‖≤C*Real.exp (-ε*z.re)) :
    ∃ D : ℝ,0<D ∧ ∀ᶠ w in sectorInfinity,
      ‖E (x w)‖≤D*Real.exp (-ε*(x (‖w‖:ℂ)).re) := by
  obtain ⟨R,B,hR,hB,hmap⟩ := inverse_halfplane_strip hb hxr hxt hi
  obtain ⟨A,hA⟩ := eventually_stripInfinity.mp he R
  obtain ⟨U,hU,hUf⟩ := hmap A
  refine ⟨C*Real.exp (ε*B)+1,by positivity,?_⟩
  filter_upwards [SectorEventually.realpart_pos,
    tendsto_norm_sectorInfinity.eventually (eventually_gt_atTop U)] with w hw hwU
  obtain ⟨ht,hx,hd⟩ := hUf w hw hwU
  have hre := (Complex.abs_re_le_norm (x w-((x (‖w‖:ℂ)).re:ℂ))).trans hd
  simp only [Complex.sub_re,Complex.ofReal_re] at hre
  have hxexp : Real.exp (-ε*(x w).re) ≤ Real.exp (ε*B)*Real.exp (-ε*(x (‖w‖:ℂ)).re) := by
    rw [←Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith [(abs_le.mp hre).1]
  calc
    _ ≤ C*Real.exp (-ε*(x w).re) := hA _ hx
    _ ≤ C*(Real.exp (ε*B)*Real.exp (-ε*(x (‖w‖:ℂ)).re)) := mul_le_mul_of_nonneg_left hxexp hC
    _ ≤ (C*Real.exp (ε*B)+1)*Real.exp (-ε*(x (‖w‖:ℂ)).re) := by nlinarith [Real.exp_pos (-ε*(x (‖w‖:ℂ)).re)]

end DegeneratingTrees.Clock
end

end OAI
