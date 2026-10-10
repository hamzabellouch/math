import Mathlib
import OAI.Analysis.PathSelection.SectorUniqueness

namespace OAI

/-! Cauchy estimates, sector narrowing, tails and subexponential losses. -/

noncomputable section
open Set Filter Topology Metric Polynomial
open scoped BigOperators NNReal ENNReal

open Set Filter Topology Complex Metric
namespace DegeneratingTrees

 

lemma AdmissibleAngularLoss.real_discs {ω : ℝ → ℝ}
    (hω : AdmissibleAngularLoss ω) (R : ℝ) :
    ∀ᶠ x : ℝ in atTop, 0 < x ∧ closedBall (x:ℂ) (x/4) ⊆ lossSector ω R := by
  obtain ⟨a,t,S,hS,ha,has,ht,hsmall,hbound⟩ := angularLoss_kernel_data hω
  filter_upwards [eventually_gt_atTop (max (2*S) (2*max R 0))] with x hx
  have hxS : 2*S < x := (le_max_left _ _).trans_lt hx
  have hxR : 2*max R 0 < x := (le_max_right _ _).trans_lt hx
  have hxp : 0 < x := by linarith
  refine ⟨hxp,?_⟩
  intro z hz
  have hd : ‖z-(x:ℂ)‖ ≤ x/4 := mem_closedBall_iff_norm.mp hz
  have hre := (abs_re_le_norm (z-(x:ℂ))).trans hd
  simp only [sub_re,ofReal_re] at hre
  have hreL : 3*x/4 ≤ z.re := by have := (abs_le.mp hre).1; linarith
  have hnL : 3*x/4 ≤ ‖z‖ := hreL.trans (re_le_norm z)
  have hnU : ‖z‖ ≤ 5*x/4 := by
    have h := norm_add_le (z-(x:ℂ)) (x:ℂ)
    rw [sub_add_cancel,Complex.norm_of_nonneg hxp.le] at h
    linarith
  have hS' : S ≤ ‖z‖ := by linarith
  have hR' : R < ‖z‖ := by have := le_max_left R 0; linarith
  refine ⟨hR',arg_lt_of_re_lower (hbound _ hS').1 (norm_pos_iff.mp (by linarith)) ?_⟩
  have hb := (hbound _ hS').2.1
  have hm := mul_le_mul_of_nonneg_right hb (norm_nonneg z)
  linarith

 

lemma sector_deriv_ray_bound {ω : ℝ → ℝ} {R a C : ℝ} {f : ℂ → ℂ}
    (hω : AdmissibleAngularLoss ω) (hf : AnalyticOnNhd ℂ f (lossSector ω R))
    (hC : 0 ≤ C) (hb : ∀ z ∈ lossSector ω R, ‖f z‖ ≤ C*Real.exp (a*z.re)) :
    ∀ᶠ x : ℝ in atTop, ‖deriv f (x:ℂ)‖ ≤ (C*Real.exp |a|)*Real.exp (a*x) := by
  filter_upwards [hω.real_discs R,eventually_ge_atTop (4:ℝ)] with x hx hx4
  have hdisc : closedBall (x:ℂ) 1 ⊆ lossSector ω R :=
    (closedBall_subset_closedBall (by linarith)).trans hx.2
  have hdiff : DiffContOnCl ℂ f (ball (x:ℂ) 1) :=
    hf.differentiableOn.diffContOnCl_ball hdisc
  have hcircle (z : ℂ) (hz : z ∈ sphere (x:ℂ) 1) :
      ‖f z‖ ≤ (C*Real.exp |a|)*Real.exp (a*x) := by
    have hd : ‖z-(x:ℂ)‖ = 1 := mem_sphere_iff_norm.mp hz
    have hzr := abs_re_le_norm (z-(x:ℂ))
    simp only [sub_re,ofReal_re,hd] at hzr
    have hmul : a*(z.re-x) ≤ |a| :=
      (le_abs_self _).trans (by rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg _) hzr)
    have hexp : Real.exp (a*z.re) ≤ Real.exp (|a|+a*x) := Real.exp_le_exp.mpr (by linarith)
    calc ‖f z‖ ≤ C*Real.exp (a*z.re) := hb _ (hdisc (sphere_subset_closedBall hz))
      _ ≤ C*Real.exp (|a|+a*x) := mul_le_mul_of_nonneg_left hexp hC
      _ = (C*Real.exp |a|)*Real.exp (a*x) := by rw [Real.exp_add,mul_assoc]
  simpa using norm_deriv_le_of_forall_mem_sphere_norm_le (by norm_num : (0:ℝ)<1) hdiff hcircle

end DegeneratingTrees

 

 

 

open Set Filter Topology Complex Metric
namespace DegeneratingTrees

private def windowSum (w : ℕ → ℝ) (n : ℕ) : ℝ := w (n+1)+w (n+2)+w (n+3)

private lemma window_bound {ω : ℝ → ℝ} {n₀ : ℕ} {w : ℕ → ℝ}
    (hw : ∀ n, 0 ≤ w n)
    (hb : ∀ n r, (2:ℝ)^(n+n₀) < r → r < (2:ℝ)^(n+n₀+2) → ω r ≤ w n)
    (n : ℕ) {r : ℝ} (hrl : (2:ℝ)^(n+(n₀+2)) < r)
    (hru : r < (2:ℝ)^(n+(n₀+2)+2)) {s : ℝ} (hsl : r/2 ≤ s) (hsu : s ≤ 2*r) :
    ω s ≤ windowSum w n := by
  have hp : (0:ℝ) < 2^(n+n₀) := by positivity
  have hl : 2^(n+n₀+1) < s := by
    simp only [show n+(n₀+2)=n+n₀+2 by omega,pow_add] at hrl ⊢
    norm_num at hrl ⊢
    linarith
  have hu : s < 2^(n+n₀+5) := by
    simp only [show n+(n₀+2)+2=n+n₀+4 by omega,pow_add] at hru ⊢
    norm_num at hru ⊢
    linarith
  by_cases hs1 : s < 2^(n+n₀+3)
  · have h := hb (n+1) s (by convert hl using 1; congr 1; omega)
      (by convert hs1 using 1; congr 1; omega)
    dsimp [windowSum]
    linarith [hw (n+2),hw (n+3)]
  · by_cases hs2 : s < 2^(n+n₀+4)
    · have hlo : 2^(n+n₀+2) < s := by
        have hp2 : (2:ℝ)^(n+n₀+2) < 2^(n+n₀+3) := by
          exact pow_lt_pow_right₀ (by norm_num) (by omega)
        exact hp2.trans_le (le_of_not_gt hs1)
      have h := hb (n+2) s (by convert hlo using 1; congr 1; omega)
        (by convert hs2 using 1; congr 1; omega)
      dsimp [windowSum]
      linarith [hw (n+1),hw (n+3)]
    · have hlo : 2^(n+n₀+3) < s := by
        have hp2 : (2:ℝ)^(n+n₀+3) < 2^(n+n₀+4) := by
          exact pow_lt_pow_right₀ (by norm_num) (by omega)
        exact hp2.trans_le (le_of_not_gt hs2)
      have h := hb (n+3) s (by convert hlo using 1; congr 1; omega)
        (by convert hu using 1; congr 1; omega)
      dsimp [windowSum]
      linarith [hw (n+1),hw (n+2)]

 

def neighboringLoss (ω : ℝ → ℝ) (r : ℝ) : ℝ := sSup (ω '' Icc (r/2) (2*r))

private lemma neighboringLoss_tail_bdd {ω : ℝ → ℝ} {n₀ : ℕ} {w : ℕ → ℝ}
    (hw : ∀ n, 0 ≤ w n)
    (hb : ∀ n r, (2:ℝ)^(n+n₀) < r → r < (2:ℝ)^(n+n₀+2) → ω r ≤ w n)
    {r : ℝ} (hr : (2:ℝ)^(n₀+3) ≤ r) : BddAbove (ω '' Icc (r/2) (2*r)) := by
  obtain ⟨n,hnl,hnu⟩ := dyadic_shell (show (0:ℝ)<2^(n₀+3) by positivity) hr
  have hrl : (2:ℝ)^(n+(n₀+2)) < r := by
    have hp : (0:ℝ) < 2^(n₀+2)*2^n := by positivity
    simp only [pow_add] at hp hnl ⊢
    norm_num at hp hnl ⊢
    have hpp : (0:ℝ) < 2^n * 2^n₀ := mul_pos (pow_pos (by norm_num) _) (pow_pos (by norm_num) _)
    nlinarith
  have hru : r < (2:ℝ)^(n+(n₀+2)+2) := by
    convert hnu using 1
    simp only [pow_add]
    ring
  refine ⟨windowSum w n,?_⟩
  rintro _ ⟨s,hs,rfl⟩
  exact window_bound hw hb n hrl hru hs.1 hs.2

lemma AdmissibleAngularLoss.neighboring {ω : ℝ → ℝ} (hω : AdmissibleAngularLoss ω) :
    AdmissibleAngularLoss (neighboringLoss ω) ∧
      ∀ᶠ r : ℝ in atTop, ∀ s ∈ Icc (r/2) (2*r), ω s ≤ neighboringLoss ω r := by
  obtain ⟨hpos,n₀,w,hw,hs,hb⟩ := hω
  have hupper : ∀ᶠ r : ℝ in atTop, ∀ s ∈ Icc (r/2) (2*r), ω s ≤ neighboringLoss ω r := by
    filter_upwards [eventually_ge_atTop ((2:ℝ)^(n₀+3))] with r hr s hs
    exact le_csSup (neighboringLoss_tail_bdd hw hb hr) (mem_image_of_mem _ hs)
  refine ⟨⟨?_,n₀+2,windowSum w,?_,?_,?_⟩,hupper⟩
  · filter_upwards [hpos,hupper,eventually_ge_atTop (0:ℝ)] with r hp hu hr
    have hn := hu r ⟨by linarith,by linarith⟩
    exact ⟨hp.1.trans_le hn,hp.2.trans hn⟩
  · intro n; dsimp [windowSum]; positivity [hw (n+1),hw (n+2),hw (n+3)]
  · exact ((summable_nat_add_iff 1).mpr hs).add ((summable_nat_add_iff 2).mpr hs) |>.add
      ((summable_nat_add_iff 3).mpr hs)
  · intro n r hrl hru
    have hr : 0 ≤ r := (show (0:ℝ)<2^(n+(n₀+2)) by positivity).trans hrl |>.le
    apply csSup_le
    · exact ⟨ω r,mem_image_of_mem _ ⟨by linarith,by linarith⟩⟩
    · rintro _ ⟨s,hs,rfl⟩
      exact window_bound hw hb n hrl hru hs.1 hs.2

lemma AdmissibleAngularLoss.const_mul {ω : ℝ → ℝ}
    (hω : AdmissibleAngularLoss ω) {c : ℝ} (hc : 1 ≤ c) :
    AdmissibleAngularLoss (fun r => c*ω r) := by
  obtain ⟨hp,n₀,w,hw,hs,hb⟩ := hω
  have hc0 : 0 < c := lt_of_lt_of_le zero_lt_one hc
  refine ⟨?_,n₀,fun n => c*w n,fun n => mul_nonneg hc0.le (hw n),hs.mul_left c,?_⟩
  · filter_upwards [hp] with r hr
    exact ⟨mul_pos hc0 hr.1,hr.2.trans (le_mul_of_one_le_left hr.1.le hc)⟩
  · intro n r hl hu
    exact mul_le_mul_of_nonneg_left (hb n r hl hu) hc0.le

lemma log_margin_grows : ∀ᶠ r : ℝ in atTop, 1 ≤ r*(Real.log r)⁻¹^2 := by
  have h := (isLittleO_log_rpow_rpow_atTop (s := 1) 2 zero_lt_one).bound
    (by norm_num : (0:ℝ)<1)
  filter_upwards [h,eventually_gt_atTop (1:ℝ)] with r hr hr1
  have hr0 : 0 < r := lt_trans zero_lt_one hr1
  have hl : 0 < Real.log r := Real.log_pos hr1
  have hs : Real.log r ^ 2 ≤ r := by
    simpa only [Real.rpow_two,Real.rpow_one,Real.norm_eq_abs,abs_of_nonneg (sq_nonneg (Real.log r)),
      abs_of_pos hr0,one_mul] using hr
  calc
    1 ≤ r/(Real.log r)^2 := (one_le_div (sq_pos_of_pos hl)).mpr hs
    _ = r*(Real.log r)⁻¹^2 := by rw [div_eq_mul_inv,inv_pow]

lemma half_loss_norm_le_re {η : ℝ} (hη0 : 0 ≤ η) (hηπ : η ≤ Real.pi/2)
    {z : ℂ} (hz : |z.arg| < Real.pi/2-η) : η/2*‖z‖ ≤ z.re := by
  have hc : η/2 ≤ Real.cos z.arg := by
    have hp : (1/2:ℝ) ≤ 2/Real.pi :=
      (le_div_iff₀ Real.pi_pos).mpr (by linarith [Real.pi_lt_four])
    calc
      η/2 ≤ 2/Real.pi*η := by nlinarith
      _ ≤ Real.sin η := Real.mul_le_sin hη0 hηπ
      _ = Real.cos (Real.pi/2-η) := (Real.cos_pi_div_two_sub η).symm
      _ ≤ Real.cos |z.arg| := Real.cos_le_cos_of_nonneg_of_le_pi
        (abs_nonneg _) (by linarith [Real.pi_pos]) hz.le
      _ = Real.cos z.arg := Real.cos_abs _
  have hm := mul_le_mul_of_nonneg_left hc (norm_nonneg z)
  rw [Complex.norm_mul_cos_arg] at hm
  nlinarith

 

theorem AdmissibleAngularLoss.narrow_discs {ω : ℝ → ℝ}
    (hω : AdmissibleAngularLoss ω) (R : ℝ) :
    ∃ (η : ℝ → ℝ) (R' : ℝ), AdmissibleAngularLoss η ∧ R ≤ R' ∧
      ∀ z ∈ lossSector η R', closedBall z 1 ⊆ lossSector ω R := by
  obtain ⟨hN,hup⟩ := hω.neighboring
  let η : ℝ → ℝ := fun r => 16*neighboringLoss ω r
  have hη : AdmissibleAngularLoss η := hN.const_mul (by norm_num)
  obtain ⟨a,t,S,hS,ha,has,ht,hsmall,hηsmall⟩ := angularLoss_kernel_data hη
  obtain ⟨T,hT⟩ := eventually_atTop.mp
    (hup.and (hN.1.and log_margin_grows))
  obtain ⟨W,hW⟩ := eventually_atTop.mp hω.1
  let R' := max (max (max S T) (W+2)) (max (R+2) 3)
  have hR : R ≤ R' := by dsimp [R']; grind [le_max_left,le_max_right]
  refine ⟨η,R',hη,hR,?_⟩
  intro z hz w hw
  have hrS : S < ‖z‖ := lt_of_le_of_lt (by dsimp [R']; grind [le_max_left,le_max_right]) hz.1
  have hrT : T < ‖z‖ := lt_of_le_of_lt (by dsimp [R']; grind [le_max_left,le_max_right]) hz.1
  have hrW : W+2 < ‖z‖ := lt_of_le_of_lt (by dsimp [R']; grind [le_max_left,le_max_right]) hz.1
  have hrR : R+2 < ‖z‖ := lt_of_le_of_lt (by dsimp [R']; grind [le_max_left,le_max_right]) hz.1
  have hr3 : 3 < ‖z‖ := lt_of_le_of_lt (by dsimp [R']; grind [le_max_left,le_max_right]) hz.1
  have hd : ‖w-z‖ ≤ 1 := mem_closedBall_iff_norm.mp hw
  have hwl : ‖z‖-1 ≤ ‖w‖ := by
    have hh := norm_sub_le w (w-z)
    rw [sub_sub_cancel] at hh
    linarith
  have hwu : ‖w‖ ≤ ‖z‖+1 := by
    have hh := norm_add_le (w-z) z
    rw [sub_add_cancel] at hh
    linarith
  have hNpos := (hT _ hrT.le).2.1.1
  have hNm : 1 ≤ ‖z‖*neighboringLoss ω ‖z‖ :=
    (hT _ hrT.le).2.2.trans (mul_le_mul_of_nonneg_left (hT _ hrT.le).2.1.2 (norm_nonneg z))
  have hωw : ω ‖w‖ ≤ neighboringLoss ω ‖z‖ :=
    (hT _ hrT.le).1 _ ⟨by linarith,by linarith⟩
  have hωpos : 0 < ω ‖w‖ := (hW _ (by linarith)).1
  have hηπ : η ‖z‖ ≤ Real.pi/2 := by
    have hh := (hηsmall _ hrS.le).2.1
    linarith [Real.pi_gt_three]
  have hre := half_loss_norm_le_re (hηsmall _ hrS.le).1.le hηπ hz.2
  have hre' := (abs_le.mp ((abs_re_le_norm (w-z)).trans hd)).1
  simp only [Complex.sub_re] at hre'
  refine ⟨by linarith,arg_lt_of_re_lower hωpos (norm_pos_iff.mp (by linarith)) ?_⟩
  have hm := mul_le_mul_of_nonneg_right hωw (norm_nonneg w)
  have hn := mul_le_mul_of_nonneg_left hwu hNpos.le
  dsimp [η] at hre
  nlinarith

 

theorem sector_deriv_bound {ω : ℝ → ℝ} {R a C : ℝ} {f : ℂ → ℂ}
    (hω : AdmissibleAngularLoss ω) (hf : AnalyticOnNhd ℂ f (lossSector ω R))
    (hC : 0 ≤ C) (hb : ∀ z ∈ lossSector ω R, ‖f z‖ ≤ C*Real.exp (a*z.re)) :
    ∃ (η : ℝ → ℝ) (R' : ℝ), AdmissibleAngularLoss η ∧ R ≤ R' ∧
      AnalyticOnNhd ℂ (deriv f) (lossSector η R') ∧
      ∀ z ∈ lossSector η R', ‖deriv f z‖ ≤ (C*Real.exp |a|)*Real.exp (a*z.re) := by
  obtain ⟨η,R',hη,hR,hdisc⟩ := hω.narrow_discs R
  refine ⟨η,R',hη,hR,?_,?_⟩
  · intro z hz
    exact (hf z (hdisc z hz (mem_closedBall_self (by norm_num)))).deriv
  · intro z hz
    have hd := hf.differentiableOn.diffContOnCl_ball (hdisc z hz)
    have hc (w : ℂ) (hw : w ∈ sphere z 1) :
        ‖f w‖ ≤ (C*Real.exp |a|)*Real.exp (a*z.re) := by
      have hwr : |w.re-z.re| ≤ 1 := by
        have hh := abs_re_le_norm (w-z)
        simpa only [sub_re,mem_sphere_iff_norm.mp hw] using hh
      have hm : a*(w.re-z.re) ≤ |a| :=
        (le_abs_self _).trans (by rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg _) hwr)
      calc
        ‖f w‖ ≤ C*Real.exp (a*w.re) := hb _ (hdisc z hz (sphere_subset_closedBall hw))
        _ ≤ C*Real.exp (|a|+a*z.re) := mul_le_mul_of_nonneg_left
          (Real.exp_le_exp.mpr (by linarith)) hC
        _ = (C*Real.exp |a|)*Real.exp (a*z.re) := by rw [Real.exp_add,mul_assoc]
    simpa using norm_deriv_le_of_forall_mem_sphere_norm_le (by norm_num : (0:ℝ)<1) hd hc

end DegeneratingTrees

 

 

 

open Set Filter Topology Complex Metric
namespace DegeneratingTrees

lemma AdmissibleAngularLoss.max {ω η : ℝ → ℝ}
    (hω : AdmissibleAngularLoss ω) (hη : AdmissibleAngularLoss η) :
    AdmissibleAngularLoss (fun r => max (ω r) (η r)) := by
  obtain ⟨hp,n,w,hw,hs,hb⟩ := hω
  obtain ⟨hq,m,v,hv,ht,hc⟩ := hη
  refine ⟨?_,n+m,fun k => w (k+m)+v (k+n),?_,?_,?_⟩
  · filter_upwards [hp] with r hr
    exact ⟨hr.1.trans_le (le_max_left _ _),hr.2.trans (le_max_left _ _)⟩
  · intro k; exact add_nonneg (hw _) (hv _)
  · exact ((summable_nat_add_iff m).mpr hs).add ((summable_nat_add_iff n).mpr ht)
  · intro k r hl hu
    have h1 := hb (k+m) r (by convert hl using 1; congr 1; omega)
      (by convert hu using 1; congr 1; omega)
    have h2 := hc (k+n) r (by convert hl using 1; congr 1; omega)
      (by convert hu using 1; congr 1; omega)
    exact max_le (h1.trans (le_add_of_nonneg_right (hv _)))
      (h2.trans (le_add_of_nonneg_left (hw _)))

def SectorEventually (P : ℂ → Prop) : Prop :=
  ∃ ω R, AdmissibleAngularLoss ω ∧ ∀ z ∈ lossSector ω R, P z

lemma SectorEventually.mono {P Q : ℂ → Prop} (h : SectorEventually P)
    (hpq : ∀ z, P z → Q z) : SectorEventually Q := by
  obtain ⟨ω,R,hω,h⟩ := h
  exact ⟨ω,R,hω,fun z hz => hpq z (h z hz)⟩

lemma SectorEventually.and {P Q : ℂ → Prop}
    (h : SectorEventually P) (k : SectorEventually Q) : SectorEventually (fun z => P z ∧ Q z) := by
  obtain ⟨ω,R,hω,h⟩ := h
  obtain ⟨η,S,hη,k⟩ := k
  refine ⟨fun r => max (ω r) (η r),max R S,hω.max hη,?_⟩
  intro z hz
  exact ⟨h z ⟨(le_max_left _ _).trans_lt hz.1,by
    have hh := le_max_left (ω ‖z‖) (η ‖z‖); linarith [hz.2]⟩,
    k z ⟨(le_max_right _ _).trans_lt hz.1,by
    have hh := le_max_right (ω ‖z‖) (η ‖z‖); linarith [hz.2]⟩⟩

lemma SectorEventually.finset_forall {ι : Type*} (s : Finset ι) {P : ι → ℂ → Prop}
    (hbase : SectorEventually (fun _ => True))
    (h : ∀ i ∈ s, SectorEventually (P i)) :
    SectorEventually (fun z => ∀ i ∈ s, P i z) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact hbase.mono (by simp)
  | @insert i s hi ih =>
    have ht := (h i (Finset.mem_insert_self _ _)).and
      (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)))
    exact ht.mono (by simp only [Finset.mem_insert,forall_eq_or_imp]; tauto)

 

theorem sector_zero_of_ray_zero {ω : ℝ → ℝ} {R : ℝ} {f : ℂ → ℂ}
    (hω : AdmissibleAngularLoss ω) (hf : AnalyticOnNhd ℂ f (lossSector ω R))
    (hz : ∀ᶠ x : ℝ in atTop, f (x:ℂ)=0) : SectorEventually (fun z => f z=0) := by
  obtain ⟨a,t,S,hS,ha,has,ht,hsmall,hcontrol⟩ := angularLoss_kernel_data hω
  obtain ⟨T,hT⟩ := eventually_atTop.mp hz
  let W := max (max R S) (max T 1)
  have hW0 : 0 < W := lt_of_lt_of_le zero_lt_one (by dsimp [W]; grind [le_max_left,le_max_right])
  have hWR : R ≤ W := by dsimp [W]; grind [le_max_left,le_max_right]
  have hWS : S ≤ W := by dsimp [W]; grind [le_max_left,le_max_right]
  have hWT : T ≤ W := by dsimp [W]; grind [le_max_left,le_max_right]
  have hsub : lossSector ω W ⊆ lossSector ω R := fun z hz => ⟨hWR.trans_lt hz.1,hz.2⟩
  have hconn : IsPreconnected (lossSector ω W) := by
    apply lossSector_isPreconnected hW0
    intro r hr
    have hh := hcontrol r (hWS.trans hr.le)
    exact ⟨hh.1,by linarith [hh.2.1,Real.pi_gt_three]⟩
  have hxmem : ((W+1:ℝ):ℂ) ∈ lossSector ω W := by
    have hpos : 0 < W+1 := by linarith
    have hh := hcontrol (W+1) (by linarith)
    simp only [lossSector,mem_ofPred_eq,Complex.norm_of_nonneg hpos.le,
      Complex.arg_ofReal_of_nonneg hpos.le,abs_zero]
    constructor <;> linarith [hh.2.1,Real.pi_gt_three]
  have hcl : ((W+1:ℝ):ℂ) ∈ closure ({z | f z=0} \ {((W+1:ℝ):ℂ)}) := by
    rw [Metric.mem_closure_iff]
    intro ε hε
    refine ⟨((W+1+ε/2:ℝ):ℂ),⟨hT _ (by linarith),?_⟩,?_⟩
    · simp only [mem_singleton_iff,Complex.ofReal_inj]
      linarith
    · simp only [dist_eq_norm,←Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs]
      exact abs_lt.mpr ⟨by linarith,by linarith⟩
  exact ⟨ω,W,hω,(hf.mono hsub).eqOn_zero_of_preconnected_of_mem_closure hconn hxmem hcl⟩

end DegeneratingTrees

 

 

 

open Set Filter Topology Complex
namespace DegeneratingTrees

lemma AdmissibleAngularLoss.tendsto_zero {ω : ℝ → ℝ}
    (hω : AdmissibleAngularLoss ω) : Tendsto ω atTop (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  let c : ℝ := Max.max 1 ε⁻¹
  have hc : 1 ≤ c := le_max_left _ _
  have hcp : 0 < c := lt_of_lt_of_le zero_lt_one hc
  have hcε : 1 ≤ c*ε := by
    have h := mul_le_mul_of_nonneg_right (le_max_right (1:ℝ) ε⁻¹) hε.le
    rw [inv_mul_cancel₀ hε.ne'] at h
    exact h
  obtain ⟨a,t,S,hS,ha,hs,ht,hsmall,hbound⟩ := angularLoss_kernel_data (hω.const_mul hc)
  filter_upwards [eventually_ge_atTop S] with r hr
  have hb := hbound r hr
  have hw : 0 < ω r := (mul_pos_iff_of_pos_left hcp).mp hb.1
  simp only [Real.dist_eq,sub_zero,abs_of_pos hw]
  have hmul : c*ω r < c*ε := by linarith [hb.2.1]
  exact (mul_lt_mul_iff_of_pos_left hcp).mp hmul

 

lemma AdmissibleAngularLoss.power_absorption {ω : ℝ → ℝ}
    (hω : AdmissibleAngularLoss ω) {a : ℝ} (ha : 0 < a) (C : ℝ) :
    ∀ᶠ r : ℝ in atTop, C*r^(-a) ≤ ω r := by
  have h := (isLittleO_log_rpow_rpow_atTop (s := a) 2 ha).bound
    (show (0:ℝ) < (Max.max C 0+1)⁻¹ by positivity)
  filter_upwards [h,hω.1,eventually_gt_atTop (1:ℝ)] with r hr hωr hr1
  have hr0 : 0 < r := zero_lt_one.trans hr1
  have hl : 0 < Real.log r := Real.log_pos hr1
  have hp : 0 < r^a := Real.rpow_pos_of_pos hr0 _
  have hc : 0 < Max.max C 0+1 := by positivity
  have hsq : (Real.log r)^2 ≤ (Max.max C 0+1)⁻¹ * r^a := by
    simpa only [Real.rpow_two,Real.norm_eq_abs,abs_of_nonneg (sq_nonneg (Real.log r)),abs_of_pos hp] using hr
  have hsmall : C*(Real.log r)^2 ≤ r^a := by
    have hmul := mul_le_mul_of_nonneg_left hsq hc.le
    have he : (Max.max C 0+1) * ((Max.max C 0+1)⁻¹ * r^a) = r^a := by field_simp
    rw [he] at hmul
    have hC := le_max_left C 0
    nlinarith [sq_nonneg (Real.log r)]
  calc
    C*r^(-a) = C/(r^a) := by rw [Real.rpow_neg hr0.le,div_eq_mul_inv]
    _ ≤ (Real.log r)⁻¹^2 := by
      rw [inv_pow,←one_div,div_le_div_iff₀ hp (sq_pos_of_pos hl)]
      simpa only [one_mul] using hsmall
    _ ≤ ω r := hωr.2

end DegeneratingTrees

 

 

 

open Set Filter Topology
namespace DegeneratingTrees

def baseLoss (r : ℝ) : ℝ := (Real.log r)⁻¹^2

lemma admissible_baseLoss : AdmissibleAngularLoss baseLoss := by
  have hlog : 0 < Real.log (2:ℝ) := Real.log_pos (by norm_num)
  refine ⟨?_,1,fun n : ℕ => ((Real.log (2:ℝ))⁻¹)^2 * (((n+1:ℕ):ℝ)^2)⁻¹,?_,?_,?_⟩
  · filter_upwards [eventually_gt_atTop (1:ℝ)] with r hr
    refine ⟨?_,le_rfl⟩
    exact sq_pos_of_pos (inv_pos.mpr (Real.log_pos hr))
  · intro n
    positivity
  · exact ((summable_nat_add_iff 1).mpr (Real.summable_nat_pow_inv.mpr (by norm_num : 1 < (2:ℕ)))).mul_left _
  · intro n r hl hu
    have hr : 0 < r := (by positivity : (0:ℝ)<2^(n+1)).trans hl
    have hnr : 0 < ((n+1:ℕ):ℝ) := by positivity
    have hh : ((n+1:ℕ):ℝ)*Real.log (2:ℝ) < Real.log r := by
      simpa only [Real.log_pow] using Real.strictMonoOn_log (by positivity : (0:ℝ)<2^(n+1)) hr hl
    have hi := inv_le_inv₀ (mul_pos hnr hlog |>.trans hh) (mul_pos hnr hlog)
    have hle : (Real.log r)⁻¹ ≤ (((n+1:ℕ):ℝ)*Real.log (2:ℝ))⁻¹ := hi.mpr hh.le
    have hs := sq_le_sq₀ (inv_nonneg.mpr ((mul_pos hnr hlog).trans hh).le)
      (inv_nonneg.mpr (mul_pos hnr hlog).le) |>.mpr hle
    dsimp [baseLoss]
    calc
      (Real.log r)⁻¹^2 ≤ (((n+1:ℕ):ℝ)*Real.log (2:ℝ))⁻¹^2 := hs
      _ = ((Real.log (2:ℝ))⁻¹)^2 * (((n+1:ℕ):ℝ)^2)⁻¹ := by
        rw [mul_inv,mul_pow,inv_pow]
        ring

lemma SectorEventually.of_radial {P : ℂ → Prop}
    (h : ∀ᶠ r : ℝ in atTop, ∀ z : ℂ, ‖z‖=r → P z) : SectorEventually P := by
  obtain ⟨R,hR⟩ := eventually_atTop.mp h
  exact ⟨baseLoss,R,admissible_baseLoss,fun z hz => hR ‖z‖ hz.1.le z rfl⟩

lemma SectorEventually.truth : SectorEventually (fun _ => True) :=
  ⟨baseLoss,0,admissible_baseLoss,fun _ _ => True.intro⟩

lemma SectorEventually.realpart_pos : SectorEventually (fun z => 0 < z.re) := by
  obtain ⟨R,hR⟩ := eventually_atTop.mp admissible_baseLoss.1
  refine ⟨baseLoss,max R 0,admissible_baseLoss,?_⟩
  intro z hz
  have hp := (hR ‖z‖ ((le_max_left _ _).trans hz.1.le)).1
  have hn : z ≠ 0 := norm_pos_iff.mp ((le_max_right _ _).trans_lt hz.1)
  have harg : |z.arg| < Real.pi/2 := by linarith [hz.2]
  exact (Complex.abs_arg_lt_pi_div_two_iff.mp harg).resolve_right hn

end DegeneratingTrees
end

end OAI
