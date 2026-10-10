import Mathlib
import OAI.Analysis.PathSelection.PerturbativeInverses
import OAI.Analysis.PathSelection.RealClocks

namespace OAI

/-! Real perturbative inverses and near-identity sector transfer. -/

noncomputable section
open Set Filter Topology Metric Polynomial
open scoped BigOperators NNReal ENNReal

open Set Filter Topology Complex Metric
open scoped Asymptotics
namespace DegeneratingTrees.Clock

lemma sector_reflection_of_real {F : ℂ → ℂ}
    (hF : ∀ᶠ z in sectorInfinity,AnalyticAt ℂ F z)
    (hr : ∀ᶠ t : ℝ in atTop,(F (t:ℂ)).im=0) :
    ∀ᶠ z in sectorInfinity,F (star z)=star (F z) := by
  have ha : ∀ᶠ z in sectorInfinity,AnalyticAt ℂ (fun z => star (F (star z))) z := by
    obtain ⟨ω,R,hω,hF⟩ := hF
    exact ⟨ω,R,hω,fun z hz => analyticAt_reflection (hF _ (mem_lossSector_star hz))⟩
  obtain ⟨ω,R,hω,hA⟩ := (hF.and ha).mono (fun z hz => hz.1.sub hz.2)
  have hz : ∀ᶠ t : ℝ in atTop,F (t:ℂ)-star (F (star (t:ℂ)))=0 := by
    filter_upwards [hr] with t ht
    apply sub_eq_zero.mpr
    apply Complex.ext <;> simp [ht]
  have hzero := sector_zero_of_ray_zero hω hA hz
  filter_upwards [hzero] with z hz
  have hh := congrArg star (sub_eq_zero.mp hz)
  simpa only [star_star] using hh.symm

lemma real_part_tendsto_of_perturbation {F : ℂ → ℂ}
    (he : (fun z => F z-z) =o[sectorInfinity] (fun z => logarithmicRadius ‖z‖)) :
    Tendsto (fun t : ℝ => (F (t:ℂ)).re) atTop atTop := by
  have hbase := admissible_baseLoss.tendsto_zero.eventually
    (eventually_le_nhds (show (0:ℝ) < 1/2 by norm_num))
  have hlower : ∀ᶠ t : ℝ in atTop,t/2 ≤ (F (t:ℂ)).re := by
    filter_upwards [tendsto_real_sectorInfinity.eventually (he.bound zero_lt_one),hbase,
      eventually_gt_atTop (1:ℝ)] with t ht hb ht1
    have ht0 : 0 < t := zero_lt_one.trans ht1
    have hn : ‖(t:ℂ)‖=t := Complex.norm_of_nonneg ht0.le
    have hr : 0 < logarithmicRadius t := logarithmicRadius_pos ht1
    have hh : ‖F (t:ℂ)-(t:ℂ)‖ ≤ logarithmicRadius t := by
      simpa only [hn,Real.norm_eq_abs,abs_of_pos hr,one_mul] using ht
    have hrep := (Complex.abs_re_le_norm (F (t:ℂ)-(t:ℂ))).trans hh
    rw [Complex.sub_re,Complex.ofReal_re,abs_le] at hrep
    have hb' := mul_le_mul_of_nonneg_left hb ht0.le
    dsimp [baseLoss] at hb'
    dsimp [logarithmicRadius] at hrep
    nlinarith [hrep.1]
  exact tendsto_atTop_mono' atTop hlower ((tendsto_id.const_mul_atTop (by norm_num : (0:ℝ) < 1/2)).congr (fun t => by dsimp; ring))

 

theorem sector_perturbative_real_inverse {F : ℂ → ℂ}
    (hF : ∀ᶠ z in sectorInfinity,AnalyticAt ℂ F z)
    (he : (fun z => F z-z) =o[sectorInfinity] (fun z => logarithmicRadius ‖z‖))
    (hr : ∀ᶠ t : ℝ in atTop,(F (t:ℂ)).im=0)
    (ω : ℝ → ℝ) (R : ℝ) (hω : AdmissibleAngularLoss ω) :
    ∃ (η : ℝ → ℝ) (T : ℝ) (g : ℂ → ℂ) (I : ℝ → ℝ),AdmissibleAngularLoss η ∧
      AnalyticOnNhd ℂ g (lossSector η T) ∧
      (∀ z∈lossSector η T,g z∈lossSector ω R ∧ F (g z)=z ∧ ‖g z-z‖ ≤ 2*‖F z-z‖) ∧
      Tendsto I atTop atTop ∧
      (∀ᶠ t : ℝ in atTop,g (t:ℂ)=(I t:ℂ) ∧ F (I t:ℂ)=(t:ℂ)) ∧
      (∀ᶠ t : ℝ in atTop,I ((F (t:ℂ)).re)=t) := by
  have htarget : ∀ᶠ z in sectorInfinity,z∈lossSector ω R := ⟨ω,R,hω,fun _ h => h⟩
  obtain ⟨θ,S,hθ,hdata⟩ := htarget.and (sector_reflection_of_real hF hr)
  obtain ⟨η,T,g,hη,hga,hg,hu⟩ := sector_perturbative_inverse_unique hF he θ S hθ
  have hdom : ∀ᶠ z in sectorInfinity,z∈lossSector η T := ⟨η,T,hη,fun _ h => h⟩
  let I : ℝ → ℝ := fun t => (g (t:ℂ)).re
  have hreal : ∀ᶠ t : ℝ in atTop,g (t:ℂ)=(I t:ℂ) ∧ F (I t:ℂ)=(t:ℂ) := by
    filter_upwards [tendsto_real_sectorInfinity.eventually hdom,eventually_gt_atTop (1:ℝ)] with t ht ht1
    have hn : ‖(t:ℂ)‖=t := Complex.norm_of_nonneg (by linarith)
    have hrad : 0 < logarithmicRadius ‖(t:ℂ)‖ := by rw [hn]; exact logarithmicRadius_pos ht1
    have hconj : ‖star (g (t:ℂ))-(t:ℂ)‖=‖g (t:ℂ)-(t:ℂ)‖ := by
      rw [show star (g (t:ℂ))-(t:ℂ)=star (g (t:ℂ)-(t:ℂ)) by simp]; exact norm_star _
    have hmem : star (g (t:ℂ))∈ball (t:ℂ) (logarithmicRadius ‖(t:ℂ)‖) := by
      rw [mem_ball_iff_norm,hconj]
      exact (hg _ ht).2.2.2.trans_lt (by linarith)
    have hroot : F (star (g (t:ℂ)))=(t:ℂ) := by
      rw [(hdata _ (hg _ ht).1).2,(hg _ ht).2.1]
      simp
    have heq := hu _ ht _ hmem hroot
    have him : (g (t:ℂ)).im=0 := by
      have hh := congrArg Complex.im heq
      simp only [Complex.star_def,Complex.conj_im] at hh
      linarith
    have heq' : g (t:ℂ)=(I t:ℂ) := Complex.ext rfl (by simpa using him)
    exact ⟨heq',by rw [←heq']; exact (hg _ ht).2.1⟩
  have hIt : Tendsto I atTop atTop := by
    have hlower : ∀ᶠ t : ℝ in atTop,t/2 ≤ I t := by
      filter_upwards [tendsto_real_sectorInfinity.eventually hdom,
        admissible_baseLoss.tendsto_zero.eventually (eventually_le_nhds zero_lt_one),
        eventually_gt_atTop (1:ℝ)] with t ht hb ht1
      have ht0 : 0 < t := by linarith
      have hn : ‖(t:ℂ)‖=t := Complex.norm_of_nonneg ht0.le
      have hh := (Complex.abs_re_le_norm (g (t:ℂ)-(t:ℂ))).trans (hg _ ht).2.2.2
      rw [Complex.sub_re,Complex.ofReal_re,hn,abs_le] at hh
      have hb' := mul_le_mul_of_nonneg_left hb ht0.le
      dsimp [baseLoss] at hb'
      dsimp [logarithmicRadius] at hh
      dsimp [I]
      nlinarith [hh.1]
    exact tendsto_atTop_mono' atTop hlower ((tendsto_id.const_mul_atTop (by norm_num : (0:ℝ) < 1/2)).congr (fun t => by dsimp; ring))
  refine ⟨η,T,g,I,hη,hga,fun z hz => ⟨(hdata _ (hg z hz).1).1,(hg z hz).2.1,(hg z hz).2.2.1⟩,hIt,hreal,?_⟩
  have hFt := real_part_tendsto_of_perturbation he
  have hFreal : ∀ᶠ t : ℝ in atTop,F (t:ℂ)=((F (t:ℂ)).re:ℂ) := hr.mono fun t ht => Complex.ext rfl (by simpa using ht)
  filter_upwards [hFreal,hFt.eventually (tendsto_real_sectorInfinity.eventually hdom),
    hFt.eventually (eventually_gt_atTop (4:ℝ)),eventually_gt_atTop (4:ℝ),
    tendsto_real_sectorInfinity.eventually (he.bound (by norm_num : (0:ℝ) < 1/32)),
    admissible_baseLoss.tendsto_zero.eventually (eventually_le_nhds zero_lt_one)] with t hrt htη hFt4 ht4 heb hb
  have ht1 : 1 < t := by linarith
  have ht0 : 0 < t := by linarith
  have hF0 : 0 < (F (t:ℂ)).re := by linarith
  have hn : ‖(t:ℂ)‖=t := Complex.norm_of_nonneg ht0.le
  have hFn : ‖F (t:ℂ)‖=(F (t:ℂ)).re := by rw [hrt]; exact Complex.norm_of_nonneg hF0.le
  have hηt : F (t:ℂ)∈lossSector η T := by rwa [hrt]
  have hrad : 0 < logarithmicRadius t := logarithmicRadius_pos ht1
  have he' : ‖F (t:ℂ)-(t:ℂ)‖ ≤ (1/32:ℝ)*logarithmicRadius t := by
    simpa only [hn,Real.norm_eq_abs,abs_of_pos hrad] using heb
  have hrle : logarithmicRadius t ≤ t := by
    have hh := mul_le_mul_of_nonneg_left hb ht0.le
    simpa only [logarithmicRadius,baseLoss,mul_one] using hh
  have hdist : |(F (t:ℂ)).re-t| ≤ t/2 := by
    have hh := (Complex.abs_re_le_norm (F (t:ℂ)-(t:ℂ))).trans he'
    simp only [Complex.sub_re,Complex.ofReal_re] at hh
    exact hh.trans (by linarith)
  have hneighbor := logarithmicRadius_neighbor hFt4.le
    (show (F (t:ℂ)).re/2 ≤ t by linarith [(abs_le.mp hdist).2])
    (show t ≤ 2*(F (t:ℂ)).re by linarith [(abs_le.mp hdist).1])
  have hmem : (t:ℂ)∈ball (F (t:ℂ)) (logarithmicRadius ‖F (t:ℂ)‖) := by
    rw [mem_ball_iff_norm,norm_sub_rev,hFn]
    have hfrr := logarithmicRadius_pos (show 1 < (F (t:ℂ)).re by linarith)
    linarith
  have hleft := hu _ hηt _ hmem rfl
  dsimp [I]
  rw [←hrt,hleft]
  simp

end DegeneratingTrees.Clock

 

 

 

open Set Filter Topology Complex Metric
open scoped Asymptotics
namespace DegeneratingTrees.Clock

theorem sector_log_increment_small {Q g : ℂ → ℂ} {C : ℝ}
    (hC : 0 ≤ C) (hQ : ∀ᶠ z in sectorInfinity,AnalyticAt ℂ Q z)
    (hQb : ∀ᶠ z in sectorInfinity,‖Q z‖ ≤ C*Real.log ‖z‖)
    (hm : ∀ᶠ z in sectorInfinity,‖g z-z‖ ≤ logarithmicRadius ‖z‖)
    (hg : (fun z => g z-z) =o[sectorInfinity] (fun z => ‖z‖/(Real.log ‖z‖)^5)) :
    (fun z => Q (g z)-Q z) =o[sectorInfinity] (fun z => (Real.log ‖z‖)⁻¹^2) := by
  obtain ⟨ω,R,hω,hdata⟩ := hQ.and hQb
  obtain ⟨η,T,hη,hRT,hT1,hdiscs⟩ := hω.logarithmic_discs R (show (0:ℝ) ≤ 2 by norm_num)
  have hdom : ∀ᶠ z in sectorInfinity,z∈lossSector η T := ⟨η,T,hη,fun _ h => h⟩
  have hbase : ∀ᶠ z in sectorInfinity,(Real.log ‖z‖)⁻¹^2 ≤ (1/4:ℝ) :=
    tendsto_norm_sectorInfinity.eventually (admissible_baseLoss.tendsto_zero.eventually
      (eventually_le_nhds (by norm_num : (0:ℝ) < 1/4)))
  apply Asymptotics.IsLittleO.of_bound
  intro δ hδ
  have hconst : 0 < δ/(2*(C+1)) := by positivity
  filter_upwards [hdom,hbase,hm,hg.bound hconst,
    tendsto_norm_sectorInfinity.eventually (eventually_gt_atTop (4:ℝ))] with z hz hb hm he hz4
  let r := logarithmicRadius ‖z‖
  have hz1 : 1 < ‖z‖ := by linarith
  have hL : 0 < Real.log ‖z‖ := Real.log_pos hz1
  have hr : 0 < r := logarithmicRadius_pos hz1
  have hrbound : 2*r ≤ ‖z‖/2 := by
    have hh := mul_le_mul_of_nonneg_left hb (norm_nonneg z)
    dsimp [r,logarithmicRadius]
    nlinarith
  have hdisc : closedBall z (2*r) ⊆ lossSector ω R := by
    convert hdiscs z hz using 1
    dsimp [r,logarithmicRadius]; ring_nf
  have hM (u : ℂ) (hu : u∈closedBall z (2*r)) : ‖Q u‖ ≤ 2*(C+1)*Real.log ‖z‖ := by
    have hdist : ‖u-z‖ ≤ 2*r := mem_closedBall_iff_norm.mp hu
    have hnu : ‖u‖ ≤ ‖z‖^2 := by
      have hh := norm_add_le (u-z) z
      rw [sub_add_cancel] at hh
      nlinarith
    have hlu : ‖z‖/2 ≤ ‖u‖ := by
      have hh := norm_sub_le u (u-z)
      rw [sub_sub_cancel] at hh
      linarith
    have hu0 : 0 < ‖u‖ := by linarith
    have hl : Real.log ‖u‖ ≤ 2*Real.log ‖z‖ := by
      simpa only [Real.log_pow,Nat.cast_ofNat] using Real.log_le_log hu0 hnu
    have hh := mul_le_mul_of_nonneg_left hl hC
    exact (hdata u (hdisc hu)).2.trans (by nlinarith)
  have hinc := cauchy_increment_inner_disc hr (fun u hu => (hdata u (hdisc hu)).1) hM
    (mem_closedBall_self hr.le) (mem_closedBall_iff_norm.mpr hm)
  have hN : 0 < ‖z‖/(Real.log ‖z‖)^5 := by positivity
  have he' : ‖g z-z‖ ≤ (δ/(2*(C+1)))*(‖z‖/(Real.log ‖z‖)^5) := by
    simpa only [Real.norm_eq_abs,abs_of_pos hN] using he
  have ht := mul_le_mul_of_nonneg_left he' (show 0 ≤ (2*(C+1)*Real.log ‖z‖)/r by positivity)
  have heq : (2*(C+1)*Real.log ‖z‖)/r * ((δ/(2*(C+1)))*(‖z‖/(Real.log ‖z‖)^5)) =
      δ*((Real.log ‖z‖)⁻¹^2) := by
    dsimp [r,logarithmicRadius]
    field_simp [hL.ne',show C+1≠0 by linarith,show ‖z‖≠0 by linarith]
  rw [heq] at ht
  simpa only [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg ((Real.log ‖z‖)⁻¹))] using hinc.trans ht

end DegeneratingTrees.Clock

 

 

 

open Set Filter Topology Complex Metric
open scoped Asymptotics
namespace DegeneratingTrees.Clock

lemma tendsto_sectorInfinity_of_logarithmic_displacement {g : ℂ → ℂ}
    (hg : ∀ᶠ z in sectorInfinity,‖g z-z‖ ≤ logarithmicRadius ‖z‖) :
    Tendsto g sectorInfinity sectorInfinity := by
  apply Filter.tendsto_def.mpr
  intro s hs
  obtain ⟨ω,R,hω,hs⟩ := hs
  obtain ⟨η,T,hη,hRT,hT,hdisc⟩ := hω.logarithmic_discs R (show (0:ℝ) ≤ 1 by norm_num)
  have hdom : ∀ᶠ z in sectorInfinity,z∈lossSector η T := ⟨η,T,hη,fun _ h => h⟩
  filter_upwards [hg,hdom] with z hg hz
  apply hs
  apply hdisc z hz
  simpa only [mem_closedBall_iff_norm,one_mul,logarithmicRadius] using hg

lemma logarithmicRadius_isBigO_re :
    (fun z : ℂ => logarithmicRadius ‖z‖) =O[sectorInfinity] Complex.re := by
  apply Asymptotics.IsBigO.of_bound 2
  have hb := tendsto_norm_sectorInfinity.eventually (admissible_baseLoss.tendsto_zero.eventually
    (eventually_le_nhds (show (0:ℝ) < Real.pi/2 by positivity)))
  have hdom : ∀ᶠ z in sectorInfinity,z∈lossSector baseLoss 1 := ⟨baseLoss,1,admissible_baseLoss,fun _ h => h⟩
  filter_upwards [hb,hdom,SectorEventually.realpart_pos] with z hb hz hzr
  have hp := logarithmicRadius_pos hz.1
  have hh := half_loss_norm_le_re (by dsimp [baseLoss]; positivity : 0 ≤ baseLoss ‖z‖) hb hz.2
  rw [Real.norm_eq_abs,Real.norm_eq_abs,abs_of_pos hp,abs_of_pos hzr]
  dsimp [logarithmicRadius,baseLoss] at *
  linarith

lemma logarithmicRadius_isBigO_norm :
    (fun z : ℂ => logarithmicRadius ‖z‖) =O[sectorInfinity] (norm : ℂ → ℝ) := by
  apply Asymptotics.IsBigO.of_bound 1
  filter_upwards [tendsto_norm_sectorInfinity.eventually
    (admissible_baseLoss.tendsto_zero.eventually (eventually_le_nhds zero_lt_one)),
    tendsto_norm_sectorInfinity.eventually (eventually_gt_atTop (1:ℝ))] with z hb hz
  have hh := mul_le_mul_of_nonneg_left hb (norm_nonneg z)
  rw [Real.norm_eq_abs,Real.norm_eq_abs,abs_of_pos (logarithmicRadius_pos hz),abs_of_nonneg (norm_nonneg z),one_mul]
  simpa only [logarithmicRadius,baseLoss,mul_one] using hh

lemma nearIdentity_re_tendsto {g : ℂ → ℂ}
    (hg : (fun z => g z-z) =o[sectorInfinity] (fun z => logarithmicRadius ‖z‖)) :
    Tendsto (fun z => (g z).re/z.re) sectorInfinity (𝓝 1) := by
  have hre : (fun z => (g z).re-z.re) =O[sectorInfinity] (fun z => g z-z) := by
    apply Asymptotics.IsBigO.of_bound 1
    exact Eventually.of_forall fun z => by simpa only [Real.norm_eq_abs,one_mul,Complex.sub_re] using Complex.abs_re_le_norm (g z-z)
  have ht := (hre.trans_isLittleO (hg.trans_isBigO logarithmicRadius_isBigO_re)).tendsto_div_nhds_zero
  have hh := ht.add_const 1
  simp only [zero_add] at hh
  apply hh.congr'
  filter_upwards [SectorEventually.realpart_pos] with z hz
  field_simp [ne_of_gt (show 0<z.re from hz)]
  ring

lemma nearIdentity_re_isBigO {g : ℂ → ℂ}
    (hg : (fun z => g z-z) =o[sectorInfinity] (fun z => logarithmicRadius ‖z‖)) :
    (fun z => (g z).re) =O[sectorInfinity] Complex.re := by
  have hre : (fun z => (g z).re-z.re) =O[sectorInfinity] (fun z => g z-z) := by
    apply Asymptotics.IsBigO.of_bound 1
    exact Eventually.of_forall fun z => by simpa only [Real.norm_eq_abs,one_mul,Complex.sub_re] using Complex.abs_re_le_norm (g z-z)
  have hh := (hre.trans (hg.isBigO.trans logarithmicRadius_isBigO_re)).add (Asymptotics.isBigO_refl Complex.re sectorInfinity)
  simpa only [sub_add_cancel] using hh

 

lemma nearIdentity_realpart_separation {F g e : ℂ → ℂ}
    (hg : (fun z => g z-z) =o[sectorInfinity] (fun z => logarithmicRadius ‖z‖))
    (hF : (fun z => (F z).re) =o[sectorInfinity] Complex.re)
    (he : e =o[sectorInfinity] (fun z => logarithmicRadius ‖z‖)) :
    (fun z => (F (g z)+e z).re) =o[sectorInfinity] Complex.re := by
  have hbound : ∀ᶠ z in sectorInfinity,‖g z-z‖ ≤ logarithmicRadius ‖z‖ := by
    filter_upwards [hg.bound zero_lt_one,tendsto_norm_sectorInfinity.eventually (eventually_gt_atTop (1:ℝ))] with z hz hz1
    simpa only [Real.norm_eq_abs,abs_of_pos (logarithmicRadius_pos hz1),one_mul] using hz
  have ht := tendsto_sectorInfinity_of_logarithmic_displacement hbound
  have hcomp := (hF.comp_tendsto ht).trans_isBigO (nearIdentity_re_isBigO hg)
  have hre : (fun z => (e z).re) =O[sectorInfinity] e := by
    apply Asymptotics.IsBigO.of_bound 1
    exact Eventually.of_forall fun z => by simpa only [Real.norm_eq_abs,one_mul] using Complex.abs_re_le_norm (e z)
  exact hcomp.add (hre.trans_isLittleO (he.trans_isBigO logarithmicRadius_isBigO_re))

end DegeneratingTrees.Clock

 

 

 

open Set Filter Topology Complex
open scoped Asymptotics
namespace DegeneratingTrees.Clock

theorem zero_exponent_real_inverse {F x : ℂ → ℂ} {X : ℝ → ℝ} {C K ε : ℝ}
    (hF : ∀ᶠ z in sectorInfinity,AnalyticAt ℂ F z)
    (hr : ∀ᶠ r : ℝ in atTop,(F (r:ℂ)).im=0)
    (hC : 1≤C) (hK : 0≤K) (hε : 0<ε)
    (hX : Tendsto X atTop atTop) (hlog : Real.log =o[atTop] X)
    (hmod : ∀ᶠ z in sectorInfinity,X ‖z‖/C≤‖x z‖ ∧ ‖x z‖≤C*X ‖z‖)
    (hx : Tendsto x sectorInfinity sectorInfinity)
    (herr : ∀ᶠ z in sectorInfinity,‖F z-z‖≤K*‖z‖*Real.exp (-ε*(x z).re)) :
    ∃ (g : ℂ → ℂ) (I : ℝ → ℝ),
      (∀ᶠ z in sectorInfinity,AnalyticAt ℂ g z ∧ F (g z)=z) ∧
      Tendsto g sectorInfinity sectorInfinity ∧
      Tendsto I atTop atTop ∧
      (∀ᶠ r : ℝ in atTop,g (r:ℂ)=(I r:ℂ) ∧ F (I r:ℂ)=(r:ℂ)) ∧
      (∀ᶠ r : ℝ in atTop,I ((F (r:ℂ)).re)=r) ∧
      (fun z => g z-z) =o[sectorInfinity] (fun z => logarithmicRadius ‖z‖) ∧
      (∀ N : ℕ,(fun z => g z-z) =o[sectorInfinity] (fun z => ‖z‖/(Real.log ‖z‖)^N)) ∧
      Tendsto (fun z => (g z).re/z.re) sectorInfinity (𝓝 1) := by
  have hsmall := zero_exponent_error_small hC hK hε hX hlog hmod hx herr
  obtain ⟨η,T,g,I,hη,hga,hg,hIt,hreal,hri⟩ :=
    sector_perturbative_real_inverse hF hsmall hr baseLoss 1 admissible_baseLoss
  have hdom : ∀ᶠ z in sectorInfinity,z∈lossSector η T := ⟨η,T,hη,fun _ h => h⟩
  have hbound : (fun z => g z-z) =O[sectorInfinity] (fun z => F z-z) := by
    apply Asymptotics.IsBigO.of_bound 2
    exact hdom.mono fun z hz => (hg z hz).2.2
  have hgs := hbound.trans_isLittleO hsmall
  have hdisp : ∀ᶠ z in sectorInfinity,‖g z-z‖≤logarithmicRadius ‖z‖ := by
    filter_upwards [hgs.bound zero_lt_one,tendsto_norm_sectorInfinity.eventually (eventually_gt_atTop (1:ℝ))] with z hz hz1
    simpa only [one_mul,Real.norm_eq_abs,abs_of_pos (logarithmicRadius_pos hz1)] using hz
  refine ⟨g,I,hdom.mono (fun z hz => ⟨hga z hz,(hg z hz).2.1⟩),
    tendsto_sectorInfinity_of_logarithmic_displacement hdisp,hIt,hreal,hri,hgs,?_,
    nearIdentity_re_tendsto hgs⟩
  intro N
  exact hbound.trans_isLittleO (zero_exponent_error_logpower N hC hK hε hX hlog hmod hx herr)

end DegeneratingTrees.Clock
end

end OAI
