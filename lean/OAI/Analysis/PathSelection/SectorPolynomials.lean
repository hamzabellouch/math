import Mathlib
import OAI.Analysis.PathSelection.CoefficientFields
import OAI.Analysis.PathSelection.PuiseuxInverses

namespace OAI

/-! Polynomial control and sector data for Puiseux expansions. -/

noncomputable section
open Set Filter Topology Metric Polynomial
open scoped BigOperators NNReal ENNReal

open Set Filter Topology Complex
namespace DegeneratingTrees.Clock

lemma sector_sqrt_le_re : ∀ᶠ z in sectorInfinity, ‖z‖^(1/2:ℝ) ≤ z.re := by
  have hdata : ∀ᶠ r : ℝ in atTop, 0<r ∧ 0≤baseLoss r ∧ baseLoss r≤Real.pi/2 ∧
      2*r^(-(1/2:ℝ)) ≤ baseLoss r := by
    filter_upwards [eventually_gt_atTop (0:ℝ),admissible_baseLoss.1,
      admissible_baseLoss.tendsto_zero.eventually (gt_mem_nhds (show (0:ℝ)<Real.pi/2 by positivity)),
      admissible_baseLoss.power_absorption (show (0:ℝ)<1/2 by norm_num) 2] with r hr hp hpi hs
    exact ⟨hr,hp.1.le,hpi.le,hs⟩
  obtain ⟨R,hR⟩ := eventually_atTop.mp hdata
  refine ⟨baseLoss,R,admissible_baseLoss,?_⟩
  intro z hz
  obtain ⟨hr,hp,hpi,hs⟩ := hR ‖z‖ hz.1.le
  have he : ‖z‖^(-(1/2:ℝ))*‖z‖=‖z‖^(1/2:ℝ) := by
    calc
      _ = ‖z‖^(-(1/2:ℝ))*‖z‖^(1:ℝ) := by rw [Real.rpow_one]
      _ = ‖z‖^(-(1/2:ℝ)+1) := (Real.rpow_add hr _ _).symm
      _ = _ := by norm_num
  have hm := mul_le_mul_of_nonneg_right hs (norm_nonneg z)
  have hl := half_loss_norm_le_re hp hpi hz.2
  rw [mul_assoc,he] at hm
  change ‖z‖^(1/2:ℝ) ≤ z.re
  nlinarith

lemma real_power_exp_sqrt (q ε : ℝ) (hε : 0<ε) :
    ∀ᶠ r : ℝ in atTop,r^q ≤ Real.exp (ε*r^(1/2:ℝ)) := by
  have hc : 0<ε/(|q|+1) := div_pos hε (by positivity)
  have hlog := (isLittleO_log_rpow_rpow_atTop (s := (1/2:ℝ)) 1 (by norm_num)).bound hc
  filter_upwards [hlog,eventually_gt_atTop (1:ℝ)] with r hh hr
  have hr0 : 0<r := zero_lt_one.trans hr
  have hp : 0<r^(1/2:ℝ) := Real.rpow_pos_of_pos hr0 _
  have hl : 0<Real.log r := Real.log_pos hr
  have hh' : Real.log r ≤ (ε/(|q|+1))*r^(1/2:ℝ) := by
    simpa only [Real.rpow_one,Real.norm_eq_abs,abs_of_pos hl,abs_of_pos hp] using hh
  have hh'' := mul_le_mul_of_nonneg_left hh' (show 0≤|q|+1 by positivity)
  have he : (|q|+1)*((ε/(|q|+1))*r^(1/2:ℝ))=ε*r^(1/2:ℝ) := by field_simp
  rw [he] at hh''
  rw [Real.rpow_def_of_pos hr0]
  apply Real.exp_le_exp.mpr
  nlinarith [le_abs_self q]

lemma polynomial_sector_slow {f : ℂ → ℂ} {C q : ℝ}
    (hC : 0≤C) (hf : ∀ᶠ z in radialInfinity,‖f z‖ ≤ C*‖z‖^q) : SectorSlow f := by
  intro ε hε
  have hFr : ∀ᶠ z in sectorInfinity,‖f z‖ ≤ C*‖z‖^q := by
    obtain ⟨R,hR⟩ := radial_eventually hf
    apply SectorEventually.of_radial
    filter_upwards [eventually_gt_atTop R] with r hr
    intro z hz
    exact hR z (hz ▸ hr)
  apply Asymptotics.IsBigO.of_bound C
  have hpower : ∀ᶠ z in sectorInfinity,‖z‖^q ≤ Real.exp (ε*‖z‖^(1/2:ℝ)) := by
    apply SectorEventually.of_radial
    filter_upwards [real_power_exp_sqrt q ε hε] with r hr
    intro z hz
    simpa only [hz] using hr
  filter_upwards [hFr,hpower,sector_sqrt_le_re] with z hF hp hs
  calc
    ‖f z‖ ≤ C*‖z‖^q := hF
    _ ≤ C*Real.exp (ε*‖z‖^(1/2:ℝ)) := mul_le_mul_of_nonneg_left hp hC
    _ ≤ C*‖Real.exp (ε*z.re)‖ := by
      rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hs hε.le)) hC

end DegeneratingTrees.Clock

 

 

 

open Set Filter Topology Complex
namespace DegeneratingTrees.Clock

lemma sector_radial_eventually {P : ℂ → Prop} (h : ∀ᶠ z in radialInfinity,P z) :
    ∀ᶠ z in sectorInfinity,P z := by
  obtain ⟨R,hR⟩ := radial_eventually h
  exact (tendsto_norm_sectorInfinity.eventually (eventually_gt_atTop R)).mono hR

lemma sector_halfplane_analytic {G : ℂ → ℂ} {R : ℝ}
    (hG : ∀ z : ℂ,R<‖z‖ → 0<z.re → AnalyticAt ℂ G z) :
    ∀ᶠ z in sectorInfinity,AnalyticAt ℂ G z := by
  filter_upwards [tendsto_norm_sectorInfinity.eventually (eventually_gt_atTop R),
    tendsto_re_sectorInfinity.eventually (eventually_gt_atTop (0:ℝ))] with z hz hre
  exact hG z hz hre

lemma sector_analytic_eq_of_ray {f g : ℂ → ℂ}
    (hf : ∀ᶠ z in sectorInfinity,AnalyticAt ℂ f z)
    (hg : ∀ᶠ z in sectorInfinity,AnalyticAt ℂ g z)
    (he : (fun t : ℝ => f (t:ℂ)) =ᶠ[atTop] fun t => g (t:ℂ)) :
    f =ᶠ[sectorInfinity] g := by
  obtain ⟨ω,R,hω,ha⟩ := hf.and hg
  have hz := sector_zero_of_ray_zero hω (fun z hz => (ha z hz).1.sub (ha z hz).2)
    (he.mono (fun _ h => sub_eq_zero.mpr h))
  exact hz.mono (fun _ h => sub_eq_zero.mp h)

 
def PuiseuxSector : Set (ℂ → ℂ) := {f | (∀ᶠ z in sectorInfinity,AnalyticAt ℂ f z) ∧
  Puiseux (fun t : ℝ => f (t:ℂ))}

lemma PuiseuxSector.slow_and_dichotomy {f : ℂ → ℂ} (hf : f∈PuiseuxSector) :
    SectorSlow f ∧ ((∀ᶠ z in sectorInfinity,f z=0) ∨ (∀ᶠ z in sectorInfinity,f z≠0)) := by
  by_cases hz : (fun t : ℝ => f (t:ℂ)) =ᶠ[atTop] fun _ => 0
  · have he := sector_analytic_eq_of_ray hf.1 (Eventually.of_forall (fun _ => analyticAt_const)) hz
    exact ⟨fun ε _ => (ExpBound.zero ε).congr he.symm,Or.inl he⟩
  · obtain ⟨q,C,G,R,hC,hGa,he,hlim⟩ := hf.2.sector_leading hz
    have hGa' := sector_halfplane_analytic hGa
    have hfg := sector_analytic_eq_of_ray hf.1 hGa' he
    have hb := radial_norm_equivalent hC hlim
    have hs := polynomial_sector_slow (show 0≤2*‖C‖ by positivity) (hb.mono (fun _ h => h.2))
    refine ⟨fun ε hε => (hs ε hε).congr hfg.symm,Or.inr ?_⟩
    filter_upwards [hfg,sector_radial_eventually hb,
      tendsto_norm_sectorInfinity.eventually (eventually_gt_atTop (0:ℝ))] with z hz hb hn
    rw [hz]
    apply norm_pos_iff.mp
    exact lt_of_lt_of_le (mul_pos (by exact div_pos (norm_pos_iff.mpr hC) (by norm_num))
      (Real.rpow_pos_of_pos hn _)) hb.1

lemma PuiseuxSector.inv_analytic {f : ℂ → ℂ} (hf : f∈PuiseuxSector) :
    ∀ᶠ z in sectorInfinity,AnalyticAt ℂ (fun z => (f z)⁻¹) z := by
  rcases (PuiseuxSector.slow_and_dichotomy hf).2 with hz | hn
  · apply sector_eventually_analytic_congr (f := fun _ => 0)
      (Eventually.of_forall (fun _ => analyticAt_const))
    exact hz.mono (fun _ hz => by simp [hz])
  · filter_upwards [hf.1,hn] with z ha hn
    exact ha.inv hn

 
theorem puiseux_lowerSectorData : LowerSectorData PuiseuxSector where
  const_mem c := ⟨Eventually.of_forall (fun _ => analyticAt_const),puiseux_const c⟩
  add_mem hf hg := ⟨by filter_upwards [hf.1,hg.1] with z hf hg; exact hf.add hg,hf.2.add hg.2⟩
  neg_mem hf := ⟨hf.1.mono (fun _ hf => hf.neg),hf.2.neg⟩
  mul_mem hf hg := ⟨by filter_upwards [hf.1,hg.1] with z hf hg; exact hf.mul hg,hf.2.mul hg.2⟩
  inv_mem hf := ⟨(PuiseuxSector.inv_analytic hf),hf.2.inv⟩
  analytic hf := hf.1
  slow hf := (PuiseuxSector.slow_and_dichotomy hf).1
  zero_or_ne hf := (PuiseuxSector.slow_and_dichotomy hf).2

end DegeneratingTrees.Clock
end

end OAI
