import OAI.Analysis.LienardCycles.FiberQuotient

namespace OAI

universe uι

open scoped Topology NNReal ContDiff Manifold
open Filter Set
open Set Filter Metric MeasureTheory
open scoped Topology NNReal ContDiff
open Set Filter Metric
open scoped Topology ENNReal
open scoped Topology
open Set Filter MeasureTheory
open Set Filter
open Set Filter Asymptotics
open scoped Topology ContDiff

open Set Filter
open scoped Topology ContDiff
namespace QuinticLienard.SmallWidth
open PartialCalculus
abbrev Space := (ℝ × ℝ) × ℝ
noncomputable def radial (F : Space → ℝ) : Space → ℝ := direction ((0,1),0) F
noncomputable def fiber (F : Space → ℝ) : Space → ℝ := direction ((0,0),1) F
noncomputable def correction (F : Space → ℝ) (q : ℝ × ℝ) : ℝ :=
  (F (q,q.2^5)-F (q,0))/q.2^3
lemma radial_chain {F : Space → ℝ} {h r : ℝ}
    (hF : DifferentiableAt ℝ F ((h,r),r^5)) :
    HasDerivAt (fun s => F ((h,s),s^5))
      (radial F ((h,r),r^5)+5*r^4*fiber F ((h,r),r^5)) r := by
  have hd := hF.hasFDerivAt.comp_hasDerivAt r
    (((hasDerivAt_const r h).prodMk (hasDerivAt_id r)).prodMk ((hasDerivAt_id r).pow 5))
  have hd' : HasDerivAt (fun s => F ((h,s),s^5))
      (fderiv ℝ F ((h,r),r^5) ((0,1),5*r^4)) r := by simpa using! hd
  have he : (((0,1),5*r^4):Space)=((0,1),0)+(5*r^4) • ((0,0),1) := by ext <;> simp
  rw [he,map_add,map_smul] at hd'
  exact hd'

lemma radial_zero_chain {F : Space → ℝ} {h r : ℝ}
    (hF : DifferentiableAt ℝ F ((h,r),0)) :
    HasDerivAt (fun s => F ((h,s),0)) (radial F ((h,r),0)) r :=
  hF.hasFDerivAt.comp_hasDerivAt r
    (((hasDerivAt_const r h).prodMk (hasDerivAt_id r)).prodMk (hasDerivAt_const r (0:ℝ)))
lemma correction_derivative {F : Space → ℝ} {h r : ℝ} (hr : r≠0)
    (hF : ContDiffAt ℝ ω F ((h,r),r^5)) (hF0 : ContDiffAt ℝ ω F ((h,r),0)) :
    deriv (fun s => correction F (h,s)) r/r =
      r*((radial F ((h,r),r^5)-radial F ((h,r),0))/r^5)+
      5*fiber F ((h,r),r^5)-3*((F ((h,r),r^5)-F ((h,r),0))/r^5) := by
  have hd := ((radial_chain (hF.differentiableAt (by simp))).sub
    (radial_zero_chain (hF0.differentiableAt (by simp)))).div ((hasDerivAt_id r).pow 3) (pow_ne_zero _ hr)
  change HasDerivAt (fun s => correction F (h,s)) _ r at hd
  rw [hd.deriv]
  dsimp
  field_simp
  ring

lemma correction_derivative_limit {F : Space → ℝ} {h₀ : ℝ}
    (hF : ContDiffAt ℝ ω F ((h₀,0),0)) {ι : Type uι} {l : Filter ι}
    {h r : ι → ℝ} (hh : Tendsto h l (𝓝 h₀)) (hr : Tendsto r l (𝓝 0))
    (hne : ∀ᶠ z in l, r z≠0) :
    Tendsto (fun z => deriv (fun s => correction F (h z,s)) (r z)/r z) l
      (𝓝 (2*fiber F ((h₀,0),0))) := by
  have hp := hh.prodMk_nhds hr
  have ht : Tendsto (fun z => (r z)^5) l (𝓝 0) := by simpa using hr.pow 5
  have htn : ∀ᶠ z in l, (r z)^5≠0 := hne.mono (fun _ hz => pow_ne_zero _ hz)
  have hf := fiber_quotient_tendsto (hF.hasStrictFDerivAt (by simp)) hp ht htn
  have hFr : ContDiffAt ℝ ω (radial F) ((h₀,0),0) := direction_contDiffAt hF _
  have hfr := fiber_quotient_tendsto (hFr.hasStrictFDerivAt (by simp)) hp ht htn
  have hFe : ContDiffAt ℝ ω (fiber F) ((h₀,0),0) := direction_contDiffAt hF _
  have hfe := hFe.continuousAt.tendsto.comp (hp.prodMk_nhds ht)
  have hs := ((hr.mul hfr).add (hfe.const_mul 5)).sub (hf.const_mul 3)
  have he : 0*(fderiv ℝ (radial F) ((h₀,0),0) (0,1))+
      5*fiber F ((h₀,0),0)-3*(fderiv ℝ F ((h₀,0),0) (0,1))=2*fiber F ((h₀,0),0) := by
    dsimp [fiber,direction]
    change 0 * _ + 5 * (fderiv ℝ F ((h₀,0),0) ((0,0),1)) -
      3 * (fderiv ℝ F ((h₀,0),0) ((0,0),1)) = 2 * (fderiv ℝ F ((h₀,0),0) ((0,0),1))
    ring
  rw [he] at hs
  apply hs.congr'
  have ha := hF.eventually (by simp)
  filter_upwards [(hp.prodMk_nhds ht).eventually ha,
    (hp.prodMk_nhds tendsto_const_nhds).eventually ha,hne] with z hz hz0 hzn
  exact (correction_derivative hzn hz hz0).symm
end QuinticLienard.SmallWidth

end OAI
