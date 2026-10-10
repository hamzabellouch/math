import OAI.Analysis.LienardCycles.CubicVariation

namespace OAI

open scoped Topology NNReal ContDiff Manifold
open Filter Set
open Set Filter Metric MeasureTheory
open scoped Topology NNReal ContDiff
open Set Filter Metric
open scoped Topology ENNReal
open scoped Topology
open Set Filter MeasureTheory
open Set Filter
open scoped Topology ContDiff

open Set Filter
open scoped Topology ContDiff
namespace QuinticLienard.QuadraticCoordinates
open PartialCalculus QuadraticVariation
lemma Hr_zero {r : ℝ} (hr : 0<r) : Hr ((0,0),r)=0 := by
  apply (Hr_hasDerivAt hr).unique ((hasDerivAt_const r (0:ℝ)).congr_of_eventuallyEq ?_)
  filter_upwards [continuousAt_const.eventually_lt continuousAt_id hr] with s hs
  exact (zero_data hs).2
lemma R_zero {r : ℝ} (hr : 0<r) : R ((0,0),r)=2*r/3 := by
  have hd : HasDerivAt (fun s : ℝ => s^2/3) (2*r/3) r := by
    convert ((hasDerivAt_id r).pow 2).div_const 3 using 1 <;> (first | rfl | (dsimp; ring))
  apply (R_hasDerivAt hr).unique (hd.congr_of_eventuallyEq ?_)
  filter_upwards [continuousAt_const.eventually_lt continuousAt_id hr] with s hs
  exact P_zero hs
lemma S_zero {r : ℝ} (hr : 0<r) : S ((0,0),r)=4*r^3/15 := by
  have hd : HasDerivAt (fun s : ℝ => s^4/15) (4*r^3/15) r := by
    convert ((hasDerivAt_id r).pow 4).div_const 15 using 1 <;> (first | rfl | (dsimp; ring))
  apply (S_hasDerivAt hr).unique (hd.congr_of_eventuallyEq ?_)
  filter_upwards [continuousAt_const.eventually_lt continuousAt_id hr] with s hs
  exact Q_zero hs
lemma fderiv_Hr {d k r : ℝ} (hr : 0<r) (a b c : ℝ) :
    fderiv ℝ Hr ((d,k),r) ((a,b),c)=a*R ((d,k),r)+b*S ((d,k),r)+c*Hrr ((d,k),r) := by
  rw [fderiv_model]
  have hd : direction ((1,0),0) Hr ((d,k),r)=R ((d,k),r) := direction_comm (H_analytic hr) _ _
  have hk : direction ((0,1),0) Hr ((d,k),r)=S ((d,k),r) := direction_comm (H_analytic hr) _ _
  rw [hd,hk]
  rfl
end QuinticLienard.QuadraticCoordinates

namespace QuinticLienard.QuadraticFit
open QuadraticCoordinates QuadraticVariation PartialCalculus
lemma fit_zero {r : ℝ} (hr : 0<r) : fitD ((r,0),0)=0 ∧ fitK ((r,0),0)=0 :=
  fit_unique hr (by simpa using hr) (by norm_num) (zero_data hr).2 (Hr_zero hr)
lemma fit_direction_zero {μ ν : ℝ → ℝ} {θ m n : ℝ}
    (hm : HasDerivAt μ m θ) (hn : HasDerivAt ν n θ) (hμ : μ θ=0) (hν : ν θ=0) :
    HasDerivAt (fun t => fitD (((1:ℝ),μ t),ν t)) (3*(4*m-n)/2) θ ∧
    HasDerivAt (fun t => fitK (((1:ℝ),μ t),ν t)) (15*(n-2*m)/2) θ := by
  let d : ℝ → ℝ := fun t => fitD (((1:ℝ),μ t),ν t)
  let k : ℝ → ℝ := fun t => fitK (((1:ℝ),μ t),ν t)
  have hpos : (0:ℝ)<1 := by norm_num
  have hz : |(0:ℝ)|<1 := by norm_num
  have hd0 : d θ=0 := by simpa only [d,hμ,hν] using (fit_zero hpos).1
  have hk0 : k θ=0 := by simpa only [k,hμ,hν] using (fit_zero hpos).2
  have hfd : DifferentiableAt ℝ d θ := by
    have hf : DifferentiableAt ℝ fitD (((1:ℝ),μ θ),ν θ) := by
      rw [hμ,hν]
      exact (fitD_analytic hpos hz hz).differentiableAt (by simp)
    have hg : DifferentiableAt ℝ (fun t => (((1:ℝ),μ t),ν t)) θ :=
      (((differentiableAt_const (1:ℝ)).prodMk hm.differentiableAt).prodMk hn.differentiableAt)
    exact DifferentiableAt.comp (g := fitD) (f := fun t => (((1:ℝ),μ t),ν t)) θ hf hg
  have hfk : DifferentiableAt ℝ k θ := by
    have hf : DifferentiableAt ℝ fitK (((1:ℝ),μ θ),ν θ) := by
      rw [hμ,hν]
      exact (fitK_analytic hpos hz hz).differentiableAt (by simp)
    have hg : DifferentiableAt ℝ (fun t => (((1:ℝ),μ t),ν t)) θ :=
      (((differentiableAt_const (1:ℝ)).prodMk hm.differentiableAt).prodMk hn.differentiableAt)
    exact DifferentiableAt.comp (g := fitK) (f := fun t => (((1:ℝ),μ t),ν t)) θ hf hg
  have he : ∀ᶠ t in 𝓝 θ, H ((d t,k t),1)=μ t ∧ Hr ((d t,k t),1)=ν t := by
    have hμb : |μ θ|<1 := by rw [hμ]; exact hz
    have hνb : |ν θ|<1 := by rw [hν]; exact hz
    filter_upwards [hm.continuousAt.abs.eventually_lt continuousAt_const hμb,
      hn.continuousAt.abs.eventually_lt continuousAt_const hνb] with t ht hu
    exact fit_spec hpos ht hu
  have hh := ((H_analytic (d:=d θ) (k:=k θ) hpos).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt θ
    ((hfd.hasDerivAt.prodMk hfk.hasDerivAt).prodMk (hasDerivAt_const θ (1:ℝ)))
  have hv := ((Hr_analytic (d:=d θ) (k:=k θ) hpos).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt θ
    ((hfd.hasDerivAt.prodMk hfk.hasDerivAt).prodMk (hasDerivAt_const θ (1:ℝ)))
  have heh := hh.unique (hm.congr_of_eventuallyEq (he.mono fun _ h => h.1))
  have hev := hv.unique (hn.congr_of_eventuallyEq (he.mono fun _ h => h.2))
  rw [hd0,hk0,fderiv_model] at heh
  change deriv d θ*P ((0,0),1)+deriv k θ*Q ((0,0),1)+0*Hr ((0,0),1)=m at heh
  rw [hd0,hk0,fderiv_Hr hpos] at hev
  norm_num only [P_zero hpos,Q_zero hpos,R_zero hpos,S_zero hpos,one_pow,mul_one,zero_mul,add_zero] at heh hev
  constructor
  · have hed : deriv d θ=3*(4*m-n)/2 := by linarith only [heh,hev]
    simpa only [hed] using hfd.hasDerivAt
  · have hek : deriv k θ=15*(n-2*m)/2 := by linarith only [heh,hev]
    simpa only [hek] using hfk.hasDerivAt
end QuinticLienard.QuadraticFit

end OAI
