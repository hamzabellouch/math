import OAI.Analysis.LienardCycles.FitSmall

namespace OAI

universe uP

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
namespace QuinticLienard.PositiveFit
open ScalarArcs ArcFamilies PositiveWidth PartialCalculus QuadraticFit
variable {P : Type uP} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
variable (Φ : P × ℝ → ℝ) (hΦ : ∀ q, 0<q.2 → ContDiffAt ℝ ω Φ q)
    (hloc : ∀ x : State P, 0<x.2.1 → ∃ f : State P × ℝ → State P,
      ContDiffAt ℝ ω f (x,0) ∧ ∀ᶠ q in 𝓝 (x,(0:ℝ)),
        f (q.1,0)=q.1 ∧ HasDerivAt (fun s => f (q.1,s)) (field Φ (f q)) q.2)
noncomputable def m (h : ℝ) (q : P × ℝ) : ℝ := midpointAtWidth Φ ((q.1,h),q.2)
noncomputable def n (h : ℝ) : P × ℝ → ℝ := direction (0,1) (m Φ h)
noncomputable def d (h r : ℝ) (p : P) : ℝ := fitD ((r,m Φ h (p,r)),n Φ h (p,r))
noncomputable def k (h r : ℝ) (p : P) : ℝ := fitK ((r,m Φ h (p,r)),n Φ h (p,r))
include hΦ hloc
lemma m_analytic {p : P} {h r : ℝ} (hh : 0<h) (hr : 0<r) :
    ContDiffAt ℝ ω (m Φ h) (p,r) :=
  (midpointAtWidth_analytic Φ hΦ hloc hh hr).comp (p,r)
    ((contDiffAt_fst.prodMk contDiffAt_const).prodMk contDiffAt_snd)
lemma n_analytic {p : P} {h r : ℝ} (hh : 0<h) (hr : 0<r) :
    ContDiffAt ℝ ω (n Φ h) (p,r) := direction_contDiffAt (m_analytic Φ hΦ hloc hh hr) _
lemma m_hasDerivAt {p : P} {h r : ℝ} (hh : 0<h) (hr : 0<r) :
    HasDerivAt (fun s => m Φ h (p,s)) (n Φ h (p,r)) r := by
  exact ((m_analytic Φ hΦ hloc (p:=p) hh hr).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt r
    ((hasDerivAt_const r p).prodMk (hasDerivAt_id r))
lemma m_abs_lt {p : P} {h r : ℝ} (hh : 0<h) (hr : 0<r) : |m Φ h (p,r)|<r :=
  midpointAtWidth_abs_lt Φ hΦ hloc hh hr
lemma n_abs_lt {p : P} {h r : ℝ} (hh : 0<h) (hr : 0<r) : |n Φ h (p,r)|<1 := by
  rw [←(m_hasDerivAt Φ hΦ hloc hh hr).deriv]
  exact PositiveTransport.midpoint_width_deriv_abs_lt Φ hΦ hloc hh hr
lemma d_analytic {p : P} {h r : ℝ} (hh : 0<h) (hr : 0<r) :
    ContDiffAt ℝ ω (d Φ h r) p :=
  (fitD_analytic hr (m_abs_lt Φ hΦ hloc hh hr) (n_abs_lt Φ hΦ hloc hh hr)).comp p
    ((contDiffAt_const.prodMk ((m_analytic Φ hΦ hloc hh hr).comp p
      (contDiffAt_id.prodMk contDiffAt_const))).prodMk
      ((n_analytic Φ hΦ hloc hh hr).comp p (contDiffAt_id.prodMk contDiffAt_const)))
lemma k_analytic {p : P} {h r : ℝ} (hh : 0<h) (hr : 0<r) :
    ContDiffAt ℝ ω (k Φ h r) p :=
  (fitK_analytic hr (m_abs_lt Φ hΦ hloc hh hr) (n_abs_lt Φ hΦ hloc hh hr)).comp p
    ((contDiffAt_const.prodMk ((m_analytic Φ hΦ hloc hh hr).comp p
      (contDiffAt_id.prodMk contDiffAt_const))).prodMk
      ((n_analytic Φ hΦ hloc hh hr).comp p (contDiffAt_id.prodMk contDiffAt_const)))
lemma fit_quadratic {p : P} {h r D K : ℝ} (hh : 0<h) (hr : 0<r)
    (he : ∀ x, Φ (p,h+x)=Φ (p,h)+D*x+K*x^2/2) :
    d Φ h r p=D ∧ k Φ h r p=K := by
  have hm : ∀ s, 0<s → m Φ h (p,s)=QuadraticCoordinates.H ((D,K),s) :=
    fun s hs => midpoint_quadratic Φ hΦ hloc hh hs he
  have hn : n Φ h (p,r)=QuadraticCoordinates.Hr ((D,K),r) := by
    apply (m_hasDerivAt Φ hΦ hloc hh hr).unique
    apply (QuadraticCoordinates.Hr_hasDerivAt hr).congr_of_eventuallyEq
    filter_upwards [continuousAt_const.eventually_lt continuousAt_id hr] with s hs
    exact hm s hs
  exact fit_unique hr (m_abs_lt Φ hΦ hloc hh hr) (n_abs_lt Φ hΦ hloc hh hr) (hm r hr).symm hn.symm

lemma n_path {γ : ℝ → P} (hγ : ContDiff ℝ ω γ) {h r θ : ℝ} (hh : 0<h) (hr : 0<r) :
    n Φ h (γ θ,r)=second (PositiveZero.pathMidpoint Φ γ h) (θ,r) := by
  exact (m_hasDerivAt Φ hΦ hloc hh hr).unique
    (second_hasDerivAt ((PositiveZero.pathMidpoint_analytic Φ hΦ hloc hγ hh hr).differentiableAt (by simp)))
lemma cubic_fit {γ : ℝ → P} (hγ : ContDiff ℝ ω γ) {h β : ℝ}
    (hbase : ∀ p, Φ (p,h)=0) (hz : ∀ x, Φ (γ 0,x)=0) (hh : 0<h)
    (hβ : ∀ x, 0<x → first (fun q : ℝ × ℝ => Φ (γ q.1,q.2)) (0,x)=β*(x-h)^3/6) :
    HasDerivAt (fun s => d Φ h 1 (γ s)) (-β/35) 0 ∧
    HasDerivAt (fun s => k Φ h 1 (γ s)) (2*β/7) 0 := by
  have hp : (0:ℝ)<1 := by norm_num
  let μ : ℝ → ℝ := fun s => m Φ h (γ s,1)
  let ν : ℝ → ℝ := fun s => n Φ h (γ s,1)
  have hm : HasDerivAt μ (β/105) 0 := by
    have hd := ((m_analytic Φ hΦ hloc (p:=γ 0) hh hp).comp 0
      (hγ.contDiffAt.prodMk contDiffAt_const)).differentiableAt (by simp)
    have he := PositiveZero.cubic_direction Φ hΦ hloc hγ hbase hz hh hp hβ
    norm_num only [one_pow,mul_one] at he
    change deriv μ 0=β/105 at he
    have hdm : DifferentiableAt ℝ μ 0 := hd
    simpa only [he] using hdm.hasDerivAt
  have hn : HasDerivAt ν (6*β/105) 0 := by
    have hd := first_hasDerivAt ((second_contDiffAt
      (PositiveZero.pathMidpoint_analytic Φ hΦ hloc (θ:=0) hγ hh hp)).differentiableAt (by simp))
    have he := PositiveZero.cubic_mixed Φ hΦ hloc hγ hbase hz hh hp hβ
    norm_num only [one_pow,mul_one] at he
    rw [he] at hd
    apply hd.congr_of_eventuallyEq
    exact Filter.Eventually.of_forall (fun s => n_path Φ hΦ hloc hγ hh hp)
  have hm0 : μ 0=0 := PositiveZero.zero_midpoint Φ hΦ hloc hz hh hp
  have hn0 : ν 0=0 := by
    apply (m_hasDerivAt Φ hΦ hloc hh hp).unique
    apply (hasDerivAt_const (1:ℝ) (0:ℝ)).congr_of_eventuallyEq
    filter_upwards [continuousAt_const.eventually_lt continuousAt_id hp] with s hs
    exact PositiveZero.zero_midpoint Φ hΦ hloc hz hh hs
  have hf := fit_direction_zero hm hn hm0 hn0
  convert hf using 2 <;> (first | rfl | ring)
end QuinticLienard.PositiveFit

end OAI
