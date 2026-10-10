import OAI.Analysis.LienardCycles.PositiveZero

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
namespace QuinticLienard.PositiveZero
open ScalarArcs ArcFamilies PositiveWidth PartialCalculus
variable {P : Type uP} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
variable (Φ : P × ℝ → ℝ) (hΦ : ∀ q, 0<q.2 → ContDiffAt ℝ ω Φ q)
    (hloc : ∀ x : State P, 0<x.2.1 → ∃ f : State P × ℝ → State P,
      ContDiffAt ℝ ω f (x,0) ∧ ∀ᶠ q in 𝓝 (x,(0:ℝ)),
        f (q.1,0)=q.1 ∧ HasDerivAt (fun s => f (q.1,s)) (field Φ (f q)) q.2)
include hΦ hloc
lemma cubic_direction {γ : ℝ → P} (hγ : ContDiff ℝ ω γ) {h r β : ℝ}
    (hbase : ∀ p, Φ (p,h)=0) (hz : ∀ x, Φ (γ 0,x)=0) (hh : 0<h) (hr : 0<r)
    (hβ : ∀ x, 0<x → first (fun q : ℝ × ℝ => Φ (γ q.1,q.2)) (0,x)=β*(x-h)^3/6) :
    deriv (fun s => midpointAtWidth Φ ((γ s,h),r)) 0=β*r^6/105 := by
  apply zero_direction Φ hΦ hloc hγ hbase hz hh hr
    (B:=fun y => β*(r^6*y/48-r^4*y^3/48+r^2*y^5/80-y^7/336))
  · intro y hy
    have hy2 : y^2≤r^2 := by nlinarith [mul_nonneg (show 0≤r-y by linarith [hy.2]) (show 0≤r+y by linarith [hy.1])]
    rw [hβ _ (by linarith)]
    convert ((((((hasDerivAt_id y).const_mul (r^6)).div_const 48).sub
      ((((hasDerivAt_id y).pow 3).const_mul (r^4)).div_const 48)).add
      ((((hasDerivAt_id y).pow 5).const_mul (r^2)).div_const 80)).sub
      (((hasDerivAt_id y).pow 7).div_const 336)).const_mul β using 1 <;>
        (first | rfl | (dsimp; ring))
  · ring

noncomputable def pathMidpoint (γ : ℝ → P) (h : ℝ) (q : ℝ × ℝ) : ℝ :=
  midpointAtWidth Φ ((γ q.1,h),q.2)
lemma pathMidpoint_analytic {γ : ℝ → P} (hγ : ContDiff ℝ ω γ) {h θ r : ℝ}
    (hh : 0<h) (hr : 0<r) : ContDiffAt ℝ ω (pathMidpoint Φ γ h) (θ,r) :=
  (midpointAtWidth_analytic Φ hΦ hloc (p:=γ θ) hh hr).comp (θ,r)
    (((hγ.contDiffAt.comp (θ,r) contDiffAt_fst).prodMk contDiffAt_const).prodMk contDiffAt_snd)
lemma cubic_mixed {γ : ℝ → P} (hγ : ContDiff ℝ ω γ) {h r β : ℝ}
    (hbase : ∀ p, Φ (p,h)=0) (hz : ∀ x, Φ (γ 0,x)=0) (hh : 0<h) (hr : 0<r)
    (hβ : ∀ x, 0<x → first (fun q : ℝ × ℝ => Φ (γ q.1,q.2)) (0,x)=β*(x-h)^3/6) :
    first (second (pathMidpoint Φ γ h)) (0,r)=6*β*r^5/105 := by
  have ha := pathMidpoint_analytic Φ hΦ hloc (θ:=0) hγ hh hr
  rw [mixed_comm ha]
  apply (second_hasDerivAt ((first_contDiffAt ha).differentiableAt (by simp))).unique
  have hd : HasDerivAt (fun s => β*s^6/105) (6*β*r^5/105) r := by
    convert (((hasDerivAt_id r).pow 6).const_mul β).div_const 105 using 1 <;>
      (first | rfl | (dsimp; ring))
  apply hd.congr_of_eventuallyEq
  filter_upwards [continuousAt_const.eventually_lt continuousAt_id hr] with s hs
  have hd := (first_hasDerivAt ((pathMidpoint_analytic Φ hΦ hloc (θ:=0) hγ hh hs).differentiableAt (by simp))).deriv
  simp only [id_eq] at hd
  rw [←hd]
  exact cubic_direction Φ hΦ hloc hγ hbase hz hh hs hβ
end QuinticLienard.PositiveZero

end OAI
