import Mathlib
import OAI.Analysis.SymmetricDomains.AnalyticNhdDifferentiableAffine
import OAI.Analysis.SymmetricDomains.AnalyticZeroRealPolydisc
import OAI.Analysis.SymmetricDomains.MeromorphicRemovablePositiveRay

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Set Filter Metric
open scoped Topology

theorem analyticOnNhd_of_differentiableOn_finDim
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    {S : Set E} (hS : IsOpen S) {f : E → ℂ} (hf : DifferentiableOn ℂ f S) :
    AnalyticOnNhd ℂ f S := by
  let e : E ≃L[ℂ] (Fin (Module.finrank ℂ E) → ℂ) := (Module.finBasis ℂ E).equivFunL
  have ha := analyticOnNhd_of_differentiableOn_finite
    (hS.preimage e.symm.continuous) (hf.comp e.symm.differentiable.differentiableOn (fun _ h => h))
  intro x hx
  have hx' : e x ∈ e.symm ⁻¹' S := by simpa only [mem_preimage,e.symm_apply_apply] using hx
  have hcomp := (ha (e x) hx').comp (e.analyticAt x)
  simpa only [Function.comp_def,e.symm_apply_apply] using hcomp

theorem real_parameter_polar_removal {n : ℕ}
    {r R S : ℝ} (hr : 0 < r) (hR : 0 < R) (hRS : R < S)
    (f : (Fin n → ℂ) × ℂ → ℂ)
    (hf : AnalyticOnNhd ℂ f (ball 0 r ×ˢ (ball 0 S \ {0})))
    (hm : ∀ s : Fin n → ℝ, ‖s‖ < r →
      MeromorphicAt (fun u => f ((fun i => (s i : ℂ)),u)) 0)
    {B ε : ℝ} (hε : 0 < ε)
    (hb : ∀ s : Fin n → ℝ, ‖s‖ < r → ∀ t : ℝ, 0 < t → t < ε →
      ‖f ((fun i => (s i : ℂ)),t)‖ ≤ B) :
    ∃ g : (Fin n → ℂ) × ℂ → ℂ,
      AnalyticOnNhd ℂ g (ball 0 r ×ˢ ball 0 R) ∧
      EqOn g f (ball 0 r ×ˢ (ball 0 R \ {0})) := by
  let g : (Fin n → ℂ) × ℂ → ℂ := fun p =>
    (2 * Real.pi * Complex.I)⁻¹ * ∮ w in C(0, R), (w - p.2)⁻¹ * f (p.1,w)
  have hboundary : ∀ u ∈ sphere (0 : ℂ) R, u ∈ ball 0 S \ {0} := by
    intro u hu
    refine ⟨sphere_subset_ball hRS hu,?_⟩
    intro hu0
    have heq : u = 0 := hu0
    subst u
    have hzero : (0 : ℝ) = R := by simpa using hu
    exact hR.ne hzero
  have hg : AnalyticOnNhd ℂ g (ball 0 r ×ˢ ball 0 R) := by
    apply analyticOnNhd_of_differentiableOn_finDim (isOpen_ball.prod isOpen_ball)
    exact differentiableOn_cauchyTransform isOpen_ball hR f
      (fun p hp => hf p ⟨hp.1,hboundary p.2 hp.2⟩)
  have hreal : ∀ s : Fin n → ℝ, ‖s‖ < r → ∀ u ∈ ball 0 R \ {0},
      g ((fun i => (s i : ℂ)),u) = f ((fun i => (s i : ℂ)),u) := by
    intro s hs
    let sc : Fin n → ℂ := fun i => (s i : ℂ)
    have hsc : sc ∈ ball 0 r := by
      rw [mem_ball, dist_zero_right]
      apply (pi_norm_lt_iff hr).mpr
      intro i
      simpa [sc] using (pi_norm_lt_iff hr).mp hs i
    have hsanalytic : AnalyticOnNhd ℂ (fun u => f (sc,u)) (ball 0 S \ {0}) := by
      intro u hu
      exact (hf (sc,u) ⟨hsc,hu⟩).comp
        ((analyticAt_const (v := sc)).prod analyticAt_id)
    obtain ⟨ga,hga,heq⟩ := meromorphic_removable_of_positive_ray_bound
      isOpen_ball (mem_ball_self (hR.trans hRS)) hsanalytic (hm s hs) hε (hb s hs)
    intro u hu
    have hc : (2 * Real.pi * Complex.I)⁻¹ *
        (∮ w in C(0,R), (w-u)⁻¹ * ga w) = ga u := by
      simpa only [smul_eq_mul] using
        Complex.two_pi_I_inv_smul_circleIntegral_sub_inv_smul_of_differentiable_on_off_countable
          (s := ∅) Set.countable_empty hu.1
          (hga.continuousOn.mono (closedBall_subset_ball hRS))
          (fun w hw => (hga w ((ball_subset_ball hRS.le) hw.1)).differentiableAt)
    change (2 * Real.pi * Complex.I)⁻¹ *
      (∮ w in C(0,R), (w-u)⁻¹ * f (sc,w)) = f (sc,u)
    have hequ : ga u = f (sc,u) := heq ⟨ball_subset_ball hRS.le hu.1,hu.2⟩
    rw [← hequ,← hc]
    congr 1
    apply circleIntegral.integral_congr hR.le
    intro w hw
    dsimp only
    have heqw : ga w = f (sc,w) := heq (hboundary w hw)
    rw [heqw]
  refine ⟨g,hg,?_⟩
  intro p hp
  let h : (Fin n → ℂ) → ℂ := fun s => g (s,p.2) - f (s,p.2)
  have hh : AnalyticOnNhd ℂ h (ball 0 r) := by
    intro s hs
    have hin : AnalyticAt ℂ (fun s : Fin n → ℂ => (s,p.2)) s :=
      analyticAt_id.prod analyticAt_const
    exact ((hg (s,p.2) ⟨hs,hp.2.1⟩).comp (f := fun s => (s,p.2)) hin).sub
      ((hf (s,p.2) ⟨hs,ball_subset_ball hRS.le hp.2.1,hp.2.2⟩).comp (f := fun s => (s,p.2)) hin)
  have hhz : ∀ s : Fin n → ℝ, ‖s‖ < r → h (fun i => (s i : ℂ)) = 0 := by
    intro s hs
    exact sub_eq_zero.mpr (hreal s hs p.2 hp.2)
  have hzero := analytic_zero_of_real_polydisc hr hh hhz hp.1
  exact sub_eq_zero.mp hzero

end Release061

end

end OAI
