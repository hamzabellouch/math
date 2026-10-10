import OAI.Analysis.CircleDomains.Reflection.HolomorphicCircleGluing
import Mathlib.Analysis.Analytic.IsolatedZeros

namespace OAI

/-! Constant values on a unit-circle arc force a holomorphic germ to be
constant. The accumulation points are constructed in the actual circle chart. -/
open Set Function Filter Metric Complex
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

lemma unit_circle_identity_germ {U:Set ℂ} {f:ℂ→ℂ} {a:ℂ}
    (hU:IsOpen U) (hcircle:sphere (0:ℂ) 1⊆U) (hf:DifferentiableOn ℂ f U)
    (hv:∀z∈U,‖z‖=1 → f z=a) : ∀ᶠz in 𝓝 (1:ℂ),f z=a := by
  have h1U : (1:ℂ)∈U := hcircle (by simp)
  have hfa : AnalyticAt ℂ f 1 := hf.analyticAt (hU.mem_nhds h1U)
  have ha : AnalyticAt ℂ (fun _ : ℂ => a) 1 := analyticAt_const
  rcases hfa.eventually_eq_or_eventually_ne ha with h|h
  · exact h
  obtain ⟨ε,hε,havoid⟩ := Metric.mem_nhdsWithin_iff.mp h
  let κ := unitExteriorBoundaryChart (1:ℂ)
  have hk : ContinuousAt κ 0 := (differentiableAt_unitExteriorBoundaryChart 1 (by simp)).continuousAt
  have h0 : κ 0∈ball 1 ε := by
    rw [show κ 0=1 from unitExteriorBoundaryChart_zero 1]
    exact mem_ball_self hε
  have hnear : κ ⁻¹' ball 1 ε∩ball 0 1∈𝓝 (0:ℂ) :=
    inter_mem (hk.preimage_mem_nhds (isOpen_ball.mem_nhds h0)) (isOpen_ball.mem_nhds (by simp))
  obtain ⟨δ,hδ,hδsub⟩ := Metric.mem_nhds_iff.mp hnear
  let t:ℂ := ((δ/2:ℝ):ℂ)
  have ht : t∈ball (0:ℂ) δ := by
    rw [mem_ball_zero_iff]
    change ‖((δ/2:ℝ):ℂ)‖<δ
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos (by linarith)]
    linarith
  have ht0 : t≠0 := by
    intro he
    have := Complex.ofReal_injective he
    linarith
  have ht1 : t∈ball (0:ℂ) 1 := (hδsub ht).2
  have hneq : κ t≠1 := by
    intro he
    have h00 : (0:ℂ)∈ball (0:ℂ) 1 := by simp
    have heq : t=0 := unitExteriorBoundaryChart_injOn one_ne_zero ht1 h00
      (he.trans (unitExteriorBoundaryChart_zero 1).symm)
    exact ht0 heq
  have hnorm : ‖κ t‖=1 := unitExteriorBoundaryChart_norm_eq_one (by simp) (by simp [t])
  have hval : f (κ t)=a := hv _ (hcircle (mem_sphere_zero_iff_norm.mpr hnorm)) hnorm
  exact (havoid ⟨(hδsub ht).1,hneq⟩ hval).elim

end CircleDomainRigidity

end

end OAI
