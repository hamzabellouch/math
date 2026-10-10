import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.CStarAlgebra.ContinuousMap

namespace OAI

/-! # Holomorphic continuous spectral functions

On a compact spectrum, a continuous family of continuous functions is
holomorphic once each scalar evaluation is holomorphic. The Cauchy integral
formula proves the required uniform derivative without enlarging Lean limits.
-/

namespace KadisonKastler

open MeasureTheory Set Metric Filter Complex
open scoped Topology

noncomputable section

variable {K : Type*} [TopologicalSpace K] [CompactSpace K]

private theorem circleIntegral_evaluation (F : ℂ → C(K, ℂ)) (c : ℂ) (r : ℝ)
    (hF : CircleIntegrable F c r) (k : K) :
    (∮ z in C(c, r), F z) k = ∮ z in C(c, r), F z k := by
  have he := (ContinuousMap.evalCLM ℂ k).intervalIntegral_comp_comm hF.out
  simpa only [circleIntegral, Function.comp_def, map_smul,
    ContinuousMap.evalCLM_apply] using he.symm

theorem continuousMap_differentiableOn_of_evaluations (F : ℂ → C(K, ℂ))
    {U : Set ℂ} (hU : IsOpen U) (hc : ContinuousOn F U)
    (hd : ∀ k : K, DifferentiableOn ℂ (fun z => F z k) U) :
    DifferentiableOn ℂ F U := by
  intro z hz
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hz)
  let r := ε / 2
  have hr : 0 < r := half_pos hε
  have hclosed : closedBall z r ⊆ U := by
    intro w hw
    apply hball
    change dist w z ≤ r at hw
    change dist w z < ε
    exact lt_of_le_of_lt hw (by dsimp [r]; linarith)
  have hFc : ContinuousOn F (closedBall z r) := hc.mono hclosed
  have hFi : CircleIntegrable F z r := (hFc.mono sphere_subset_closedBall).circleIntegrable hr.le
  let G : ℂ → C(K, ℂ) := fun w => (2 * Real.pi * Complex.I : ℂ)⁻¹ •
    ∮ ζ in C(z, r), (ζ - w)⁻¹ • F ζ
  have hG : HasDerivAt G
      ((2 * Real.pi * Complex.I : ℂ)⁻¹ • ∮ ζ in C(z, r), (ζ - z) ^ (-2 : ℤ) • F ζ) z := by
    have hn : z ∉ sphere z |r| := by
      rw [abs_of_pos hr]
      exact sphere_disjoint_ball.notMem_of_mem_right (mem_ball_self hr)
    exact (Complex.hasDerivAt_circleIntegral_sub_inv_smul hFi hn).const_smul ((2 * Real.pi * Complex.I : ℂ)⁻¹)
  have heq : ∀ w ∈ ball z r, G w = F w := by
    intro w hw
    have hwn : w ∉ sphere z |r| := by
      rw [abs_of_pos hr]
      exact sphere_disjoint_ball.notMem_of_mem_right hw
    apply ContinuousMap.ext
    intro k
    change ((2 * Real.pi * Complex.I : ℂ)⁻¹ •
      (∮ ζ in C(z, r), (ζ - w)⁻¹ • F ζ)) k = F w k
    rw [ContinuousMap.smul_apply]
    rw [circleIntegral_evaluation _ _ _ (by
      simpa only [zpow_neg_one] using hFi.sub_zpow_smul (-1) hwn)]
    apply Complex.two_pi_I_inv_smul_circleIntegral_sub_inv_smul_of_differentiable_on_off_countable
      Set.countable_empty hw
    · exact ((ContinuousMap.evalCLM ℂ k).continuous.comp_continuousOn hFc)
    · intro v hv
      exact (hd k).differentiableAt (hU.mem_nhds (hclosed (ball_subset_closedBall hv.1)))
  have hnb : ∀ᶠ w in 𝓝 z, w ∈ ball z r := ball_mem_nhds z hr
  have hEq : G =ᶠ[𝓝 z] F := hnb.mono (fun w hw => heq w hw)
  exact (hG.congr_of_eventuallyEq hEq.symm).differentiableAt.differentiableWithinAt

end

end KadisonKastler

end OAI
