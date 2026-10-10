import OAI.Analysis.CircleDomains.Sobolev.L2ProductConvergence
import OAI.Analysis.CircleDomains.Sobolev.SmoothPlaneSobolev
import Mathlib.MeasureTheory.Function.LpSpace.Complete

namespace OAI

/-! Bounded pointwise convergence and strong L2 convergence of actual
weak partial derivatives identify the derivative of the limit. Only the
compact support of the testing function is used for the value limit. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem weakPartial_of_bounded_pointwise_strong_limit
    {U : Set EuclideanPlane} (hU : IsOpen U)
    {u : ℕ → EuclideanPlane → ℝ} {v : EuclideanPlane → ℝ}
    (hu : ∀ n, ContinuousOn (u n) U)
    {C : ℝ} (hb : ∀ n x, x ∈ U → ‖u n x‖ ≤ C)
    (hp : ∀ x ∈ U, Tendsto (fun n => u n x) atTop (𝓝 (v x)))
    {i : Fin 2} {g : ℕ → EuclideanPlane → ℝ}
    (hg : ∀ n, MemLp (g n) 2 (volume.restrict U))
    (hweak : ∀ n, DeGiorgi.HasWeakPartialDeriv i (g n) (u n) U)
    (G : Lp ℝ 2 (volume.restrict U))
    (hG : Tendsto (fun n => (hg n).toLp (g n)) atTop (𝓝 G)) :
    DeGiorgi.HasWeakPartialDeriv i G v U := by
  intro φ hφ hs hsub
  let ψ := fun x => fderiv ℝ φ x (EuclideanSpace.single i 1)
  have hψ : Continuous ψ := (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hsψ : HasCompactSupport ψ := hs.fderiv_apply (𝕜 := ℝ) _
  have hleft : Tendsto (fun n => ∫ x in U, u n x*ψ x) atTop
      (𝓝 (∫ x in U, v x*ψ x)) := by
    apply tendsto_integral_of_dominated_convergence (bound := fun x => C*‖ψ x‖)
    · intro n
      exact ((hu n).aestronglyMeasurable hU.measurableSet).mul hψ.aestronglyMeasurable
    · exact ((hψ.integrable_of_hasCompactSupport hsψ).restrict (s := U)).norm.const_mul C
    · intro n
      filter_upwards [ae_restrict_mem hU.measurableSet] with x hx
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hb n x hx) (norm_nonneg _)
    · filter_upwards [ae_restrict_mem hU.measurableSet] with x hx
      exact (hp x hx).mul_const _
  have hφL : MemLp φ 2 (volume.restrict U) :=
    (hφ.continuous.memLp_of_hasCompactSupport hs).restrict U
  have hpair (n : ℕ) : inner ℝ ((hg n).toLp (g n)) (hφL.toLp φ) =
      ∫ x in U, g n x*φ x := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [(hg n).coeFn_toLp,hφL.coeFn_toLp] with x hx hy
    simp only [Real.inner_apply,hx,hy]
  have hpairG : inner ℝ G (hφL.toLp φ) = ∫ x in U, G x*φ x := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hφL.coeFn_toLp] with x hx
    simp only [Real.inner_apply,hx]
  have hright := hG.inner (𝕜 := ℝ) (tendsto_const_nhds (x := hφL.toLp φ))
  simp only [hpair,hpairG] at hright
  have he : (fun n => ∫ x in U, u n x*ψ x) =
      (fun n => -(∫ x in U, g n x*φ x)) := funext fun n => hweak n φ hφ hs hsub
  rw [he] at hleft
  exact tendsto_nhds_unique hleft hright.neg

end CircleDomainRigidity

end

end OAI
