import OAI.Analysis.CircleDomains.Uniformization.PrincipalCoefficientConvergence
import OAI.Geometry.Cannon.Beltrami.Mollifier

namespace OAI

/-! Smooth principal maps whose actual densities converge strongly to a
specified compact-coefficient L2 solution. The common coefficient support
will give uniform exterior estimates for the maps. -/
open MeasureTheory Set Filter
open scoped Topology ContDiff
noncomputable section
namespace CircleDomainRigidity
open CannonBeltrami

lemma density_operator_equation {μ : ℂ → ℂ} (hm : MemLp μ 2 volume)
    {k : ℝ} (hk : 0 ≤ k) (hb : ∀ᵐ z ∂volume, ‖μ z‖ ≤ k)
    (g : PlaneL2) (he : ∀ᵐ z ∂volume, g z=μ z*(1+beurling g z)) :
    g-multiplier μ hm.aestronglyMeasurable hk hb (beurling g)=hm.toLp μ := by
  apply Lp.ext
  filter_upwards [he, Lp.coeFn_sub g (multiplier μ hm.aestronglyMeasurable hk hb (beurling g)),
    multiplier_ae μ hm.aestronglyMeasurable hk hb (beurling g),
    MemLp.coeFn_toLp hm] with z hz hsub hmul hμ
  simp only [Pi.sub_apply] at hsub
  rw [hsub, hmul, hμ, hz]
  ring

structure PrincipalSmoothApproximation (g : PlaneL2) (k R : ℝ) where
  coefficient : ℕ → SchwartzMap ℂ ℂ
  density : ℕ → SchwartzMap ℂ ℂ
  map : ℕ → ℂ ≃ₜ ℂ
  coefficient_compact : ∀ n, HasCompactSupport (coefficient n : ℂ → ℂ)
  coefficient_bound : ∀ n z, ‖coefficient n z‖ ≤ k
  coefficient_zero : ∀ n z, R+2 ≤ ‖z‖ → coefficient n z=0
  density_compact : ∀ n, HasCompactSupport (density n : ℂ → ℂ)
  values : ∀ n z, map n z=z+cauchyTransform (density n) z
  smooth : ∀ n, ContDiff ℝ ∞ (map n : ℂ → ℂ)
  inverse_smooth : ∀ n, ContDiff ℝ ∞ ((map n).symm : ℂ → ℂ)
  equation : ∀ n z, partialBar (map n) z=coefficient n z*partialZ (map n) z
  partials : ∀ n z, partialBar (map n) z=density n z ∧
    partialZ (map n) z=1+smoothBeurling (density n) z
  strong_density : Tendsto (fun n => (density n).toLp 2 (μ:=volume)) atTop (𝓝 g)

lemma exists_principal_smooth_approximation_with_coefficient (μ : ℂ → ℂ)
    (hm : AEStronglyMeasurable μ volume) {k R : ℝ}
    (hk : 0 ≤ k) (hk1 : k < 1) (hb : ∀ z, ‖μ z‖ ≤ k)
    (hs : ∀ z, R ≤ ‖z‖ → μ z=0) (g : PlaneL2)
    (he : ∀ᵐ z ∂volume, g z=μ z*(1+beurling g z)) :
    ∃ S : PrincipalSmoothApproximation g k R,
      ∀ᵐz ∂volume,Tendsto (fun n => S.coefficient n z) atTop (𝓝 (μ z)) := by
  classical
  obtain ⟨ν, hνc, hνb, hνs, hνlim⟩ := exists_smooth_coefficient_approximation hm hk hb hs
  have hsol (n : ℕ) := smooth_principal_solution (ν n) (hνc n) hk hk1 (hνb n)
  choose h F hhc hF hsm hsmi heq hpart hnorm using hsol
  let K := Metric.closedBall (0 : ℂ) (R+2)
  have hzμ : ∀ z ∉ K, μ z=0 := by
    intro z hz
    apply hs
    have hh : R+2 < ‖z‖ := by simpa only [K, Metric.mem_closedBall, dist_zero_right, not_le] using hz
    linarith
  have hzν : ∀ n z, z ∉ K → ν n z=0 := by
    intro n z hz
    apply hνs n z
    have hh : R+2 < ‖z‖ := by simpa only [K, Metric.mem_closedBall, dist_zero_right, not_le] using hz
    exact hh.le
  let hμ := compact_coefficient_memLp hm (isCompact_closedBall _ _) hk hb hzμ
  have hcoeff : Tendsto (fun n => (ν n).toLp 2 (μ:=volume)) atTop (𝓝 (hμ.toLp μ)) := by
    simpa only [SchwartzMap.toLp] using compact_coefficient_L2_convergence hm
      (fun n => (ν n).continuous.aestronglyMeasurable) (isCompact_closedBall _ _)
      hk hb hνb hzμ hzν hνlim
  have hdens : Tendsto (fun n => (h n).toLp 2 (μ:=volume)) atTop (𝓝 g) := by
    apply principal_density_strong_convergence μ (fun n => (ν n : ℂ → ℂ)) hm
      (fun n => (ν n).continuous.aestronglyMeasurable) hk hk1
      (.of_forall hb) (fun n => .of_forall (hνb n)) hνlim g (hμ.toLp μ)
      (fun n => (h n).toLp 2 (μ:=volume)) (fun n => (ν n).toLp 2 (μ:=volume))
      (density_operator_equation hμ hk (.of_forall hb) g he) _ hcoeff
    intro n
    apply schwartz_principal_density_equation (ν n) (h n) hk (hνb n)
    intro z
    have h1 := heq n z
    rw [(hpart n z).1, (hpart n z).2] at h1
    linear_combination h1
  exact ⟨⟨ν, h, F, hνc, hνb, hνs, hhc, hF, hsm, hsmi, heq, hpart, hdens⟩,hνlim⟩

lemma exists_principal_smooth_approximation (μ : ℂ → ℂ)
    (hm : AEStronglyMeasurable μ volume) {k R : ℝ}
    (hk : 0 ≤ k) (hk1 : k < 1) (hb : ∀ z, ‖μ z‖ ≤ k)
    (hs : ∀ z, R ≤ ‖z‖ → μ z=0) (g : PlaneL2)
    (he : ∀ᵐ z ∂volume, g z=μ z*(1+beurling g z)) :
    Nonempty (PrincipalSmoothApproximation g k R) := by
  obtain ⟨S,_⟩ := exists_principal_smooth_approximation_with_coefficient μ hm hk hk1 hb hs g he
  exact ⟨S⟩

end CircleDomainRigidity

end

end OAI
