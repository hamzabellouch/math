import OAI.Analysis.CircleDomains.Uniformization.ConformalInverse
import OAI.Analysis.CircleDomains.Uniformization.LimitConformality
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Analytic.IsolatedZeros

namespace OAI

/-! A holomorphic plane homeomorphism has a holomorphic inverse on the
image domain. Isolated critical points are removed from the continuous
inverse; the chain rule then excludes them altogether. -/
open Set Filter Function Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem holomorphicHomeomorph_deriv_not_locally_zero
    (φ : ℂ ≃ₜ ℂ) {U : Set ℂ} (hU : IsOpen U) (hφ : DifferentiableOn ℂ φ U)
    {z : ℂ} (hz : z ∈ U) : ¬ ∀ᶠ w in 𝓝 z, deriv φ w = 0 := by
  intro hzero
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp ((show ∀ᶠ w in 𝓝 z, w ∈ U from hU.mem_nhds hz).and hzero)
  have hsub : ball z r ⊆ U := fun w hw => (hball (by simpa only [mem_ball] using hw)).1
  obtain ⟨c, hc⟩ := isOpen_ball.exists_is_const_of_deriv_eq_zero
    (convex_ball z r).isPreconnected (hφ.mono hsub)
    (fun w hw => (hball (by simpa only [mem_ball] using hw)).2)
  let w : ℂ := z + (r/2 : ℝ)
  have hw : w ∈ ball z r := by
    rw [mem_ball, dist_eq_norm]
    dsimp only [w]
    rw [add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    linarith
  have heq : w = z := φ.injective ((hc w hw).trans (hc z (mem_ball_self hr)).symm)
  have hr0 : (r/2 : ℝ) ≠ 0 := ne_of_gt (by positivity)
  exact hr0 (Complex.ofReal_injective (add_left_cancel (show z + (r/2 : ℝ) = z+0 by
    simpa only [add_zero] using heq)))

 theorem holomorphicHomeomorph_inverse_differentiableAt
    (φ : ℂ ≃ₜ ℂ) {U : Set ℂ} (hU : IsOpen U) (hφ : DifferentiableOn ℂ φ U)
    {z : ℂ} (hz : z ∈ U) : DifferentiableAt ℂ φ.symm (φ z) := by
  have ha := hφ.analyticAt (hU.mem_nhds hz)
  have hn : ∀ᶠ w in 𝓝[≠] z, deriv φ w ≠ 0 :=
    ha.deriv.eventually_eq_zero_or_eventually_ne_zero.resolve_left
      (holomorphicHomeomorph_deriv_not_locally_zero φ hU hφ hz)
  have ht : Tendsto φ.symm (𝓝[≠] (φ z)) (𝓝[≠] z) := by
    change map φ.symm (𝓝[≠] (φ z)) ≤ 𝓝[≠] z
    rw [φ.symm.map_punctured_nhds_eq, φ.symm_apply_apply]
  apply (Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt
    ?_ φ.symm.continuous.continuousAt).differentiableAt
  have hu : ∀ᶠ y in 𝓝 (φ z), φ.symm y ∈ U := by
    have ht₀ : Tendsto φ.symm (𝓝 (φ z)) (𝓝 z) := by
      simpa only [φ.symm_apply_apply] using φ.symm.continuous.tendsto (φ z)
    exact ht₀.eventually (hU.mem_nhds hz)
  filter_upwards [ht.eventually hn, hu.filter_mono nhdsWithin_le_nhds] with y hy hyU
  have hcont : ContDiffAt ℂ 1 φ (φ.symm y) :=
    (hφ.analyticAt (hU.mem_nhds hyU)).contDiffAt
  have hs := hcont.hasStrictDerivAt'
    ((hφ _ hyU).differentiableAt (hU.mem_nhds hyU)).hasDerivAt (by norm_num)
  have hi := hs.to_local_left_inverse hy (Eventually.of_forall φ.symm_apply_apply)
  simpa only [φ.apply_symm_apply] using hi.hasDerivAt.differentiableAt

 theorem holomorphicHomeomorph_deriv_ne_zero
    (φ : ℂ ≃ₜ ℂ) {U : Set ℂ} (hU : IsOpen U) (hφ : DifferentiableOn ℂ φ U)
    {z : ℂ} (hz : z ∈ U) : deriv φ z ≠ 0 := by
  have hf := ((hφ z hz).differentiableAt (hU.mem_nhds hz)).hasDerivAt
  have hi := (holomorphicHomeomorph_inverse_differentiableAt φ hU hφ hz).hasDerivAt
  have hh := (hi.comp z hf).deriv
  have hid : ((φ.symm : ℂ → ℂ) ∘ (φ : ℂ → ℂ)) = id := funext φ.symm_apply_apply
  have hidder : deriv (id : ℂ → ℂ) z = 1 := (hasDerivAt_id z).deriv
  rw [hid, hidder] at hh
  intro hzero
  rw [hzero, mul_zero] at hh
  exact one_ne_zero hh

 theorem holomorphicHomeomorph_conformal (φ : ℂ ≃ₜ ℂ) {U : Set ℂ}
    (hU : IsOpen U) (hφ : DifferentiableOn ℂ φ U)
    (hb : (fun z => φ z-z) =O[Bornology.cobounded ℂ] (fun z => z⁻¹)) :
    IsConformalOn φ.onePointCongr (((↑) : ℂ → Sphere) '' U ∪ {OnePoint.infty}) := by
  have he : (φ.onePointCongr : Sphere → Sphere) = extendAtInfinity φ := by
    funext p
    cases p using OnePoint.rec <;> rfl
  rw [he]
  exact isConformalOn_extendAtInfinity hU hφ
    (fun z hz => holomorphicHomeomorph_deriv_ne_zero φ hU hφ hz) hb

end CircleDomainRigidity

end

end OAI
