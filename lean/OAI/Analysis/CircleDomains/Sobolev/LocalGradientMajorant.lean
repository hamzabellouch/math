import OAI.Analysis.CircleDomains.Modulus.FiniteCircleLinePayment

namespace OAI

/-! A finite-energy scalar has an integrable gradient majorant on each
fixed planar square. It is the actual gradient norm truncated to a disk. -/
open Set Function Filter Metric MeasureTheory
namespace CircleDomainRigidity

 theorem exists_integrable_gradient_majorant_on_square
    {U : Set ℂ} (hU : IsOpen U) {v : ℂ → ℝ}
    (he : IntegrableOn (euclideanGradientEnergy v) U) {L : ℝ} (hL : 0 ≤ L) :
    ∃ ρ : ℂ → ℝ, Integrable ρ ∧ ∀ z ∈ U,
      |z.re| ≤ L → |z.im| ≤ L → euclideanGradientNorm v z ≤ ρ z := by
  let E := U ∩ closedBall (0 : ℂ) (2 * L)
  let ρ := E.indicator (euclideanGradientNorm v)
  have hm : MeasurableSet E := hU.measurableSet.inter measurableSet_closedBall
  have he' : IntegrableOn (euclideanGradientEnergy v) E := he.mono_set inter_subset_left
  have hρ := memLp_indicator_euclideanGradientNorm hm he'
  have hp : ∀ z, 0 ≤ ρ z := fun z => indicator_nonneg
    (fun _ _ => Real.sqrt_nonneg _) z
  have hs : support ρ ⊆ closedBall 0 (2 * L) := by
    intro z hz
    by_contra h
    exact hz (indicator_of_notMem (fun he : z ∈ E => h he.2) _)
  refine ⟨ρ, (integral_le_disk_L2 (mul_nonneg (by norm_num) hL) hρ hp hs).1, ?_⟩
  intro z hz hre him
  have hnorm : ‖z‖ ≤ 2 * L := (Complex.norm_le_abs_re_add_abs_im z).trans (by linarith)
  have hE : z ∈ E := ⟨hz, by simpa only [mem_closedBall, dist_zero_right] using hnorm⟩
  change euclideanGradientNorm v z ≤ E.indicator (euclideanGradientNorm v) z
  rw [indicator_of_mem hE]

end CircleDomainRigidity

end OAI
