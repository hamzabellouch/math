import OAI.Analysis.CircleDomains.Transfer.ComplexSourceWitness
import OAI.Analysis.CircleDomains.Sobolev.SummableEnergyCutoffs

namespace OAI

/-! A compact source cutoff turns local differential energy into a
compact continuous Sobolev test without making any boundary extension
assumption. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ContDiff ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem scalar_times_cutoff_derivative_memLp
    {D : Set ℂ} {f η : ℂ → ℝ} (hc : Continuous f)
    (hη : ContDiff ℝ ∞ η) (hs : HasCompactSupport η) :
    MemLp (fun z => f z • fderiv ℝ η z) 2 (volume.restrict D) := by
  have hdη : HasCompactSupport (fderiv ℝ η) := hs.fderiv (𝕜 := ℝ)
  have hh : HasCompactSupport (f • fderiv ℝ η) := hdη.smul_left (f := f)
  exact ((hc.smul (hη.continuous_fderiv (by simp))).memLp_of_hasCompactSupport hh).restrict D

 theorem cutoff_times_local_derivative_memLp
    {D : Set ℂ} (hD : IsOpen D) {f η : ℂ → ℝ}
    (hf : ContDiffOn ℝ ∞ f D) (hη : ContDiff ℝ ∞ η)
    (hs : HasCompactSupport η) {R : ℝ} (hR : tsupport η ⊆ ball 0 R)
    (hE : MemLp (fderiv ℝ f) 2 (volume.restrict (D ∩ ball 0 R))) :
    MemLp (fun z => η z • fderiv ℝ f z) 2 (volume.restrict D) := by
  obtain ⟨C, hC⟩ := hη.continuous.bounded_above_of_compact_support hs
  have hI : MemLp ((ball (0 : ℂ) R).indicator (fun z => ‖fderiv ℝ f z‖))
      2 (volume.restrict D) := by
    apply (memLp_indicator_iff_restrict (μ := volume.restrict D)
      (p := 2) (f := fun z => ‖fderiv ℝ f z‖) measurableSet_ball).mpr
    simpa only [Measure.restrict_restrict measurableSet_ball, inter_comm] using hE.norm
  let K := max C 0
  have hKn : 0 ≤ K := le_max_right _ _
  have hm : AEStronglyMeasurable (fun z => η z • fderiv ℝ f z) (volume.restrict D) :=
    (hη.continuous.continuousOn.smul
      (hf.continuousOn_fderiv_of_isOpen hD (by simp))).aestronglyMeasurable hD.measurableSet
  apply (hI.const_mul K).of_le hm
  filter_upwards [] with z
  by_cases hz : z ∈ ball (0 : ℂ) R
  · rw [indicator_of_mem hz]
    simp only [norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg hKn (norm_nonneg _))]
    exact mul_le_mul_of_nonneg_right ((hC z).trans (le_max_left _ _)) (norm_nonneg _)
  · have hηz : η z = 0 := image_eq_zero_of_notMem_tsupport (fun ht => hz (hR ht))
    simp only [hηz, zero_smul, norm_zero]
    exact norm_nonneg _

 theorem compact_source_cutoff_gradient_memLp_on
    {D : Set ℂ} (hD : IsOpen D) {f η : ℂ → ℝ}
    (hc : Continuous f) (hf : ContDiffOn ℝ ∞ f D)
    (hη : ContDiff ℝ ∞ η) (hs : HasCompactSupport η)
    {R : ℝ} (hR : tsupport η ⊆ ball 0 R)
    (hE : MemLp (fderiv ℝ f) 2 (volume.restrict (D ∩ ball 0 R))) :
    MemLp (fderiv ℝ (fun z => η z*f z)) 2 (volume.restrict D) := by
  have hA := scalar_times_cutoff_derivative_memLp (D := D) hc hη hs
  have hB := cutoff_times_local_derivative_memLp hD hf hη hs hR hE
  have hsum := hA.norm.add hB.norm
  have hp : ContDiffOn ℝ ∞ (fun z => η z*f z) D := hη.contDiffOn.mul hf
  have hm : AEStronglyMeasurable (fderiv ℝ (fun z => η z*f z)) (volume.restrict D) :=
    (hp.continuousOn_fderiv_of_isOpen hD (by simp)).aestronglyMeasurable hD.measurableSet
  apply hsum.of_le hm
  filter_upwards [ae_restrict_mem hD.measurableSet] with z hz
  rw [fderiv_fun_mul (hη.differentiable (by simp) z)
    ((hf.contDiffAt (hD.mem_nhds hz)).differentiableAt (by simp))]
  simpa only [Pi.add_apply, Real.norm_eq_abs, abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _)), add_comm]
    using norm_add_le (η z • fderiv ℝ f z) (f z • fderiv ℝ η z)

 theorem compact_source_cutoff_gradient_memLp
    {D : Set ℂ} (hD : IsOpen D) {f η : ℂ → ℝ}
    (hc : Continuous f) (hf : ContDiffOn ℝ ∞ f D)
    (hη : ContDiff ℝ ∞ η) (hs : HasCompactSupport η)
    (hE : ∀ R : ℝ, MemLp (fderiv ℝ f) 2 (volume.restrict (D ∩ ball 0 R))) :
    MemLp (fderiv ℝ (fun z => η z*f z)) 2 (volume.restrict D) := by
  obtain ⟨R, hR⟩ := hs.isCompact.isBounded.subset_ball 0
  exact compact_source_cutoff_gradient_memLp_on hD hc hf hη hs hR (hE R)

end CircleDomainRigidity

end

end OAI
