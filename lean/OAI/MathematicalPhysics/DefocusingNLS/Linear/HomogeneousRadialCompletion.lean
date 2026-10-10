import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousRadialMeasure
import Mathlib.MeasureTheory.Function.LocallyIntegrable

namespace OAI

/-! # Local integrability of the completed radial derivative

The extension by zero is only a measurable representative. On positive radii
its weighted square integral is exactly the polar L² integral.
-/

open MeasureTheory Set Filter

namespace DefocusingNLS

noncomputable def positiveRadiusExtension (g : PhysicalPositiveRadius → ℂ) (r : ℝ) : ℂ :=
  if h : 0 < r then g ⟨r, h⟩ else 0

@[simp] theorem positiveRadiusExtension_coe (g : PhysicalPositiveRadius → ℂ)
    (r : PhysicalPositiveRadius) : positiveRadiusExtension g r = g r := by
  unfold positiveRadiusExtension
  split
  · rfl
  · rename_i h
    exact (h r.2).elim

theorem positiveRadiusExtension_aestronglyMeasurable
    (g : PhysicalPositiveRadius → ℂ) (hg : MemLp g 2 physicalRadiusMeasure) :
    AEStronglyMeasurable (positiveRadiusExtension g) (volume.restrict (Ioi 0)) := by
  have hμ : volume.comap (Subtype.val : PhysicalPositiveRadius → ℝ) ≪
      physicalRadiusMeasure := by
    apply withDensity_absolutelyContinuous'
    · exact (show Measurable (fun r : PhysicalPositiveRadius =>
        ENNReal.ofReal (r.1 ^ (11 : ℕ))) by fun_prop).aemeasurable
    · exact Eventually.of_forall (fun r =>
        (ENNReal.ofReal_pos.mpr (pow_pos r.2 11)).ne')
  have hm := hg.aestronglyMeasurable.mono_ac hμ
  rw [← map_comap_subtype_coe measurableSet_Ioi,
    (MeasurableEmbedding.subtype_coe measurableSet_Ioi).aestronglyMeasurable_map_iff]
  simpa only [Function.comp_def, positiveRadiusExtension_coe] using hm

theorem positiveRadiusExtension_weighted_square
    (g : PhysicalPositiveRadius → ℂ) (hg : MemLp g 2 physicalRadiusMeasure) :
    IntegrableOn (fun r : ℝ => r ^ (11 : ℕ) * ‖positiveRadiusExtension g r‖ ^ 2)
      (Ioi 0) := by
  apply radial_weighted_integrable_of_memLp
  simpa only [positiveRadiusExtension_coe] using hg

/-- The Jacobian times the completed radial derivative is locally integrable
on the entire positive half-line. -/
theorem positiveRadiusExtension_weighted_locallyIntegrable
    (g : PhysicalPositiveRadius → ℂ) (hg : MemLp g 2 physicalRadiusMeasure) :
    LocallyIntegrableOn (fun r : ℝ => (r : ℂ) ^ (11 : ℕ) * positiveRadiusExtension g r)
      (Ioi 0) := by
  have hm := positiveRadiusExtension_aestronglyMeasurable g hg
  have hsq := positiveRadiusExtension_weighted_square g hg
  intro x hx
  change 0 < x at hx
  have hlo : 0 < x / 2 := by linarith [hx]
  have hlx : x / 2 < x := by linarith [hx]
  have hxu : x < x + 1 := by linarith
  have hs : Icc (x / 2) (x + 1) ⊆ Ioi (0 : ℝ) :=
    fun r hr => lt_of_lt_of_le hlo hr.1
  refine ⟨Icc (x / 2) (x + 1),
    mem_nhdsWithin_of_mem_nhds (Icc_mem_nhds hlx hxu), ?_⟩
  have hi : IntegrableOn (fun r : ℝ => r ^ (11 : ℕ) +
      r ^ (11 : ℕ) * ‖positiveRadiusExtension g r‖ ^ 2)
      (Icc (x / 2) (x + 1)) :=
    (continuous_id.pow 11).continuousOn.integrableOn_Icc.add (hsq.mono_set hs)
  apply hi.mono'
    (((Complex.continuous_ofReal.pow 11).aestronglyMeasurable).mul
      (hm.mono_measure (Measure.restrict_mono hs le_rfl)))
  filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
  have hr0 : 0 ≤ r := (hs hr).le
  have hnorm : ‖positiveRadiusExtension g r‖ ≤ 1 + ‖positiveRadiusExtension g r‖ ^ 2 := by
    nlinarith [sq_nonneg (‖positiveRadiusExtension g r‖ - 1)]
  change ‖(r : ℂ) ^ (11 : ℕ) * positiveRadiusExtension g r‖ ≤ _
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hr0]
  nlinarith [mul_le_mul_of_nonneg_left hnorm (pow_nonneg hr0 11)]

/-- Once a classical representative agrees almost everywhere on a tail, it
inherits the exact radial weighted L² condition. -/
theorem positiveRadiusExtension_weighted_square_tail
    (g : PhysicalPositiveRadius → ℂ) (hg : MemLp g 2 physicalRadiusMeasure)
    (R : ℝ) (hR : 0 ≤ R) (F : ℝ → ℂ)
    (heq : ∀ᵐ r ∂volume, r ∈ Ioi R → positiveRadiusExtension g r = F r) :
    IntegrableOn (fun r : ℝ => r ^ (11 : ℕ) * ‖F r‖ ^ 2) (Ioi R) := by
  apply ((positiveRadiusExtension_weighted_square g hg).mono_set
    (Ioi_subset_Ioi hR)).congr
  filter_upwards [heq.filter_mono ae_restrict_le,
    ae_restrict_mem measurableSet_Ioi] with r hr hmem
  rw [hr hmem]

end DefocusingNLS

end OAI
