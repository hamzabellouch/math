import OAI.Analysis.CoulombTransport.Model

namespace OAI

noncomputable section

open MeasureTheory Set Filter
open scoped Topology ENNReal

namespace Problem356

/-- A smooth function on an open set extends smoothly by zero whenever its
closed support stays in that open set.  The function is already defined
on the ambient space; the support hypothesis expresses the extension. -/
theorem contDiff_of_contDiffOn_of_tsupport_subset
    {f : E3 → ℝ} {s : Set E3} {n : WithTop ENat}
    (hs : IsOpen s) (hf : ContDiffOn ℝ n f s) (hfs : tsupport f ⊆ s) :
    ContDiff ℝ n f := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ s
  · exact hf.contDiffAt (hs.mem_nhds hx)
  · have hxt : x ∉ tsupport f := fun ht => hx (hfs ht)
    apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
    filter_upwards [(isClosed_tsupport f).isOpen_compl.mem_nhds hxt] with y hy
    exact image_eq_zero_of_notMem_tsupport hy

/-- Transport of a compactly supported amplitude through a local
homeomorphism, with a prescribed Jacobian square-root factor. -/
def localTransportAmplitude (e : OpenPartialHomeomorph E3 E3)
    (g J : E3 → ℝ) : E3 → ℝ :=
  e.target.indicator (fun y => g (e.symm y) * J y)

theorem localTransportAmplitude_nonneg
    (e : OpenPartialHomeomorph E3 E3) {g J : E3 → ℝ}
    (hg : ∀ x, 0 ≤ g x) (hJ : ∀ y ∈ e.target, 0 ≤ J y) :
    ∀ y, 0 ≤ localTransportAmplitude e g J y := by
  intro y
  by_cases hy : y ∈ e.target
  · simp only [localTransportAmplitude, indicator_of_mem hy]
    exact mul_nonneg (hg _) (hJ _ hy)
  · simp [localTransportAmplitude, hy]

theorem support_localTransportAmplitude_subset
    (e : OpenPartialHomeomorph E3 E3) (g J : E3 → ℝ) :
    Function.support (localTransportAmplitude e g J) ⊆ e '' tsupport g := by
  intro y hy
  have hyt : y ∈ e.target := by
    by_contra hn
    exact hy (by simp [localTransportAmplitude, hn])
  refine ⟨e.symm y, ?_, e.right_inv hyt⟩
  apply subset_tsupport g
  intro hz
  apply hy
  simp [localTransportAmplitude, hyt, hz]

theorem tsupport_localTransportAmplitude_subset
    (e : OpenPartialHomeomorph E3 E3) {g : E3 → ℝ} (J : E3 → ℝ)
    (hg : HasCompactSupport g) (hgs : tsupport g ⊆ e.source) :
    tsupport (localTransportAmplitude e g J) ⊆ e '' tsupport g := by
  apply closure_minimal (support_localTransportAmplitude_subset e g J)
  exact (hg.image_of_continuousOn (e.continuousOn.mono hgs)).isClosed

theorem hasCompactSupport_localTransportAmplitude
    (e : OpenPartialHomeomorph E3 E3) {g : E3 → ℝ} (J : E3 → ℝ)
    (hg : HasCompactSupport g) (hgs : tsupport g ⊆ e.source) :
    HasCompactSupport (localTransportAmplitude e g J) := by
  exact (hg.image_of_continuousOn (e.continuousOn.mono hgs)).of_isClosed_subset
    (isClosed_tsupport _) (tsupport_localTransportAmplitude_subset e J hg hgs)

theorem tsupport_localTransportAmplitude_subset_target
    (e : OpenPartialHomeomorph E3 E3) {g : E3 → ℝ} (J : E3 → ℝ)
    (hg : HasCompactSupport g) (hgs : tsupport g ⊆ e.source) :
    tsupport (localTransportAmplitude e g J) ⊆ e.target := by
  intro y hy
  obtain ⟨x, hx, rfl⟩ := tsupport_localTransportAmplitude_subset e J hg hgs hy
  exact e.map_source (hgs hx)

theorem contDiff_localTransportAmplitude
    (e : OpenPartialHomeomorph E3 E3) {g J : E3 → ℝ} {n : WithTop ENat}
    (hg : ContDiff ℝ n g) (hgc : HasCompactSupport g)
    (hgs : tsupport g ⊆ e.source)
    (he : ContDiffOn ℝ n e.symm e.target)
    (hJ : ContDiffOn ℝ n J e.target) :
    ContDiff ℝ n (localTransportAmplitude e g J) := by
  apply contDiff_of_contDiffOn_of_tsupport_subset e.open_target
    _ (tsupport_localTransportAmplitude_subset_target e J hgc hgs)
  have hcomp : ContDiffOn ℝ n (fun y => g (e.symm y) * J y) e.target :=
    (hg.comp_contDiffOn he).mul hJ
  refine hcomp.congr ?_
  intro y hy
  simp [localTransportAmplitude, hy]

/-- The inverse-Jacobian change-of-variables formula for a local
homeomorphism.  No global behavior outside its source is required. -/
theorem map_withDensity_localHomeomorph
    (e : OpenPartialHomeomorph E3 E3) (w : E3 → ℝ≥0∞)
    (D : E3 → E3 →L[ℝ] E3)
    (hD : ∀ y ∈ e.target, HasFDerivAt e.symm (D y) y) :
    Measure.map e (((volume : Measure E3).restrict e.source).withDensity w) =
      ((volume : Measure E3).restrict e.target).withDensity
        (fun y => ENNReal.ofReal |(D y).det| * w (e.symm y)) := by
  have he : AEMeasurable e ((volume : Measure E3).restrict e.source) :=
    e.continuousOn.aemeasurable e.open_source.measurableSet
  have hew : AEMeasurable e
      (((volume : Measure E3).restrict e.source).withDensity w) :=
    he.mono_ac (withDensity_absolutelyContinuous _ _)
  apply Measure.ext
  intro s hs
  have hpre : NullMeasurableSet (e ⁻¹' s)
      ((volume : Measure E3).restrict e.source) :=
    he.nullMeasurableSet_preimage hs
  rw [Measure.map_apply_of_aemeasurable hew hs,
    withDensity_apply₀ _ hpre, withDensity_apply _ hs,
    Measure.restrict_restrict₀ hpre, Measure.restrict_restrict hs]
  have hset : e.symm '' (s ∩ e.target) = e ⁻¹' s ∩ e.source := by
    ext x
    constructor
    · rintro ⟨y, ⟨hys, hyt⟩, rfl⟩
      exact ⟨by simpa only [mem_preimage, e.right_inv hyt] using hys,
        e.symm.map_source hyt⟩
    · rintro ⟨hxs, hxe⟩
      exact ⟨e x, ⟨hxs, e.map_source hxe⟩, e.left_inv hxe⟩
  rw [← hset]
  exact lintegral_image_eq_lintegral_abs_det_fderiv_mul volume
    (hs.inter e.open_target.measurableSet)
    (fun y hy => (hD y hy.2).hasFDerivWithinAt)
    (e.symm.injOn.mono inter_subset_right) w

/-- The local inverse-Jacobian formula carries a square density to a
square density, exactly as required by the five-component construction. -/
theorem map_squareDensity_localHomeomorph
    (e : OpenPartialHomeomorph E3 E3) (g : E3 → ℝ)
    (hgs : tsupport g ⊆ e.source)
    (D : E3 → E3 →L[ℝ] E3)
    (hD : ∀ y ∈ e.target, HasFDerivAt e.symm (D y) y) :
    Measure.map e (densityMeasure (fun x => g x ^ 2)) =
      densityMeasure (fun y =>
        localTransportAmplitude e g (fun z => Real.sqrt |(D z).det|) y ^ 2) := by
  have hsource : densityMeasure (fun x => g x ^ 2) =
      ((volume : Measure E3).restrict e.source).withDensity
        (fun x => ENNReal.ofReal (g x ^ 2)) := by
    rw [densityMeasure, ← withDensity_indicator e.open_source.measurableSet]
    congr 1
    ext x
    by_cases hx : x ∈ e.source
    · simp [hx]
    · have hgx : g x = 0 := image_eq_zero_of_notMem_tsupport
        (fun h => hx (hgs h))
      simp [hx, hgx]
  rw [hsource, map_withDensity_localHomeomorph e _ D hD, densityMeasure,
    ← withDensity_indicator e.open_target.measurableSet]
  congr 1
  ext y
  by_cases hy : y ∈ e.target
  · simp only [indicator_of_mem hy, localTransportAmplitude, mul_pow,
      Real.sq_sqrt (abs_nonneg _)]
    rw [mul_comm (g (e.symm y) ^ 2), ENNReal.ofReal_mul (abs_nonneg _)]
  · simp [localTransportAmplitude, hy]

end Problem356

end

end OAI
