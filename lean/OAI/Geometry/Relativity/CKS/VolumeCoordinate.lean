import OAI.Geometry.Relativity.CKS.VolumeUnique

namespace OAI

noncomputable section
open Bundle Manifold Set MeasureTheory
open scoped ContDiff ENNReal
namespace CKSIntrinsicVolume
variable {M : Type*} [TopologicalSpace M]
abbrev CoordinateTensor := E → E →L[ℝ] E →L[ℝ] ℝ

def coordinateDensity (A : CoordinateTensor) (y : E) : ℝ :=
  Real.sqrt (LinearMap.BilinForm.toMatrix stdBasis (A y).toBilinForm).det

section
variable [MeasurableSpace M] [BorelSpace M]

def coordinateMeasure (e : OpenPartialHomeomorph M E) (A : CoordinateTensor) : Measure M :=
  Measure.map e.symm ((volume.restrict e.target).withDensity
    (fun y => ENNReal.ofReal (coordinateDensity A y)))

def coordinatePreimage (e : OpenPartialHomeomorph M E) (s : Set M) : Set E :=
  e.symm ⁻¹' s ∩ e.target

lemma coordinatePreimage_measurable [ChartedSpace H M] [IsManifold I 1 M]
    (e : OpenPartialHomeomorph M E)
    {s : Set M} (hs : MeasurableSet s) : MeasurableSet (coordinatePreimage e s) := by
  have h : Measurable (e.target.domRestrict e.symm) :=
    (continuousOn_iff_continuous_domRestrict.mp e.continuousOn_symm).measurable
  convert e.open_target.measurableSet.subtype_image (hs.preimage h) using 1
  ext y
  simp [coordinatePreimage]

lemma coordinateMeasure_apply [ChartedSpace H M] [IsManifold I 1 M]
    (e : OpenPartialHomeomorph M E) (A : CoordinateTensor)
    {s : Set M} (hs : MeasurableSet s) :
    coordinateMeasure e A s = ∫⁻ y in coordinatePreimage e s,
      ENNReal.ofReal (coordinateDensity A y) := by
  have hf := e.continuousOn_symm.aemeasurable
    (μ := (volume : Measure E)) e.open_target.measurableSet
  rw [coordinateMeasure, Measure.map_apply_of_aemeasurable
    (hf.mono_ac (withDensity_absolutelyContinuous _ _)) hs, withDensity_apply']
  rw [← Measure.restrict_comm e.open_target.measurableSet,
    Measure.restrict_restrict e.open_target.measurableSet]
  congr 1
  exact congrArg ((volume : Measure E).restrict) (inter_comm _ _)

end

variable [ChartedSpace H M]

section
variable [IsManifold I 1 M]

def coordinateTransition (e : OpenPartialHomeomorph M E) (z : M) : E → E :=
  e ∘ (extChartAt I z).symm

def coordinateTransitionDeriv (e : OpenPartialHomeomorph M E) (z : M) (y : E) : E →L[ℝ] E :=
  (mfderiv I 𝓘(ℝ,E) e ((extChartAt I z).symm y)).comp (chartFrame z y)

end

lemma coordinateTransition_image [IsManifold I 1 M] [MeasurableSpace M] [BorelSpace M]
    (e : OpenPartialHomeomorph M E) (z : M) (s : Set M) :
    coordinateTransition e z '' chartPreimage z (s ∩ e.source) =
      coordinatePreimage e (s ∩ (extChartAt I z).source) := by
  ext y
  constructor
  · rintro ⟨u,⟨⟨hs,hx⟩,hu⟩,rfl⟩
    have heq : e.symm (coordinateTransition e z u) = (extChartAt I z).symm u := e.left_inv hx
    refine ⟨?_,e.map_source hx⟩
    change e.symm (coordinateTransition e z u) ∈ s ∩ (extChartAt I z).source
    rw [heq]
    exact ⟨hs,(extChartAt I z).map_target hu⟩
  · rintro ⟨⟨hs,hz⟩,hy⟩
    refine ⟨extChartAt I z (e.symm y),?_,?_⟩
    · refine ⟨?_,(extChartAt I z).map_source hz⟩
      change (extChartAt I z).symm (extChartAt I z (e.symm y)) ∈ s ∩ e.source
      rw [(extChartAt I z).left_inv hz]
      exact ⟨hs,e.map_target hy⟩
    · change e ((extChartAt I z).symm (extChartAt I z (e.symm y))) = y
      rw [(extChartAt I z).left_inv hz,e.right_inv hy]

lemma coordinateTransition_injOn [IsManifold I 1 M] [MeasurableSpace M] [BorelSpace M]
    (e : OpenPartialHomeomorph M E) (z : M) (s : Set M) :
    InjOn (coordinateTransition e z) (chartPreimage z (s ∩ e.source)) := by
  intro u hu v hv heq
  apply (extChartAt I z).symm.injOn hu.2 hv.2
  exact e.injOn hu.1.2 hv.1.2 heq

variable [IsManifold I 1 M]

lemma hasFDerivWithinAt_coordinateTransition [MeasurableSpace M] [BorelSpace M]
    (e : OpenPartialHomeomorph M E)
    (hf : ContMDiffOn I 𝓘(ℝ,E) 1 e e.source) (z : M) {y : E}
    (hz : y ∈ (extChartAt I z).target) (he : (extChartAt I z).symm y ∈ e.source) :
    HasFDerivWithinAt (coordinateTransition e z) (coordinateTransitionDeriv e z y) (range I) y := by
  exact (((hf _ he).contMDiffAt (e.open_source.mem_nhds he)).mdifferentiableAt one_ne_zero).hasMFDerivAt.comp_hasMFDerivWithinAt y
    (mdifferentiableWithinAt_extChartAt_symm hz).hasMFDerivWithinAt |>.hasFDerivWithinAt

lemma chartDensity_coordinate [MeasurableSpace M] [BorelSpace M] (g : Metric (M := M))
    (e : OpenPartialHomeomorph M E) (A : CoordinateTensor)
    (hrep : ∀ x ∈ e.source, ∀ v w, g.inner x v w =
      A (e x) (mfderiv I 𝓘(ℝ,E) e x v) (mfderiv I 𝓘(ℝ,E) e x w))
    (z : M) {y : E} (he : (extChartAt I z).symm y ∈ e.source) :
    chartDensity g z y = |(coordinateTransitionDeriv e z y).det| *
      coordinateDensity A (coordinateTransition e z y) := by
  simp only [chartDensity,chartMatrix_eq_toMatrix]
  have heq : pullbackInner g z y =
      (A (coordinateTransition e z y)).toBilinForm.comp
      (coordinateTransitionDeriv e z y).toLinearMap
      (coordinateTransitionDeriv e z y).toLinearMap := by
    ext v w
    exact hrep _ he _ _
  rw [heq,sqrt_gram_det_comp]
  rfl

variable [MeasurableSpace M] [BorelSpace M]

lemma coordinateMeasure_compatible (g : Metric (M := M))
    (e : OpenPartialHomeomorph M E) (A : CoordinateTensor)
    (hf : ContMDiffOn I 𝓘(ℝ,E) 1 e e.source)
    (hrep : ∀ x ∈ e.source, ∀ v w, g.inner x v w =
      A (e x) (mfderiv I 𝓘(ℝ,E) e x v) (mfderiv I 𝓘(ℝ,E) e x w)) (z : M) :
    (coordinateMeasure e A).restrict (extChartAt I z).source =
      (localVolume g z).restrict e.source := by
  ext s hs
  rw [Measure.restrict_apply hs,Measure.restrict_apply hs,
    coordinateMeasure_apply e A (hs.inter (isOpen_extChartAt_source z).measurableSet),
    localVolume_apply g z (hs.inter e.open_source.measurableSet),
    ← coordinateTransition_image e z s]
  have hd : ∀ y ∈ chartPreimage z (s ∩ e.source), HasFDerivWithinAt
      (coordinateTransition e z) (coordinateTransitionDeriv e z y)
      (chartPreimage z (s ∩ e.source)) y := by
    intro y hy
    exact (hasFDerivWithinAt_coordinateTransition e hf z hy.2 hy.1.2).mono
      (fun u hu => extChartAt_target_subset_range z hu.2)
  rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul volume
    (chartPreimage_measurable z (hs.inter e.open_source.measurableSet)) hd
    (coordinateTransition_injOn e z s)]
  apply setLIntegral_congr_fun (chartPreimage_measurable z (hs.inter e.open_source.measurableSet))
  intro y hy
  dsimp only
  rw [chartDensity_coordinate g e A hrep z hy.1.2,ENNReal.ofReal_mul (abs_nonneg _)]

variable [SecondCountableTopology M]
theorem riemannianVolume_coordinate (g : Metric (M := M))
    (e : OpenPartialHomeomorph M E) (A : CoordinateTensor)
    (hf : ContMDiffOn I 𝓘(ℝ,E) 1 e e.source)
    (hrep : ∀ x ∈ e.source, ∀ v w, g.inner x v w =
      A (e x) (mfderiv I 𝓘(ℝ,E) e x v) (mfderiv I 𝓘(ℝ,E) e x w)) :
    (riemannianVolume g).restrict e.source = coordinateMeasure e A := by
  apply measure_eq_of_chart_restrict
  intro z
  rw [Measure.restrict_comm (isOpen_extChartAt_source z).measurableSet,
    riemannianVolume_isVolume g z,coordinateMeasure_compatible g e A hf hrep]

end CKSIntrinsicVolume

end

end OAI
