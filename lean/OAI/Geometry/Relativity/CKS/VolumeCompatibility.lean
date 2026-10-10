import OAI.Geometry.Relativity.CKS.VolumeMeasurable
import OAI.Geometry.Relativity.CKS.VolumeTransition

namespace OAI

noncomputable section
open Bundle Manifold Set MeasureTheory
open scoped ContDiff ENNReal
namespace CKSIntrinsicVolume
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

lemma chartTransition_image [IsManifold I 1 M] [MeasurableSpace M] [BorelSpace M]
    (x z : M) (s : Set M) :
    chartTransition x z '' chartPreimage z (s ∩ (extChartAt I x).source) =
      chartPreimage x (s ∩ (extChartAt I z).source) := by
  ext y
  constructor
  · rintro ⟨u, ⟨⟨hs,hx⟩,hu⟩,rfl⟩
    have heq : (extChartAt I x).symm (chartTransition x z u) = (extChartAt I z).symm u :=
      (extChartAt I x).left_inv hx
    refine ⟨?_, (extChartAt I x).map_source hx⟩
    change (extChartAt I x).symm (chartTransition x z u) ∈ s ∩ (extChartAt I z).source
    rw [heq]
    exact ⟨hs, (extChartAt I z).map_target hu⟩
  · rintro ⟨⟨hs,hz⟩,hy⟩
    refine ⟨extChartAt I z ((extChartAt I x).symm y), ?_, ?_⟩
    · refine ⟨?_, (extChartAt I z).map_source hz⟩
      change (extChartAt I z).symm (extChartAt I z ((extChartAt I x).symm y)) ∈
        s ∩ (extChartAt I x).source
      rw [(extChartAt I z).left_inv hz]
      exact ⟨hs, (extChartAt I x).map_target hy⟩
    · change extChartAt I x ((extChartAt I z).symm
        (extChartAt I z ((extChartAt I x).symm y))) = y
      rw [(extChartAt I z).left_inv hz, (extChartAt I x).right_inv hy]

lemma chartTransition_injOn [IsManifold I 1 M] [MeasurableSpace M] [BorelSpace M]
    (x z : M) (s : Set M) :
    InjOn (chartTransition x z) (chartPreimage z (s ∩ (extChartAt I x).source)) := by
  intro u hu v hv heq
  apply (extChartAt I z).symm.injOn hu.2 hv.2
  exact (extChartAt I x).injOn hu.1.2 hv.1.2 heq

variable [IsManifold I 1 M] [MeasurableSpace M] [BorelSpace M]

lemma localVolume_compatible (g : Metric (M := M)) (x z : M) :
    (localVolume g x).restrict (extChartAt I z).source =
      (localVolume g z).restrict (extChartAt I x).source := by
  ext s hs
  rw [Measure.restrict_apply hs, Measure.restrict_apply hs,
    localVolume_apply g x (hs.inter (isOpen_extChartAt_source z).measurableSet),
    localVolume_apply g z (hs.inter (isOpen_extChartAt_source x).measurableSet),
    ← chartTransition_image x z s]
  have hd : ∀ y ∈ chartPreimage z (s ∩ (extChartAt I x).source),
      HasFDerivWithinAt (chartTransition x z) (transitionDeriv x z y)
        (chartPreimage z (s ∩ (extChartAt I x).source)) y := by
    intro y hy
    exact (hasFDerivWithinAt_chartTransition x z hy.2 hy.1.2).mono
      (fun u hu => extChartAt_target_subset_range z hu.2)
  rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul volume
    (chartPreimage_measurable z (hs.inter (isOpen_extChartAt_source x).measurableSet))
    hd (chartTransition_injOn x z s)]
  apply setLIntegral_congr_fun
    (chartPreimage_measurable z (hs.inter (isOpen_extChartAt_source x).measurableSet))
  intro y hy
  dsimp only
  rw [chartDensity_transition g x z hy.1.2, ENNReal.ofReal_mul (abs_nonneg _)]

end CKSIntrinsicVolume

end

end OAI
