import OAI.Geometry.Relativity.CKS.SurfaceMapDerivative
import OAI.Geometry.Relativity.CKS.WeightedArea

namespace OAI

noncomputable section
open Set Manifold Bundle MeasureTheory
open scoped ContDiff ENNReal
namespace CKSSurfaceVolume
variable {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace H M] [ChartedSpace H N] [IsManifold I 1 M] [IsManifold I 1 N]
  [MeasurableSpace M] [BorelSpace M] [MeasurableSpace N] [BorelSpace N]

lemma mapChart_image {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
    [ChartedSpace H M] [ChartedSpace H N] [IsManifold I 1 M] [IsManifold I 1 N]
    [MeasurableSpace M] [BorelSpace M] [MeasurableSpace N] [BorelSpace N]
    (f : M → N) (x : M) (y : N) {s : Set M}
    (hx : s ⊆ (extChartAt I x).source) (hy : MapsTo f s (extChartAt I y).source) :
    mapChart f x y '' chartPreimage x s = chartPreimage y (f '' s) := by
  ext z
  constructor
  · rintro ⟨w,hw,rfl⟩
    have hfy := hy hw.1
    have heq : (extChartAt I y).symm (mapChart f x y w) = f ((extChartAt I x).symm w) :=
      (extChartAt I y).left_inv hfy
    refine ⟨?_,(extChartAt I y).map_source hfy⟩
    change (extChartAt I y).symm (mapChart f x y w) ∈ f '' s
    rw [heq]
    exact mem_image_of_mem f hw.1
  · rintro ⟨⟨p,hps,hpf⟩,hz⟩
    refine ⟨extChartAt I x p,?_,?_⟩
    · exact ⟨by change (extChartAt I x).symm (extChartAt I x p) ∈ s;
                   rwa [(extChartAt I x).left_inv (hx hps)], (extChartAt I x).map_source (hx hps)⟩
    · change extChartAt I y (f ((extChartAt I x).symm (extChartAt I x p))) = z
      rw [(extChartAt I x).left_inv (hx hps),hpf,(extChartAt I y).right_inv hz]

lemma localVolume_image_le (g : Metric (M := M)) (h : Metric (M := N)) (f : M → N)
    (hf : ContMDiff I I 1 f)
    (hshort : ∀ x v, h.inner (f x) (mfderiv I I f x v) (mfderiv I I f x v) ≤ g.inner x v v)
    (x : M) (y : N) {s : Set M} (hs : MeasurableSet s) (hfs : MeasurableSet (f '' s))
    (hx : s ⊆ (extChartAt I x).source) (hy : MapsTo f s (extChartAt I y).source) :
    localVolume h y (f '' s) ≤ localVolume g x s := by
  classical
  let w := (extChartAt I y).target.piecewise (fun z => ENNReal.ofReal (chartDensity h y z))
    (fun _ => 0)
  have hwm : Measurable w :=
    (ENNReal.continuous_ofReal.comp_continuousOn (chartDensity_continuousOn h y)).measurable_piecewise
      continuous_const.continuousOn (chart_target_measurable y)
  have hB : MeasurableSet (chartPreimage x s) := chartPreimage_measurable x hs
  have hd : ∀ z ∈ chartPreimage x s, HasFDerivWithinAt (mapChart f x y) (mapChartDeriv f x y z)
      (chartPreimage x s) z := by
    intro z hz
    exact (hasFDerivWithinAt_mapChart f hf x y hz.2 (hy hz.1)).mono
      (fun a ha => extChartAt_target_subset_range x ha.2)
  have hwz : ∀ z ∈ chartPreimage x s, w (mapChart f x y z) =
      ENNReal.ofReal (chartDensity h y (mapChart f x y z)) := by
    intro z hz
    exact piecewise_eq_of_mem _ _ _ ((extChartAt I y).map_source (hy hz.1))
  have hn : ∫⁻ z in chartPreimage y (f '' s), w z = localVolume h y (f '' s) := by
    rw [localVolume_apply h y hfs]
    apply setLIntegral_congr_fun (chartPreimage_measurable y hfs)
    intro z hz
    exact piecewise_eq_of_mem _ _ _ hz.2
  rw [localVolume_apply g x hs,← hn,← mapChart_image f x y hx hy]
  calc
    _ ≤ ∫⁻ z in chartPreimage x s, ENNReal.ofReal |(mapChartDeriv f x y z).det| *
        w (mapChart f x y z) := lintegral_image_le_jacobian_on hB hd w hwm
    _ ≤ ∫⁻ z in chartPreimage x s, ENNReal.ofReal (chartDensity g x z) := by
      apply lintegral_mono_ae
      filter_upwards [self_mem_ae_restrict hB] with z hz
      rw [hwz z hz,← ENNReal.ofReal_mul (abs_nonneg _)]
      exact ENNReal.ofReal_le_ofReal (mapChart_density_le g h f hshort x y (hy hz.1))

end CKSSurfaceVolume

end

end OAI
