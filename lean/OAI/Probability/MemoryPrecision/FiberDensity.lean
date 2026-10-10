import Mathlib
import OAI.Probability.GaussianRegression.Main
import OAI.Probability.MemoryPrecision.GaussianConvolution
import OAI.Probability.MemoryPrecision.PointwiseDensity
import OAI.Probability.MemoryPrecision.SphericalProjection

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter EuclideanGeometry
open scoped ENNReal NNReal RealInnerProductSpace Topology Pointwise

noncomputable section
universe u v

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology Pointwise
namespace MemoryPrecision
open NoiselessRegression

def PiGaussianConvolution {m : ℕ} (ν : Measure (Fin m → ℝ)) (δ : ℝ) (y : Fin m → ℝ) : ℝ :=
  ∫ x, ∏ j, gaussianPDFReal 0 ⟨δ^2,sq_nonneg δ⟩ (y j - x j) ∂ν

lemma piGaussianConvolution_eq {m : ℕ} (ν : Measure (Fin m → ℝ)) (δ : ℝ) (y : Fin m → ℝ) :
    PiGaussianConvolution ν δ y =
      GaussianConvolution (ν.map (WithLp.toLp 2)) δ (WithLp.toLp 2 y) := by
  unfold GaussianConvolution
  rw [integral_map (WithLp.measurable_toLp 2 (Fin m → ℝ)).aemeasurable
    ((show Continuous (fun x : Space m => GaussianKernel m δ (WithLp.toLp 2 y - x)) from
      (gaussianKernel_continuous m δ).comp (continuous_const.sub continuous_id)).aestronglyMeasurable)]
  rfl

lemma ae_tendsto_piGaussianConvolution {m : ℕ} (hm : 1 ≤ m) (ν : Measure (Fin m → ℝ))
    [IsFiniteMeasure ν] (hν : ν ≪ volume) :
    ∀ᵐ y ∂(volume : Measure (Fin m → ℝ)), Tendsto (fun δ : ℝ => PiGaussianConvolution ν δ y)
      (𝓝[>] (0:ℝ)) (𝓝 ((ν.rnDeriv volume y).toReal)) := by
  let e := MeasurableEquiv.toLp 2 (Fin m → ℝ)
  have hp : MeasurePreserving e volume volume := PiLp.volume_preserving_toLp (Fin m)
  have hac : ν.map e ≪ volume := by
    rw [← hp.map_eq]
    exact hν.map e.measurable
  have ht := ae_tendsto_gaussianConvolution hm (ν.map e) hac
  have ht' : ∀ᵐ y ∂(volume : Measure (Fin m → ℝ)),
      Tendsto (fun δ : ℝ => GaussianConvolution (ν.map e) δ (e y))
        (𝓝[>] (0:ℝ)) (𝓝 (((ν.map e).rnDeriv volume (e y)).toReal)) := by
    have ht0 : ∀ᵐ y ∂(volume.map e),
        Tendsto (fun δ : ℝ => GaussianConvolution (ν.map e) δ y)
          (𝓝[>] (0:ℝ)) (𝓝 (((ν.map e).rnDeriv volume y).toReal)) := by
      rwa [hp.map_eq]
    exact e.measurableEmbedding.ae_map_iff.mp ht0
  have hRN := e.measurableEmbedding.rnDeriv_map ν volume
  rw [hp.map_eq] at hRN
  filter_upwards [ht', hRN] with y hy hyRN
  rw [hyRN] at hy
  simpa only [piGaussianConvolution_eq, e, MeasurableEquiv.coe_toLp] using hy

lemma GaussianRegularization_eq_convolution {d m : ℕ} (μ : Measure (Space d))
    (A : Fin m → Space d) (δ : ℝ) (y : Fin m → ℝ) :
    GaussianRegularization μ m δ (A,y) =
      PiGaussianConvolution (μ.map (fun s => fun j => ⟪s,A j⟫)) δ y := by
  unfold PiGaussianConvolution
  rw [integral_map (by fun_prop)
    (((show Continuous (fun x : Fin m → ℝ => ∏ j,
      gaussianPDFReal 0 ⟨δ^2,sq_nonneg δ⟩ (y j - x j)) from
      by unfold gaussianPDFReal; fun_prop)).aestronglyMeasurable)]
  rfl

lemma ae_tendsto_GaussianRegularization {d m : ℕ} (hm : 1 ≤ m) (μ : Measure (Space d))
    [IsFiniteMeasure μ] (A : Fin m → Space d)
    (hA : μ.map (fun s => fun j => ⟪s,A j⟫) ≪ (volume : Measure (Fin m → ℝ))) :
    ∀ᵐ y ∂(volume : Measure (Fin m → ℝ)), Tendsto
      (fun δ : ℝ => GaussianRegularization μ m δ (A,y)) (𝓝[>] (0:ℝ))
      (𝓝 (((μ.map (fun s => fun j => ⟪s,A j⟫)).rnDeriv volume y).toReal)) := by
  simpa only [GaussianRegularization_eq_convolution] using
    ae_tendsto_piGaussianConvolution hm (μ.map (fun s => fun j => ⟪s,A j⟫)) hA

lemma reciprocal_nat_tendsto :
    Tendsto (fun i : ℕ => 1/(i:ℝ)) atTop (𝓝[>] (0:ℝ)) := by
  refine tendsto_nhdsWithin_iff.mpr ⟨tendsto_one_div_atTop_nhds_zero_nat, ?_⟩
  filter_upwards [eventually_gt_atTop (0:ℕ)] with i hi
  change 0 < 1/(i:ℝ)
  positivity

lemma pointwiseDensity_fiber {d m : ℕ} (hm : 1 ≤ m) (μ : Measure (Space d))
    [IsFiniteMeasure μ] (A : Fin m → Space d)
    (hA : μ.map (fun s => fun j => ⟪s,A j⟫) ≪ (volume : Measure (Fin m → ℝ))) :
    (volume : Measure (Fin m → ℝ)).withDensity
      (fun y => ENNReal.ofReal (PointwiseDensity μ m (A,y))) =
      μ.map (fun s => fun j => ⟪s,A j⟫) := by
  let ν := μ.map (fun s => fun j => ⟪s,A j⟫)
  have he : (fun y => ENNReal.ofReal (PointwiseDensity μ m (A,y))) =ᵐ[volume]
      ν.rnDeriv volume := by
    filter_upwards [ae_tendsto_GaussianRegularization hm μ A hA, ν.rnDeriv_lt_top volume]
      with y hy hyfin
    rw [PointwiseDensity_eq_of_tendsto μ (A,y) (hy.comp reciprocal_nat_tendsto)]
    exact ENNReal.ofReal_toReal hyfin.ne
  rw [withDensity_congr_ae he]
  exact Measure.withDensity_rnDeriv_eq _ _ hA

lemma pointwiseDensity_fullRank {d m : ℕ} (hd : 2 ≤ d) (hm : 1 ≤ m) (hmd : m < d)
    (μ : Measure (Space d)) [IsFiniteMeasure μ] (hμ : μ ≪ UniformSphere d)
    (A : Fin m → Space d) (hA : LinearIndependent ℝ A) :
    (volume : Measure (Fin m → ℝ)).withDensity
      (fun y => ENNReal.ofReal (PointwiseDensity μ m (A,y))) =
      μ.map (fun s => fun j => ⟪s,A j⟫) :=
  pointwiseDensity_fiber hm μ A (spherical_projection_ac hd hmd A hA μ hμ)
end MemoryPrecision


end

end OAI
