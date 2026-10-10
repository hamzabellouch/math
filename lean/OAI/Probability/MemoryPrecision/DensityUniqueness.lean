import Mathlib
import OAI.Probability.GaussianRegression.Main
import OAI.Probability.MemoryPrecision.FiberDensity

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter EuclideanGeometry
open scoped ENNReal NNReal RealInnerProductSpace Topology Pointwise

noncomputable section
universe u v

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology Pointwise
namespace MemoryPrecision
open NoiselessRegression

lemma piGaussianConvolution_withDensity {m : ℕ} (F : (Fin m → ℝ) → ℝ≥0∞)
    (hF : Measurable F) (δ : ℝ) (y : Fin m → ℝ) :
    PiGaussianConvolution (volume.withDensity F) δ y =
      (∫⁻ x, (∏ j, gaussianPDF 0 ⟨δ^2,sq_nonneg δ⟩ (y j-x j)) * F x).toReal := by
  unfold PiGaussianConvolution
  rw [integral_eq_lintegral_of_nonneg_ae
    (Eventually.of_forall (fun x => Finset.prod_nonneg (fun j _ => gaussianPDFReal_nonneg _ _ _)))
    ((show Continuous (fun x : Fin m → ℝ => ∏ j,
      gaussianPDFReal 0 ⟨δ^2,sq_nonneg δ⟩ (y j-x j)) from
      by unfold gaussianPDFReal; fun_prop).aestronglyMeasurable),
    lintegral_withDensity_eq_lintegral_mul _ hF (by fun_prop)]
  congr 1
  apply lintegral_congr
  intro x
  simp only [Pi.mul_apply, gaussianPDF]
  rw [ENNReal.ofReal_prod_of_nonneg (fun j _ =>
    gaussianPDFReal_nonneg 0 ⟨δ^2,sq_nonneg δ⟩ (y j-x j)), mul_comm]

lemma ae_tendsto_fiberGaussian {Ω : Type*} [MeasurableSpace Ω] (γ : Measure Ω)
    [SigmaFinite γ] {m : ℕ} (hm : 1 ≤ m)
    (F : Ω × (Fin m → ℝ) → ℝ≥0∞) (hF : Measurable F)
    (hfin : (∫⁻ z, F z ∂γ.prod volume) ≠ ∞) :
    ∀ᵐ z ∂γ.prod volume, Tendsto
      (fun i : ℕ => (fiberSmoothing volume F
        (fun y : Fin m → ℝ => ∏ j, gaussianPDF 0
          ⟨(1/(i:ℝ))^2,sq_nonneg _⟩ (y j)) z).toReal)
      atTop (𝓝 (F z).toReal) := by
  have hmeas (i : ℕ) : Measurable (fun z => (fiberSmoothing volume F
      (fun y : Fin m → ℝ => ∏ j, gaussianPDF 0
        ⟨(1/(i:ℝ))^2,sq_nonneg _⟩ (y j)) z).toReal) :=
    (measurable_fiberSmoothing volume hF (by fun_prop)).ennreal_toReal
  rw [Measure.ae_prod_iff_ae_ae (measurableSet_tendsto_fun hmeas hF.ennreal_toReal)]
  have hinner : (∫⁻ A, ∫⁻ y : Fin m → ℝ, F (A,y) ∂volume ∂γ) ≠ ∞ := by
    rwa [← lintegral_prod _ hF.aemeasurable]
  filter_upwards [ae_lt_top (Measurable.lintegral_prod_right
    (show Measurable (fun z : Ω × (Fin m → ℝ) => F (z.1,z.2)) from hF)) hinner] with A hA
  let ν : Measure (Fin m → ℝ) := volume.withDensity (fun y => F (A,y))
  have hFA : Measurable (fun y : Fin m → ℝ => F (A,y)) :=
    hF.comp (measurable_const.prodMk measurable_id)
  let : IsFiniteMeasure ν := isFiniteMeasure_withDensity hA.ne
  have hac : ν ≪ volume := withDensity_absolutelyContinuous _ _
  have hRN := Measure.rnDeriv_withDensity volume hFA
  filter_upwards [ae_tendsto_piGaussianConvolution hm ν hac, hRN] with y hy hyRN
  rw [hyRN] at hy
  convert hy.comp reciprocal_nat_tendsto using 1
  ext i
  exact (piGaussianConvolution_withDensity (fun y => F (A,y)) hFA _ y).symm

lemma pointwiseDensity_ae_eq {d m : ℕ} (hm : 1 ≤ m) (μ : Measure (Space d))
    [IsFiniteMeasure μ] (F : ((Fin m → Space d) × (Fin m → ℝ)) → ℝ)
    (hFm : Measurable F) (hF0 : ∀ x, 0 ≤ F x)
    (hden : (MatrixLabelReference d m).withDensity (fun x => ENNReal.ofReal (F x)) =
      ProjectionLaw μ m) :
    PointwiseDensity μ m =ᵐ[MatrixLabelReference d m] F := by
  have hfin : (∫⁻ z, ENNReal.ofReal (F z) ∂MatrixLabelReference d m) ≠ ∞ := by
    have he := congrArg (fun ν => ν Set.univ) hden
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at he
    rw [he]
    let : IsFiniteMeasure (ProjectionLaw μ m) := by unfold ProjectionLaw; infer_instance
    exact measure_ne_top _ _
  have ht := ae_tendsto_fiberGaussian
    (Measure.pi (fun _ : Fin m => stdGaussian (Space d))) hm
    (fun x => ENNReal.ofReal (F x)) hFm.ennreal_ofReal hfin
  have he (i : ℕ) := projectionSmoothing_ae_eq_fiberSmoothing μ m
    (fun x => ENNReal.ofReal (F x)) hFm.ennreal_ofReal hden
    (gaussianPDF 0 ⟨(1/(i:ℝ))^2,sq_nonneg _⟩) (measurable_gaussianPDF _ _)
  filter_upwards [ht, ae_all_iff.mpr he] with x hx hxe
  apply PointwiseDensity_eq_of_tendsto
  rw [ENNReal.toReal_ofReal (hF0 x)] at hx
  convert hx using 1
  ext i
  rw [GaussianRegularization_eq_toReal μ m _, hxe i]
end MemoryPrecision


end

end OAI
