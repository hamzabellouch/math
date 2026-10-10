import Mathlib
import OAI.Probability.GaussianRegression.Main
import OAI.Probability.MemoryPrecision.FiniteDensity
import OAI.Probability.MemoryPrecision.KernelModel
import OAI.Probability.MemoryPrecision.LabelTranslations

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter EuclideanGeometry
open scoped ENNReal NNReal RealInnerProductSpace Topology Pointwise

noncomputable section
universe u v

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology Pointwise
namespace MemoryPrecision
open NoiselessRegression
def UniformSphere (d : ℕ) : @Measure (Space d)
    (WithLp.measurableSpace
      (@OfNat.ofNat ℝ≥0∞ 2
        (@instOfNatAtLeastTwo ℝ≥0∞ 2 ENNReal.instAddCommMonoidWithOne.toNatCast
          (Mathlib.Meta.NormNum.instAtLeastTwo (nat_lit 0)))) (Fin d → ℝ)) :=
  let euclideanMeasurable := WithLp.measurableSpace
    (@OfNat.ofNat ℝ≥0∞ 2
      (@instOfNatAtLeastTwo ℝ≥0∞ 2 ENNReal.instAddCommMonoidWithOne.toNatCast
        (Mathlib.Meta.NormNum.instAtLeastTwo (nat_lit 0)))) (Fin d → ℝ)
  @Measure.map (Kernel.Sphere d) (Space d)
    (MeasurableSpace.comap Subtype.val euclideanMeasurable) euclideanMeasurable
    Subtype.val (Kernel.UniformSphere d)

def GaussianRegularization {d : ℕ}
    (μ : @Measure (Space d)
      (WithLp.measurableSpace
        (@OfNat.ofNat ℝ≥0∞ 2
          (@instOfNatAtLeastTwo ℝ≥0∞ 2 ENNReal.instAddCommMonoidWithOne.toNatCast
            (Mathlib.Meta.NormNum.instAtLeastTwo (nat_lit 0)))) (Fin d → ℝ)))
    (m : ℕ) (δ : ℝ)
    (Ay : (Fin m → Space d) × (Fin m → ℝ)) : ℝ :=
  let exponent : ℝ≥0∞ := @OfNat.ofNat ℝ≥0∞ 2
    (@instOfNatAtLeastTwo ℝ≥0∞ 2 ENNReal.instAddCommMonoidWithOne.toNatCast
      (Mathlib.Meta.NormNum.instAtLeastTwo (nat_lit 0)))
  letI : MeasurableSpace (Space d) := WithLp.measurableSpace exponent (Fin d → ℝ)
  ∫ signal, ∏ index, gaussianPDFReal 0 ⟨δ^2, sq_nonneg δ⟩
    (Ay.2 index - @inner ℝ (Space d)
      (@InnerProductSpace.toInner ℝ (Space d) _
        (PiLp.seminormedAddCommGroup exponent (fun _ : Fin d => ℝ))
        (PiLp.innerProductSpace (𝕜 := ℝ) (fun _ : Fin d => ℝ)))
      signal (Ay.1 index)) ∂μ

lemma gaussianPDF_zero_sub_comm (v : ℝ≥0) (a b : ℝ) :
    gaussianPDF 0 v (a-b) = gaussianPDF 0 v (b-a) := by
  simp only [gaussianPDF, gaussianPDFReal, sub_zero]
  congr 4
  ring

lemma GaussianRegularization_eq_toReal {d : ℕ} (μ : Measure (Space d))
    [IsFiniteMeasure μ] (m : ℕ) (δ : ℝ)
    (x : (Fin m → Space d) × (Fin m → ℝ)) :
    GaussianRegularization μ m δ x =
      (projectionSmoothing μ (gaussianPDF 0 ⟨δ^2,sq_nonneg δ⟩) m x).toReal := by
  let v : ℝ≥0 := ⟨δ^2,sq_nonneg δ⟩
  change (∫ s, ∏ j, gaussianPDFReal 0 v (x.2 j - ⟪s,x.1 j⟫) ∂μ) = _
  have hn : ∀ s : Space d, 0 ≤ ∏ j, gaussianPDFReal 0 v (x.2 j - ⟪s,x.1 j⟫) :=
    fun s => Finset.prod_nonneg (fun _ _ => gaussianPDFReal_nonneg _ _ _)
  have hm : Measurable (fun s : Space d => ∏ j, gaussianPDFReal 0 v (x.2 j - ⟪s,x.1 j⟫)) := by
    fun_prop
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall hn) hm.aestronglyMeasurable]
  unfold projectionSmoothing
  congr 1
  apply lintegral_congr
  intro s
  rw [ENNReal.ofReal_prod_of_nonneg (fun _ _ => gaussianPDFReal_nonneg _ _ _)]
  rfl

lemma GaussianRegularization_ae_eq_average {d : ℕ} (μ : Measure (Space d))
    [IsFiniteMeasure μ] (m : ℕ)
    (F : ((Fin m → Space d) × (Fin m → ℝ)) → ℝ)
    (hF : Measurable F) (hF0 : ∀ x, 0 ≤ F x)
    (hden : (MatrixLabelReference d m).withDensity (fun x => ENNReal.ofReal (F x)) =
      ProjectionLaw μ m) (δ : ℝ) (hδ : δ ≠ 0) :
    GaussianRegularization μ m δ =ᵐ[MatrixLabelReference d m]
      averageTranslate (Measure.pi (fun _ : Fin m => gaussianReal 0 1)) δ F := by
  have he := projectionSmoothing_ae_eq_fiberSmoothing μ m
    (fun x => ENNReal.ofReal (F x)) hF.ennreal_ofReal hden
    (gaussianPDF 0 ⟨δ^2,sq_nonneg δ⟩) (measurable_gaussianPDF _ _)
  filter_upwards [he] with x hx
  rw [GaussianRegularization_eq_toReal, hx]
  unfold averageTranslate
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall (fun u => hF0 _))
    ((hF.comp (by fun_prop)).aestronglyMeasurable)]
  congr 1
  change fiberSmoothing volume (fun x => ENNReal.ofReal (F x))
    (fun y : Fin m → ℝ => ∏ j, gaussianPDF 0 _ (y j)) x =
      ∫⁻ u : Fin m → ℝ, ENNReal.ofReal (F (x.1,fun j => x.2 j + δ * u j))
        ∂Measure.pi (fun _ => gaussianReal 0 1)
  rw [lintegral_gaussian_shift_scale m δ hδ x.2 (fun y => ENNReal.ofReal (F (x.1,y)))
    (by fun_prop)]
  apply lintegral_congr
  intro y
  congr 1
  apply Finset.prod_congr rfl
  intro j _
  exact gaussianPDF_zero_sub_comm _ _ _

lemma memLp_density_of_finite {X : Type*} [MeasurableSpace X]
    (ν₀ η : Measure X) [IsFiniteMeasure η] {F : X → ℝ}
    (hFm : Measurable F) (hF0 : ∀ x, 0 ≤ F x)
    (hden : ν₀.withDensity (fun x => ENNReal.ofReal (F x)) = η) :
    MemLp F 1 ν₀ := by
  rw [memLp_iff, eLpNorm_one_eq_lintegral_enorm hFm.aestronglyMeasurable]
  have he : (fun x => ‖F x‖ₑ) = (fun x => ENNReal.ofReal (F x)) := by
    funext x
    exact Real.enorm_eq_ofReal (hF0 x)
  rw [he]
  have he2 := congrArg (fun ν : Measure X => ν Set.univ) hden
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at he2
  rw [he2]
  exact measure_lt_top _ _

lemma density_ae_unique_real {X : Type*} [MeasurableSpace X]
    (ν₀ : Measure X) [SigmaFinite ν₀] {F G : X → ℝ}
    (hFm : Measurable F) (hF0 : ∀ x, 0 ≤ F x)
    (hGm : Measurable G) (hG0 : ∀ x, 0 ≤ G x)
    (hden : ν₀.withDensity (fun x => ENNReal.ofReal (F x)) =
      ν₀.withDensity (fun x => ENNReal.ofReal (G x))) : F =ᵐ[ν₀] G := by
  have he := (withDensity_eq_iff_of_sigmaFinite hFm.ennreal_ofReal.aemeasurable
    hGm.ennreal_ofReal.aemeasurable).mp hden
  filter_upwards [he] with x hx
  exact (ENNReal.ofReal_eq_ofReal_iff (hF0 x) (hG0 x)).mp hx

def JointL1Statement : Prop :=
  let two : ℝ := @OfNat.ofNat ℝ 2 (@instOfNatAtLeastTwo ℝ 2 Real.commRing.toNatCast
    (Mathlib.Meta.NormNum.instAtLeastTwo (nat_lit 0)))
  let exponent : ℝ≥0∞ := @OfNat.ofNat ℝ≥0∞ 2
    (@instOfNatAtLeastTwo ℝ≥0∞ 2 ENNReal.instAddCommMonoidWithOne.toNatCast
      (Mathlib.Meta.NormNum.instAtLeastTwo (nat_lit 0)))
  ∀ d m p : ℕ,
  letI : MeasurableSpace (Space d) := WithLp.measurableSpace exponent (Fin d → ℝ)
  2 ≤ d → 1 ≤ m → m < d → 2 ≤ p →
  ∀ β H R : ℝ, (m : ℝ)+(p : ℝ)-two < β → 0 < H → 0 < R →
  ∀ z : Space d, ∀ μ : Measure (Space d), IsFiniteMeasure μ →
    @Measure.support (Space d)
      (PiLp.topologicalSpace (p := exponent) (β := fun _ : Fin d => ℝ))
      (WithLp.measurableSpace exponent (Fin d → ℝ)) μ ⊆
      @Metric.closedBall (Space d)
        (PiLp.instPseudoMetricSpace (p := exponent) (β := fun _ : Fin d => ℝ)) z R →
    AmbientBallBound μ H β →
    μ ≪ UniformSphere d →
  ∀ F : ((Fin m → Space d) × (Fin m → ℝ)) → ℝ,
    Measurable F → (∀ x, 0 ≤ F x) →
    (MatrixLabelReference d m).withDensity (fun x => ENNReal.ofReal (F x)) =
      ProjectionLaw μ m →
    Tendsto (fun δ => eLpNorm (fun Ay => GaussianRegularization μ m δ Ay - F Ay)
      1 (MatrixLabelReference d m)) (𝓝[Set.Ioi 0] 0) (𝓝 0) ∧
    eLpNorm F (p : ℝ≥0∞) (MatrixLabelReference d m) ≤
      ENNReal.ofReal (ProjectionNormScale m p H β R)
theorem joint_l1 : JointL1Statement := by
  intro d m p hd hm hmd hp β H R hgap hH hR z μ hμ hs hb hac F hFm hF0 hden
  have : IsFiniteMeasure μ := hμ
  have : IsFiniteMeasure (ProjectionLaw μ m) := by unfold ProjectionLaw; infer_instance
  have : SigmaFinite (MatrixLabelReference d m) := by unfold MatrixLabelReference; infer_instance
  have hF := memLp_density_of_finite (MatrixLabelReference d m) (ProjectionLaw μ m) hFm hF0 hden
  constructor
  · have ht := tendsto_eLpNorm_averageTranslate_sub
      (Measure.pi (fun _ : Fin m => stdGaussian (Space d)))
      (volume : Measure (Fin m → ℝ))
      (Measure.pi (fun _ : Fin m => gaussianReal 0 1)) hFm hF
    apply (ht.mono_left nhdsWithin_le_nhds).congr'
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    apply eLpNorm_congr_ae
    filter_upwards [GaussianRegularization_ae_eq_average μ m F hFm hF0 hden δ
      (ne_of_gt hδ)] with x hx
    exact congrArg (fun t => t - F x) hx.symm
  · obtain ⟨G,hGm,hG0,hGden,hGs,hGnorm⟩ :=
      exact_finite_density d m p hp hm β H R hgap hH hR z μ hs hb
    have he := density_ae_unique_real (MatrixLabelReference d m) hFm hF0 hGm hG0
      (hden.trans hGden.symm)
    exact (eLpNorm_congr_ae he).symm ▸ hGnorm
end MemoryPrecision


end

end OAI
