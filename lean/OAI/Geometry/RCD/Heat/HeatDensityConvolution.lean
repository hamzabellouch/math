import OAI.Geometry.RCD.Heat.HeatGeneralRepresentation

namespace OAI

/-! # Density-level Chapman--Kolmogorov without a pre-existing kernel -/

open Set Filter MeasureTheory Metric TopologicalSpace ProbabilityTheory
open scoped NNReal ENNReal Topology ProbabilityTheory

noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X)
  (hn : 2 ≤ n) (p : X) [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]

def heatDensityConvolution (s t : ℝ) (hs : 0 < s) (ht : 0 < t) (x y : X) : ℝ≥0∞ :=
  ∫⁻ z, ENNReal.ofReal (hX.heatJointDensity hn p s hs x z) *
    ENNReal.ofReal (hX.heatJointDensity hn p t ht z y) ∂hausdorff n X

theorem heatDensityConvolution_measurable (s t : ℝ) (hs : 0 < s) (ht : 0 < t) :
    Measurable (fun xy : X × X => hX.heatDensityConvolution hn p s t hs ht xy.1 xy.2) := by
  have H : Measurable (fun q : (X × X) × X =>
      ENNReal.ofReal (hX.heatJointDensity hn p s hs q.1.1 q.2) *
        ENNReal.ofReal (hX.heatJointDensity hn p t ht q.2 q.1.2)) :=
    (((hX.heatJointDensity_measurable hn p s hs).comp
      (measurable_fst.fst.prodMk measurable_snd)).ennreal_ofReal).mul
      (((hX.heatJointDensity_measurable hn p t ht).comp
        (measurable_snd.prodMk measurable_fst.snd)).ennreal_ofReal)
  exact H.lintegral_prod_right

/-- Tonelli and the already proved measure semigroup law identify the
convolution as the Radon--Nikodym density at the sum of the two times. -/
theorem heatDensityConvolution_withDensity (s t : ℝ) (hs : 0 < s) (ht : 0 < t) (x : X) :
    (hausdorff n X).withDensity (hX.heatDensityConvolution hn p s t hs ht x) =
      hX.heatRadonMeasure hn p (s + t) (add_pos hs ht) x := by
  let μ := hausdorff n X
  let a (z : X) := ENNReal.ofReal (hX.heatJointDensity hn p s hs x z)
  let b (z y : X) := ENNReal.ofReal (hX.heatJointDensity hn p t ht z y)
  have ha : Measurable a := ((hX.heatJointDensity_measurable hn p s hs).comp
    (measurable_const.prodMk measurable_id)).ennreal_ofReal
  have hb : Measurable (Function.uncurry b) :=
    (hX.heatJointDensity_measurable hn p t ht).ennreal_ofReal
  ext A hA
  rw [withDensity_apply _ hA]
  change (∫⁻ y in A, ∫⁻ z, a z * b z y ∂μ ∂μ) = _
  calc
    _ = ∫⁻ z, ∫⁻ y in A, a z * b z y ∂μ ∂μ := by
      apply lintegral_lintegral_swap
      exact ((ha.comp measurable_snd).mul (hb.comp measurable_swap)).aemeasurable
    _ = ∫⁻ z, a z * hX.heatRadonMeasure hn p t ht z A ∂μ := by
      apply lintegral_congr
      intro z
      have hbz : Measurable (b z) := by
        simpa only [Function.comp_def, Function.uncurry_apply_pair, id_eq] using
          hb.comp (measurable_const.prodMk measurable_id)
      rw [lintegral_const_mul _ hbz]
      congr 1
      rw [← hX.heatJointDensity_withDensity hn p t ht z, withDensity_apply _ hA]
    _ = ∫⁻ z, hX.heatRadonMeasure hn p t ht z A ∂hX.heatRadonMeasure hn p s hs x := by
      rw [← hX.heatJointDensity_withDensity hn p s hs x]
      change (∫⁻ z, a z * hX.heatRadonMeasure hn p t ht z A ∂μ) =
        ∫⁻ z, hX.heatRadonMeasure hn p t ht z A ∂μ.withDensity a
      have hm : Measurable (fun z => hX.heatRadonMeasure hn p t ht z A) :=
        (hX.heatMarkovKernel hn p t ht).measurable_coe hA
      exact (lintegral_withDensity_eq_lintegral_mul μ ha hm).symm
    _ = _ := by
      have H := congrArg (fun κ : Kernel X X => κ x A) (hX.heatMarkovKernel_comp hn p s t hs ht)
      rw [Kernel.comp_apply' _ _ _ hA] at H
      exact H

theorem heatDensityConvolution_ae (s t : ℝ) (hs : 0 < s) (ht : 0 < t) (x : X) :
    hX.heatDensityConvolution hn p s t hs ht x =ᵐ[hausdorff n X]
      fun y => ENNReal.ofReal (hX.heatJointDensity hn p (s + t) (add_pos hs ht) x y) := by
  apply (withDensity_eq_iff_of_sigmaFinite
    ((hX.heatDensityConvolution_measurable hn p s t hs ht).comp
      (measurable_const.prodMk measurable_id)).aemeasurable
    (((hX.heatJointDensity_measurable hn p (s + t) (add_pos hs ht)).comp
      (measurable_const.prodMk measurable_id)).ennreal_ofReal.aemeasurable)).mp
  change (hausdorff n X).withDensity (hX.heatDensityConvolution hn p s t hs ht x) =
    (hausdorff n X).withDensity (fun y => ENNReal.ofReal (hX.heatJointDensity hn p (s+t) (add_pos hs ht) x y))
  rw [hX.heatDensityConvolution_withDensity hn p s t hs ht x,
    hX.heatJointDensity_withDensity hn p (s + t) (add_pos hs ht) x]

/-- The density convolution is a finite real integral for almost every
endpoint, for each fixed starting point. -/
theorem heatJointDensity_convolution_ae (s t : ℝ) (hs : 0 < s) (ht : 0 < t) (x : X) :
    ∀ᵐ y ∂hausdorff n X,
      Integrable (fun z => hX.heatJointDensity hn p s hs x z *
        hX.heatJointDensity hn p t ht z y) (hausdorff n X) ∧
      (∫ z, hX.heatJointDensity hn p s hs x z * hX.heatJointDensity hn p t ht z y
        ∂hausdorff n X) = hX.heatJointDensity hn p (s + t) (add_pos hs ht) x y := by
  filter_upwards [hX.heatDensityConvolution_ae hn p s t hs ht x] with y hy
  let f (z : X) := hX.heatJointDensity hn p s hs x z * hX.heatJointDensity hn p t ht z y
  have hf0 (z : X) : 0 ≤ f z := mul_nonneg (hX.heatJointDensity_nonneg hn p s hs x z)
    (hX.heatJointDensity_nonneg hn p t ht z y)
  have hm : Measurable f :=
    ((hX.heatJointDensity_measurable hn p s hs).comp (measurable_const.prodMk measurable_id)).mul
      ((hX.heatJointDensity_measurable hn p t ht).comp (measurable_id.prodMk measurable_const))
  have he : (∫⁻ z, ENNReal.ofReal (f z) ∂hausdorff n X) =
      ENNReal.ofReal (hX.heatJointDensity hn p (s + t) (add_pos hs ht) x y) := by
    calc
      _ = hX.heatDensityConvolution hn p s t hs ht x y := by
        apply lintegral_congr
        intro z
        exact ENNReal.ofReal_mul (hX.heatJointDensity_nonneg hn p s hs x z)
      _ = _ := hy
  have hi : Integrable f (hausdorff n X) :=
    ⟨hm.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal (Eventually.of_forall hf0)).mpr
      (by rw [he]; exact ENNReal.ofReal_lt_top)⟩
  refine ⟨hi, ?_⟩
  have H := congrArg ENNReal.toReal
    ((ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall hf0)).trans he)
  simpa only [ENNReal.toReal_ofReal (integral_nonneg hf0),
    ENNReal.toReal_ofReal (hX.heatJointDensity_nonneg hn p (s+t) (add_pos hs ht) x y)] using H

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
