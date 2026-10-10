import Mathlib
import OAI.Geometry.WeakHessian.LocalBounds.SquareControl
import OAI.Geometry.WeakHessian.Sobolev.LocalSobolevLipschitz
import OAI.Geometry.WeakHessian.Transport.FiniteLocalization

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open Set Filter
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter Topology Bornology
open scoped InnerProductSpace
open Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable
namespace WeakHessian
open MeasureTheory Filter Set
open scoped Topology ENNReal NNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

omit [MeasurableSpace X] [BorelSpace X] in
lemma IsGeodesic.squareControl {γ : Curve X} (h : IsGeodesic γ) :
    IsSquareControl γ (fun _ => dist (γ timeZero) (γ timeOne)) := by
  refine ⟨measurable_const,memLp_const _,ae_of_all _ (fun _ => dist_nonneg),?_⟩
  intro s t hst
  rw [h s t,intervalIntegral.integral_const,smul_eq_mul,
    abs_sub_comm (s:ℝ),abs_of_nonneg (sub_nonneg.mpr hst)]

omit [MeasurableSpace X] [BorelSpace X] in
lemma IsGeodesic.ae_metricSpeed_le {γ : Curve X} (h : IsGeodesic γ) :
    ∀ᵐ s ∂volume.restrict (Icc (0:ℝ) 1),
      metricSpeed γ s ≤ ENNReal.ofReal (dist (γ timeZero) (γ timeOne)) :=
  h.squareControl.metricSpeed_le

omit [MeasurableSpace X] [BorelSpace X] in
lemma BoundedTracks.integrable_length_sq {π : Measure (Curve X)} [IsFiniteMeasure π]
    (hb : BoundedTracks π) :
    Integrable (fun γ => dist (γ timeZero) (γ timeOne)^2) π := by
  obtain ⟨o,R,hR,hb⟩ := hb
  apply (integrable_const ((2*R)^2)).mono'
    (((continuous_eval_const timeZero).dist (continuous_eval_const timeOne)).pow 2).aestronglyMeasurable
  filter_upwards [hb] with γ hγ
  rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
  apply (sq_le_sq₀ dist_nonneg (by positivity)).mpr
  have H := dist_triangle (γ timeZero) o (γ timeOne)
  rw [dist_comm o] at H
  linarith [hγ timeZero,hγ timeOne]

variable [CompleteSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}

lemma IsLocalWeakUpperGradient.geodesic_young
    {f D : X → ℝ} (hD : IsLocalWeakUpperGradient m f D) (hf : AEMeasurable f m)
    {B : ℝ} (hB : 0 ≤ B) (hDb : ∀ᵐ x ∂m, |D x| ≤ B)
    {π : Measure (Curve X)} (hπ : IsTestPlan m π) (hb : BoundedTracks π)
    (hgeo : ∀ᵐ γ ∂π, IsGeodesic γ) (t : Time) (ht : 0 < t.val) :
    (∫ γ, f (γ timeZero)-f (γ t) ∂π) ≤
      ∫ z : Curve X × ℝ, ((D (evalReal z.1 z.2))^2+
        dist (z.1 timeZero) (z.1 timeOne)^2)/2
        ∂(π.prod (volume.restrict (Icc (0:ℝ) t.val))) := by
  let : IsProbabilityMeasure π := hπ.1
  let ν := volume.restrict (Icc (0:ℝ) t.val)
  have hν : ν ≤ volume.restrict (Icc (0:ℝ) 1) :=
    Measure.restrict_mono_set _ (Icc_subset_Icc le_rfl t.property.2)
  have hprod : π.prod ν ≤ π.prod (volume.restrict (Icc (0:ℝ) 1)) := Measure.prod_mono le_rfl hν
  have hDm := (hπ.aemeasurable_evalReal hD.1.aemeasurable).mono_measure hprod
  have hDI : Integrable (fun z : Curve X × ℝ => (D (evalReal z.1 z.2))^2) (π.prod ν) := by
    apply (integrable_const (B^2)).mono' (hDm.pow_const 2).aestronglyMeasurable
    filter_upwards [ae_mono hprod (hπ.ae_prod_eval_of_ae hDb)] with z hz
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hB).mpr hz
  have hLI := hb.integrable_length_sq.comp_fst ν
  have hI := (hDI.add hLI).div_const (2:ℝ)
  dsimp only [Pi.add_apply] at hI
  have hn : 0 ≤ᵐ[π.prod ν] (fun z : Curve X × ℝ =>
      ((D (evalReal z.1 z.2))^2+dist (z.1 timeZero) (z.1 timeOne)^2)/2) :=
    ae_of_all _ fun z => by positivity
  have H : ENNReal.ofReal (∫ γ, f (γ timeZero)-f (γ t) ∂π) ≤
      ∫⁻ z : Curve X × ℝ, ENNReal.ofReal (((D (evalReal z.1 z.2))^2+
        dist (z.1 timeZero) (z.1 timeOne)^2)/2) ∂(π.prod ν) := by
    calc
      _ ≤ ENNReal.ofReal |∫ γ, f (γ timeZero)-f (γ t) ∂π| := ENNReal.ofReal_le_ofReal (le_abs_self _)
      _ ≤ ∫⁻ γ, ENNReal.ofReal |f (γ timeZero)-f (γ t)| ∂π := by
        simpa only [Real.enorm_eq_ofReal_abs] using
          enorm_integral_le_lintegral_enorm (μ := π) (fun γ => f (γ timeZero)-f (γ t))
      _ ≤ ∫⁻ γ, ∫⁻ s, ENNReal.ofReal (((D (evalReal γ s))^2+
          dist (γ timeZero) (γ timeOne)^2)/2) ∂ν ∂π := by
        apply lintegral_mono_ae
        filter_upwards [hD.ae_subinterval_le hf hπ hb timeZero t ht,hgeo,
          hπ.ae_ae_eval_of_ae hD.2.1] with γ hg hγ hpos
        rw [abs_sub_comm] at hg
        apply hg.trans
        apply lintegral_mono_ae
        filter_upwards [ae_mono hν hγ.ae_metricSpeed_le,ae_mono hν hpos] with s hs hDs
        calc
          _ ≤ ENNReal.ofReal (D (evalReal γ s))*ENNReal.ofReal (dist (γ timeZero) (γ timeOne)) :=
            mul_le_mul_of_nonneg_left hs bot_le
          _ = ENNReal.ofReal (D (evalReal γ s)*dist (γ timeZero) (γ timeOne)) := (ENNReal.ofReal_mul hDs).symm
          _ ≤ _ := ENNReal.ofReal_le_ofReal (by nlinarith [sq_nonneg (D (evalReal γ s)-dist (γ timeZero) (γ timeOne))])
      _ = _ := (lintegral_prod _ hI.aestronglyMeasurable.aemeasurable.ennreal_ofReal).symm
  rw [← ofReal_integral_eq_lintegral_ofReal hI hn] at H
  exact (ENNReal.ofReal_le_ofReal_iff (integral_nonneg_of_ae hn)).mp H


lemma IsLocalWeakUpperGradient.geodesic_young_time
    {f D : X → ℝ} (hD : IsLocalWeakUpperGradient m f D) (hf : AEMeasurable f m)
    {B : ℝ} (hB : 0 ≤ B) (hDb : ∀ᵐ x ∂m, |D x| ≤ B)
    {π : Measure (Curve X)} (hπ : IsTestPlan m π) (hb : BoundedTracks π)
    (hgeo : ∀ᵐ γ ∂π, IsGeodesic γ) (t : Time) (ht : 0 < t.val) :
    (∫ γ, f (γ timeZero)-f (γ t) ∂π) ≤
      ((∫ s in 0..t.val, ∫ γ, (D (evalReal γ s))^2 ∂π)+
        t.val*(∫ γ, dist (γ timeZero) (γ timeOne)^2 ∂π))/2 := by
  let : IsProbabilityMeasure π := hπ.1
  let ν := volume.restrict (Icc (0:ℝ) t.val)
  have hν : ν ≤ volume.restrict (Icc (0:ℝ) 1) :=
    Measure.restrict_mono_set _ (Icc_subset_Icc le_rfl t.property.2)
  have hprod : π.prod ν ≤ π.prod (volume.restrict (Icc (0:ℝ) 1)) := Measure.prod_mono le_rfl hν
  have hDm := (hπ.aemeasurable_evalReal hD.1.aemeasurable).mono_measure hprod
  have hDI : Integrable (fun z : Curve X × ℝ => (D (evalReal z.1 z.2))^2) (π.prod ν) := by
    apply (integrable_const (B^2)).mono' (hDm.pow_const 2).aestronglyMeasurable
    filter_upwards [ae_mono hprod (hπ.ae_prod_eval_of_ae hDb)] with z hz
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hB).mpr hz
  have hLI := hb.integrable_length_sq.comp_fst ν
  have H := hD.geodesic_young hf hB hDb hπ hb hgeo t ht
  calc
    _ ≤ _ := H
    _ = _ := by
      rw [integral_div,integral_add hDI hLI,integral_prod_symm _ hDI,integral_prod _ hLI]
      simp only [ν,integral_const,Measure.real,Measure.restrict_apply_univ,
        Real.volume_Icc,sub_zero,smul_eq_mul,ENNReal.toReal_ofReal ht.le]
      rw [integral_const_mul,integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le ht.le]

lemma IsTestPlan.continuous_gradient_energy (hfinite : FiniteOnBoundedSets m)
    {π : Measure (Curve X)} (hπ : IsTestPlan m π) (hb : BoundedTracks π)
    {f : X → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f) :
    Continuous (fun s : ℝ => ∫ γ, (weakGradient m f (evalReal γ s))^2 ∂π) := by
  have hfS := localSobolev_of_lipschitz hfinite hf
  have hm := (weakGradient_isMinimal hfS.2).1.1.aemeasurable
  have hbD : ∀ᵐ x ∂m, |(weakGradient m f x)^2| ≤ (L:ℝ)^2 := by
    filter_upwards [weakGradient_le_lipschitz hfinite hf,weakGradient_nonneg (m := m) f] with x hx hn
    rw [abs_of_nonneg (sq_nonneg _)]
    exact (sq_le_sq₀ hn L.coe_nonneg).mpr hx
  exact (hπ.continuous_integral_eval_bounded hfinite hb (hm.pow_const 2) hbD).comp continuous_clampTime

lemma IsTestPlan.tendsto_average_gradient_energy (hfinite : FiniteOnBoundedSets m)
    {π : Measure (Curve X)} (hπ : IsTestPlan m π) (hb : BoundedTracks π)
    {f : X → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f) :
    Tendsto (fun t : ℝ => (∫ s in 0..t, ∫ γ, (weakGradient m f (evalReal γ s))^2 ∂π)/t)
      (𝓝[>] 0) (𝓝 (∫ γ, (weakGradient m f (γ timeZero))^2 ∂π)) := by
  have hc := hπ.continuous_gradient_energy hfinite hb hf
  have H := (intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 0)
    (hc.stronglyMeasurableAtFilter _ _) hc.continuousAt).tendsto_slope_zero_right
  have he : clampTime 0 = timeZero := Subtype.ext (by simp [clampTime,timeZero])
  simpa only [zero_add,intervalIntegral.integral_same,sub_zero,smul_eq_mul,
    evalReal,he,div_eq_mul_inv,mul_comm] using H

end WeakHessian

end

end OAI
