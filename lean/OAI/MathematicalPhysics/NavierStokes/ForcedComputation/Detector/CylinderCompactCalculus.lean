import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.CylinderLocalEnergyInput
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.PlaneTestIntegral

namespace OAI

/-! Compact horizontal localization of integrals over one vertical period.
These lemmas are the measure-theoretic part of the localized energy identity. -/

noncomputable section
namespace ForcedComputation.VelocityDetector.CylinderLocalCalculus
open ShearFlows Set MeasureTheory Filter
open scoped Topology

local instance : IsLocallyFiniteMeasure cylinderMeasure := by
  unfold cylinderMeasure verticalPeriodMeasure
  infer_instance

theorem ae_vertical_period : ∀ᵐ y ∂cylinderMeasure, y.2 ∈ Icc (0 : ℝ) 1 := by
  apply (Measure.ae_prod_iff_ae_ae
    (measurableSet_Icc.preimage measurable_snd)).2
  exact Eventually.of_forall (fun _ => ae_restrict_mem measurableSet_Icc)

theorem integrable_horizontal_compact {f : Plane × ℝ → ℝ}
    (hf : Continuous f) {K : Set Plane} (hK : IsCompact K)
    (hs : ∀ y, y.1 ∉ K → f y = 0) : Integrable f cylinderMeasure := by
  have hi : IntegrableOn f (K ×ˢ Icc (0 : ℝ) 1) cylinderMeasure :=
    hf.continuousOn.integrableOn_compact (hK.prod isCompact_Icc)
  apply hi.integrable_of_ae_notMem_eq_zero
  filter_upwards [ae_vertical_period] with y hy
  intro hn
  exact hs y (fun hx => hn ⟨hx, hy⟩)

private theorem slice_continuous {g : ℝ × (Plane × ℝ) → ℝ} {a b t : ℝ}
    (hg : ContinuousOn g (Icc a b ×ˢ univ)) (ht : t ∈ Icc a b) :
    Continuous (fun y => g (t, y)) :=
  hg.comp_continuous (continuous_const.prodMk continuous_id)
    (fun _ => ⟨ht, mem_univ _⟩)

theorem compact_integral_hasDerivAt {g d : ℝ × (Plane × ℝ) → ℝ} {a b t : ℝ}
    (hg : ContinuousOn g (Icc a b ×ˢ univ))
    (hd : ContinuousOn d (Icc a b ×ˢ univ))
    (he : ∀ s ∈ Ioo a b, ∀ y, HasDerivAt (fun r => g (r, y)) (d (s, y)) s)
    {K : Set Plane} (hK : IsCompact K) (ht : t ∈ Ioo a b) :
    HasDerivAt (fun r => ∫ y in K ×ˢ Icc (0 : ℝ) 1, g (r, y) ∂cylinderMeasure)
      (∫ y in K ×ˢ Icc (0 : ℝ) 1, d (t, y) ∂cylinderMeasure) t := by
  let S := K ×ˢ Icc (0 : ℝ) 1
  have hS : IsCompact S := hK.prod isCompact_Icc
  obtain ⟨B, hB⟩ := (isCompact_Icc.prod hS).bddAbove_image
    (hd.norm.mono (fun _ hp => ⟨hp.1, mem_univ _⟩))
  have hb : ∀ᵐ y ∂(cylinderMeasure.restrict S),
      ∀ s ∈ Ioo a b, ‖d (s, y)‖ ≤ B := by
    filter_upwards [ae_restrict_mem hS.measurableSet] with y hy
    intro s hs
    exact hB (mem_image_of_mem _ ⟨Ioo_subset_Icc_self hs, hy⟩)
  have hm : ∀ᶠ s in 𝓝 t,
      AEStronglyMeasurable (fun y => g (s, y)) (cylinderMeasure.restrict S) := by
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
    exact (slice_continuous hg (Ioo_subset_Icc_self hs)).aestronglyMeasurable
  have hi : IntegrableOn (fun y => g (t, y)) S cylinderMeasure :=
    (slice_continuous hg (Ioo_subset_Icc_self ht)).continuousOn.integrableOn_compact hS
  have hdm : AEStronglyMeasurable (fun y => d (t, y)) (cylinderMeasure.restrict S) :=
    (slice_continuous hd (Ioo_subset_Icc_self ht)).aestronglyMeasurable
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le (Ioo_mem_nhds ht.1 ht.2)
    hm hi hdm hb (integrableOn_const hS.measure_ne_top)
    (Eventually.of_forall (fun y s hs => he s hs y))).2

theorem integral_restrict_eq_of_horizontal_support {f : Plane × ℝ → ℝ} {K : Set Plane}
    (hs : ∀ y, y.1 ∉ K → f y = 0) :
    (∫ y in K ×ˢ Icc (0 : ℝ) 1, f y ∂cylinderMeasure) = ∫ y, f y ∂cylinderMeasure := by
  apply setIntegral_eq_integral_of_ae_compl_eq_zero
  filter_upwards [ae_vertical_period] with y hy
  intro hn
  exact hs y (fun hx => hn ⟨hx, hy⟩)

theorem supported_integral_hasDerivAt {g d : ℝ × (Plane × ℝ) → ℝ} {a b t : ℝ}
    (hg : ContinuousOn g (Icc a b ×ˢ univ))
    (hd : ContinuousOn d (Icc a b ×ˢ univ))
    (he : ∀ s ∈ Ioo a b, ∀ y, HasDerivAt (fun r => g (r, y)) (d (s, y)) s)
    {K : Set Plane} (hK : IsCompact K)
    (hs : ∀ r y, y.1 ∉ K → g (r, y) = 0)
    (hds : ∀ y, y.1 ∉ K → d (t, y) = 0) (ht : t ∈ Ioo a b) :
    HasDerivAt (fun r => ∫ y, g (r, y) ∂cylinderMeasure)
      (∫ y, d (t, y) ∂cylinderMeasure) t := by
  have h := compact_integral_hasDerivAt hg hd he hK ht
  have hi : (fun r => ∫ y in K ×ˢ Icc (0 : ℝ) 1, g (r, y) ∂cylinderMeasure) =
      (fun r => ∫ y, g (r, y) ∂cylinderMeasure) :=
    funext (fun r => integral_restrict_eq_of_horizontal_support (hs r))
  rw [hi, integral_restrict_eq_of_horizontal_support hds] at h
  exact h

end ForcedComputation.VelocityDetector.CylinderLocalCalculus

end

end OAI
