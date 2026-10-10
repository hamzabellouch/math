import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.PlaneCompactIntegration
import OAI.MathematicalPhysics.NavierStokes.ShearFlows.EnergyCalculus

namespace OAI

/-! Differentiation under a compact spatial test integral on a finite time
interval. No global spatial support assumption is made on the solution. -/

noncomputable section
namespace ForcedComputation.VelocityDetector
open ShearFlows Set MeasureTheory Filter
open scoped ContDiff Topology

private theorem plane_slice_continuous {g : ℝ × Plane → ℝ} {a b t : ℝ}
    (hg : ContinuousOn g (Icc a b ×ˢ univ)) (ht : t ∈ Icc a b) :
    Continuous (fun x => g (t, x)) :=
  hg.comp_continuous (continuous_const.prodMk continuous_id)
    (fun _ => ⟨ht, mem_univ _⟩)

theorem compact_integral_continuousOn {g : ℝ × Plane → ℝ} {a b : ℝ}
    (hg : ContinuousOn g (Icc a b ×ˢ univ)) {K : Set Plane} (hK : IsCompact K) :
    ContinuousOn (fun t => ∫ x in K, g (t, x)) (Icc a b) := by
  rw [continuousOn_iff_continuous_domRestrict]
  apply continuous_parametric_integral_of_continuous (s := K) _ hK
  exact hg.comp_continuous
    ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
    (fun y => ⟨y.1.property, mem_univ _⟩)

theorem compact_supported_integral_continuousOn {g : ℝ × Plane → ℝ} {a b : ℝ}
    (hg : ContinuousOn g (Icc a b ×ˢ univ)) {K : Set Plane} (hK : IsCompact K)
    (hs : ∀ r, Function.support (fun x => g (r, x)) ⊆ K) :
    ContinuousOn (fun r => ∫ x, g (r, x)) (Icc a b) := by
  have hi (r : ℝ) : (∫ x in K, g (r, x)) = ∫ x, g (r, x) :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
      by_contra hn
      exact hx (hs r hn))
  simpa only [hi] using compact_integral_continuousOn hg hK

theorem compact_integral_hasDerivAt {g d : ℝ × Plane → ℝ} {a b t : ℝ}
    (hg : ContinuousOn g (Icc a b ×ˢ univ))
    (hd : ContinuousOn d (Icc a b ×ˢ univ))
    (he : ∀ s ∈ Ioo a b, ∀ x, HasDerivAt (fun r => g (r, x)) (d (s, x)) s)
    {K : Set Plane} (hK : IsCompact K) (ht : t ∈ Ioo a b) :
    HasDerivAt (fun r => ∫ x in K, g (r, x)) (∫ x in K, d (t, x)) t := by
  obtain ⟨B, hB⟩ := (isCompact_Icc.prod hK).bddAbove_image
    (hd.norm.mono (fun _ hp => ⟨hp.1, mem_univ _⟩))
  have hb : ∀ᵐ x ∂(volume.restrict K), ∀ s ∈ Ioo a b, ‖d (s, x)‖ ≤ B := by
    filter_upwards [ae_restrict_mem hK.measurableSet] with x hx
    intro s hs
    exact hB (mem_image_of_mem _ ⟨Ioo_subset_Icc_self hs, hx⟩)
  have hm : ∀ᶠ s in 𝓝 t, AEStronglyMeasurable (fun x => g (s, x)) (volume.restrict K) := by
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
    exact (plane_slice_continuous hg (Ioo_subset_Icc_self hs)).aestronglyMeasurable
  have hi : IntegrableOn (fun x => g (t, x)) K :=
    (plane_slice_continuous hg (Ioo_subset_Icc_self ht)).continuousOn.integrableOn_compact hK
  have hdm : AEStronglyMeasurable (fun x => d (t, x)) (volume.restrict K) :=
    (plane_slice_continuous hd (Ioo_subset_Icc_self ht)).aestronglyMeasurable
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le (Ioo_mem_nhds ht.1 ht.2)
    hm hi hdm hb (integrableOn_const hK.measure_ne_top)
    (Eventually.of_forall (fun x s hs => he s hs x))).2

theorem compact_supported_integral_hasDerivAt {g d : ℝ × Plane → ℝ} {a b t : ℝ}
    (hg : ContinuousOn g (Icc a b ×ˢ univ))
    (hd : ContinuousOn d (Icc a b ×ˢ univ))
    (he : ∀ s ∈ Ioo a b, ∀ x, HasDerivAt (fun r => g (r, x)) (d (s, x)) s)
    {K : Set Plane} (hK : IsCompact K)
    (hs : ∀ r, Function.support (fun x => g (r, x)) ⊆ K)
    (hds : Function.support (fun x => d (t, x)) ⊆ K) (ht : t ∈ Ioo a b) :
    HasDerivAt (fun r => ∫ x, g (r, x)) (∫ x, d (t, x)) t := by
  have hh := compact_integral_hasDerivAt hg hd he hK ht
  have hi (r : ℝ) : (∫ x in K, g (r, x)) = ∫ x, g (r, x) :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
      by_contra hn
      exact hx (hs r hn))
  rw [show (fun r => ∫ x in K, g (r, x)) = (fun r => ∫ x, g (r, x)) from funext hi] at hh
  have hdi : (∫ x in K, d (t, x)) = ∫ x, d (t, x) :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
      by_contra hn
      exact hx (hds hn))
  exact hdi ▸ hh

end ForcedComputation.VelocityDetector

end

end OAI
