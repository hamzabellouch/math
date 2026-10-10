import Mathlib
import OAI.Geometry.TamingCompatibility.Charts.GeometricCutoff

namespace OAI

section
section
section

section

noncomputable section
namespace TamingCompatibility.GeometricChart
open ManifoldForms ManifoldLocalization ManifoldHodge ManifoldVolume
open Set MeasureTheory
open scoped Manifold ContDiff SchwartzMap
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)

include hs hD in
lemma density_lower_on_support (p : A.centers) :
    ∃ C : ℝ, 0 < C ∧ ∀ z ∈ coordinateSupport A p, 1 ≤ C * chartDensity J α p.val z := by
  have hd : ∀ z ∈ coordinateSupport A p, 0 < chartDensity J α p.val z := fun z hz =>
    chartDensity_pos J α ht p.val ((coordinateSupport_domain A J α ht D hD p).trans (D p).domain_subset hz)
  have hc := (chartDensity_smooth J α hs ht p.val).continuousOn.mono
    ((coordinateSupport_domain A J α ht D hD p).trans (D p).domain_subset)
  obtain ⟨B,hB⟩ := (coordinateSupport_compact A p).exists_bound_of_continuousOn
    (f := fun z => (chartDensity J α p.val z)⁻¹) (hc.inv₀ (fun z hz => ne_of_gt (hd z hz)))
  refine ⟨max 1 B,lt_of_lt_of_le zero_lt_one (le_max_left _ _),?_⟩
  intro z hz
  have h := (le_abs_self ((chartDensity J α p.val z)⁻¹)).trans ((hB z hz).trans (le_max_right 1 B))
  have hmul := mul_le_mul_of_nonneg_right h (hd z hz).le
  simpa only [inv_mul_cancel₀ (ne_of_gt (hd z hz))] using hmul

include hs hD in
lemma scalar_norm_bound (p : A.centers) :
    ∃ C : ℝ, 0 < C ∧ ∀ a : TwoForm X, antiInvariantPart J a = a → ∀ z,
      (scalar A J α ht D p a 2 z)^2 + (scalar A J α ht D p a 3 z)^2 ≤
        C * (chartDensity J α p.val z * MetricForms.pairing (coordinateMetric J α ht p.val z)
          (localizedFunction A p a z) (localizedFunction A p a z)) := by
  obtain ⟨C,hC,hbound⟩ := density_lower_on_support A J α hs ht D hD p
  refine ⟨C,hC,?_⟩
  intro a hanti z
  by_cases hz : z ∈ coordinateSupport A p
  · rw [localizedPairing_scalars A J α ht D hD p hanti]
    have hb := hbound z hz
    have hn := add_nonneg (sq_nonneg (scalar A J α ht D p a 2 z)) (sq_nonneg (scalar A J α ht D p a 3 z))
    have hm := mul_le_mul_of_nonneg_right hb hn
    nlinarith
  · rw [scalar_zero_off A J α ht D p a 2 hz,scalar_zero_off A J α ht D p a 3 hz,
      localizedFunction_zero_off A p a hz]
    simp only [zero_pow (by decide : 2≠0),add_zero,(MetricForms.pairing_self_eq_zero _ _).mpr rfl,mul_zero,le_refl]

omit [CompactSpace X] in
lemma pairing_cutoff (p : A.centers) (a : TwoForm X) (x : X) :
    GeometricAdjoint.pairing J α ht (cutoffForm A p a) (cutoffForm A p a) x =
      (A.partition p x)^2 * GeometricAdjoint.pairing J α ht a a x := by
  let v : MetricForms.Form Space 2 := a x
  change MetricForms.pairing (GeometricAdjoint.pointMetric J α ht x)
    (A.partition p x • v) (A.partition p x • v) = (A.partition p x)^2 * MetricForms.pairing _ v v
  rw [MetricForms.pairing_smul_left,MetricForms.pairing_smul_right]
  ring

variable [MeasurableSpace X] [BorelSpace X]
include hs hD in
lemma integral_scalar_bound (p : A.centers) :
    ∃ C : ℝ, 0 < C ∧ ∀ a : TwoForm X, Smooth a → antiInvariantPart J a = a →
      (∫ z, (scalar A J α ht D p a 2 z)^2 + (scalar A J α ht D p a 3 z)^2) ≤
        C * ∫ x, GeometricAdjoint.pairing J α ht (cutoffForm A p a)
          (cutoffForm A p a) x ∂geometricVolume A J α := by
  obtain ⟨C,hC,hbound⟩ := scalar_norm_bound A J α hs ht D hD p
  refine ⟨C,hC,?_⟩
  intro a ha hanti
  have h := integral_mono_of_nonneg (Filter.Eventually.of_forall (fun z => add_nonneg
    (sq_nonneg (scalar A J α ht D p a 2 z)) (sq_nonneg (scalar A J α ht D p a 3 z))))
    ((localizedPairing_integrable A J α ht hs p (Or.inr rfl) ha).const_mul C)
    (Filter.Eventually.of_forall (hbound a hanti))
  rw [integral_const_mul,integral_localizedPairing A J α ht hs p (Or.inr rfl) ha] at h
  simpa only [pairing_cutoff A J α ht p a] using h
end TamingCompatibility.GeometricChart

end
end

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldVolume ManifoldLocalization GeometricAdjoint
open MeasureTheory Set
open scoped Manifold ContDiff
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)

include hs in
lemma cutoff_energy_bound {f : X → ℝ} (hf : ContMDiff Model 𝓘(ℝ,ℝ) ∞ f) :
    ∃ C : ℝ, 0 < C ∧ ∀ a : TwoForm X, Smooth a → antiInvariantPart J a = a →
      (∫ x, pairing J α ht (fun y => f y • a y) (fun y => f y • a y) x ∂geometricVolume A J α) +
      (∫ x, pairing J α ht (codifferential J α ht (fun y => f y • a y))
        (codifferential J α ht (fun y => f y • a y)) x ∂geometricVolume A J α) ≤
      C * ((∫ x, pairing J α ht a a x ∂geometricVolume A J α) +
        (∫ x, pairing J α ht (codifferential J α ht a) (codifferential J α ht a) x ∂geometricVolume A J α)) := by
  let := geometricVolume_finite A J α hs ht
  have hdf := scalarDifferential_smooth hf
  have hc := (pairing_one_smooth J α hs ht hdf hdf).continuous
  obtain ⟨B,hB⟩ := isCompact_univ.exists_bound_of_continuousOn
    (f := fun x => (f x)^2 + pairing J α ht (scalarDifferential f) (scalarDifferential f) x)
    ((hf.continuous.pow 2).add hc).continuousOn
  obtain ⟨D,hD⟩ := isCompact_univ.exists_bound_of_continuousOn
    (f := fun x => 2*(f x)^2) ((hf.continuous.pow 2).const_mul 2).continuousOn
  let C := max 1 (max B D)
  have hC : 0 < C := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  refine ⟨C,hC,?_⟩
  intro a ha hanti
  have hb₁ (x : X) : (f x)^2 + pairing J α ht (scalarDifferential f) (scalarDifferential f) x ≤ C :=
    (le_abs_self _).trans ((hB x (mem_univ x)).trans ((le_max_left B D).trans (le_max_right 1 (max B D))))
  have hb₂ (x : X) : 2*(f x)^2 ≤ C :=
    (le_abs_self _).trans ((hD x (mem_univ x)).trans ((le_max_right B D).trans (le_max_right 1 (max B D))))
  have hal := (pairing_two_smooth J α hs ht ha ha).continuous.integrable_of_hasCompactSupport (μ := geometricVolume A J α)
    (HasCompactSupport.of_compactSpace _)
  have had := codifferential_smooth J α hs ht ha
  have hadl := (pairing_one_smooth J α hs ht had had).continuous.integrable_of_hasCompactSupport (μ := geometricVolume A J α)
    (HasCompactSupport.of_compactSpace _)
  have hfa := Smooth.fun_smul hf ha
  have hfal := (pairing_two_smooth J α hs ht hfa hfa).continuous.integrable_of_hasCompactSupport (μ := geometricVolume A J α)
    (HasCompactSupport.of_compactSpace _)
  have hfad := codifferential_smooth J α hs ht (b := (fun y => f y • a y : TwoForm X)) hfa
  have hfadl := (pairing_one_smooth J α hs ht hfad hfad).continuous.integrable_of_hasCompactSupport (μ := geometricVolume A J α)
    (HasCompactSupport.of_compactSpace _)
  rw [← integral_add hfal hfadl,← integral_add hal hadl,← integral_const_mul]
  apply integral_mono (hfal.add hfadl) ((hal.add hadl).const_mul C)
  intro x
  have hx := cutoff_delta_pointwise J α ht ha hanti hf x
  have he : pairing J α ht (fun y => f y • a y) (fun y => f y • a y) x =
      (f x)^2 * pairing J α ht a a x := by
    let v : MetricForms.Form Space 2 := a x
    change MetricForms.pairing (pointMetric J α ht x) (f x • v) (f x • v) = _
    rw [MetricForms.pairing_smul_left,MetricForms.pairing_smul_right]
    change f x * (f x * MetricForms.pairing (pointMetric J α ht x) v v) =
      (f x)^2 * MetricForms.pairing (pointMetric J α ht x) v v
    ring
  simp only [Pi.add_apply]
  rw [he]
  have h₁ := mul_le_mul_of_nonneg_right (hb₁ x) (MetricForms.pairing_self_nonneg (pointMetric J α ht x) (a x))
  have h₂ := mul_le_mul_of_nonneg_right (hb₂ x) (MetricForms.pairing_self_nonneg (pointMetric J α ht x) (codifferential J α ht a x))
  change ((f x)^2 + pairing J α ht (scalarDifferential f) (scalarDifferential f) x) *
    pairing J α ht a a x ≤ C * pairing J α ht a a x at h₁
  change 2*(f x)^2 * pairing J α ht (codifferential J α ht a) (codifferential J α ht a) x ≤
    C * pairing J α ht (codifferential J α ht a) (codifferential J α ht a) x at h₂
  nlinarith
end TamingCompatibility.GeometricHilbert

end
end

end
end
end

end OAI
