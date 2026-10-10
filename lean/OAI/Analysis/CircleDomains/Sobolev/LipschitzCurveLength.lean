import OAI.Analysis.CircleDomains.Sobolev.DifferentiableCurveLength
import Mathlib.Analysis.Calculus.Rademacher

namespace OAI

/-! Exact arclength for Lipschitz plane curves on bounded Borel parameter sets. -/
open Set Function Filter MeasureTheory Metric Bornology
open scoped ENNReal NNReal Topology
noncomputable section
namespace CircleDomainRigidity

lemma lipschitz_curve_hausdorff_eq {γ : ℝ → ℂ} {K : ℝ≥0} (hγ : LipschitzWith K γ)
    {S : Set ℝ} (hS : MeasurableSet S) (hb : IsBounded S) (hi : InjOn γ S) :
    (μH[1] : Measure ℂ) (γ '' S) = ∫⁻ t in S, ENNReal.ofReal ‖deriv γ t‖ := by
  let D := {t | DifferentiableAt ℝ γ t}
  have hD : MeasurableSet D := measurableSet_of_differentiableAt ℝ γ
  have hae : ∀ᵐ t ∂volume, t ∈ D := hγ.ae_differentiableAt
  have hn : volume (S \ D) = 0 := by
    apply measure_mono_null (show S \ D ⊆ Dᶜ from fun _ hx => hx.2)
    exact measure_eq_zero_iff_ae_notMem.mpr (by simpa only [mem_compl_iff, not_not] using hae)
  have hex : (μH[1] : Measure ℂ) (γ '' (S \ D)) = 0 := by
    apply le_antisymm _ (by positivity)
    calc
      _ ≤ (K : ℝ≥0∞)^ (1:ℝ) * (μH[1] : Measure ℝ) (S \ D) :=
        hγ.hausdorffMeasure_image_le (by norm_num) _
      _ = 0 := by rw [hausdorffMeasure_real, hn, mul_zero]
  have he : (μH[1] : Measure ℂ) (γ '' S) = (μH[1] : Measure ℂ) (γ '' (S ∩ D)) := by
    apply le_antisymm _ (measure_mono (image_mono inter_subset_left))
    have hsub : γ '' S ⊆ γ '' (S ∩ D) ∪ γ '' (S \ D) := by
      rintro _ ⟨t, ht, rfl⟩
      by_cases htD : t ∈ D
      · exact Or.inl ⟨t, ⟨ht, htD⟩, rfl⟩
      · exact Or.inr ⟨t, ⟨ht, htD⟩, rfl⟩
    calc
      _ ≤ (μH[1] : Measure ℂ) (γ '' (S ∩ D) ∪ γ '' (S \ D)) := measure_mono hsub
      _ ≤ (μH[1] : Measure ℂ) (γ '' (S ∩ D))+(μH[1] : Measure ℂ) (γ '' (S \ D)) := measure_union_le _ _
      _ = _ := by rw [hex, add_zero]
  have hres : volume.restrict (S ∩ D) = volume.restrict S := by
    apply Measure.restrict_congr_set
    filter_upwards [hae] with t ht
    simp only [mem_inter_iff, ht, and_true]
  rw [he]
  have hd : ∀ t ∈ S ∩ D, HasFDerivWithinAt γ (fderiv ℝ γ t) (S ∩ D) t :=
    fun t ht => ht.2.hasFDerivAt.hasFDerivWithinAt
  have hformula := differentiable_curve_hausdorff_eq (hS.inter hD) (hb.subset inter_subset_left)
    hd (hi.mono inter_subset_left)
  rw [hres] at hformula
  simpa only [norm_deriv_eq_norm_fderiv] using hformula

end CircleDomainRigidity

end

end OAI
