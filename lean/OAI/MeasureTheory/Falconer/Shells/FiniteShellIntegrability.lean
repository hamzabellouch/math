import OAI.MeasureTheory.Falconer.Shells.FiniteSpatialShell

namespace OAI

/-! # Square integrability of the finite stationary sum

The radial coefficients need only be bounded almost everywhere on the
source shell. No global bound at zero or negative frequency is required.
-/

namespace Falconer
open Set MeasureTheory

theorem finite_weighted_sum_sq_integrable {ι : Type*} (S : Finset ι)
    (μ : Measure ℝ) [IsFiniteMeasure μ] (c F : ι → ℝ → ℂ)
    (hc : ∀ i ∈ S, Measurable (c i)) (hF : ∀ i ∈ S, Measurable (F i))
    (A B : ι → ℝ) (hA : ∀ i ∈ S, 0 ≤ A i) (hB : ∀ i ∈ S, 0 ≤ B i)
    (hbF : ∀ i ∈ S, ∀ r, ‖F i r‖ ≤ B i)
    (hbC : ∀ᵐ r ∂μ, ∀ i ∈ S, ‖c i r‖ ≤ A i) :
    Integrable (fun r => ‖∑ i ∈ S, c i r*F i r‖^2) μ := by
  have hm : Measurable (fun r => ∑ i ∈ S, c i r*F i r) :=
    Finset.measurable_sum S (fun i hi => (hc i hi).mul (hF i hi))
  let K := ∑ i ∈ S, A i*B i
  have hK : 0 ≤ K := Finset.sum_nonneg (fun i hi => mul_nonneg (hA i hi) (hB i hi))
  apply Integrable.of_bound (hm.norm.pow_const 2).aestronglyMeasurable (K^2)
  filter_upwards [hbC] with r hr
  rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
  apply (sq_le_sq₀ (norm_nonneg _) hK).mpr
  apply (norm_sum_le S (fun i => c i r*F i r)).trans
  apply Finset.sum_le_sum
  intro i hi
  rw [norm_mul]
  exact mul_le_mul (hr i hi) (hbF i hi r) (norm_nonneg _) (hA i hi)

theorem finite_spatial_shell_sq_integrable {d : ℕ} {ι : Type*} (S : Finset ι)
    (v : ℝ) (Ψ : ℝ → ℝ)
    [IsFiniteMeasure (PlanarFalconer.sourceAngularShellMeasure v Ψ)]
    (δ L : ℝ) (hδ : 0 < δ) (hL : 0 < L) (j : ι → ℕ)
    (U V : ι → Space d × (ℝ × Sphere d) → ℂ)
    (hU : ∀ i ∈ S, Measurable (U i)) (hV : ∀ i ∈ S, Measurable (V i))
    (B C : ι → ℝ) (hB : ∀ i ∈ S, 0 ≤ B i) (hC : ∀ i ∈ S, 0 ≤ C i)
    (hbU : ∀ i ∈ S, ∀ z, ‖U i z‖ ≤ B i)
    (hbV : ∀ i ∈ S, ∀ z, ‖V i z‖ ≤ C i)
    (c : ι → ℝ → ℂ) (A : ι → ℝ)
    (hc : ∀ i ∈ S, Measurable (c i)) (hA : ∀ i ∈ S, 0 ≤ A i)
    (hbound : ∀ᵐ r ∂PlanarFalconer.sourceAngularShellMeasure v Ψ,
      ∀ i ∈ S, ‖c i r‖ ≤ A i) :
    Integrable (fun r => ‖∑ i ∈ S, c i r *
      spatialSharedAmplitude (spatialFourierCoeff δ L hδ hL (j i)) (U i) (V i) r‖^2)
      (PlanarFalconer.sourceAngularShellMeasure v Ψ) := by
  refine finite_weighted_sum_sq_integrable S _ c
    (fun i => spatialSharedAmplitude (spatialFourierCoeff δ L hδ hL (j i)) (U i) (V i)) hc ?_
    A (fun i => ((∫ ξ : Space d, ‖spatialFourierCoeff δ L hδ hL (j i) ξ‖)*
      (B i*C i))*(sphereMeasure d).real univ) hA ?_ ?_ hbound
  · intro i hi
    exact spatialSharedAmplitude_measurable _
      (spatialFourierCoeff (d := d) δ L hδ hL (j i)).continuous.measurable
      (U i) (V i) (hU i hi) (hV i hi)
  · intro i hi
    exact mul_nonneg (mul_nonneg (integral_nonneg (fun _ => norm_nonneg _))
      (mul_nonneg (hB i hi) (hC i hi))) measureReal_nonneg
  · intro i hi r
    exact spatialSharedAmplitude_norm_le _ (spatialFourierCoeff_integrable δ L hδ hL (j i))
      (U i) (V i) (hB i hi) (hbU i hi) (hbV i hi) r

end Falconer

end OAI
