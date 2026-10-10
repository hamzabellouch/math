import Mathlib
import OAI.Analysis.CoulombIonization.Ionization.MasterJointPosterior
import OAI.Analysis.CoulombIonization.Variational.MasterKernelFubini
import OAI.Analysis.CoulombIonization.FieldAnalysis.PuncturedGreenBarrier

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped BigOperators Topology

namespace CoulombBarrier
open CoulombAtom CoulombObservation
attribute [local instance] physicalObservationLaw_probability
attribute [local irreducible] masterWidth masterKernel originalRawKernel physicalObservationLaw
  originalDatum jointMasterPosterior

lemma bounded_integrable_square {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P] {f : Ω → ℝ} (hf : Measurable f) {C : ℝ}
    (hC : ∀ x, ‖f x‖ ≤ C) : Integrable (fun x => (f x)^2) P := by
  apply Integrable.of_bound (hf.pow_const 2).aestronglyMeasurable (C^2)
  exact ae_of_all _ fun x => by
    rw [norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (hC x) 2

lemma square_integral_le_of_bound {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {f : Ω → ℝ} (hf : Measurable f) {C : ℝ}
    (hC : ∀ x, ‖f x‖ ≤ C) : (∫ x, f x ∂P)^2 ≤ ∫ x, (f x)^2 ∂P := by
  have hi : Integrable f P := Integrable.of_bound hf.aestronglyMeasurable C (ae_of_all _ hC)
  exact (Even.convexOn_pow (by decide : Even (2:ℕ))).map_integral_le (continuous_pow 2).continuousOn isClosed_univ
    (ae_of_all _ fun _ => mem_univ _) hi (bounded_integrable_square hf hC)

lemma bounded_original_posterior_mean {N K : ℕ} (μ : Measure (Configuration N))
    [IsProbabilityMeasure μ] (ell : Fin K → ℝ) (j : ℕ)
    {f : Configuration N → ℝ} (hf : Measurable f) {C : ℝ}
    (hC : ∀ x, ‖f x‖ ≤ C) :
    (∫ z, (∫ x, f x ∂originalRawKernel μ ell j (originalDatum ell j z))
      ∂physicalObservationLaw μ K) = ∫ x, f x ∂μ := by
  have hi : Integrable f μ := Integrable.of_bound hf.aestronglyMeasurable C (ae_of_all _ hC)
  have hm : StronglyMeasurable (fun d => ∫ x, f x ∂originalRawKernel μ ell j d) :=
    hf.stronglyMeasurable.integral_kernel
  rw [←integral_map (originalDatum_measurable ell j).aemeasurable hm.aestronglyMeasurable]
  have hh : Integrable f (originalRawKernel μ ell j ∘ₘ
      (physicalObservationLaw μ K).map (originalDatum ell j)) := by
    rwa [originalRawKernel_comp]
  conv_rhs => rw [←originalRawKernel_comp μ ell j]
  rw [Measure.comp_eq_comp_const_apply] at hh ⊢
  simpa only [Kernel.const_apply] using (Kernel.integral_comp hh).symm

theorem original_posterior_square_le {N K : ℕ} (μ : Measure (Configuration N))
    [IsProbabilityMeasure μ] (ell : Fin K → ℝ) (j : ℕ)
    {f : Configuration N → ℝ} (hf : Measurable f) {C : ℝ}
    (hC : ∀ x, ‖f x‖ ≤ C) :
    (∫ z, (∫ x, f x ∂originalRawKernel μ ell j (originalDatum ell j z))^2
      ∂physicalObservationLaw μ K) ≤ ∫ x, (f x)^2 ∂μ := by
  have hm : Measurable (fun z => ∫ x, f x ∂originalRawKernel μ ell j (originalDatum ell j z)) :=
    hf.stronglyMeasurable.integral_kernel.measurable.comp (originalDatum_measurable ell j)
  have hb (z) : ‖∫ x, f x ∂originalRawKernel μ ell j (originalDatum ell j z)‖ ≤ C := by
    calc
      _ ≤ ∫ _ : Configuration N, C ∂originalRawKernel μ ell j (originalDatum ell j z) :=
        norm_integral_le_of_norm_le (integrable_const C) (ae_of_all _ hC)
      _ = C := by simp
  have hsq (x) : ‖(f x)^2‖ ≤ C^2 := by rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg _) (hC x) _
  have hm2 : Measurable (fun z => ∫ x, (f x)^2 ∂originalRawKernel μ ell j (originalDatum ell j z)) :=
    (hf.pow_const 2).stronglyMeasurable.integral_kernel.measurable.comp (originalDatum_measurable ell j)
  have hb2 (z) : ‖∫ x, (f x)^2 ∂originalRawKernel μ ell j (originalDatum ell j z)‖ ≤ C^2 := by
    calc
      _ ≤ ∫ _ : Configuration N, C^2 ∂originalRawKernel μ ell j (originalDatum ell j z) :=
        norm_integral_le_of_norm_le (integrable_const _) (ae_of_all _ hsq)
      _ = C^2 := by simp
  calc
    _ ≤ ∫ z, (∫ x, (f x)^2 ∂originalRawKernel μ ell j (originalDatum ell j z))
        ∂physicalObservationLaw μ K :=
      integral_mono (bounded_integrable_square hm hb)
        (Integrable.of_bound hm2.aestronglyMeasurable _ (ae_of_all _ hb2))
        (fun _ => square_integral_le_of_bound hf hC)
    _ = _ := bounded_original_posterior_mean μ ell j (hf.pow_const 2) hsq

theorem original_master_second_moment_from_count {N K : ℕ} (μ : Measure (Configuration N))
    [IsProbabilityMeasure μ] (ell : Fin K → ℝ) (j : ℕ) {c₁ r₀ s : ℝ}
    (hc : 0 < c₁) (hr : 0 < r₀) (hs : 0 < s) {g : Space → ℝ}
    (hg : Continuous g) (y : Space) {R A : ℝ} (hA : 0 ≤ A)
    (hbound : ∀ x, masterKernel c₁ r₀ s g x y ≤ A)
    (hsupport : Function.support (fun x => masterKernel c₁ r₀ s g x y) ⊆ ball y R) :
    (∫ z, (jointMasterPosterior μ ell j c₁ r₀ s g (originalDatum ell j z) y)^2
      ∂physicalObservationLaw μ K) ≤ A^2*(∫ x, (rawBallCount y R x)^2 ∂μ) := by
  let f : Configuration N → ℝ := fun x => ∑ i, masterKernel c₁ r₀ s g (x i) y
  have hm : Measurable f := Finset.measurable_sum _ (fun i _ =>
    ((masterKernel_joint_continuous hc hr hs hg).measurable.comp
      (f := fun x : Configuration N => (x i,y))
      ((measurable_pi_apply i).prodMk measurable_const)))
  have hn (x) : 0 ≤ f x := Finset.sum_nonneg fun i _ => masterKernel_nonneg _ _ _ _ _ _
  have hb (x) : f x ≤ A*rawBallCount y R x := by
    rw [rawBallCount,Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    split_ifs with h
    · simpa only [mul_one] using hbound (x i)
    · have hz : masterKernel c₁ r₀ s g (x i) y = 0 := by
        by_contra hh
        have hmem := hsupport hh
        simp only [mem_ball,dist_eq_norm] at hmem
        exact h hmem
      simp only [hz,mul_zero,le_refl]
  have hfb (x) : ‖f x‖ ≤ A*N := by
    rw [Real.norm_of_nonneg (hn x)]
    exact (hb x).trans (mul_le_mul_of_nonneg_left (rawBallCount_le y R x) hA)
  have hci : Integrable (fun x => (rawBallCount y R x)^2) μ :=
    bounded_integrable_square (rawBallCount_measurable y R) (fun x => by
      rw [Real.norm_of_nonneg (rawBallCount_nonneg y R x)]; exact rawBallCount_le y R x)
  calc
    _ ≤ ∫ x, (f x)^2 ∂μ := by
      unfold jointMasterPosterior
      exact original_posterior_square_le μ ell j hm hfb
    _ ≤ ∫ x, A^2*(rawBallCount y R x)^2 ∂μ := by
      apply integral_mono (bounded_integrable_square hm hfb) (hci.const_mul _)
      intro x
      simpa only [mul_pow] using pow_le_pow_left₀ (hn x) (hb x) 2
    _ = _ := integral_const_mul _ _

end CoulombBarrier

end

end OAI
