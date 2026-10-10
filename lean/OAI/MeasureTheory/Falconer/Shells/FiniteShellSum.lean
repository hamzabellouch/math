import OAI.MeasureTheory.Falconer.Shells.SpatialSharedShell

namespace OAI

/-! # Finite summation of the stationary shell terms

The finite inverse order and separated factor count contribute only their
explicit finite cardinality. No supremum or interchange with a variable
measure is hidden in this step.
-/

namespace Falconer
open Set MeasureTheory

private theorem norm_sum_sq_le_card {ι : Type*} (S : Finset ι) (f : ι → ℂ) :
    ‖∑ i ∈ S, f i‖^2 ≤ (S.card:ℝ)*∑ i ∈ S, ‖f i‖^2 := by
  apply (pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le S f) 2).trans
  simpa only [one_mul,one_pow,Finset.sum_const,nsmul_eq_mul,mul_one]
    using Finset.sum_mul_sq_le_sq_mul_sq S (fun _ => (1:ℝ)) (fun i => ‖f i‖)

theorem finite_shell_sum_sq_integrable {α ι : Type*} [MeasurableSpace α]
    (μ : Measure α) (S : Finset ι) (c F : ι → α → ℂ) (C : ι → ℝ)
    (hc : ∀ i ∈ S, Measurable (c i)) (hF : ∀ i ∈ S, Measurable (F i))
    (hFi : ∀ i ∈ S, Integrable (fun r => ‖F i r‖^2) μ)
    (hC : ∀ i ∈ S, 0 ≤ C i)
    (hbound : ∀ᵐ r ∂μ, ∀ i ∈ S, ‖c i r‖ ≤ C i) :
    Integrable (fun r => ‖∑ i ∈ S, c i r*F i r‖^2) μ := by
  have hr : Integrable (fun r => (S.card:ℝ)*∑ i ∈ S, (C i)^2*‖F i r‖^2) μ :=
    (integrable_finsetSum S (fun i hi => (hFi i hi).const_mul ((C i)^2))).const_mul _
  have hm : Measurable (fun r => ‖∑ i ∈ S, c i r*F i r‖^2) :=
    (Finset.measurable_sum S (fun i hi => (hc i hi).mul (hF i hi))).norm.pow_const 2
  apply hr.mono' hm.aestronglyMeasurable
  filter_upwards [hbound] with r h
  rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
  apply (norm_sum_sq_le_card S (fun i => c i r*F i r)).trans
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  apply Finset.sum_le_sum
  intro i hi
  rw [norm_mul,mul_pow]
  exact mul_le_mul_of_nonneg_right
    ((sq_le_sq₀ (norm_nonneg _) (hC i hi)).mpr (h i hi)) (sq_nonneg _)

theorem finite_shell_sum_le {ι : Type*} (S : Finset ι) (v : ℝ) (Ψ : ℝ → ℝ)
    (c F : ι → ℝ → ℂ) (C E : ι → ℝ)
    (hc : ∀ i ∈ S, Measurable (c i)) (hF : ∀ i ∈ S, Measurable (F i))
    (hFi : ∀ i ∈ S, Integrable (fun r => ‖F i r‖^2)
      (PlanarFalconer.sourceAngularShellMeasure v Ψ))
    (hC : ∀ i ∈ S, 0 ≤ C i)
    (hbound : ∀ᵐ r ∂PlanarFalconer.sourceAngularShellMeasure v Ψ,
      ∀ i ∈ S, ‖c i r‖ ≤ C i)
    {P : ℝ} (hP : 0 ≤ P)
    (hE : ∀ i ∈ S, P*(∫ r, ‖F i r‖^2 ∂PlanarFalconer.sourceAngularShellMeasure v Ψ) ≤ E i) :
    P*(∫ r, ‖∑ i ∈ S, c i r*F i r‖^2
      ∂PlanarFalconer.sourceAngularShellMeasure v Ψ) ≤
      (S.card:ℝ)*∑ i ∈ S, (C i)^2*E i := by
  let μ := PlanarFalconer.sourceAngularShellMeasure v Ψ
  have hr : Integrable (fun r => (S.card:ℝ)*∑ i ∈ S, (C i)^2*‖F i r‖^2) μ :=
    (integrable_finsetSum S (fun i hi => (hFi i hi).const_mul ((C i)^2))).const_mul _
  have hm : Measurable (fun r => ‖∑ i ∈ S, c i r*F i r‖^2) :=
    (Finset.measurable_sum S (fun i hi => (hc i hi).mul (hF i hi))).norm.pow_const 2
  have hb : ∀ᵐ r ∂μ, ‖∑ i ∈ S, c i r*F i r‖^2 ≤
      (S.card:ℝ)*∑ i ∈ S, (C i)^2*‖F i r‖^2 := by
    filter_upwards [hbound] with r hr
    apply (norm_sum_sq_le_card S (fun i => c i r*F i r)).trans
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    apply Finset.sum_le_sum
    intro i hi
    rw [norm_mul,mul_pow]
    exact mul_le_mul_of_nonneg_right
      ((sq_le_sq₀ (norm_nonneg _) (hC i hi)).mpr (hr i hi)) (sq_nonneg _)
  have hi : Integrable (fun r => ‖∑ i ∈ S, c i r*F i r‖^2) μ := by
    apply hr.mono' hm.aestronglyMeasurable
    filter_upwards [hb] with r h
    rwa [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
  calc
    _ ≤ P*(∫ r, (S.card:ℝ)*∑ i ∈ S, (C i)^2*‖F i r‖^2 ∂μ) :=
      mul_le_mul_of_nonneg_left (integral_mono_ae hi hr hb) hP
    _ = (S.card:ℝ)*∑ i ∈ S,
        (C i)^2*(P*(∫ r, ‖F i r‖^2 ∂μ)) := by
      rw [integral_const_mul,integral_finsetSum S (fun i hi => (hFi i hi).const_mul _)]
      simp only [integral_const_mul,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum (fun i hi => mul_le_mul_of_nonneg_left (hE i hi) (sq_nonneg _)))
      (Nat.cast_nonneg _)

end Falconer

end OAI
