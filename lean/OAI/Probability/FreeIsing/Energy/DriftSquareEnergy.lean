import OAI.Probability.FreeIsing.Energy.DiscrepancyEnergy

namespace OAI

noncomputable section

open MeasureTheory Filter Set
open scoped Topology

namespace Problem367.DiscrepancyEnergy

theorem intervalIntegrable_primitive_mul
    {b : ℝ → ℝ} {a t : ℝ} (hb : IntervalIntegrable b volume a t) :
    IntervalIntegrable (fun s => (∫ u in a..s, b u) * b s) volume a t := by
  exact hb.continuousOn_mul
    (hb.absolutelyContinuousOnInterval_intervalIntegral (c := a) (by simp)).continuousOn

theorem primitive_sq_eq_two_integral
    {b : ℝ → ℝ} {a t : ℝ} (hb : IntervalIntegrable b volume a t) :
    (∫ s in a..t, b s) ^ 2 =
      2 * ∫ s in a..t, (∫ u in a..s, b u) * b s := by
  let A : ℝ → ℝ := fun s => ∫ u in a..s, b u
  have hA : AbsolutelyContinuousOnInterval A a t :=
    hb.absolutelyContinuousOnInterval_intervalIntegral (c := a) (by simp)
  have h := hA.integral_deriv_mul_eq_sub hA
  have heq : (∫ s in a..t, deriv A s * A s + A s * deriv A s) =
      ∫ s in a..t, 2 * (A s * b s) := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hb.ae_hasDerivAt_integral] with s hs hst
    have hd : deriv A s = b s :=
      (hs (uIoc_subset_uIcc hst) a (by simp)).deriv
    rw [hd]
    ring
  rw [heq, intervalIntegral.integral_const_mul] at h
  simpa only [A, intervalIntegral.integral_same, mul_zero, sub_zero, pow_two] using h.symm

theorem ae_timePrimitive_sq
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [SFinite μ]
    {b : ℝ → Ω → ℝ} {T t : ℝ} (ht : t ∈ Icc 0 T)
    (hb : Integrable (fun p : ℝ × Ω => b p.1 p.2)
      ((volume.restrict (Ioc 0 T)).prod μ)) :
    ∀ᵐ ω ∂μ, (∫ s in (0 : ℝ)..t, b s ω) ^ 2 =
      2 * ∫ s in (0 : ℝ)..t, (∫ u in (0 : ℝ)..s, b u ω) * b s ω := by
  have hbt : Integrable (fun p : ℝ × Ω => b p.1 p.2)
      ((volume.restrict (Ioc 0 t)).prod μ) :=
    hb.mono_measure (Measure.prod_mono
      (Measure.restrict_mono_set _ (Ioc_subset_Ioc_right ht.2)) le_rfl)
  filter_upwards [hbt.prod_left_ae] with ω hω
  exact primitive_sq_eq_two_integral
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le ht.1).mpr hω)

theorem integral_timePrimitive_sq
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [SFinite μ]
    {b : ℝ → Ω → ℝ} {T t : ℝ} (ht : t ∈ Icc 0 T)
    (hb : Integrable (fun p : ℝ × Ω => b p.1 p.2)
      ((volume.restrict (Ioc 0 T)).prod μ))
    (hAb : Integrable (fun p : ℝ × Ω =>
      (∫ u in (0 : ℝ)..p.1, b u p.2) * b p.1 p.2)
      ((volume.restrict (Ioc 0 T)).prod μ)) :
    (∫ ω, (∫ s in (0 : ℝ)..t, b s ω) ^ 2 ∂μ) =
      2 * ∫ s in (0 : ℝ)..t, ∫ ω, (∫ u in (0 : ℝ)..s, b u ω) * b s ω ∂μ := by
  rw [integral_congr_ae (ae_timePrimitive_sq ht hb), integral_const_mul]
  congr 1
  exact integral_timePrimitive ht hAb

theorem integrable_timePrimitive_sq
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [SFinite μ]
    {b : ℝ → Ω → ℝ} {T t : ℝ} (ht : t ∈ Icc 0 T)
    (hb : Integrable (fun p : ℝ × Ω => b p.1 p.2)
      ((volume.restrict (Ioc 0 T)).prod μ))
    (hAb : Integrable (fun p : ℝ × Ω =>
      (∫ u in (0 : ℝ)..p.1, b u p.2) * b p.1 p.2)
      ((volume.restrict (Ioc 0 T)).prod μ)) :
    Integrable (fun ω => (∫ s in (0 : ℝ)..t, b s ω) ^ 2) μ := by
  have hAbt : Integrable (fun p : ℝ × Ω =>
      (∫ u in (0 : ℝ)..p.1, b u p.2) * b p.1 p.2)
      ((volume.restrict (Ioc 0 t)).prod μ) :=
    hAb.mono_measure (Measure.prod_mono
      (Measure.restrict_mono_set _ (Ioc_subset_Ioc_right ht.2)) le_rfl)
  have hI : Integrable (fun ω => ∫ s in (0 : ℝ)..t,
      (∫ u in (0 : ℝ)..s, b u ω) * b s ω) μ := by
    simpa only [intervalIntegral.integral_of_le ht.1] using hAbt.integral_prod_right
  exact (hI.const_mul 2).congr ((ae_timePrimitive_sq ht hb).mono (fun ω hω => hω.symm))

end Problem367.DiscrepancyEnergy

end

end OAI
