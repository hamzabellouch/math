import OAI.Probability.FreeIsing.Energy.CompensatedSquareEnergy
import OAI.Probability.FreeIsing.Estimates.MessageFunction
import OAI.Probability.FreeIsing.Estimates.ThresholdArithmetic

namespace OAI

noncomputable section

open MeasureTheory Set Filter

namespace Problem367

theorem abs_sub_le_of_shared_innovation
    {m m' : ℝ → ℝ} {x x' w t : ℝ} (ht : 0 ≤ t)
    (hx : x = w + ∫ s in (0 : ℝ)..t, m s)
    (hx' : x' = w + ∫ s in (0 : ℝ)..t, m' s)
    (hm : ∀ᵐ s : ℝ, s ∈ Ioc 0 t → |m s| ≤ 1)
    (hm' : ∀ᵐ s : ℝ, s ∈ Ioc 0 t → |m' s| ≤ 1) :
    |x - x'| ≤ 2 * t := by
  have bound {f : ℝ → ℝ}
      (hf : ∀ᵐ s : ℝ, s ∈ Ioc 0 t → |f s| ≤ 1) :
      |∫ s in (0 : ℝ)..t, f s| ≤ t := by
    have hb := intervalIntegral.norm_integral_le_of_norm_le_const_ae
      (a := 0) (b := t) (C := 1) (f := f)
      (by simpa only [uIoc_of_le ht, Real.norm_eq_abs] using hf)
    simpa only [Real.norm_eq_abs, sub_zero, abs_of_nonneg ht, one_mul] using hb
  rw [hx, hx']
  have heq : (w + ∫ s in (0 : ℝ)..t, m s) -
      (w + ∫ s in (0 : ℝ)..t, m' s) =
      (∫ s in (0 : ℝ)..t, m s) - ∫ s in (0 : ℝ)..t, m' s := by ring
  rw [heq]
  exact (abs_sub _ _).trans ((add_le_add (bound hm) (bound hm')).trans_eq (by ring))

theorem abs_cavity_field_sub_observation_le
    {d : ℕ} {beta h x : ℝ} (hbeta : 0 ≤ beta) (z : Fin d → ℝ)
    (hh : h = x + ∑ i, cavityMessage (Real.tanh beta) (z i)) :
    |h - x| ≤ (d : ℝ) * beta := by
  rw [hh, add_sub_cancel_left]
  calc
    |∑ i, cavityMessage (Real.tanh beta) (z i)| ≤
        ∑ i, |cavityMessage (Real.tanh beta) (z i)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _ : Fin d, beta := by
      apply Finset.sum_le_sum
      intro i _
      simpa only [Real.artanh_tanh] using
        cavityMessage_abs_le_artanh (tanh_nonneg_of_beta_nonneg hbeta)
          (Real.tanh_lt_one beta) (z i)
    _ = (d : ℝ) * beta := by simp

theorem abs_cavity_field_sub_le_of_shared_innovation
    {d : ℕ} {beta h h' x x' w t : ℝ} {m m' : ℝ → ℝ}
    (hbeta : 0 ≤ beta) (ht : 0 ≤ t) (z z' : Fin d → ℝ)
    (hx : x = w + ∫ s in (0 : ℝ)..t, m s)
    (hx' : x' = w + ∫ s in (0 : ℝ)..t, m' s)
    (hm : ∀ᵐ s : ℝ, s ∈ Ioc 0 t → |m s| ≤ 1)
    (hm' : ∀ᵐ s : ℝ, s ∈ Ioc 0 t → |m' s| ≤ 1)
    (hh : h = x + ∑ i, cavityMessage (Real.tanh beta) (z i))
    (hh' : h' = x' + ∑ i, cavityMessage (Real.tanh beta) (z' i)) :
    |h - h'| ≤ 2 * t + 2 * (d : ℝ) * beta := by
  have hobs := abs_sub_le_of_shared_innovation ht hx hx' hm hm'
  have hleft := abs_cavity_field_sub_observation_le hbeta z hh
  have hright := abs_cavity_field_sub_observation_le hbeta z' hh'
  have heq : h - h' = (h - x) + (x - x') + (x' - h') := by ring
  rw [heq]
  calc
    |(h - x) + (x - x') + (x' - h')| ≤
        |(h - x) + (x - x')| + |x' - h'| := abs_add_le _ _
    _ ≤ |h - x| + |x - x'| + |x' - h'| := by
      linarith [abs_add_le (h - x) (x - x')]
    _ ≤ (d : ℝ) * beta + 2 * t + (d : ℝ) * beta := by
      exact add_le_add (add_le_add hleft hobs) (by simpa only [abs_sub_comm] using hright)
    _ = 2 * t + 2 * (d : ℝ) * beta := by ring

theorem discrepancy_secondMoment_bounds
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {h h' : Ω → ℝ} {H : ℝ}
    (hmeas : AEStronglyMeasurable (fun ω => h ω - h' ω) μ)
    (hbound : ∀ᵐ ω ∂μ, |h ω - h' ω| ≤ H) :
    MemLp (fun ω => h ω - h' ω) 2 μ ∧
      0 ≤ (∫ ω, (h ω - h' ω) ^ 2 ∂μ) ∧
      (∫ ω, (h ω - h' ω) ^ 2 ∂μ) ≤ H ^ 2 := by
  have hLp : MemLp (fun ω => h ω - h' ω) 2 μ :=
    MemLp.of_bound hmeas H (by simpa only [Real.norm_eq_abs] using hbound)
  exact ⟨hLp, integral_nonneg (fun _ => sq_nonneg _),
    DiscrepancyEnergy.secondMoment_le_of_ae_abs_le
      (X := fun _ ω => h ω - h' ω) (t := 0) hLp.integrable_sq hbound⟩

theorem discrepancy_bounds_of_shared_innovation
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {d : ℕ} {beta t T : ℝ} (hbeta : 0 ≤ beta) (ht : 0 ≤ t) (htT : t ≤ T)
    {h h' x x' w : Ω → ℝ} {m m' : ℝ → Ω → ℝ}
    (z z' : Ω → Fin d → ℝ)
    (hmeas : AEStronglyMeasurable (fun ω => h ω - h' ω) μ)
    (hx : ∀ᵐ ω ∂μ, x ω = w ω + ∫ s in (0 : ℝ)..t, m s ω)
    (hx' : ∀ᵐ ω ∂μ, x' ω = w ω + ∫ s in (0 : ℝ)..t, m' s ω)
    (hm : ∀ᵐ ω ∂μ, ∀ᵐ s : ℝ, s ∈ Ioc 0 t → |m s ω| ≤ 1)
    (hm' : ∀ᵐ ω ∂μ, ∀ᵐ s : ℝ, s ∈ Ioc 0 t → |m' s ω| ≤ 1)
    (hh : ∀ᵐ ω ∂μ,
      h ω = x ω + ∑ i, cavityMessage (Real.tanh beta) (z ω i))
    (hh' : ∀ᵐ ω ∂μ,
      h' ω = x' ω + ∑ i, cavityMessage (Real.tanh beta) (z' ω i)) :
    (∀ᵐ ω ∂μ, |h ω - h' ω| ≤ 2 * T + 2 * (d : ℝ) * beta) ∧
    MemLp (fun ω => h ω - h' ω) 2 μ ∧
      0 ≤ (∫ ω, (h ω - h' ω) ^ 2 ∂μ) ∧
      (∫ ω, (h ω - h' ω) ^ 2 ∂μ) ≤ (2 * T + 2 * (d : ℝ) * beta) ^ 2 := by
  have hbound : ∀ᵐ ω ∂μ, |h ω - h' ω| ≤ 2 * T + 2 * (d : ℝ) * beta := by
    filter_upwards [hx, hx', hm, hm', hh, hh'] with ω hxω hxω' hmω hmω' hhω hhω'
    exact (abs_cavity_field_sub_le_of_shared_innovation hbeta ht (z ω) (z' ω)
      hxω hxω' hmω hmω' hhω hhω').trans (by linarith)
  exact ⟨hbound, discrepancy_secondMoment_bounds hmeas hbound⟩

end Problem367

end

end OAI
