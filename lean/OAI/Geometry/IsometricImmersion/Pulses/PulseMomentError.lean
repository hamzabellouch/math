import OAI.Geometry.IsometricImmersion.Pulses.ActualForcingMoment

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology

namespace SmoothLocal.Pulse
open SmoothLocal.Geometry SmoothLocal.Weighted

theorem pulseTest_abs_le (a tau x : ℝ) : |pulseTest a tau x| ≤ axisBump a x := by
  unfold pulseTest
  rw [abs_mul,abs_of_nonneg (axisBump_nonneg a x)]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (axisBump_nonneg a x)

theorem axisBump_Icc_integral {a : ℝ} (ha : 0 < a) :
    (∫ x in Icc (-a) a, axisBump a x) = ∫ x : ℝ, axisBump a x := by
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro x hx
  by_contra hn
  have h := abs_lt.mp (axisBump_support_bound ha hn)
  exact hx ⟨h.1.le,h.2.le⟩

theorem pulse_spatial_mass_integral {a delta tau : ℝ}
    (ha : 0 < a) (hd : 0 ≤ delta) (ht : 0 < tau) :
    (∫ q in pulsePairRectangle a delta tau, axisBump a q.2 ∂volume.prod volume) =
      (2*delta/tau)*(∫ x : ℝ, axisBump a x) := by
  have hw : -(delta/tau) ≤ delta/tau := by linarith [div_nonneg hd ht.le]
  have hh := setIntegral_prod_mul (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
    (fun _ : ℝ => (1 : ℝ)) (axisBump a) (Icc (-(delta/tau)) (delta/tau)) (Icc (-a) a)
  simp only [one_mul] at hh
  rw [show pulsePairRectangle a delta tau =
    Icc (-(delta/tau)) (delta/tau) ×ˢ Icc (-a) a from rfl,hh,
    setIntegral_const,Real.volume_real_Icc_of_le hw,smul_eq_mul,mul_one,axisBump_Icc_integral ha]
  ring

theorem pulseWeightedMoment_bound {a delta tau B : ℝ} {f : Coord → ℝ}
    (ha : 0 < a) (hd : 0 ≤ delta) (ht : 0 < tau) (hB : 0 ≤ B)
    (hf : ∀ p ∈ pulseStrip a delta tau, |f p| ≤ B) :
    |pulseWeightedMoment a delta tau f| ≤
      B*(2*delta/tau)*(∫ x : ℝ, axisBump a x) := by
  have hmajor : IntegrableOn (fun q : ℝ × ℝ => B*axisBump a q.2)
      (pulsePairRectangle a delta tau) (volume.prod volume) :=
    ((continuous_const.mul ((axisBump_contDiff a).continuous.comp continuous_snd)).continuousOn).integrableOn_compact
      (pulsePairRectangle_isCompact a delta tau)
  have hpoint : ∀ᵐ q ∂(volume.prod volume).restrict (pulsePairRectangle a delta tau),
      ‖f (pulsePairPoint q)*pulseTest a tau q.2‖ ≤ B*axisBump a q.2 := by
    filter_upwards [ae_restrict_mem (pulsePairRectangle_isCompact a delta tau).measurableSet] with q hq
    rw [Real.norm_eq_abs,abs_mul]
    exact mul_le_mul (hf _ (pulsePairPoint_mem hq)) (pulseTest_abs_le a tau q.2)
      (abs_nonneg _) hB
  have h := norm_integral_le_of_norm_le hmajor hpoint
  simp only [Real.norm_eq_abs,integral_const_mul] at h
  rw [pulse_spatial_mass_integral ha hd ht] at h
  simpa only [pulseWeightedMoment,mul_assoc] using h

theorem pulseWeightedMoment_integrable {a delta tau : ℝ} {f : Coord → ℝ}
    (hf : ContinuousOn f (pulseStrip a delta tau)) :
    IntegrableOn (fun q => f (pulsePairPoint q)*pulseTest a tau q.2)
      (pulsePairRectangle a delta tau) (volume.prod volume) :=
  ((hf.comp pulsePairPoint_continuous.continuousOn (fun _ hq => pulsePairPoint_mem hq)).mul
    ((pulseTest_continuous a tau).comp continuous_snd).continuousOn).integrableOn_compact
      (pulsePairRectangle_isCompact a delta tau)

theorem pulseWeightedMoment_sub {a delta tau : ℝ} {f h : Coord → ℝ}
    (hf : ContinuousOn f (pulseStrip a delta tau)) (hh : ContinuousOn h (pulseStrip a delta tau)) :
    pulseWeightedMoment a delta tau (fun p => f p-h p) =
      pulseWeightedMoment a delta tau f-pulseWeightedMoment a delta tau h := by
  unfold pulseWeightedMoment
  simp_rw [sub_mul]
  exact integral_sub (pulseWeightedMoment_integrable hf) (pulseWeightedMoment_integrable hh)

theorem pulseWeightedMoment_lower_of_remainder {a delta tau B L : ℝ} {f h : Coord → ℝ}
    (ha : 0 < a) (hd : 0 ≤ delta) (ht : 0 < tau) (hB : 0 ≤ B)
    (hf : ContinuousOn f (pulseStrip a delta tau)) (hh : ContinuousOn h (pulseStrip a delta tau))
    (hrem : ∀ p ∈ pulseStrip a delta tau, |f p-h p| ≤ B)
    (hlead : L ≤ |pulseWeightedMoment a delta tau h|) :
    L-B*(2*delta/tau)*(∫ x : ℝ, axisBump a x) ≤ |pulseWeightedMoment a delta tau f| := by
  have herr := pulseWeightedMoment_bound ha hd ht hB hrem
  rw [pulseWeightedMoment_sub hf hh] at herr
  have htriangle : |pulseWeightedMoment a delta tau h| ≤
      |pulseWeightedMoment a delta tau f|+
      |pulseWeightedMoment a delta tau f-pulseWeightedMoment a delta tau h| := by
    calc
      _ = |pulseWeightedMoment a delta tau f-
        (pulseWeightedMoment a delta tau f-pulseWeightedMoment a delta tau h)| := by congr 1; ring
      _ ≤ _ := abs_sub _ _
  linarith

theorem pulseWeightedMoment_lower_order_error {a delta tau C : ℝ} {N : ℕ} {f : Coord → ℝ}
    (ha : 0 < a) (hd : 0 ≤ delta) (ht : 0 < tau) (hC : 0 ≤ C)
    (hf : ∀ p ∈ pulseStrip a delta tau, |f p| ≤ C*tau/tau^N) :
    |pulseWeightedMoment a delta tau f| ≤
      (2*C*(∫ x : ℝ, axisBump a x))*delta/tau^N := by
  have hB : 0 ≤ C*tau/tau^N := div_nonneg (mul_nonneg hC ht.le) (pow_nonneg ht.le N)
  apply (pulseWeightedMoment_bound ha hd ht hB hf).trans_eq
  field_simp [ht.ne']

end SmoothLocal.Pulse

end

end OAI
