import OAI.Geometry.CylinderCovering.Angular.Taylor

namespace OAI

open Set MeasureTheory Filter
open scoped Topology ENNReal

namespace CylinderCovering.RationalCost

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

theorem integral_weight_remainder {D : Set X} {E : X → ℝ} {M ε : ℝ}
    (hD : MeasurableSet D) (hfin : μ D < ∞) (hE : Measurable E)
    (hM : 0 ≤ M) (hbound : ∀ x ∈ D, 0 ≤ E x ∧ E x ≤ M) :
    |(∫ x in D, 1 / Real.sqrt (1 + ε ^ 2 * E x) ∂μ) -
       (μ.real D - ε ^ 2 / 2 * ∫ x in D, E x ∂μ)| ≤
      (3 / 8) * ε ^ 4 * M ^ 2 * μ.real D := by
  have hEi : IntegrableOn E D μ := by
    apply IntegrableOn.of_bound hfin hE.aestronglyMeasurable M
    filter_upwards [ae_restrict_mem hD] with x hx
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hbound x hx).1] using (hbound x hx).2
  have hwmeas : Measurable (fun x => 1 / Real.sqrt (1 + ε ^ 2 * E x)) := by
    fun_prop
  have hwi : IntegrableOn (fun x => 1 / Real.sqrt (1 + ε ^ 2 * E x)) D μ := by
    apply IntegrableOn.of_bound hfin hwmeas.aestronglyMeasurable 1
    filter_upwards [ae_restrict_mem hD] with x hx
    have hn : 0 ≤ ε ^ 2 * E x := mul_nonneg (sq_nonneg ε) (hbound x hx).1
    have hs : 1 ≤ Real.sqrt (1 + ε ^ 2 * E x) := by
      exact (Real.le_sqrt (by norm_num) (by linarith)).2 (by linarith)
    have hs0 : 0 < Real.sqrt (1 + ε ^ 2 * E x) := lt_of_lt_of_le zero_lt_one hs
    rw [Real.norm_eq_abs, abs_of_pos (by positivity)]
    exact (div_le_one hs0).2 hs
  have hc : IntegrableOn (fun _ : X => (1 : ℝ)) D μ := integrableOn_const hfin.ne
  have hlin : IntegrableOn (fun x => 1 - ε ^ 2 / 2 * E x) D μ :=
    hc.sub (hEi.const_mul (ε ^ 2 / 2))
  have hrem := norm_setIntegral_le_of_norm_le_const_ae (μ := μ) (s := D)
    (f := fun x => 1 / Real.sqrt (1 + ε ^ 2 * E x) - (1 - ε ^ 2 / 2 * E x))
    hfin (C := (3 / 8) * ε ^ 4 * M ^ 2) ?_
  · rw [integral_sub hwi hlin, integral_sub hc (hEi.const_mul (ε ^ 2 / 2)),
      integral_const_mul, setIntegral_const] at hrem
    simpa only [Real.norm_eq_abs, smul_eq_mul, mul_one] using hrem
  · filter_upwards [ae_restrict_mem hD] with x hx
    rw [Real.norm_eq_abs]
    have h := AngularTaylor.inv_sqrt_remainder (mul_nonneg (sq_nonneg ε) (hbound x hx).1)
    have hsq : (E x) ^ 2 ≤ M ^ 2 := by nlinarith [(hbound x hx).1, (hbound x hx).2]
    have hp := mul_le_mul_of_nonneg_left hsq (show 0 ≤ (3 / 8 : ℝ) * ε ^ 4 by positivity)
    calc
      |1 / Real.sqrt (1 + ε ^ 2 * E x) - (1 - ε ^ 2 / 2 * E x)| =
        |1 / Real.sqrt (1 + ε ^ 2 * E x) - (1 - ε ^ 2 * E x / 2)| := by congr 1; ring
      _ ≤ (3 / 8) * (ε ^ 2 * E x) ^ 2 := h
      _ = (3 / 8) * ε ^ 4 * (E x) ^ 2 := by ring
      _ ≤ (3 / 8) * ε ^ 4 * M ^ 2 := hp

theorem changing_domain_remainder {D D₀ : Set X} {E : X → ℝ} {M ε : ℝ}
    (hD : MeasurableSet D) (hD₀ : MeasurableSet D₀) (hsub : D₀ ⊆ D)
    (hfin : μ D < ∞) (hE : Measurable E) (hM : 0 ≤ M)
    (hbound : ∀ x ∈ D, 0 ≤ E x ∧ E x ≤ M) :
    |(∫ x in D, 1 / Real.sqrt (1 + ε ^ 2 * E x) ∂μ) -
       (μ.real D - ε ^ 2 / 2 * ∫ x in D₀, E x ∂μ)| ≤
      (3 / 8) * ε ^ 4 * M ^ 2 * μ.real D +
        ε ^ 2 / 2 * M * μ.real (D \ D₀) := by
  have hEi : IntegrableOn E D μ := by
    apply IntegrableOn.of_bound hfin hE.aestronglyMeasurable M
    filter_upwards [ae_restrict_mem hD] with x hx
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hbound x hx).1] using (hbound x hx).2
  have hdiff : |(∫ x in D, E x ∂μ) - ∫ x in D₀, E x ∂μ| ≤
      M * μ.real (D \ D₀) := by
    rw [← setIntegral_sdiff hD₀ hEi hsub, ← Real.norm_eq_abs]
    apply norm_setIntegral_le_of_norm_le_const ((measure_mono sdiff_subset).trans_lt hfin)
    intro x hx
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hbound x hx.1).1] using (hbound x hx.1).2
  have hquad : |ε ^ 2 / 2 * ((∫ x in D, E x ∂μ) - ∫ x in D₀, E x ∂μ)| ≤
      ε ^ 2 / 2 * M * μ.real (D \ D₀) := by
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ ε ^ 2 / 2)]
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hdiff (by positivity : 0 ≤ ε ^ 2 / 2)
  have hid : (∫ x in D, 1 / Real.sqrt (1 + ε ^ 2 * E x) ∂μ) -
      (μ.real D - ε ^ 2 / 2 * ∫ x in D₀, E x ∂μ) =
      ((∫ x in D, 1 / Real.sqrt (1 + ε ^ 2 * E x) ∂μ) -
        (μ.real D - ε ^ 2 / 2 * ∫ x in D, E x ∂μ)) -
      ε ^ 2 / 2 * ((∫ x in D, E x ∂μ) - ∫ x in D₀, E x ∂μ) := by ring
  rw [hid]
  exact (abs_sub _ _).trans (add_le_add
    (integral_weight_remainder hD hfin hE hM hbound) hquad)

theorem cost_expansion_bound {D D₀ : Set X} {E : X → ℝ}
    {M ε A J q K B V : ℝ}
    (hD : MeasurableSet D) (hD₀ : MeasurableSet D₀) (hsub : D₀ ⊆ D)
    (hfin : μ D < ∞) (hE : Measurable E) (hM : 0 ≤ M)
    (hbound : ∀ x ∈ D, 0 ≤ E x ∧ E x ≤ M)
    (harea : |μ.real D - (A + ε ^ 2 * J + q / 2)| ≤ K * ε ^ 4)
    (hadded : μ.real (D \ D₀) ≤ B * ε ^ 2) (hvolume : μ.real D ≤ V) :
    |(∫ x in D, 1 / Real.sqrt (1 + ε ^ 2 * E x) ∂μ) -
      (A + ε ^ 2 * (J - (1 / 2) * ∫ x in D₀, E x ∂μ) + q / 2)| ≤
      ((3 / 8) * M ^ 2 * V + M * B / 2 + K) * ε ^ 4 := by
  have hr := changing_domain_remainder hD hD₀ hsub hfin hE hM hbound (ε := ε)
  have hv := mul_le_mul_of_nonneg_left hvolume
    (show 0 ≤ (3 / 8 : ℝ) * ε ^ 4 * M ^ 2 by positivity)
  have ha := mul_le_mul_of_nonneg_left hadded
    (show 0 ≤ ε ^ 2 / 2 * M by positivity)
  have hid : (∫ x in D, 1 / Real.sqrt (1 + ε ^ 2 * E x) ∂μ) -
      (A + ε ^ 2 * (J - (1 / 2) * ∫ x in D₀, E x ∂μ) + q / 2) =
      ((∫ x in D, 1 / Real.sqrt (1 + ε ^ 2 * E x) ∂μ) -
        (μ.real D - ε ^ 2 / 2 * ∫ x in D₀, E x ∂μ)) +
      (μ.real D - (A + ε ^ 2 * J + q / 2)) := by ring
  rw [hid]
  have ht := (abs_add_le _ _).trans (add_le_add hr harea)
  nlinarith only [ht, hv, ha]

theorem cost_expansion_bound_of_area {D D₀ : Set X} {E : X → ℝ}
    {M ε A J q K Q : ℝ}
    (hD : MeasurableSet D) (hD₀ : MeasurableSet D₀) (hsub : D₀ ⊆ D)
    (hfin : μ D < ∞) (hE : Measurable E) (hM : 0 ≤ M)
    (hbound : ∀ x ∈ D, 0 ≤ E x ∧ E x ≤ M)
    (hbase : μ.real D₀ = A) (heps : ε ^ 2 ≤ 1) (hK : 0 ≤ K) (hQ : 0 ≤ Q)
    (hq : q ≤ Q * ε ^ 2)
    (harea : |μ.real D - (A + ε ^ 2 * J + q / 2)| ≤ K * ε ^ 4) :
    |(∫ x in D, 1 / Real.sqrt (1 + ε ^ 2 * E x) ∂μ) -
      (A + ε ^ 2 * (J - (1 / 2) * ∫ x in D₀, E x ∂μ) + q / 2)| ≤
      ((3 / 8) * M ^ 2 * (A + (|J| + Q / 2 + K)) +
        M * (|J| + Q / 2 + K) / 2 + K) * ε ^ 4 := by
  have hpow : ε ^ 4 ≤ ε ^ 2 := by nlinarith [sq_nonneg ε]
  have hkpow := mul_le_mul_of_nonneg_left hpow hK
  have hj := mul_le_mul_of_nonneg_left (le_abs_self J) (sq_nonneg ε)
  have he := (abs_le.mp harea).2
  have hadded : μ.real (D \ D₀) ≤ (|J| + Q / 2 + K) * ε ^ 2 := by
    rw [measureReal_sdiff hsub hD₀ hfin.ne, hbase]
    nlinarith only [hkpow, hj, he, hq]
  have hB : 0 ≤ |J| + Q / 2 + K := by positivity
  have hb := mul_le_mul_of_nonneg_left heps hB
  have hvolume : μ.real D ≤ A + (|J| + Q / 2 + K) := by
    rw [measureReal_sdiff hsub hD₀ hfin.ne, hbase] at hadded
    linarith
  exact cost_expansion_bound hD hD₀ hsub hfin hE hM hbound harea hadded hvolume

end CylinderCovering.RationalCost

end OAI
