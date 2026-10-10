import Mathlib

namespace OAI
noncomputable section
open Filter
open scoped Topology

namespace Problem337.DivisorMoment

/-- The slowly varying coefficient in the prime-prefix band estimate is negligible
    compared with the logarithm of the band parameter. -/
theorem tendsto_loglog_coefficient (r K : ℝ) :
    Tendsto (fun v : ℝ => r * (K + Real.log (Real.log v)) / Real.log v)
      atTop (𝓝 0) := by
  have hc : Tendsto (fun v : ℝ => K / Real.log v) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop Real.tendsto_log_atTop
  have hl : Tendsto (fun v : ℝ => Real.log (Real.log v) / Real.log v) atTop (𝓝 0) :=
    (Real.isLittleO_log_id_atTop.comp_tendsto Real.tendsto_log_atTop).tendsto_div_nhds_zero
  have hh := (hc.add hl).const_mul r
  simp only [add_zero, mul_zero] at hh
  convert hh using 1
  ext v
  ring

/-- Uniform domination of the two positive errors in an intermediate-prime band. -/
theorem eventually_intermediate_band_decay (r C K : ℝ) (hr : 0 ≤ r) (hC : 0 ≤ C) :
    ∀ᶠ v : ℝ in atTop, ∀ Q t B : ℝ,
      v ^ (1 / 16 : ℝ) ≤ Q → 0 < t → t ≤ v →
      B ≤ K + Real.log (Real.log v) →
      r * B * Q - Q * Real.log Q / 50 +
        C * Q ^ (1 / 5 : ℝ) * Real.log (2 * t) ≤ -Q * Real.log Q / 100 := by
  have hsmall : ∀ᶠ v : ℝ in atTop,
      r * (K + Real.log (Real.log v)) / Real.log v ≤ (1 / 3200 : ℝ) :=
    (tendsto_loglog_coefficient r K).eventually (eventually_le_nhds (by norm_num))
  have hpower : ∀ᶠ v : ℝ in atTop,
      6400 * C ≤ (v ^ (1 / 16 : ℝ)) ^ (4 / 5 : ℝ) :=
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 4 / 5)).comp
      (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 16))).eventually
        (eventually_ge_atTop (6400 * C))
  filter_upwards [hsmall, hpower, eventually_ge_atTop (2 : ℝ)] with v hvsmall hvpower hv2
  intro Q t B hQ ht htv hB
  have hvpos : 0 < v := by linarith
  have hvlog : 0 < Real.log v := Real.log_pos (by linarith)
  have hvrootpos : 0 < v ^ (1 / 16 : ℝ) := Real.rpow_pos_of_pos hvpos _
  have hQpos : 0 < Q := hvrootpos.trans_le hQ
  have hQlog : (1 / 16 : ℝ) * Real.log v ≤ Real.log Q := by
    calc
      _ = Real.log (v ^ (1 / 16 : ℝ)) := (Real.log_rpow hvpos _).symm
      _ ≤ Real.log Q := Real.log_le_log hvrootpos hQ
  have hlogQpos : 0 < Real.log Q := by nlinarith
  have hBsmall : r * B ≤ Real.log Q / 200 := by
    have hh := (div_le_iff₀ hvlog).mp hvsmall
    have hb' : r * B ≤ r * (K + Real.log (Real.log v)) :=
      mul_le_mul_of_nonneg_left hB hr
    nlinarith
  have hlogtwo : Real.log 2 ≤ Real.log v :=
    Real.log_le_log (by norm_num) hv2
  have htlog : Real.log (2 * t) ≤ 32 * Real.log Q := by
    have hh : Real.log (2 * t) ≤ Real.log (2 * v) :=
      Real.log_le_log (by positivity) (by nlinarith)
    rw [Real.log_mul (by norm_num) hvpos.ne'] at hh
    nlinarith
  have hQpower : 6400 * C ≤ Q ^ (4 / 5 : ℝ) :=
    hvpower.trans (Real.rpow_le_rpow hvrootpos.le hQ (by norm_num))
  have hQfifth : 0 ≤ Q ^ (1 / 5 : ℝ) := (Real.rpow_pos_of_pos hQpos _).le
  have hQpowers : Q ^ (4 / 5 : ℝ) * Q ^ (1 / 5 : ℝ) = Q := by
    rw [← Real.rpow_add hQpos]
    norm_num
  have hscale : 6400 * C * Q ^ (1 / 5 : ℝ) ≤ Q := by
    nlinarith [mul_le_mul_of_nonneg_right hQpower hQfifth]
  have herror : C * Q ^ (1 / 5 : ℝ) * Real.log (2 * t) ≤ Q * Real.log Q / 200 := by
    have hll := mul_le_mul_of_nonneg_left htlog (mul_nonneg hC hQfifth)
    have hss := mul_le_mul_of_nonneg_right hscale hlogQpos.le
    nlinarith
  have hmain := mul_le_mul_of_nonneg_right hBsmall hQpos.le
  nlinarith

/-- The intermediate-prime exponent is uniformly negative over all
    admissible logarithmic scales. Only the lower bound on `v` is needed. -/
theorem eventually_uniform_intermediate_band_decay (E r C : ℝ)
    (hE : 2 ≤ E) (hr : 0 ≤ r) (hC : 0 ≤ C) :
    ∀ᶠ S : ℝ in atTop, ∀ v t : ℝ,
      S / (2 * Real.log S) ≤ v → 0 < t → t ≤ v ^ (15 / 16 : ℝ) →
      r * (1 + Real.log (E * S / v)) * (v / t) -
        (v / t) * Real.log (v / t) / 50 +
        C * (v / t) ^ (1 / 5 : ℝ) * Real.log (2 * t) ≤
          -(v / t) * Real.log (v / t) / 100 := by
  obtain ⟨V, hV⟩ := eventually_atTop.mp
    (eventually_intermediate_band_decay r C (1 + Real.log (4 * E)) hr hC)
  have hroot : ∀ᶠ S : ℝ in atTop, max 2 V ≤ S ^ (1 / 2 : ℝ) :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).eventually
      (eventually_ge_atTop (max 2 V))
  have hlogsmall : ∀ᶠ S : ℝ in atTop,
      ‖Real.log S‖ ≤ (1 / 2 : ℝ) * ‖S ^ (1 / 2 : ℝ)‖ :=
    (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).def (by norm_num)
  filter_upwards [hroot, hlogsmall, eventually_ge_atTop (2 : ℝ)] with S hroot hlogsmall hS
  intro v t hv ht htv
  have hSpos : 0 < S := by linarith
  have hlogS : 0 < Real.log S := Real.log_pos (by linarith)
  have hrootpos : 0 < S ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hSpos _
  have hrootsq : S ^ (1 / 2 : ℝ) * S ^ (1 / 2 : ℝ) = S := by
    rw [← Real.rpow_add hSpos]
    norm_num
  have hsmall : 2 * Real.log S ≤ S ^ (1 / 2 : ℝ) := by
    simpa only [Real.norm_eq_abs, abs_of_pos hlogS, abs_of_pos hrootpos] using
      (show 2 * ‖Real.log S‖ ≤ ‖S ^ (1 / 2 : ℝ)‖ by linarith)
  have hrootle : S ^ (1 / 2 : ℝ) ≤ S / (2 * Real.log S) := by
    apply (le_div_iff₀ (by positivity : 0 < 2 * Real.log S)).mpr
    nlinarith [mul_le_mul_of_nonneg_left hsmall hrootpos.le]
  have hvroot : S ^ (1 / 2 : ℝ) ≤ v := hrootle.trans hv
  have hv2 : 2 ≤ v := (le_max_left 2 V).trans (hroot.trans hvroot)
  have hVv : V ≤ v := (le_max_right 2 V).trans (hroot.trans hvroot)
  have hvpos : 0 < v := by linarith
  have hlogv : 0 < Real.log v := Real.log_pos (by linarith)
  have hlogs : Real.log S ≤ 2 * Real.log v := by
    have hh := Real.log_le_log hrootpos hvroot
    rw [Real.log_rpow hSpos] at hh
    linarith
  have hratio : E * S / v ≤ 4 * E * Real.log v := by
    have hbase := (div_le_iff₀ (by positivity : 0 < 2 * Real.log S)).mp hv
    have hEpos : 0 < E := by linarith
    apply (div_le_iff₀ hvpos).mpr
    have hb := mul_le_mul_of_nonneg_left hbase hEpos.le
    have hl := mul_le_mul_of_nonneg_left hlogs (by positivity : 0 ≤ 2 * E * v)
    nlinarith
  have hB : 1 + Real.log (E * S / v) ≤
      (1 + Real.log (4 * E)) + Real.log (Real.log v) := by
    have hh := Real.log_le_log (by positivity : 0 < E * S / v) hratio
    rw [Real.log_mul (by positivity : 4 * E ≠ 0) hlogv.ne'] at hh
    linarith
  have htv' : t ≤ v := by
    calc
      t ≤ v ^ (15 / 16 : ℝ) := htv
      _ ≤ v ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
      _ = v := Real.rpow_one v
  have hQ : v ^ (1 / 16 : ℝ) ≤ v / t := by
    apply (le_div_iff₀ ht).mpr
    have hh := mul_le_mul_of_nonneg_left htv
      (Real.rpow_pos_of_pos hvpos (1 / 16 : ℝ)).le
    have heq : v ^ (1 / 16 : ℝ) * v ^ (15 / 16 : ℝ) = v := by
      rw [← Real.rpow_add hvpos]
      norm_num
    exact hh.trans_eq heq
  exact hV v hVv (v / t) t (1 + Real.log (E * S / v)) hQ ht htv' hB

end Problem337.DivisorMoment

end

end OAI
