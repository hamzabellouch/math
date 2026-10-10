import OAI.Probability.SLE.Mass.CanonicalMassExhaustion

namespace OAI

/-! Local exhaustion implies convergence of every compact continuous test.
This provides the terminal value of the fixed raw driver functional. -/

noncomputable section
open Set Filter MeasureTheory Classical
open scoped NNReal ENNReal Topology CompactlySupported

namespace SLEExactGauge

local instance : LocallyCompactSpace upperHalfPlane := isOpen_upperHalfPlane.locallyCompactSpace

lemma compact_test_norm_le_mass (μ : Measure upperHalfPlane)
    [IsFiniteMeasureOnCompacts μ] (f : C_c(upperHalfPlane,ℝ)) :
    ‖∫ z, f z ∂μ‖ ≤ ‖f.toBoundedContinuousFunction‖ * (μ (tsupport f)).toReal := by
  let : IsFiniteMeasure (μ.restrict (tsupport f)) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using f.hasCompactSupport.measure_lt_top (μ := μ)⟩
  have he := setIntegral_eq_integral_of_forall_compl_eq_zero (μ := μ)
    (s := tsupport f) (fun z hz => image_eq_zero_of_notMem_tsupport hz)
  rw [← he]
  have hb : ∀ᵐ z ∂μ.restrict (tsupport f), ‖f z‖ ≤ ‖f.toBoundedContinuousFunction‖ :=
    ae_of_all _ (fun z => f.toBoundedContinuousFunction.norm_coe_le_norm z)
  have h := norm_integral_le_of_norm_le_const hb
  simpa only [Measure.real,Measure.restrict_apply_univ] using h

theorem terminal_mass_test_tendsto
    (ν : Measure upperHalfPlane) [ν.Regular]
    (N : ℝ≥0 → Measure upperHalfPlane) (hNr : ∀ t, (N t).Regular)
    (hdom : ∀ t, N t ≤ ν)
    (hlim : ∀ K : Set upperHalfPlane, IsCompact K →
      Tendsto (fun t : ℝ≥0 => (ν-N t) K) atTop (𝓝 0))
    (f : C_c(upperHalfPlane,ℝ)) :
    Tendsto (fun t : ℝ≥0 => ∫ z, f z ∂N t) atTop (𝓝 (∫ z, f z ∂ν)) := by
  let (t : ℝ≥0) : IsFiniteMeasureOnCompacts (ν-N t) :=
    ⟨fun K hK => lt_of_le_of_lt (Measure.sub_le K) hK.measure_lt_top⟩
  have hrem : Tendsto (fun t : ℝ≥0 => ∫ z, f z ∂(ν-N t)) atTop (𝓝 0) := by
    apply squeeze_zero_norm (fun t => compact_test_norm_le_mass (ν-N t) f)
    have hh := (ENNReal.continuousAt_toReal ENNReal.zero_ne_top).tendsto.comp
      (hlim (tsupport f) f.hasCompactSupport)
    simpa only [Function.comp_def,ENNReal.toReal_zero,mul_zero] using
      (tendsto_const_nhds (x := ‖f.toBoundedContinuousFunction‖)).mul hh
  have he (t : ℝ≥0) : (∫ z, f z ∂ν)-(∫ z, f z ∂(ν-N t)) = ∫ z, f z ∂N t := by
    let := hNr t
    have : (ν-N t).Regular := inferInstance
    have hsum := integral_add_measure (μ := ν-N t) (ν := N t) f.integrable f.integrable
    rw [sigmaFinite_sub_add_cancel_of_le (hdom t)] at hsum
    linarith
  simpa only [he,sub_zero] using (tendsto_const_nhds (x := ∫ z, f z ∂ν)).sub hrem

end SLEExactGauge

end

end OAI
