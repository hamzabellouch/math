import OAI.Probability.SLE.Mass.RadonTestFamily

namespace OAI

/-! Order and closed-support properties of the reconstructed Radon limits. -/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology CompactlySupported ENNReal

namespace SLEExactGauge

variable {X : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
  [MeasurableSpace X] [BorelSpace X]

lemma compact_measure_le_test_integral (μ : Measure X) [μ.Regular]
    (f : C_c(X, ℝ)) (hf : ∀ x, 0 ≤ f x) {K : Set X} (hK : IsCompact K)
    (hfone : ∀ x ∈ K, f x=1) : μ K ≤ ENNReal.ofReal (∫ x, f x ∂μ) := by
  simpa only [RealRMK.rieszMeasure_integralPositiveLinearMap,
    CompactlySupportedContinuousMap.integralPositiveLinearMap_apply] using
    RealRMK.rieszMeasure_le_of_eq_one
      (CompactlySupportedContinuousMap.integralPositiveLinearMap μ) hf hK hfone

lemma test_integral_le_measure (μ : Measure X) [μ.Regular]
    (f : C_c(X, ℝ)) (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1) {U : Set X}
    (hs : tsupport f ⊆ U) : ENNReal.ofReal (∫ x, f x ∂μ) ≤ μ U := by
  simpa only [RealRMK.rieszMeasure_integralPositiveLinearMap,
    CompactlySupportedContinuousMap.integralPositiveLinearMap_apply] using
    RealRMK.le_rieszMeasure_tsupport_subset
      (CompactlySupportedContinuousMap.integralPositiveLinearMap μ) hf hs

/-- The positive compact-test order determines the order of Radon measures. -/
theorem radon_measure_le_of_nonneg_tests (μ ν : Measure X) [μ.Regular] [ν.Regular]
    (h : ∀ f : C_c(X, ℝ), (∀ x, 0 ≤ f x) → (∫ x, f x ∂μ) ≤ ∫ x, f x ∂ν) : μ ≤ ν := by
  have hc (K : Set X) (hK : IsCompact K) : μ K ≤ ν K := by
    apply ENNReal.le_of_forall_pos_le_add
    intro ε hε _
    obtain ⟨U,hKU,hU,hνU⟩ := K.exists_isOpen_le_add ν
      (ne_of_gt (ENNReal.coe_lt_coe.mpr hε))
    obtain ⟨f,hf1,hfc,hfs,hf01⟩ := exists_continuousMap_one_of_isCompact_subset_isOpen
      hK hU hKU
    let g : C_c(X, ℝ) := ⟨f,hfc⟩
    have hg0 : ∀ x, 0 ≤ g x := fun x => (hf01 x).1
    calc
      μ K ≤ ENNReal.ofReal (∫ x, g x ∂μ) := compact_measure_le_test_integral μ g hg0 hK hf1
      _ ≤ ENNReal.ofReal (∫ x, g x ∂ν) := ENNReal.ofReal_le_ofReal (h g hg0)
      _ ≤ ν U := test_integral_le_measure ν g hf01 hfs
      _ ≤ ν K+ε := hνU
  have ho (U : Set X) (hU : IsOpen U) : μ U ≤ ν U := by
    rw [Measure.Regular.innerRegular.measure_eq_iSup hU]
    exact iSup_le fun K => iSup_le fun hKU => iSup_le fun hK => (hc K hK).trans (measure_mono hKU)
  apply Measure.le_iff'.mpr
  intro A
  rw [A.measure_eq_iInf_isOpen ν]
  exact le_iInf fun U => le_iInf fun hAU => le_iInf fun hU => (measure_mono hAU).trans (ho U hU)

/-- Order of positive approximants passes to every compact-test limit. -/
theorem radon_limits_mono (μ ν : ℕ → Measure X)
    [∀ n, IsFiniteMeasureOnCompacts (μ n)] [∀ n, IsFiniteMeasureOnCompacts (ν n)]
    (μ₀ ν₀ : Measure X) [μ₀.Regular] [ν₀.Regular]
    (hμ : ∀ f : C_c(X, ℝ), Tendsto (fun n => ∫ x, f x ∂μ n) atTop (𝓝 (∫ x, f x ∂μ₀)))
    (hν : ∀ f : C_c(X, ℝ), Tendsto (fun n => ∫ x, f x ∂ν n) atTop (𝓝 (∫ x, f x ∂ν₀)))
    (hle : ∀ n, μ n ≤ ν n) : μ₀ ≤ ν₀ := by
  apply radon_measure_le_of_nonneg_tests
  intro f hf
  exact le_of_tendsto_of_tendsto' (hμ f) (hν f) (fun n =>
    integral_mono_measure (hle n) (ae_of_all _ hf) f.integrable)

/-- Vanishing compact tests inside an open set force the Radon mass of
that open set to vanish. -/
theorem radon_open_eq_zero_of_tests (μ : Measure X) [μ.Regular] (U : Set X) (hU : IsOpen U)
    (hzero : ∀ f : C_c(X, ℝ), tsupport f ⊆ U → (∫ x, f x ∂μ)=0) : μ U=0 := by
  apply le_antisymm ?_ bot_le
  rw [Measure.Regular.innerRegular.measure_eq_iSup hU]
  refine iSup_le fun K => iSup_le fun hKU => iSup_le fun hK => ?_
  obtain ⟨f,hf1,hfc,hfs,hf01⟩ := exists_continuousMap_one_of_isCompact_subset_isOpen
    hK hU hKU
  let g : C_c(X, ℝ) := ⟨f,hfc⟩
  have hg0 : ∀ x, 0 ≤ g x := fun x => (hf01 x).1
  have hb := compact_measure_le_test_integral μ g hg0 hK hf1
  change μ K ≤ 0
  simpa only [hzero g hfs,ENNReal.ofReal_zero] using hb

/-- The compact-test limit is carried by a closed set if each compact
test separated from it eventually vanishes. -/
theorem radon_limit_carried_by_closed (μ : ℕ → Measure X) (ν : Measure X) [ν.Regular]
    (hlim : ∀ f : C_c(X, ℝ), Tendsto (fun n => ∫ x, f x ∂μ n) atTop (𝓝 (∫ x, f x ∂ν)))
    (S : Set X) (hS : IsClosed S)
    (hvanish : ∀ f : C_c(X, ℝ), tsupport f ⊆ Sᶜ →
      ∀ᶠ n in atTop, (∫ x, f x ∂μ n)=0) : ν Sᶜ=0 := by
  apply radon_open_eq_zero_of_tests ν Sᶜ hS.isOpen_compl
  intro f hf
  have heq : (fun _ : ℕ => (0:ℝ)) =ᶠ[atTop] (fun n => ∫ x, f x ∂μ n) :=
    (hvanish f hf).mono (fun _ h => h.symm)
  exact tendsto_nhds_unique (hlim f) (tendsto_const_nhds.congr' heq)

end SLEExactGauge

end

end OAI
