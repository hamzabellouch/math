import OAI.Probability.SLE.Mass.RadonTestMeasurability

namespace OAI

/-! Measurable selection of the pathwise Radon limit. Only a measurable
full-measure set is retained; the limit is set to zero on its complement. -/

noncomputable section
open Set Filter MeasureTheory Classical
open scoped Topology CompactlySupported

namespace SLEExactGauge

variable {X : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
  [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]

/-- An almost-sure regular vague limit of random positive measures has a
measurable regular version. The approximants need only have measurable
compact-test integrals. -/
theorem exists_measurable_random_radon_limit
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (μ : ℕ → Ω → Measure X)
    (hmeas : ∀ n (f : C_c(X,ℝ)), Measurable (fun ω => ∫ x, f x ∂μ n ω))
    (hex : ∀ᵐ ω ∂P, ∃ ν : Measure X, ν.Regular ∧
      ∀ f : C_c(X,ℝ), Tendsto (fun n => ∫ x, f x ∂μ n ω) atTop (𝓝 (∫ x, f x ∂ν))) :
    ∃ ν : Ω → Measure X, Measurable ν ∧
      (∀ ω, (ν ω).Regular ∧ IsFiniteMeasureOnCompacts (ν ω)) ∧
      ∀ᵐ ω ∂P, ∀ f : C_c(X,ℝ),
        Tendsto (fun n => ∫ x, f x ∂μ n ω) atTop (𝓝 (∫ x, f x ∂ν ω)) := by
  let good (ω : Ω) : Prop := ∃ ν : Measure X, ν.Regular ∧
    ∀ f : C_c(X,ℝ), Tendsto (fun n => ∫ x, f x ∂μ n ω) atTop (𝓝 (∫ x, f x ∂ν))
  have hnull : P {ω | ¬good ω}=0 := ae_iff.mp hex
  obtain ⟨N,hN,hNm,hN0⟩ := exists_measurable_superset_of_null hnull
  have hgood (ω : Ω) (hω : ω ∉ N) : good ω := by
    by_contra h
    exact hω (hN h)
  have hall (ω : Ω) : ∃ ν : Measure X, ν.Regular ∧
      ∀ f : C_c(X,ℝ), Tendsto (fun n => if ω ∈ N then (0:ℝ) else ∫ x, f x ∂μ n ω)
        atTop (𝓝 (∫ x, f x ∂ν)) := by
    by_cases hω : ω ∈ N
    · refine ⟨0,inferInstance,fun f => ?_⟩
      simpa only [ite_eq_left hω,integral_zero_measure] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0:ℝ)) atTop (𝓝 0))
    · obtain ⟨ν,hν,hlim⟩ := hgood ω hω
      exact ⟨ν,hν,fun f => by simpa only [ite_eq_right hω] using hlim f⟩
  choose ν hν hlim using hall
  have hνm : Measurable ν := by
    apply measurable_radon_of_tests ν hν
    intro f
    apply measurable_of_tendsto_metrizable
      (f := fun n ω => if ω ∈ N then (0:ℝ) else ∫ x, f x ∂μ n ω)
    · intro n
      exact measurable_const.ite hNm (hmeas n f)
    · exact tendsto_pi_nhds.mpr (fun ω => hlim ω f)
  refine ⟨ν,hνm,fun ω => ?_,?_⟩
  · let : (ν ω).Regular := hν ω
    exact ⟨hν ω,inferInstance⟩
  · filter_upwards [compl_mem_ae_iff.mpr hN0] with ω hω
    intro f
    simpa only [ite_eq_right hω] using hlim ω f

/-- Countably many times retain one common event of convergence, and each
selected time slice is a measurable locally finite regular random measure. -/
theorem exists_measurable_countable_radon_limits
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (μ : ℕ → ℕ → Ω → Measure X)
    (hmeas : ∀ n j (f : C_c(X,ℝ)), Measurable (fun ω => ∫ x, f x ∂μ n j ω))
    (hex : ∀ᵐ ω ∂P, ∃ ν : ℕ → Measure X, (∀ j, (ν j).Regular) ∧
      ∀ j (f : C_c(X,ℝ)), Tendsto (fun n => ∫ x, f x ∂μ n j ω) atTop (𝓝 (∫ x, f x ∂ν j))) :
    ∃ ν : ℕ → Ω → Measure X, (∀ j, Measurable (ν j)) ∧
      (∀ j ω, (ν j ω).Regular ∧ IsFiniteMeasureOnCompacts (ν j ω)) ∧
      ∀ᵐ ω ∂P, ∀ j (f : C_c(X,ℝ)),
        Tendsto (fun n => ∫ x, f x ∂μ n j ω) atTop (𝓝 (∫ x, f x ∂ν j ω)) := by
  have hj (j : ℕ) : ∀ᵐ ω ∂P, ∃ ν : Measure X, ν.Regular ∧
      ∀ f : C_c(X,ℝ), Tendsto (fun n => ∫ x, f x ∂μ n j ω) atTop (𝓝 (∫ x, f x ∂ν)) := by
    filter_upwards [hex] with ω hω
    obtain ⟨ν,hν,hlim⟩ := hω
    exact ⟨ν j,hν j,hlim j⟩
  choose ν hνm hνr hlim using fun j =>
    exists_measurable_random_radon_limit P (fun n => μ n j) (fun n => hmeas n j) (hj j)
  exact ⟨ν,hνm,hνr,ae_all_iff.mpr hlim⟩

omit [SecondCountableTopology X] in
/-- Regular vague limits of the same sequence are unique. -/
theorem radon_test_limit_unique (μ : ℕ → Measure X) (ν η : Measure X)
    [ν.Regular] [η.Regular]
    (hν : ∀ f : C_c(X,ℝ), Tendsto (fun n => ∫ x, f x ∂μ n) atTop (𝓝 (∫ x, f x ∂ν)))
    (hη : ∀ f : C_c(X,ℝ), Tendsto (fun n => ∫ x, f x ∂μ n) atTop (𝓝 (∫ x, f x ∂η))) :
    ν=η :=
  Measure.ext_of_integral_eq_on_compactlySupported fun f => tendsto_nhds_unique (hν f) (hη f)

/-- Any pathwise version of the same limit is almost everywhere
measurable, useful when the approximants are measurable in a smaller
stopped or deterministic-time sigma algebra. -/
theorem aemeasurable_radon_of_test_limits_ae
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (μ : ℕ → Ω → Measure X)
    (ν : Ω → Measure X)
    (hmeas : ∀ n (f : C_c(X,ℝ)), Measurable (fun ω => ∫ x, f x ∂μ n ω))
    (hν : ∀ᵐ ω ∂P, (ν ω).Regular)
    (hlim : ∀ᵐ ω ∂P, ∀ f : C_c(X,ℝ),
      Tendsto (fun n => ∫ x, f x ∂μ n ω) atTop (𝓝 (∫ x, f x ∂ν ω))) :
    AEMeasurable ν P := by
  have hex : ∀ᵐ ω ∂P, ∃ η : Measure X, η.Regular ∧
      ∀ f : C_c(X,ℝ), Tendsto (fun n => ∫ x, f x ∂μ n ω) atTop (𝓝 (∫ x, f x ∂η)) := by
    filter_upwards [hν,hlim] with ω hr hl
    exact ⟨ν ω,hr,hl⟩
  obtain ⟨η,hηm,hηr,hηlim⟩ := exists_measurable_random_radon_limit P μ hmeas hex
  apply hηm.aemeasurable.congr
  filter_upwards [hν,hlim,hηlim] with ω hr hl hηl
  let : (ν ω).Regular := hr
  let : (η ω).Regular := (hηr ω).1
  exact (radon_test_limit_unique (fun n => μ n ω) (ν ω) (η ω) hl hηl).symm

end SLEExactGauge

end

end OAI
