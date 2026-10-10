import OAI.Probability.SLE.Mass.SubSigmaRadonLimit

namespace OAI

/-! A deterministic choice of the vague limit, with value zero when no
regular limit exists. The same choice is measurable for every sigma-algebra
making the approximating compact tests measurable. -/

noncomputable section
open Set Filter MeasureTheory Classical
open scoped Topology CompactlySupported

namespace SLEExactGauge

variable {X : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
  [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]

def HasRegularTestLimit (μ : ℕ → Measure X) (ν : Measure X) : Prop :=
  ν.Regular ∧ ∀ f : C_c(X,ℝ),
    Tendsto (fun n => ∫ x, f x ∂μ n) atTop (𝓝 (∫ x, f x ∂ν))

def canonicalRadonLimit (μ : ℕ → Measure X) : Measure X :=
  if h : ∃ ν, HasRegularTestLimit μ ν then h.choose else 0

omit [T2Space X] [LocallyCompactSpace X] [SecondCountableTopology X] [BorelSpace X] in
theorem canonicalRadonLimit_regular (μ : ℕ → Measure X) :
    (canonicalRadonLimit μ).Regular := by
  classical
  unfold canonicalRadonLimit
  split_ifs with h
  · exact h.choose_spec.1
  · infer_instance

omit [SecondCountableTopology X] in
theorem canonicalRadonLimit_identified (μ : ℕ → Measure X) (ν : Measure X)
    (hν : HasRegularTestLimit μ ν) : canonicalRadonLimit μ = ν := by
  classical
  have hex : ∃ η, HasRegularTestLimit μ η := ⟨ν,hν⟩
  have hspec := hex.choose_spec
  let := hspec.1
  let := hν.1
  rw [canonicalRadonLimit,dite_eq_left hex]
  exact radon_test_limit_unique μ _ ν hspec.2 hν.2

theorem canonicalRadonLimit_measurable
    {Ω : Type*} [MeasurableSpace Ω] (μ : ℕ → Ω → Measure X)
    (hfinite : ∀ n ω, IsFiniteMeasureOnCompacts (μ n ω))
    (hmeas : ∀ n (f : C_c(X,ℝ)), Measurable (fun ω => ∫ x, f x ∂μ n ω)) :
    Measurable (fun ω => canonicalRadonLimit (fun n => μ n ω)) := by
  classical
  let D := localTestFamily X
  let G : Set Ω := {ω | ∀ j, ∃ a : ℝ,
    Tendsto (fun n => ∫ x, D.test j x ∂μ n ω) atTop (𝓝 a)}
  have hG : MeasurableSet G := by
    simpa only [G,Set.ofPred_forall] using MeasurableSet.iInter
      (fun j => measurableSet_exists_tendsto (fun n => hmeas n (D.test j)))
  have hex (ω : Ω) : ω ∈ G ↔ ∃ ν, HasRegularTestLimit (fun n => μ n ω) ν := by
    constructor
    · intro hω
      let (n : ℕ) : IsFiniteMeasureOnCompacts (μ n ω) := hfinite n ω
      obtain ⟨ν,hr,_,hl⟩ := D.exists_radon_limit (fun n => μ n ω) hω
      exact ⟨ν,hr,hl⟩
    · rintro ⟨ν,_,hl⟩ j
      exact ⟨∫ x, D.test j x ∂ν,hl (D.test j)⟩
  apply measurable_radon_of_tests _ (fun ω => canonicalRadonLimit_regular _)
  intro f
  apply measurable_of_tendsto_metrizable
    (f := fun n ω => if ω ∈ G then ∫ x, f x ∂μ n ω else 0)
  · intro n
    exact (hmeas n f).ite hG measurable_const
  · apply tendsto_pi_nhds.mpr
    intro ω
    by_cases hω : ω ∈ G
    · obtain ⟨ν,hν⟩ := (hex ω).mp hω
      rw [canonicalRadonLimit_identified _ ν hν]
      simpa only [ite_eq_left hω] using hν.2 f
    · have he : canonicalRadonLimit (fun n => μ n ω) = 0 := by
        rw [canonicalRadonLimit,dite_eq_right (mt (hex ω).mpr hω)]
      simpa only [ite_eq_right hω,he,integral_zero_measure] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0:ℝ)) atTop (𝓝 0))

end SLEExactGauge

end

end OAI
