import OAI.Probability.SLE.Mass.RandomRadonLimit
import OAI.Probability.SLE.Mass.RadonTestFamily

namespace OAI

/-! A vague Radon limit has a version measurable in the same sigma-algebra
as its approximants. The probability measure may use a larger sigma-algebra;
the exceptional convergence set is detected by countably many tests. -/

noncomputable section
open Set Filter MeasureTheory Classical
open scoped Topology CompactlySupported

namespace SLEExactGauge

variable {X : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
  [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]

theorem exists_subsigma_radon_version_identified
    {Ω : Type*} (m : MeasurableSpace Ω) (μ : ℕ → Ω → Measure X)
    (hfinite : ∀ n ω, IsFiniteMeasureOnCompacts (μ n ω))
    (hmeas : ∀ n (f : C_c(X,ℝ)), Measurable[m] (fun ω => ∫ x, f x ∂μ n ω)) :
    ∃ η : Ω → Measure X, Measurable[m] η ∧
      (∀ ω, (η ω).Regular ∧ IsFiniteMeasureOnCompacts (η ω)) ∧
      ∀ ω (ν : Measure X), ν.Regular →
        (∀ f : C_c(X,ℝ), Tendsto (fun n => ∫ x, f x ∂μ n ω) atTop (𝓝 (∫ x, f x ∂ν))) →
        η ω = ν := by
  let : MeasurableSpace Ω := m
  let D := localTestFamily X
  let G : Set Ω := {ω | ∀ j, ∃ a : ℝ,
    Tendsto (fun n => ∫ x, D.test j x ∂μ n ω) atTop (𝓝 a)}
  have hG : MeasurableSet[m] G := by
    let : MeasurableSpace Ω := m
    simpa only [G,Set.ofPred_forall] using MeasurableSet.iInter
      (fun j => measurableSet_exists_tendsto (fun n => hmeas n (D.test j)))
  have hex (ω : Ω) : ∃ η : Measure X, η.Regular ∧
      ∀ f : C_c(X,ℝ), Tendsto
        (fun n => if ω ∈ G then ∫ x, f x ∂μ n ω else 0) atTop (𝓝 (∫ x, f x ∂η)) := by
    by_cases hω : ω ∈ G
    · let (n : ℕ) : IsFiniteMeasureOnCompacts (μ n ω) := hfinite n ω
      obtain ⟨η,hη,_,hl⟩ := D.exists_radon_limit (fun n => μ n ω) hω
      exact ⟨η,hη,fun f => by simpa only [ite_eq_left hω] using hl f⟩
    · refine ⟨0,inferInstance,fun f => ?_⟩
      simpa only [ite_eq_right hω,integral_zero_measure] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0:ℝ)) atTop (𝓝 0))
  choose η hηr hηlim using hex
  have hηm : Measurable[m] η := by
    let : MeasurableSpace Ω := m
    apply measurable_radon_of_tests η hηr
    intro f
    apply measurable_of_tendsto_metrizable
      (f := fun n ω => if ω ∈ G then ∫ x, f x ∂μ n ω else 0)
    · intro n
      exact (hmeas n f).ite hG measurable_const
    · exact tendsto_pi_nhds.mpr (fun ω => hηlim ω f)
  refine ⟨η,hηm,fun ω => ?_,?_⟩
  · let := hηr ω
    exact ⟨hηr ω,inferInstance⟩
  · intro ω ν hr hl
    have hg : ω ∈ G := fun j => ⟨∫ x, D.test j x ∂ν,hl (D.test j)⟩
    let := hηr ω
    let := hr
    apply radon_test_limit_unique (fun n => μ n ω) (η ω) ν
    · intro f
      simpa only [ite_eq_left hg] using hηlim ω f
    · exact hl

theorem exists_subsigma_radon_version
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (m : MeasurableSpace Ω) (P : @Measure Ω mΩ)
    (μ : ℕ → Ω → Measure X) (ν : Ω → Measure X)
    (hfinite : ∀ n ω, IsFiniteMeasureOnCompacts (μ n ω))
    (hmeas : ∀ n (f : C_c(X,ℝ)), Measurable[m] (fun ω => ∫ x, f x ∂μ n ω))
    (hν : ∀ᵐ ω ∂P, (ν ω).Regular)
    (hlim : ∀ᵐ ω ∂P, ∀ f : C_c(X,ℝ),
      Tendsto (fun n => ∫ x, f x ∂μ n ω) atTop (𝓝 (∫ x, f x ∂ν ω))) :
    ∃ η : Ω → Measure X, Measurable[m] η ∧
      (∀ ω, (η ω).Regular ∧ IsFiniteMeasureOnCompacts (η ω)) ∧ η =ᵐ[P] ν := by
  obtain ⟨η,hm,hr,he⟩ := exists_subsigma_radon_version_identified m μ hfinite hmeas
  refine ⟨η,hm,hr,?_⟩
  filter_upwards [hν,hlim] with ω hν hlim
  exact he ω (ν ω) hν hlim


end SLEExactGauge

end

end OAI
