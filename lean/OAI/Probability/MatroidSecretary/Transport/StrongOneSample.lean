import OAI.Probability.MatroidProphet.Main

namespace OAI

/-!
# The stronger constant for the concrete one-sample rule

The introduction explicitly records the stronger `2⁻²⁹³` constant proved in
accounting.tex.  The root endpoint uses its announced `2⁻³¹⁰` constant.  This
supporting theorem exposes the stronger claim for the actual constructed rule,
without changing the endpoint or imposing moments on individual loop values.

The rule and initial seed law below depend only on the known labeled matroid.
The probability space, matching input laws, and full-seed-aware adversary are
supplied afterwards.  Feasibility is pointwise at every prefix and the reward
estimate uses only integrability of the actual offline optimum.
-/

namespace MatroidProphet

open MeasureTheory ProbabilityTheory

/-- The actual simulated source rule is feasible before any laws are chosen. -/
theorem source_one_sample_feasible {n : ℕ} (M : Matroid (Fin n))
    (hE : M.E = Set.univ) :
    Feasible M (sampleSimulation (completeHiddenRule M hE)) :=
  sampleSimulation_feasible M (completeHiddenRule M hE)
    (completeHiddenRule_feasible M hE)

/-- The source construction attains the stronger constant advertised after
`thm:main`, even when the order sees the complete initial seed.  This is a
consequence for the concrete rule, not a premise asserting its performance. -/
theorem source_one_sample_strong {n : ℕ} (M : Matroid (Fin n))
    (hE : M.E = Set.univ)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (S V : Ω → Weights n) (R : Ω → Seed (mainSeedBits n))
    (hS : Measurable S) (hV : Measurable V) (hR : Measurable R)
    (hSN : ∀ᵐ ω ∂μ, ∀ e, 0 ≤ S ω e)
    (hVN : ∀ᵐ ω ∂μ, ∀ e, 0 ≤ V ω e)
    (hi : iIndepFun (pairedCoordinates S V) μ)
    (hlaw : ∀ e, μ.map (fun ω => S ω e) = μ.map (fun ω => V ω e))
    (hseed : IndepFun (fun ω => (S ω, V ω)) R μ)
    (hRlaw : μ.map R = sourceSeedLaw n)
    (hopt : Integrable (fun ω => optimum M (V ω)) μ)
    (π : Ω → ArrivalOrder n) (hπ : Measurable π) :
    Integrable (fun ω =>
      reward (sampleSimulation (completeHiddenRule M hE))
        (R ω) (S ω) (V ω) (π ω)) μ ∧
      ((2 : ℝ) ^ 293)⁻¹ * (∫ ω, optimum M (V ω) ∂μ) ≤
        ∫ ω, reward (sampleSimulation (completeHiddenRule M hE))
          (R ω) (S ω) (V ω) (π ω) ∂μ :=
  oneSample_of_hidden M (completeHiddenRule M hE) (sourceSeedLaw n)
    (((2 : ℝ) ^ 293)⁻¹) (completeHiddenRule_feasible M hE)
    (complete_hidden_guarantee M hE) μ S V R hS hV hR hSN hVN
    hi hlaw hseed hRlaw hopt π hπ

end MatroidProphet

end OAI
