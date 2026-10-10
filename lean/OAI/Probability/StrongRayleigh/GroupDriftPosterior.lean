import OAI.Probability.StrongRayleigh.GroupDrift
import OAI.Probability.StrongRayleigh.PosteriorLimit

namespace OAI

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9

noncomputable section
open MeasureTheory Filter

namespace Problem336AdditiveD139

theorem groupDrift_ae_eq_condExp_of_finite_posteriors
    {Γ : Type u_1} {Ω : Type u_2} {T : Type u_3} [Group Γ] [Countable Γ] [DecidableEq Γ]
    [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    (μ : ProbabilityMeasure (Γ → Bool)) (X : Γ → Ω → ℝ)
    (Y : Γ → T → Ω → ℝ) (hY : ∀ j s, Measurable (Y j s))
    (t : ℝ) (endpoint : T)
    (hfinite : ∀ (i : Γ) (S : Finset Γ),
      (fun ω => finiteObservationDrift μ i S t (fun j => Y j endpoint ω)) =ᵐ[P]
        P[X i | PosteriorLimit.observationSpace Y (S : Set Γ)])
    (i : Γ) :
    (fun ω => groupDrift μ t (fun j => Y j endpoint ω) i) =ᵐ[P]
      P[X i | PosteriorLimit.observationSpace Y Set.univ] := by
  apply PosteriorLimit.limsup_ae_eq_full_observation_condExp
    Y hY (fun n => (translatedGroupExhaustion Γ i n : Set Γ))
  · intro n m hnm
    exact translatedGroupExhaustion_monotone Γ i hnm
  · intro j
    obtain ⟨N, hN⟩ := mem_translatedGroupExhaustion_eventually Γ i j
    exact ⟨N, hN N le_rfl⟩
  · exact fun n => hfinite i (translatedGroupExhaustion Γ i n)

theorem groupDrift_ae_all_eq_condExp_of_finite_posteriors
    {Γ : Type u_4} {Ω : Type u_5} {T : Type u_6} [Group Γ] [Countable Γ] [DecidableEq Γ]
    [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    (μ : ProbabilityMeasure (Γ → Bool)) (X : Γ → Ω → ℝ)
    (Y : Γ → T → Ω → ℝ) (hY : ∀ j s, Measurable (Y j s))
    (t : ℝ) (endpoint : T)
    (hfinite : ∀ (i : Γ) (S : Finset Γ),
      (fun ω => finiteObservationDrift μ i S t (fun j => Y j endpoint ω)) =ᵐ[P]
        P[X i | PosteriorLimit.observationSpace Y (S : Set Γ)]) :
    ∀ᵐ ω ∂P, ∀ i, groupDrift μ t (fun j => Y j endpoint ω) i =
      P[X i | PosteriorLimit.observationSpace Y Set.univ] ω := by
  exact ae_all_iff.mpr (groupDrift_ae_eq_condExp_of_finite_posteriors
    P μ X Y hY t endpoint hfinite)

theorem groupDrift_ae_eq_condExp_of_observed_posteriors
    {Γ : Type u_7} {Ω : Type u_8} {T : Type u_9} [Group Γ] [Countable Γ] [DecidableEq Γ]
    [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    (μ : ProbabilityMeasure (Γ → Bool)) (X : Γ → Ω → ℝ)
    (Y : Γ → T → Ω → ℝ) (hY : ∀ j s, Measurable (Y j s))
    (t : ℝ) (endpoint : T)
    (hfinite : ∀ (S : Finset Γ) (i : S),
      (fun ω => tiltMean (finiteMarginal μ S)
        (fun j : S => Y j.1 endpoint ω - t / 2) i) =ᵐ[P]
        P[X i.1 | PosteriorLimit.observationSpace Y (S : Set Γ)])
    (i : Γ) :
    (fun ω => groupDrift μ t (fun j => Y j endpoint ω) i) =ᵐ[P]
      P[X i | PosteriorLimit.observationSpace Y Set.univ] := by
  apply PosteriorLimit.limsup_ae_eq_full_observation_condExp
    Y hY (fun n => (translatedGroupExhaustion Γ i n : Set Γ))
  · intro n m hnm
    exact translatedGroupExhaustion_monotone Γ i hnm
  · intro j
    obtain ⟨N, hN⟩ := mem_translatedGroupExhaustion_eventually Γ i j
    exact ⟨N, hN N le_rfl⟩
  · intro n
    simpa only [finiteObservationDrift_eq_tiltMean_of_mem μ i
      (translatedGroupExhaustion Γ i n) (self_mem_translatedGroupExhaustion Γ i n)] using
      hfinite (translatedGroupExhaustion Γ i n)
        ⟨i, self_mem_translatedGroupExhaustion Γ i n⟩

end Problem336AdditiveD139

end

end OAI
