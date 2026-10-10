import OAI.Probability.FreeIsing.Brownian.SpatialAssociativity
import OAI.Probability.FreeIsing.Stochastic.StoppedIntegralAssociativity

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

namespace Problem367.StoppedSpatialAssociativity

variable {Ω ι : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

theorem stopped_uniformSum_spatial_associativity [IsFiniteMeasure P]
    {F : Filtration ℝ≥0 mΩ} {B H I J : ι → ℝ≥0 → Ω → ℝ}
    {Y Z K : ℝ≥0 → Ω → ℝ}
    (hB : ∀ a, IsPreBrownianReal (B a) P)
    (hAd : ∀ a, StronglyAdapted F (B a))
    (hind : ∀ a s t, s ≤ t → Indep
      (MeasurableSpace.comap (fun ω => B a t ω - B a s ω) inferInstance) (F s) P)
    (hH : ∀ a, StronglyAdapted F (H a)) (hK : StronglyAdapted F K)
    (hcK : ∀ᵐ ω ∂P, Continuous (fun t => K t ω))
    {C : ι → ℝ} {D : ℝ} (hC : ∀ a, 0 ≤ C a) (hD : 0 ≤ D)
    (hbH : ∀ a, ∀ᵐ ω ∂P, ∀ t, |H a t ω| ≤ C a)
    (hbK : ∀ᵐ ω ∂P, ∀ t, |K t ω| ≤ D)
    (hI : ∀ a, Martingale (I a) F P) (hY : Martingale Y F P)
    (hI2 : ∀ a t, MemLp (I a t) 2 P) (hY2 : ∀ t, MemLp (Y t) 2 P)
    (hJ2 : ∀ a t, MemLp (J a t) 2 P)
    (hZ : Martingale Z F P) (hZ2 : ∀ t, MemLp (Z t) 2 P)
    (hcY : ∀ᵐ ω ∂P, Continuous (fun t => Y t ω))
    (hcZ : ∀ᵐ ω ∂P, Continuous (fun t => Z t ω))
    (T : ℝ≥0)
    (hsumI : HasSum (fun a => (hI2 a T).toLp (I a T)) ((hY2 T).toLp (Y T)))
    (hsumJ : HasSum (fun a => (hJ2 a T).toLp (J a T)) ((hZ2 T).toLp (Z T)))
    (hIlim : ∀ a, Tendsto (fun n => ∫ ω,
      (BrownianGrid.uniformSum (B a) (H a) T n ω - I a T ω) ^ 2 ∂P)
        atTop (𝓝 0))
    (hJlim : ∀ a, Tendsto (fun n => ∫ ω,
      (BrownianGrid.uniformSum (B a) (fun t ω => K t ω * H a t ω) T n ω -
        J a T ω) ^ 2 ∂P) atTop (𝓝 0))
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime F τ) :
    Tendsto (fun n => ∫ ω,
      (BrownianGrid.uniformSum (stoppedProcess Y τ) K T n ω -
        stoppedProcess Z τ T ω) ^ 2 ∂P) atTop (𝓝 0) := by
  have hglobal : Tendsto (fun n => ∫ ω,
      (BrownianGrid.uniformSum Y K T n ω - Z T ω) ^ 2 ∂P) atTop (𝓝 0) := by
    apply BrownianSpatialAssociativity.uniformSum_spatial_limit_of_channel_limits
      hI hY hI2 hY2 (fun a => hJ2 a T) (hZ2 T) hK hD
      (fun t => hbK.mono (fun ω hω => hω t)) T hsumI hsumJ
    intro a
    exact BrownianContinuousAssociativity.uniformSum_associativity
      (hB a) (hAd a) (hind a) (hH a) hK hcK (hC a) hD (hbH a) hbK
      (hI a) (hI2 a) T (hIlim a) (hJ2 a T) (hJlim a)
  exact StoppedIntegralAssociativity.tendsto_stopped_outer_uniformSum
    hY hY2 hcY hK hbK hZ hZ2 hcZ T hglobal hτ

end Problem367.StoppedSpatialAssociativity

end

end OAI
