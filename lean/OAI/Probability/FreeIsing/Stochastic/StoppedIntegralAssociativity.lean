import OAI.Probability.FreeIsing.Brownian.ContinuousAssociativity
import OAI.Probability.FreeIsing.Stochastic.RandomStoppedBrownianIntegral

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

namespace Problem367.StoppedIntegralAssociativity

open BrownianGrid BrownianIntegralProcess

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

theorem stoppedUniformSum_martingale [IsFiniteMeasure P]
    {M K : ℝ≥0 → Ω → ℝ} {F : Filtration ℝ≥0 mΩ}
    (hM : Martingale M F P) (hK : StronglyAdapted F K)
    {D : ℝ} (hbK : ∀ᵐ ω ∂P, ∀ t, |K t ω| ≤ D) (T : ℝ≥0) (n : ℕ) :
    Martingale (stoppedUniformSum M K T n) F P := by
  apply StoppedSimpleIntegral.finite_intervalSum_martingale hM (Finset.range n)
    (uniformGrid T n) (fun i => uniformGrid T n (i + 1))
    (fun i => K (uniformGrid T n i))
    (fun i _ => uniformGrid_mono T n (Nat.le_succ i))
    (fun i _ => hK _) (fun _ => D)
  intro i hi
  filter_upwards [hbK] with ω hω
  exact hω _

theorem stoppedUniformSum_memLp [IsFiniteMeasure P]
    {M K : ℝ≥0 → Ω → ℝ} {F : Filtration ℝ≥0 mΩ}
    (hM2 : ∀ t, MemLp (M t) 2 P) (hK : StronglyAdapted F K)
    {D : ℝ} (hbK : ∀ᵐ ω ∂P, ∀ t, |K t ω| ≤ D)
    (T : ℝ≥0) (n : ℕ) (t : ℝ≥0) :
    MemLp (stoppedUniformSum M K T n t) 2 P := by
  apply memLp_finsetSum
  intro i hi
  exact BrownianGrid.memLp_compose_of_bounded
    ((hM2 (min t (uniformGrid T n (i + 1)))).sub (hM2 (min t (uniformGrid T n i))))
    ((hK _).mono (F.le _)).aestronglyMeasurable (hbK.mono (fun ω hω => hω _))

theorem tendsto_stopped_outer_uniformSum [IsFiniteMeasure P]
    {M K J : ℝ≥0 → Ω → ℝ} {F : Filtration ℝ≥0 mΩ}
    (hM : Martingale M F P) (hM2 : ∀ t, MemLp (M t) 2 P)
    (hcM : ∀ᵐ ω ∂P, Continuous (fun t => M t ω))
    (hK : StronglyAdapted F K) {D : ℝ}
    (hbK : ∀ᵐ ω ∂P, ∀ t, |K t ω| ≤ D)
    (hJ : Martingale J F P) (hJ2 : ∀ t, MemLp (J t) 2 P)
    (hcJ : ∀ᵐ ω ∂P, Continuous (fun t => J t ω)) (T : ℝ≥0)
    (hlim : Tendsto (fun n => ∫ ω,
      (uniformSum M K T n ω - J T ω) ^ 2 ∂P) atTop (𝓝 0))
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime F τ) :
    Tendsto (fun n => ∫ ω,
      (uniformSum (stoppedProcess M τ) K T n ω - stoppedProcess J τ T ω) ^ 2 ∂P)
      atTop (𝓝 0) := by
  have hterminal : Tendsto (fun n => ∫ ω,
      (stoppedUniformSum M K T n T ω - J T ω) ^ 2 ∂P) atTop (𝓝 0) := by
    simpa only [stoppedUniformSum_terminal] using hlim
  have h := StoppedMartingaleL2.tendsto_stoppedProcess_meanSquare
    (N := fun n => stoppedUniformSum M K T n) (L := J) (t := T) (T := T)
    (fun n => stoppedUniformSum_martingale hM hK hbK T n) hJ
    (fun n t => stoppedUniformSum_memLp hM2 hK hbK T n t) hJ2
    (ae_continuous_stoppedUniformSum hcM T) hcJ (fun _ => τ) (fun _ => hτ)
    le_rfl hterminal
  have heq (n : ℕ) : stoppedProcess (stoppedUniformSum M K T n) τ T =
      uniformSum (stoppedProcess M τ) K T n := by
    have hfinite := RandomStoppedSimpleIntegral.stopped_finite_intervalSum
      (Finset.range n) M (fun i => K (uniformGrid T n i))
      (uniformGrid T n) (fun i => uniformGrid T n (i + 1)) τ
    have ht := congrArg (fun S => S T) hfinite
    change stoppedProcess (stoppedUniformSum M K T n) τ T =
      stoppedUniformSum (stoppedProcess M τ) K T n T at ht
    simpa only [stoppedUniformSum_terminal] using ht
  simpa only [heq] using h

theorem stopped_uniformSum_associativity
    {B H K I J : ℝ≥0 → Ω → ℝ} {F : Filtration ℝ≥0 mΩ}
    (hB : IsPreBrownianReal B P) (hAd : StronglyAdapted F B)
    (hind : ∀ s t, s ≤ t → Indep
      (MeasurableSpace.comap (fun ω => B t ω - B s ω) inferInstance) (F s) P)
    (hH : StronglyAdapted F H) (hK : StronglyAdapted F K)
    (hcK : ∀ᵐ ω ∂P, Continuous (fun t => K t ω))
    {C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hbH : ∀ᵐ ω ∂P, ∀ t, |H t ω| ≤ C)
    (hbK : ∀ᵐ ω ∂P, ∀ t, |K t ω| ≤ D)
    (hI : Martingale I F P) (hI2 : ∀ t, MemLp (I t) 2 P)
    (hcI : ∀ᵐ ω ∂P, Continuous (fun t => I t ω))
    (hJ : Martingale J F P) (hJ2 : ∀ t, MemLp (J t) 2 P)
    (hcJ : ∀ᵐ ω ∂P, Continuous (fun t => J t ω)) (T : ℝ≥0)
    (hIlim : Tendsto (fun n => ∫ ω,
      (uniformSum B H T n ω - I T ω) ^ 2 ∂P) atTop (𝓝 0))
    (hJlim : Tendsto (fun n => ∫ ω,
      (uniformSum B (fun t ω => K t ω * H t ω) T n ω - J T ω) ^ 2 ∂P)
      atTop (𝓝 0))
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime F τ) :
    Tendsto (fun n => ∫ ω,
      (uniformSum (stoppedProcess I τ) K T n ω - stoppedProcess J τ T ω) ^ 2 ∂P)
      atTop (𝓝 0) := by
  let : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  exact tendsto_stopped_outer_uniformSum hI hI2 hcI hK hbK hJ hJ2 hcJ T
    (BrownianContinuousAssociativity.uniformSum_associativity hB hAd hind hH hK hcK
      hC hD hbH hbK hI hI2 T hIlim (hJ2 T) hJlim) hτ

end Problem367.StoppedIntegralAssociativity

end

end OAI
