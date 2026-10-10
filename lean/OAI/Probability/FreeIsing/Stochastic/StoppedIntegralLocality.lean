import OAI.Probability.FreeIsing.Brownian.SpatialAssociativity
import OAI.Probability.FreeIsing.Stochastic.StoppedIntegralAssociativity

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

namespace Problem367.StoppedIntegralLocality

variable {Ω : Type*}

theorem uniformSum_stopped_congr (M H K : ℝ≥0 → Ω → ℝ)
    (τ : Ω → WithTop ℝ≥0) (T : ℝ≥0) (n : ℕ) (ω : Ω)
    (hlocal : ∀ t : ℝ≥0, (t : WithTop ℝ≥0) ≤ τ ω → H t ω = K t ω) :
    BrownianGrid.uniformSum (stoppedProcess M τ) H T n ω =
      BrownianGrid.uniformSum (stoppedProcess M τ) K T n ω := by
  unfold BrownianGrid.uniformSum BrownianGrid.integralSum
  apply Finset.sum_congr rfl
  intro i hi
  dsimp only
  by_cases ht : (BrownianGrid.uniformGrid T n i : WithTop ℝ≥0) ≤ τ ω
  · rw [hlocal _ ht]
  · have ha : τ ω ≤ (BrownianGrid.uniformGrid T n i : WithTop ℝ≥0) :=
      le_of_not_ge ht
    have hab : (BrownianGrid.uniformGrid T n i : WithTop ℝ≥0) ≤
        (BrownianGrid.uniformGrid T n (i + 1) : WithTop ℝ≥0) := by
      exact_mod_cast BrownianGrid.uniformGrid_mono T n (Nat.le_succ i)
    rw [stoppedProcess_eq_of_ge ha, stoppedProcess_eq_of_ge (ha.trans hab)]
    simp only [sub_self, mul_zero]

variable [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]

theorem stopped_integral_eq_of_local_eq
    {F : Filtration ℝ≥0 mΩ} {M H K I J : ℝ≥0 → Ω → ℝ}
    (hM : Martingale M F P) (hM2 : ∀ t, MemLp (M t) 2 P)
    (hcM : ∀ᵐ ω ∂P, Continuous (fun t => M t ω))
    (hH : StronglyAdapted F H) (hK : StronglyAdapted F K)
    {C D : ℝ} (hbH : ∀ᵐ ω ∂P, ∀ t, |H t ω| ≤ C)
    (hbK : ∀ᵐ ω ∂P, ∀ t, |K t ω| ≤ D)
    (hI : Martingale I F P) (hJ : Martingale J F P)
    (hI2 : ∀ t, MemLp (I t) 2 P) (hJ2 : ∀ t, MemLp (J t) 2 P)
    (hcI : ∀ᵐ ω ∂P, Continuous (fun t => I t ω))
    (hcJ : ∀ᵐ ω ∂P, Continuous (fun t => J t ω))
    (T : ℝ≥0)
    (hIlim : Tendsto (fun n => ∫ ω,
      (BrownianGrid.uniformSum M H T n ω - I T ω) ^ 2 ∂P) atTop (𝓝 0))
    (hJlim : Tendsto (fun n => ∫ ω,
      (BrownianGrid.uniformSum M K T n ω - J T ω) ^ 2 ∂P) atTop (𝓝 0))
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime F τ)
    (hlocal : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, (t : WithTop ℝ≥0) ≤ τ ω → H t ω = K t ω) :
    stoppedProcess I τ T =ᵐ[P] stoppedProcess J τ T := by
  have hIs := StoppedMartingaleL2.memLp_stoppedProcess_two hI hI2 hcI hτ T
  have hJs := StoppedMartingaleL2.memLp_stoppedProcess_two hJ hJ2 hcJ hτ T
  have hMs (t : ℝ≥0) :=
    StoppedMartingaleL2.memLp_stoppedProcess_two hM hM2 hcM hτ t
  have hX (n : ℕ) : MemLp (BrownianGrid.uniformSum (stoppedProcess M τ) H T n) 2 P :=
    BrownianSpatialAssociativity.uniformSum_memLp hMs
      (fun t => ((hH t).mono (F.le t)).aestronglyMeasurable)
      (fun t => hbH.mono (fun ω hω => hω t)) T n
  have hi := StoppedIntegralAssociativity.tendsto_stopped_outer_uniformSum
    hM hM2 hcM hH hbH hI hI2 hcI T hIlim hτ
  have hj := StoppedIntegralAssociativity.tendsto_stopped_outer_uniformSum
    hM hM2 hcM hK hbK hJ hJ2 hcJ T hJlim hτ
  apply BrownianGrid.ae_eq_of_mean_square_limits hX hIs hJs hi
  apply hj.congr
  intro n
  apply integral_congr_ae
  filter_upwards [hlocal] with ω hω
  rw [uniformSum_stopped_congr M H K τ T n ω hω]

end Problem367.StoppedIntegralLocality

end

end OAI
