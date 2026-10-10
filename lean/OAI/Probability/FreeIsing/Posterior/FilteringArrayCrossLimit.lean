import OAI.Probability.FreeIsing.Posterior.FilteringCrossLimit

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology BigOperators

namespace Problem367.FilteringCrossEnergy

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

theorem integrable_posterior_mul_uniformSum [IsFiniteMeasure P]
    {F : Filtration ℝ≥0 mΩ} {W H : ℝ≥0 → Ω → ℝ}
    (hW : Martingale W F P) {Q : Ω → ℝ} {A D : ℝ}
    (hQb : ∀ᵐ ω ∂P, |Q ω| ≤ D)
    (hH : StronglyAdapted F H) (hHb : ∀ r, ∀ᵐ ω ∂P, |H r ω| ≤ A)
    (T : ℝ≥0) (n : ℕ) :
    Integrable (fun ω => P[Q | F T] ω * BrownianGrid.uniformSum W H T n ω) P := by
  simp only [BrownianGrid.uniformSum, BrownianGrid.integralSum, Finset.mul_sum]
  apply integrable_finsetSum
  intro i hi
  simpa only [mul_assoc] using
    integrable_posterior_weighted_increment hW hQb (hH (BrownianGrid.uniformGrid T n i))
      (hHb (BrownianGrid.uniformGrid T n i)) (t := BrownianGrid.uniformGrid T n (i + 1))
      (T := T)

theorem tendsto_posterior_sum_uniformSum_cross_energy [IsFiniteMeasure P]
    {ι : Type*} {F G : Filtration ℝ≥0 mΩ}
    {B m K : ι → ℝ≥0 → Ω → ℝ} {S : ι → Ω → ℝ} {Q : Ω → ℝ}
    (hB : ∀ i, Martingale (B i) G P) (hFG : ∀ r, F r ≤ G r)
    {A C : ι → ℝ} {D : ℝ}
    (hQ : StronglyMeasurable[G 0] Q) (hQb : ∀ᵐ ω ∂P, |Q ω| ≤ D)
    (hS : ∀ i, Integrable (S i) P) (hSb : ∀ i, ∀ᵐ ω ∂P, |S i ω| ≤ C i)
    (hX : ∀ i, StronglyAdapted F (fun r ω => B i r ω + (r : ℝ) * S i ω))
    (hm : ∀ i, IsStronglyProgressive F (m i))
    (hpost : ∀ i r, m i r =ᵐ[P] P[S i | F r])
    (hK : ∀ i, StronglyAdapted F (K i))
    (hKc : ∀ i, ∀ᵐ ω ∂P, Continuous (fun r => K i r ω))
    (hA : ∀ i, 0 ≤ A i) (hKb : ∀ i, ∀ᵐ ω ∂P, ∀ r, |K i r ω| ≤ A i)
    (hKversion : ∀ i r, K i r =ᵐ[P] fun ω =>
      P[(fun ω => Q ω * S i ω) | F r] ω - P[Q | F r] ω * m i r ω)
    (I : Finset ι) (T : ℝ≥0) :
    Tendsto (fun n : ℕ => ∫ ω, P[Q | F T] ω *
      (∑ i ∈ I, BrownianGrid.uniformSum (innovation (B i) (S i) (m i)) (K i) T n ω) ∂P)
      atTop (𝓝 (∑ i ∈ I, ∫ r in (0 : ℝ)..(T : ℝ),
        ∫ ω, K i r.toNNReal ω ^ 2 ∂P)) := by
  have hlim := tendsto_finsetSum I (fun i _ =>
    tendsto_posterior_uniformSum_cross_energy (hB i) hFG hQ hQb (hS i) (hSb i)
      (hX i) (hm i) (hpost i) (hK i) (hKc i) (hA i) (hKb i) (hKversion i) T)
  apply hlim.congr
  intro n
  rw [← integral_finsetSum I]
  · apply integral_congr_ae
    exact Eventually.of_forall fun ω => (Finset.mul_sum I _ _).symm
  · intro i hi
    exact integrable_posterior_mul_uniformSum
      (compensated_observation_martingale_of_bounded_signal (hB i) hFG (hS i)
        (hX i) (hm i) (hpost i) (C i) (hSb i))
      hQb (hK i) (fun r => (hKb i).mono (fun ω hω => hω r)) T n

end Problem367.FilteringCrossEnergy

end

end OAI
