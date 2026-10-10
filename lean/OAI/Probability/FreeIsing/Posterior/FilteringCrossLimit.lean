import OAI.Probability.FreeIsing.Energy.CrossEnergyRiemann
import OAI.Probability.FreeIsing.Posterior.FilteringSimpleCrossEnergy

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology BigOperators

namespace Problem367.FilteringCrossEnergy

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

theorem tendsto_posterior_uniformSum_cross_energy [IsFiniteMeasure P]
    {F G : Filtration ℝ≥0 mΩ} {B m K : ℝ≥0 → Ω → ℝ}
    (hB : Martingale B G P) (hFG : ∀ r, F r ≤ G r)
    {Q S : Ω → ℝ} {A C D : ℝ}
    (hQ : StronglyMeasurable[G 0] Q) (hQb : ∀ᵐ ω ∂P, |Q ω| ≤ D)
    (hS : Integrable S P) (hSb : ∀ᵐ ω ∂P, |S ω| ≤ C)
    (hX : StronglyAdapted F (fun r ω => B r ω + (r : ℝ) * S ω))
    (hm : IsStronglyProgressive F m) (hpost : ∀ r, m r =ᵐ[P] P[S | F r])
    (hK : StronglyAdapted F K)
    (hKc : ∀ᵐ ω ∂P, Continuous (fun r => K r ω))
    (hA : 0 ≤ A) (hKb : ∀ᵐ ω ∂P, ∀ r, |K r ω| ≤ A)
    (hKversion : ∀ r, K r =ᵐ[P] fun ω =>
      P[(fun ω => Q ω * S ω) | F r] ω - P[Q | F r] ω * m r ω)
    (T : ℝ≥0) :
    Tendsto (fun n : ℕ => ∫ ω, P[Q | F T] ω *
      BrownianGrid.uniformSum (innovation B S m) K T n ω ∂P) atTop
      (𝓝 (∫ r in (0 : ℝ)..(T : ℝ), ∫ ω, K r.toNNReal ω ^ 2 ∂P)) := by
  have hlim := CrossEnergyRiemann.tendsto_cross_energy
    (fun r => (hK r).mono (F.le r) |>.aestronglyMeasurable) hKc hA hKb T
  apply hlim.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  have he := integral_posterior_mul_uniformSum hB hFG hQ hQb hS hSb hX hm hpost hK
    (fun r => hKb.mono (fun ω hω => hω r)) T (show 0 < n from hn)
  rw [he]
  apply Finset.sum_congr rfl
  intro i hi
  apply intervalIntegral.integral_congr
  intro r hr
  apply integral_congr_ae
  filter_upwards [hKversion r.toNNReal] with ω hω
  rw [hω]

end Problem367.FilteringCrossEnergy

end

end OAI
