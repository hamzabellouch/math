import OAI.Probability.FreeIsing.Energy.MixedCrossEnergyRiemann
import OAI.Probability.FreeIsing.Posterior.FilteringSimpleCrossEnergy

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology BigOperators
namespace Problem367.FilteringCrossEnergy

theorem tendsto_posterior_uniformSum_mixed_cross_energy
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {F G : Filtration ℝ≥0 mΩ} {B m H K : ℝ≥0 → Ω → ℝ}
    (hB : Martingale B G P) (hFG : ∀ r, F r ≤ G r)
    {Q S : Ω → ℝ} {A C D L : ℝ}
    (hQ : StronglyMeasurable[G 0] Q) (hQb : ∀ᵐ ω ∂P, |Q ω| ≤ D)
    (hS : Integrable S P) (hSb : ∀ᵐ ω ∂P, |S ω| ≤ C)
    (hX : StronglyAdapted F (fun r ω => B r ω + (r : ℝ) * S ω))
    (hm : IsStronglyProgressive F m) (hpost : ∀ r, m r =ᵐ[P] P[S | F r])
    (hH : StronglyAdapted F H) (hcH : ∀ ω, Continuous (fun r => H r ω))
    (hA : 0 ≤ A) (hbH : ∀ r ω, |H r ω| ≤ A)
    (hK : Measurable (Function.uncurry K)) (hL : 0 ≤ L)
    (hbK : ∀ r ω, |K r ω| ≤ L)
    (hKversion : ∀ r, K r =ᵐ[P] fun ω =>
      P[(fun ω => Q ω * S ω) | F r] ω - P[Q | F r] ω * m r ω)
    (T : ℝ≥0) :
    Tendsto (fun n : ℕ => ∫ ω, P[Q | F T] ω *
      BrownianGrid.uniformSum (innovation B S m) H T n ω ∂P) atTop
      (𝓝 (∫ r in (0 : ℝ)..(T : ℝ), ∫ ω, H r.toNNReal ω * K r.toNNReal ω ∂P)) := by
  have hlim := CrossEnergyRiemann.tendsto_mixed_cross_energy (P := P)
    (fun r => ((hH r).mono (F.le r)).measurable) hcH hK hA hL hbH hbK T
  apply hlim.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  have he := integral_posterior_mul_uniformSum hB hFG hQ hQb hS hSb hX hm hpost hH
    (fun r => Eventually.of_forall (hbH r)) T (show 0 < n from hn)
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
