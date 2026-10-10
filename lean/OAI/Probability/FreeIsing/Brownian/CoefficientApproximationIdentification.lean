import OAI.Probability.FreeIsing.Brownian.ArrayCrossIsometry

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

namespace Problem367.BrownianFiltrationGrid

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} {F : Filtration ℝ≥0 mΩ}
    (hB : IsPreBrownianReal B P) (hAd : StronglyAdapted F B)
    (hind : ∀ s t, s ≤ t → Indep
      (MeasurableSpace.comap (fun ω => B t ω - B s ω) inferInstance) (F s) P)
    (K : ℕ → ℝ≥0 → Ω → ℝ) (H : ℝ≥0 → Ω → ℝ)
    (hK : ∀ n, StronglyAdapted F (K n)) (hH : StronglyAdapted F H)
    (hcK : ∀ n, ∀ᵐ ω ∂P, Continuous (fun t => K n t ω))
    (hcH : ∀ᵐ ω ∂P, Continuous (fun t => H t ω))
    (C : ℕ → ℝ) (D : ℝ) (hC : ∀ n, 0 ≤ C n) (hD : 0 ≤ D)
    (hbK : ∀ n, ∀ᵐ ω ∂P, ∀ t, |K n t ω| ≤ C n)
    (hbH : ∀ᵐ ω ∂P, ∀ t, |H t ω| ≤ D)
    (T : ℝ≥0) {X : ℕ → Ω → ℝ} {J : Ω → ℝ}
    (hX : ∀ n, MemLp (X n) 2 P) (hJ : MemLp J 2 P)
    (haX : ∀ n, Tendsto (fun k => ∫ ω,
      (BrownianGrid.uniformSum B (K n) T k ω - X n ω) ^ 2 ∂P) atTop (𝓝 0))
    (haJ : Tendsto (fun k => ∫ ω,
      (BrownianGrid.uniformSum B H T k ω - J ω) ^ 2 ∂P) atTop (𝓝 0))

include hB hAd hind hK hH hcK hcH hC hD hbK hbH hX hJ haX haJ

theorem tendsto_meanSquare_of_coefficient_interval
    (hcoeff : Tendsto (fun n => ∫ t in (0 : ℝ)..(T : ℝ), ∫ ω,
      (K n t.toNNReal ω - H t.toNNReal ω) ^ 2 ∂P) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ ω, (X n ω - J ω) ^ 2 ∂P) atTop (𝓝 0) := by
  have he (n : ℕ) := uniform_meanSquare_difference_isometry
    hB hAd hind (K n) H (hK n) hH (hcK n) hcH (hC n) hD
    (hbK n) hbH T (hX n) hJ (haX n) haJ
  simpa only [he] using hcoeff

theorem tendsto_meanSquare_of_coefficient_timeSpace
    (hInt : ∀ n, Integrable (fun p : ℝ × Ω =>
      (K n p.1.toNNReal p.2 - H p.1.toNNReal p.2) ^ 2)
      ((volume.restrict (Set.Ioc (0 : ℝ) (T : ℝ))).prod P))
    (hcoeff : Tendsto (fun n => ∫ p : ℝ × Ω,
      (K n p.1.toNNReal p.2 - H p.1.toNNReal p.2) ^ 2
      ∂(volume.restrict (Set.Ioc (0 : ℝ) (T : ℝ))).prod P) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ ω, (X n ω - J ω) ^ 2 ∂P) atTop (𝓝 0) := by
  let : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  apply tendsto_meanSquare_of_coefficient_interval hB hAd hind K H hK hH hcK hcH
    C D hC hD hbK hbH T hX hJ haX haJ
  have he (n : ℕ) :
      (∫ t in (0 : ℝ)..(T : ℝ), ∫ ω,
        (K n t.toNNReal ω - H t.toNNReal ω) ^ 2 ∂P) =
      ∫ p : ℝ × Ω, (K n p.1.toNNReal p.2 - H p.1.toNNReal p.2) ^ 2
        ∂(volume.restrict (Set.Ioc (0 : ℝ) (T : ℝ))).prod P := by
    rw [intervalIntegral.integral_of_le T.coe_nonneg]
    exact (integral_prod _ (hInt n)).symm
  simpa only [he] using hcoeff

theorem ae_eq_of_coefficient_timeSpace_approximation
    (hInt : ∀ n, Integrable (fun p : ℝ × Ω =>
      (K n p.1.toNNReal p.2 - H p.1.toNNReal p.2) ^ 2)
      ((volume.restrict (Set.Ioc (0 : ℝ) (T : ℝ))).prod P))
    (hcoeff : Tendsto (fun n => ∫ p : ℝ × Ω,
      (K n p.1.toNNReal p.2 - H p.1.toNNReal p.2) ^ 2
      ∂(volume.restrict (Set.Ioc (0 : ℝ) (T : ℝ))).prod P) atTop (𝓝 0))
    {I : Ω → ℝ} (hI : MemLp I 2 P)
    (hlimI : Tendsto (fun n => ∫ ω, (X n ω - I ω) ^ 2 ∂P) atTop (𝓝 0)) :
    I =ᵐ[P] J := by
  exact BrownianGrid.ae_eq_of_mean_square_limits hX hI hJ hlimI
    (tendsto_meanSquare_of_coefficient_timeSpace hB hAd hind K H hK hH hcK hcH
      C D hC hD hbK hbH T hX hJ haX haJ hInt hcoeff)

end Problem367.BrownianFiltrationGrid

end

end OAI
