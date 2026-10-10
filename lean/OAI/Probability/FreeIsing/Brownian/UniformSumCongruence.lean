import OAI.Probability.FreeIsing.Brownian.IntegralTransport

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

namespace Problem367.BrownianGrid

theorem integralSum_congr_ae
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B B' : ℝ≥0 → Ω → ℝ} {t : ℕ → ℝ≥0} {H H' : ℕ → Ω → ℝ}
    (hB : ∀ i, B (t i) =ᵐ[P] B' (t i))
    (hH : ∀ i, H i =ᵐ[P] H' i) (n : ℕ) :
    integralSum B t H n =ᵐ[P] integralSum B' t H' n := by
  filter_upwards [ae_all_iff.mpr hB, ae_all_iff.mpr hH] with ω hωB hωH
  simp only [integralSum, hωB, hωH]

theorem uniformSum_congr_ae
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B B' H H' : ℝ≥0 → Ω → ℝ}
    (hB : ∀ t, B t =ᵐ[P] B' t) (hH : ∀ t, H t =ᵐ[P] H' t)
    (T : ℝ≥0) (n : ℕ) :
    uniformSum B H T n =ᵐ[P] uniformSum B' H' T n :=
  integralSum_congr_ae (fun i => hB (uniformGrid T n i))
    (fun i => hH (uniformGrid T n i)) n

theorem integral_uniformSum_sq_error_congr_ae
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B B' H H' : ℝ≥0 → Ω → ℝ} {I J : Ω → ℝ}
    (hB : ∀ t, B t =ᵐ[P] B' t) (hH : ∀ t, H t =ᵐ[P] H' t)
    (hIJ : I =ᵐ[P] J) (T : ℝ≥0) (n : ℕ) :
    (∫ ω, (uniformSum B H T n ω - I ω) ^ 2 ∂P) =
      ∫ ω, (uniformSum B' H' T n ω - J ω) ^ 2 ∂P := by
  apply integral_congr_ae
  filter_upwards [uniformSum_congr_ae hB hH T n, hIJ] with ω hω hωIJ
  rw [hω, hωIJ]

theorem uniform_meanSquare_limit_congr_ae
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B B' H H' : ℝ≥0 → Ω → ℝ} {I J : Ω → ℝ}
    (hB : ∀ t, B t =ᵐ[P] B' t) (hH : ∀ t, H t =ᵐ[P] H' t)
    (hIJ : I =ᵐ[P] J) (T : ℝ≥0)
    (hlim : Tendsto (fun n => ∫ ω, (uniformSum B H T n ω - I ω) ^ 2 ∂P)
      atTop (𝓝 0)) :
    Tendsto (fun n => ∫ ω, (uniformSum B' H' T n ω - J ω) ^ 2 ∂P)
      atTop (𝓝 0) := by
  exact hlim.congr' (Eventually.of_forall
    (integral_uniformSum_sq_error_congr_ae hB hH hIJ T))

theorem uniformSum_comp_congr_ae
    {Ω Ω' : Type*} [MeasurableSpace Ω'] {Q : Measure Ω'}
    (φ : Ω' → Ω) (B H : ℝ≥0 → Ω → ℝ)
    {B' H' : ℝ≥0 → Ω' → ℝ}
    (hB : ∀ t, B t ∘ φ =ᵐ[Q] B' t)
    (hH : ∀ t, H t ∘ φ =ᵐ[Q] H' t) (T : ℝ≥0) (n : ℕ) :
    uniformSum B H T n ∘ φ =ᵐ[Q] uniformSum B' H' T n :=
  uniformSum_congr_ae hB hH T n

theorem uniform_meanSquare_limit_comp_congr_ae
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {Q : Measure Ω'} {φ : Ω' → Ω}
    (hφ : MeasurePreserving φ Q P) (B H : ℝ≥0 → Ω → ℝ)
    {B' H' : ℝ≥0 → Ω' → ℝ} {I : Ω → ℝ} {J : Ω' → ℝ}
    (hB : ∀ t, B t ∘ φ =ᵐ[Q] B' t)
    (hH : ∀ t, H t ∘ φ =ᵐ[Q] H' t) (hIJ : I ∘ φ =ᵐ[Q] J)
    (T : ℝ≥0)
    (hX : ∀ n, AEStronglyMeasurable (uniformSum B H T n) P)
    (hI : AEStronglyMeasurable I P)
    (hlim : Tendsto (fun n => ∫ ω, (uniformSum B H T n ω - I ω) ^ 2 ∂P)
      atTop (𝓝 0)) :
    Tendsto (fun n => ∫ ω, (uniformSum B' H' T n ω - J ω) ^ 2 ∂Q)
      atTop (𝓝 0) := by
  apply uniform_meanSquare_limit_congr_ae
    (B := fun t => B t ∘ φ) (H := fun t => H t ∘ φ)
    (I := I ∘ φ) hB hH hIJ T
  change Tendsto (fun n => ∫ ω,
    (uniformSum B H T n (φ ω) - I (φ ω)) ^ 2 ∂Q) atTop (𝓝 0)
  exact meanSquare_limit_comp (X := fun n => uniformSum B H T n) (I := I)
    hφ hX hI hlim

end Problem367.BrownianGrid

end

end OAI
