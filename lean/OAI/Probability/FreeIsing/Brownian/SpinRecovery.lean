import OAI.Probability.FreeIsing.Gaussian.NoiseSlope
import OAI.Probability.FreeIsing.Spins.Recovery

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal

namespace Problem367.SpinRecovery

theorem decode_brownian_observations_ae {Ω V : Type*}
    [MeasurableSpace Ω] [Countable V] {μ : Measure Ω}
    (B : V → ℝ≥0 → Ω → ℝ) (hB : ∀ v, IsPreBrownianReal (B v) μ)
    (s : Ω → V → IsingSpin) :
    (fun ω => decodeArray (fun v (n : ℕ) =>
      (n : ℝ) * spinSign (s ω v) + B v n ω)) =ᵐ[μ] s := by
  apply decodeArray_ae_eq
  intro v
  exact ae_brownian_signal_recovery (B v) (hB v) (fun ω => spinSign (s ω v))

theorem map_decode_brownian_observations {Ω V : Type*}
    [MeasurableSpace Ω] [Countable V] {μ : Measure Ω}
    (B : V → ℝ≥0 → Ω → ℝ) (hB : ∀ v, IsPreBrownianReal (B v) μ)
    (s : Ω → V → IsingSpin) :
    Measure.map (fun ω => decodeArray (fun v (n : ℕ) =>
      (n : ℝ) * spinSign (s ω v) + B v n ω)) μ = Measure.map s μ :=
  Measure.map_congr (decode_brownian_observations_ae B hB s)

theorem hasFreeIsingLaw_decode_brownian_observations {Ω : Type*}
    [MeasurableSpace Ω] {μ : Measure Ω} {d : ℕ} {theta : ℝ}
    (B : TreeVertex d → ℝ≥0 → Ω → ℝ)
    (hB : ∀ v, IsPreBrownianReal (B v) μ)
    (s : Ω → TreeVertex d → IsingSpin)
    (hs : HasFreeIsingLaw theta (Measure.map s μ)) :
    HasFreeIsingLaw theta (Measure.map (fun ω => decodeArray (fun v (n : ℕ) =>
      (n : ℝ) * spinSign (s ω v) + B v n ω)) μ) := by
  rw [map_decode_brownian_observations B hB s]
  exact hs

theorem isFactorOfIID_of_observation_recovery {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {d : ℕ} {theta : ℝ}
    (U : Ω → TreeVertex d → ℝ) (hU : Measurable U)
    (hUlaw : Measure.map U μ = labelMeasure d)
    (s : Ω → TreeVertex d → IsingSpin)
    (hs : HasFreeIsingLaw theta (Measure.map s μ))
    (F : (TreeVertex d → ℝ) → TreeVertex d → ℕ → ℝ)
    (hF : Measurable F)
    (hFeq : ∀ g : TreeAut d, ∀ᵐ u ∂labelMeasure d,
      F (relabel g u) = relabel g (F u))
    (hrec : ∀ v, ∀ᵐ ω ∂μ,
      Tendsto (fun n : ℕ => F (U ω) v n / (n : ℝ))
        atTop (𝓝 (spinSign (s ω v)))) :
    IsFactorOfIID d theta := by
  let Phi := fun u => decodeArray (F u)
  have hPhi : Measurable Phi := measurable_decodeArray.comp hF
  refine ⟨Phi, hPhi, ?_, ?_⟩
  · have hmap : Measure.map Phi (labelMeasure d) =
        Measure.map (fun ω => decodeArray (F (U ω))) μ := by
      rw [← hUlaw, Measure.map_map hPhi hU]
      rfl
    rw [hmap, map_decodeArray_eq hrec]
    exact hs
  · intro g
    filter_upwards [hFeq g] with u hu
    change decodeArray (F (relabel g u)) = relabel g (decodeArray (F u))
    rw [hu, decodeArray_relabel]

end Problem367.SpinRecovery

end

end OAI
