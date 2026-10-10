import OAI.Probability.InvariantIsing.Gaussian.GaussianGGBounds

namespace OAI

/-! Replica energy covariance with Haar-dependent observables and tests. -/

noncomputable section

open MeasureTheory IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

/-- Integrate the replica covariance estimate while allowing both the inserted
observable and the replica test to depend on the disorder. -/
theorem random_replica_energy_covariance_bound {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] [Countable X] [MeasurableSingletonClass X]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {ν : Ω → Measure X}
    [∀ ω, IsProbabilityMeasure (ν ω)] {H Y : Ω × X → ℝ} {r : ℕ}
    (D : Ω × (Fin (r + 1) → X) → ℝ) (hD : Measurable D)
    {c : ℝ} (hc : 0 ≤ c) (hDb : ∀ ω σ, |D (ω, σ)| ≤ c) (b : ℝ)
    (he : ∀ᵐ ω ∂μ, Integrable (fun x => Real.exp (H (ω, x))) (ν ω))
    (hY : ∀ᵐ ω ∂μ, Integrable (fun x => Y (ω, x))
      ((ν ω).tilted (fun x => H (ω, x))))
    (hU : Integrable (fun ω => referenceReplicaMean (ν ω) (fun x => H (ω, x))
      (fun σ => Y (ω, σ 0) * D (ω, σ))) μ)
    (hV : Integrable (fun ω => referenceReplicaMean (ν ω) (fun x => H (ω, x))
      (fun σ => D (ω, σ))) μ)
    (hE : Integrable (fun ω => ∫ x, |Y (ω, x) - b|
      ∂(ν ω).tilted (fun x => H (ω, x))) μ) :
    |(∫ ω, referenceReplicaMean (ν ω) (fun x => H (ω, x))
        (fun σ => Y (ω, σ 0) * D (ω, σ)) ∂μ) -
      b * (∫ ω, referenceReplicaMean (ν ω) (fun x => H (ω, x))
        (fun σ => D (ω, σ)) ∂μ)| ≤
      c * (∫ ω, ∫ x, |Y (ω, x) - b|
        ∂(ν ω).tilted (fun x => H (ω, x)) ∂μ) := by
  have hb : ∀ᵐ ω ∂μ,
      |referenceReplicaMean (ν ω) (fun x => H (ω, x))
          (fun σ => Y (ω, σ 0) * D (ω, σ)) -
        b * referenceReplicaMean (ν ω) (fun x => H (ω, x))
          (fun σ => D (ω, σ))| ≤
      c * (∫ x, |Y (ω, x) - b| ∂(ν ω).tilted (fun x => H (ω, x))) := by
    filter_upwards [he, hY] with ω hω hYω
    have : IsProbabilityMeasure ((ν ω).tilted (fun x => H (ω, x))) :=
      isProbabilityMeasure_tilted hω
    rw [referenceReplicaMean_eq_tilted _ _ hω, referenceReplicaMean_eq_tilted _ _ hω]
    exact replica_energy_covariance_bound hYω (fun σ => D (ω, σ))
      (hD.comp measurable_prodMk_left) hc (hDb ω) b
  rw [← integral_const_mul, ← integral_sub hU (hV.const_mul b)]
  exact abs_integral_le_integral_abs.trans
    ((integral_mono_ae (hU.sub (hV.const_mul b)).abs (hE.const_mul c) hb).trans_eq
      (integral_const_mul _ _))

end InvariantIsing

end

end OAI
