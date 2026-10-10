import OAI.Geometry.RCD.Sobolev.LocalProbabilityGammaBound

namespace OAI

/-! # Compact cutoff masses and energies for a probability density -/

open Set Filter MeasureTheory
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) (Q : QuadraticCheegerEnergy μ)

omit [MetricSpace X] [BorelSpace X] [ProperSpace X] in
theorem probability_cutoff_mass (ρ φ : X → ℝ) (hρ : Measurable ρ)
    (hρ0 : ∀ x, 0 ≤ ρ x)
    [IsProbabilityMeasure (μ.withDensity (fun x => ENNReal.ofReal (ρ x)))]
    (hφ : ∀ x, φ x ∈ Icc (0:ℝ) 1) :
    (∫ x, φ x*ρ x ∂μ) ∈ Icc (0:ℝ) 1 := by
  refine ⟨integral_nonneg (fun x => mul_nonneg (hφ x).1 (hρ0 x)),?_⟩
  exact (le_abs_self _).trans (probability_density_pairing_bound μ hρ hρ0
    (Eventually.of_forall fun x => by rw [abs_of_nonneg (hφ x).1]; exact (hφ x).2))

omit [ProperSpace X] in
theorem local_probability_energy_bound {Ω : Set X} (hΩ : MeasurableSet Ω)
    (ρ φ : X → ℝ) (hρ : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x)
    [IsProbabilityMeasure (μ.withDensity (fun x => ENNReal.ofReal (ρ x)))]
    (hφ : ∀ x, φ x ∈ Icc (0:ℝ) 1) (hs : ∀ x ∉ Ω, φ x = 0)
    (u : SobolevSpace μ Q) {L : ℝ}
    (hL : ∀ᵐ x ∂μ.restrict Ω, SobolevSpace.minimalSlope μ Q u x ≤ L) :
    weightedGamma μ Q (fun x => φ x*ρ x) u u ∈ Icc (0:ℝ) (L^2) := by
  have he : weightedGamma μ Q (fun x => φ x*ρ x) u u =
      ∫ x, (φ x*localGamma μ Q u u x)*ρ x ∂μ := by
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by ring
  rw [he]
  constructor
  · apply integral_nonneg_of_ae
    filter_upwards [localGamma_self μ Q u] with x hx
    rw [hx]
    exact mul_nonneg (mul_nonneg (hφ x).1 (sq_nonneg _)) (hρ0 x)
  · apply (le_abs_self _).trans
    apply probability_density_pairing_bound μ hρ hρ0
    filter_upwards [(ae_restrict_iff' hΩ).mp hL,localGamma_self μ Q u,
      (Lp.coeFn_nonneg _).mpr (SobolevSpace.minimalSlope_nonneg μ Q u)] with x hl hg h0
    rw [hg,abs_of_nonneg (mul_nonneg (hφ x).1 (sq_nonneg _))]
    by_cases hx : x ∈ Ω
    · exact (mul_le_of_le_one_left (sq_nonneg _) (hφ x).2).trans
        (pow_le_pow_left₀ h0 (hl hx) 2)
    · rw [hs x hx,zero_mul]
      exact sq_nonneg L

end RegularPointCoordinates

end

end OAI
