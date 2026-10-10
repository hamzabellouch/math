import OAI.Geometry.RCD.Sobolev.GoodLaplacianCutoff
import OAI.Geometry.RCD.Sobolev.BochnerCutoffIdentity

namespace OAI

/-! # Comparing two local realizations of the same Bochner energy -/

open Set Metric MeasureTheory
open scoped NNReal InnerProductSpace BoundedContinuousFunction

noncomputable section
namespace RegularPointCoordinates

variable {X E F : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- Two local Bochner constructions have identical cutoff masses when
their energy densities agree on the cutoff region. This also compares
measures constructed on different finite dimensional spans. -/
theorem LocalHarmonicEnergy.cutoff_mass_eq
    {U : E →L[ℝ] SobolevSpace μ hQ} {V : F →L[ℝ] SobolevSpace μ hQ}
    {M : PositiveBilinearMeasure X E} {N : PositiveBilinearMeasure X F}
    {κ : ℝ} {p : X} {r ρ C : ℝ} {L H : ℝ≥0} {v : E} {w : F}
    (G : LocalHarmonicEnergy μ hQ U M κ p r L v)
    (G' : LocalHarmonicEnergy μ hQ V N κ p r H w)
    (χ : GoodLaplacianCutoff μ hQ p ρ C) (hρr : ρ < r)
    (heq : localGamma μ hQ (U v) (U v) =ᵐ[μ.restrict (ball p (2 * r))]
      localGamma μ hQ (V w) (V w)) :
    ⟪v, M.weightedOperator χ.weight v⟫_ℝ =
      ⟪w, N.weightedOperator χ.weight w⟫_ℝ := by
  have hs : tsupport (χ.weight : X → ℝ) ⊆ ball p (2 * r) := by
    intro x hx
    have hd : dist x p ≤ 2 * ρ := χ.tsupport_subset μ hQ hx
    change dist x p < 2 * r
    linarith
  have hq : ∀ᵐ x ∂μ, x ∉ ball p (2 * r) → χ.laplacian x = 0 := by
    filter_upwards [χ.laplacian_locality] with x hx hnot
    apply hx
    right
    have hd : 2 * r ≤ dist p x := by
      simpa only [mem_ball, dist_comm, not_lt] using hnot
    linarith
  have hG := G.test_cutoff μ hQ χ.weight (χ.hasCompactSupport μ hQ) hs
    χ.sobolev χ.representative χ.laplacian χ.weak_laplacian hq
  have hG' := G'.test_cutoff μ hQ χ.weight (χ.hasCompactSupport μ hQ) hs
    χ.sobolev χ.representative χ.laplacian χ.weak_laplacian hq
  have hqeq : (∫ x, localGamma μ hQ (U v) (U v) x * χ.laplacian x ∂μ) =
      ∫ x, localGamma μ hQ (V w) (V w) x * χ.laplacian x ∂μ := by
    apply integral_congr_ae
    filter_upwards [(ae_restrict_iff' measurableSet_ball).mp heq, hq] with x hx hqx
    by_cases hin : x ∈ ball p (2 * r)
    · rw [hx hin]
    · rw [hqx hin, mul_zero, mul_zero]
  have hχeq : (∫ x, χ.weight x * localGamma μ hQ (U v) (U v) x ∂μ) =
      ∫ x, χ.weight x * localGamma μ hQ (V w) (V w) x ∂μ := by
    apply integral_congr_ae
    filter_upwards [(ae_restrict_iff' measurableSet_ball).mp heq] with x hx
    by_cases hin : x ∈ ball p (2 * r)
    · rw [hx hin]
    · have hz : χ.weight x = 0 := by
        apply χ.zero
        have hd : 2 * r ≤ dist p x := by
          simpa only [mem_ball, dist_comm, not_lt] using hin
        linarith
      rw [hz, zero_mul, zero_mul]
  rw [hG, hG', hqeq, hχeq]

/-- Positivity turns equality of the cutoff masses into comparison on
nested balls. The full measures, including singular parts, are retained. -/
theorem LocalHarmonicEnergy.mass_le_of_same_energy
    {U : E →L[ℝ] SobolevSpace μ hQ} {V : F →L[ℝ] SobolevSpace μ hQ}
    {M : PositiveBilinearMeasure X E} {N : PositiveBilinearMeasure X F}
    {κ : ℝ} {p : X} {r ρ C : ℝ} {L H : ℝ≥0} {v : E} {w : F}
    (G : LocalHarmonicEnergy μ hQ U M κ p r L v)
    (G' : LocalHarmonicEnergy μ hQ V N κ p r H w)
    (χ : GoodLaplacianCutoff μ hQ p ρ C) (hρ : 0 < ρ) (hρr : ρ < r)
    (heq : localGamma μ hQ (U v) (U v) =ᵐ[μ.restrict (ball p (2 * r))]
      localGamma μ hQ (V w) (V w)) :
    ⟪v, M.massOperator (ball p ρ) v⟫_ℝ ≤
      ⟪w, N.massOperator (ball p (3 * ρ)) w⟫_ℝ := by
  have hlow := M.massOperator_le_weightedOperator χ.weight
    (fun x => (χ.bounds x).1) (ball p ρ) measurableSet_ball 1
    (fun x hx => (χ.one x hx).ge) v
  have hupp := N.weightedOperator_le_massOperator χ.weight
    (ball p (3 * ρ)) measurableSet_ball (fun x hx => by
      apply χ.zero
      have hd : 3 * ρ ≤ dist p x := by
        simpa only [mem_ball, dist_comm, not_lt] using hx
      linarith) 1 (fun x _ => (χ.bounds x).2) w
  rw [one_mul] at hlow hupp
  rw [G.cutoff_mass_eq μ hQ G' χ hρr heq] at hlow
  exact hlow.trans hupp

end RegularPointCoordinates

end

end OAI
