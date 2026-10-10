import OAI.Probability.InvariantIsing.Cavity.CavityOrientedFamily
import OAI.Probability.InvariantIsing.Spectral.SpectralComparison

namespace OAI

/-! The spectral discretization squeeze for physical orthogonal pressure. -/

noncomputable section
open MeasureTheory ProbabilityTheory

namespace InvariantIsing

lemma cavity_meanPressure_squeeze {N : ℕ} (hN : 0 < N)
    (μ : Measure (Orthogonal N)) [IsProbabilityMeasure μ]
    (eig lo hi c : Fin N → ℝ) (δ K : ℝ)
    (heig : ∀ i, |eig i| ≤ K) (hlo : ∀ i, |lo i| ≤ K) (hhi : ∀ i, |hi i| ≤ K)
    (hl : ∀ i, lo i-δ ≤ eig i) (hu : ∀ i, eig i ≤ hi i+δ) :
    (∫ V, rotatedPressure lo (matrixRotation V⁻¹) c ∂μ)-δ/2 ≤
      ∫ V, rotatedPressure eig (matrixRotation V⁻¹) c ∂μ ∧
    (∫ V, rotatedPressure eig (matrixRotation V⁻¹) c ∂μ) ≤
      (∫ V, rotatedPressure hi (matrixRotation V⁻¹) c ∂μ)+δ/2 := by
  have hh := meanPressure_squeeze hN (cavityOrientedBaseLaw hN μ) eig lo hi c δ K heig hlo hhi hl hu
  simpa only [cavity_oriented_pressure] using hh

end InvariantIsing

end

end OAI
