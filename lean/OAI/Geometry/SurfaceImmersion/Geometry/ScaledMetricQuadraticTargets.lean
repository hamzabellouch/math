import OAI.Geometry.Immersion.ClosedSurface.QuadraticSupport

namespace OAI

/-! Metric quadratic coefficients have size delta squared when the
oscillatory amplitudes have size delta times their wavelength. -/
noncomputable section
open scoped ContDiff
namespace ClosedSurfaceR4.RealModes
open SmallModes WeightedEstimates

theorem scaled_quadraticAmplitude_bound {n : ℕ} {ι : Type*} {U : Set Base}
    (hU : IsOpen U) {φ : ι → Base → ℝ} {Z : ι → Field n}
    (hφ : ∀ i, ContDiffOn ℝ ∞ (φ i) U) (hZ : ∀ i, ContDiffOn ℝ ∞ (Z i) U)
    {s τ δ A P : ℝ} (hτ : 0 < τ) (hs : 0 < s) (hτs : τ ≤ s)
    (hδ : 0 ≤ δ) (hA : 0 ≤ A) (hP : 0 ≤ P) (m : ℕ)
    (hb : ∀ i, WeightedBound U s (m + 1) (A * (δ * τ)) (Z i))
    (hp : ∀ i v, ‖v‖ ≤ 1 → WeightedBound U s m P (coordDeriv v (φ i)))
    (l : QuadraticLabel ι) :
    WeightedBound U s m (δ ^ 2 * ((n : ℝ) * 2 ^ m * ((1 + 2 ^ m * P) * A) ^ 2))
      (quadraticAmplitude τ φ Z l) := by
  have hh (i j : ι) := weighted_phaseCrossTensor hU hτ hs hτs
    (show 0 ≤ A * (δ * τ) by positivity) (show 0 ≤ A * (δ * τ) by positivity) hP
    (hφ i) (hφ j) (hZ i) (hZ j) (hb i) (hb j) (hp i) (hp j)
  have he : (n : ℝ) * (2 ^ m * ((1 + 2 ^ m * P) * (A * (δ * τ)) / τ) *
      ((1 + 2 ^ m * P) * (A * (δ * τ)) / τ)) =
      δ ^ 2 * ((n : ℝ) * 2 ^ m * ((1 + 2 ^ m * P) * A) ^ 2) := by
    field_simp [hτ.ne']
  rcases l with i | ⟨i,j,b⟩
  · change WeightedBound U s m _ (phasePlusTensor τ (φ i) (φ i) (Z i) (Z i))
    simpa only [he] using (hh i i).1
  · cases b
    · simpa only [quadraticAmplitude, Bool.false_eq_true, ↓reduceIte, he] using (hh i j).1
    · simpa only [quadraticAmplitude, ↓reduceIte, he] using (hh i j).2

end ClosedSurfaceR4.RealModes

end

end OAI
