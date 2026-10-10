import OAI.Probability.InvariantIsing.Cavity.CavityGeometricTail
import OAI.Probability.InvariantIsing.Magnetic.RestrictedFullTail

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped BigOperators Matrix MatrixOrder Matrix.Norms.L2Operator
namespace InvariantIsing

theorem restricted_full_geometric_tail {N n m d depth : ℕ}
    (S : Finset (Spin (N+n))) (hS : S.Nonempty)
    (μ : Measure (SpecialOrthogonal (N + n))) [IsProbabilityMeasure μ]
    (T : LabeledTree depth) (eig : Fin (N + n) → ℝ) (g : Fin (N + n) → Fin m)
    (u : ℕ → ℝ)
    {M₀ : ℝ} (hmean : restrictedCavityFullDisorderTest S hS μ T eig (cavitySpectralGroup g) u
      (cavityProjectionAxesTest (cavitySpectralGroup g) (Fin.natAdd N)) ≤ M₀)
    (B : SpecialOrthogonal (N + n) → Matrix (Fin (m * n)) (Fin d) ℝ)
    (hmB : Measurable B) (hB : ∀ U, (B U).transpose * B U = 1)
    (good : Set (SpecialOrthogonal (N + n))) (hgood : MeasurableSet good)
    {L R : ℝ} (hL : 0 < L) (hR : 0 < R)
    (hbound : ∀ U ∈ good, ∀ a,
      ‖(CFC.sqrt (cavityCompressionGrams g (cavitySpecialOrthogonal U) a))⁻¹‖ ≤ L) :
    restrictedCavityFullDisorderTest S hS μ T eig (cavitySpectralGroup g) u
      (fun U σ => if R < ‖cavityFullSpecialCoordinates g (B U) U (σ 0).1‖ then 1 else 0) ≤
    μ.real goodᶜ + L ^ 2 * M₀ / R ^ 2 := by
  let y := fun (U : SpecialOrthogonal (N + n))
    (σ : Fin 2 → Spin (N + n) × LabeledLeaf depth) =>
      cavityFullSpecialCoordinates g (B U) U (σ 0).1
  have hmy : Measurable (Function.uncurry y) := by
    apply measurable_from_prod_countable_left
    intro σ
    exact measurable_cavityFullSpecialCoordinates g B hmB (σ 0).1
  have hgeom : ∀ U ∈ good, ∀ σ,
      (L ^ 2)⁻¹ * ‖y U σ‖ ^ 2 ≤
        cavityProjectionAxesTest (cavitySpectralGroup g) (Fin.natAdd N) U σ := by
    intro U hU σ
    have h := cavity_full_special_coordinates_control g (B U) (hB U) U (σ 0).1 hL.le (hbound U hU)
    have he : (∑ a, ∑ j : Fin n,
        (cavitySpectralProjection (specialRotation U) (cavitySpectralGroup g a)
          (spinVector (σ 0).1) (Fin.natAdd N j)) ^ 2) =
        cavityProjectionAxesTest (cavitySpectralGroup g) (Fin.natAdd N) U σ := by
      exact (Fintype.sum_prod_type (fun t : Fin m × Fin n =>
        (cavitySpectralProjection (specialRotation U) (cavitySpectralGroup g t.1)
          (spinVector (σ 0).1) (Fin.natAdd N t.2)) ^ 2)).symm
    rw [he] at h
    exact (inv_mul_le_iff₀ (sq_pos_of_pos hL)).mpr h
  have ht := restricted_full_tail_probability S hS μ T eig (cavitySpectralGroup g) u
    (Fin.natAdd N) hmean good hgood y hmy (inv_pos.mpr (sq_pos_of_pos hL)) hR hgeom
  have hid : M₀ / ((L ^ 2)⁻¹ * R ^ 2) =
      L ^ 2 * M₀ / R ^ 2 := by
    field_simp
  simpa only [hid, y] using ht

end InvariantIsing

end

end OAI
