import OAI.Geometry.SurfaceImmersion.Correction.PolynomialQuadraticTensorBounds
import OAI.Geometry.SurfaceImmersion.Correction.NormalizedPolynomialMean

namespace OAI

/-! Quadratic targets have size O(delta^2), with the polynomial contribution
retaining an eta factor when the input amplitudes have size delta * tau. -/
noncomputable section
open scoped ContDiff
namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open WeightedEstimates

lemma quadratic_product_scale {δ τ s ε E A : ℝ} {r p : ℕ}
    (hδ : 0 < δ) (hτ : 0 < τ) (hs : 0 < s) (hτ1 : τ ≤ 1)
    (hε : 0 ≤ ε) (hE : 0 ≤ E) (hA : 0 ≤ A) (hp : r ≤ p) :
    E * ε * (A * (δ * τ)) ^ 2 / τ ^ r ≤
      δ ^ 2 * (τ / s + ε / τ ^ p) * E * A ^ 2 := by
  have hh := normalized_product_scale hδ hτ hs hτ1 hε hE hA hA hp
  calc
    _ = δ ^ 2 * (δ⁻¹ ^ 2 * (E * ε * (A * (δ * τ)) * (A * (δ * τ)) / τ ^ r)) := by
      field_simp [hδ.ne']
    _ ≤ δ ^ 2 * ((τ / s + ε / τ ^ p) * E * A * A) :=
      mul_le_mul_of_nonneg_left hh (sq_nonneg δ)
    _ = _ := by ring

theorem scaled_quadraticFamilyTensor_bound {n : ℕ} {ι : Type*}
    {U : Set Base} {O Q : Set LowJet}
    (hU : IsOpen U) (hO : IsOpen O) (hQ : IsCompact Q) (hQO : Q ⊆ O)
    (P : Fin 3 → Fin n → Expression) (hP : ∀ k l, (P k l).SmoothCoeffs O)
    (m : ℕ) (B F : ℝ) (hB : 1 ≤ B) (hF : 0 ≤ F) :
    ∃ E : ℝ, 0 ≤ E ∧ ∀ (G : Base → Space) (φ : ι → Base → ℝ)
      (H : ι → Base → Fin 4 → ℂ) (s δ τ ε A : ℝ) (p : ℕ),
      0 < δ → 0 < τ → 0 < s → τ ≤ s → s ≤ 1 → 0 ≤ ε → ε ≤ 1 → 0 < A →
      tensorLoss P ≤ p → ContDiff ℝ ∞ G → (∀ i, ContDiff ℝ ∞ (φ i)) →
      (∀ i, ContDiff ℝ ∞ (H i)) → Set.MapsTo (lowJet G) U Q →
      WeightedBound U s (m + tensorOrder P) B (lowJet G) →
      (∀ i, WeightedBound U s (m + tensorOrder P) (A * (δ * τ)) (H i)) →
      (∀ i v, WeightedBound U s (m + tensorOrder P) F
        (fun x => fderiv ℝ (φ i) x (coordinateVector v))) →
      ∀ (l : RealModes.QuadraticLabel ι), ∀ t ∈ Set.Icc (0 : ℝ) 1,
        WeightedBound U s m (δ ^ 2 * (τ / s + ε / τ ^ p) * E * A ^ 2)
          (quadraticFamilyTensor P ε G φ H τ t l) := by
  obtain ⟨E, hE, he⟩ := quadraticFamilyTensor_bound (ι := ι) hU hO hQ hQO P hP m B F hB hF
  refine ⟨E, hE, ?_⟩
  intro G φ H s δ τ ε A p hδ hτ hs hτs hs1 hε hε1 hA hp hG hφ hH hGQ hGb hHb hφb l t ht
  exact (he G φ H s τ ε (A * (δ * τ)) hτ hs hτs hs1 hε hε1 (by positivity)
    hG hφ hH hGQ hGb hHb hφb l t ht).mono_const
      (quadratic_product_scale hδ hτ hs (hτs.trans hs1) hε hE hA.le hp)

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
