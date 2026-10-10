import OAI.Geometry.SurfaceImmersion.Correction.PolynomialQuadraticTargets
import OAI.Geometry.SurfaceImmersion.Correction.PolynomialPhaseBounds

namespace OAI

/-! One constant controls every doubled and mixed polynomial phase. -/
noncomputable section
open scoped ContDiff BigOperators
namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open WeightedEstimates

theorem quadraticFamilyCoefficient_bound {n : ℕ} {ι : Type*}
    {U : Set Base} {O Q : Set LowJet}
    (hU : IsOpen U) (hO : IsOpen O) (hQ : IsCompact Q) (hQO : Q ⊆ O)
    (P : Fin n → Expression) (hP : ∀ l, (P l).SmoothCoeffs O)
    (m : ℕ) (B F : ℝ) (hB : 1 ≤ B) (hF : 0 ≤ F) :
    ∃ E : ℝ, 0 ≤ E ∧ ∀ (G : Base → Space) (φ : ι → Base → ℝ)
      (H : ι → Base → Fin 4 → ℂ) (s τ ε C : ℝ),
      0 < τ → 0 < s → τ ≤ s → s ≤ 1 → 0 ≤ ε → ε ≤ 1 → 0 < C →
      ContDiff ℝ ∞ G → (∀ i, ContDiff ℝ ∞ (φ i)) → (∀ i, ContDiff ℝ ∞ (H i)) →
      Set.MapsTo (lowJet G) U Q → WeightedBound U s (m + order P) B (lowJet G) →
      (∀ i, WeightedBound U s (m + order P) C (H i)) →
      (∀ i v, WeightedBound U s (m + order P) F
        (fun p => fderiv ℝ (φ i) p (coordinateVector v))) →
      ∀ (l : RealModes.QuadraticLabel ι), ∀ t ∈ Set.Icc (0 : ℝ) 1,
        WeightedBound U s m (E * ε * C ^ 2 / τ ^ loss P)
          (quadraticFamilyCoefficient P ε G φ H τ t l) := by
  obtain ⟨E, hE, he⟩ := quadraticPhaseCoefficient_bound hU hO hQ hQO P hP m B F hB hF
  refine ⟨E, hE, ?_⟩
  intro G φ H s τ ε C hτ hs hτs hs1 hε hε1 hC hG hφ hH hGQ hGb hHb hφb l t ht
  have hneg (i : ι) (v : Fin 2) : WeightedBound U s (m + order P) F
      (fun p => fderiv ℝ (fun x => -φ i x) p (coordinateVector v)) := by
    have hh := (hφb i v).neg hU.uniqueDiffOn
      (((hφ i).fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const).contDiffOn
    simpa only [fderiv_fun_neg, neg_apply] using hh
  rcases l with i | ⟨i,j,b⟩
  · simpa only [quadraticFamilyCoefficient, pow_two, mul_assoc] using
      he G (φ i) (φ i) (H i) (H i) s τ ε C C hτ hs hτs hs1 hε hε1 hC hC
        hG (hφ i) (hφ i) (hH i) (hH i) hGQ hGb (hHb i) (hHb i) (hφb i) (hφb i) t ht
  · cases b
    · simpa only [quadraticFamilyCoefficient, Bool.false_eq_true, ↓reduceIte, pow_two, mul_assoc] using
        he G (φ i) (φ j) (H i) (H j) s τ ε C C hτ hs hτs hs1 hε hε1 hC hC
          hG (hφ i) (hφ j) (hH i) (hH j) hGQ hGb (hHb i) (hHb j) (hφb i) (hφb j) t ht
    · simpa only [quadraticFamilyCoefficient, ↓reduceIte, pow_two, mul_assoc] using
        he G (φ i) (fun x => -φ j x) (H i) (starField (H j)) s τ ε C C hτ hs hτs hs1 hε hε1 hC hC
          hG (hφ i) (hφ j).neg (hH i) (starField_smooth (hH j)) hGQ hGb (hHb i)
          (weighted_starField hU.uniqueDiffOn hs hC.le (hH j) (hHb j)) (hφb i) (hneg j) t ht

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
