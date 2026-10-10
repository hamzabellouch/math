import OAI.MeasureTheory.Falconer.Estimates.RotatedInverse
import OAI.MeasureTheory.Falconer.Fourier.ScaledInverseIntegration

namespace OAI

/-! # The cell-scaled inverse in a fixed orthogonal angular frame

Only the angular variable changes. All spatial displacements, distance powers,
frequencies and endpoint laws in the separated formula are the original ones.
-/

namespace Falconer
open Set MeasureTheory NormedSpace
open scoped ContDiff

noncomputable def rotatedScaledWeightedInverseSum (m J : ℕ)
    (T : Space (m+3) ≃ₗᵢ[ℝ] Space (m+3)) (s r : ℝ)
    (z : Space (m+3)) (B : Space (m+3) → ℂ) : ℂ :=
  scaledWeightedInverseSum m J s r (T z) (B ∘ T.symm)

noncomputable def rotatedScaledInverseTerm (m j : ℕ)
    (T : Space (m+3) ≃ₗᵢ[ℝ] Space (m+3)) (s r : ℝ)
    (B : Space (m+3) → Space (m+3) → Space (m+3) → ℂ)
    (z : Space (m+3) × Space (m+3)) : ℂ :=
  (↑((dist z.1 z.2/s)^j)⁻¹ : ℂ) *
    ∫ w : Sphere (m+3),
      Complex.exp (Complex.I*((r*inner ℝ (w : Space (m+3)) (z.1-z.2) : ℝ) : ℂ))*
        rotatedInverseAmplitude m T (B z.1 z.2) j w ∂sphereMeasure (m+3)

theorem rotatedScaledWeightedInverseSum_eq_terms (m J : ℕ)
    (T : Space (m+3) ≃ₗᵢ[ℝ] Space (m+3)) (s r : ℝ)
    (B : Space (m+3) → Space (m+3) → Space (m+3) → ℂ)
    (z : Space (m+3) × Space (m+3)) :
    rotatedScaledWeightedInverseSum m J T s r (z.1-z.2) (B z.1 z.2) =
      ∑ j ∈ Finset.range (J+1),
        (((r*s)^(((m+2 : ℕ) : ℝ)/2)*((r*s)^j)⁻¹ : ℝ) : ℂ)*
          rotatedScaledInverseTerm m j T s r B z := by
  unfold rotatedScaledWeightedInverseSum scaledWeightedInverseSum rotatedScaledInverseTerm
  apply Finset.sum_congr rfl
  intro j _
  rw [← sphere_integral_rotation T]
  simp only [T.norm_map,dist_eq_norm,Complex.ofReal_mul,mul_assoc]
  congr 3
  apply integral_congr_ae
  filter_upwards with w
  simp only [sphereMap,T.inner_map_map,rotatedInverseAmplitude]

 theorem exists_rotated_scaled_weighted_inverse_order
    (hgnomonic : PublishedGnomonicSurface) (hquadratic : PublishedQuadraticStationary)
    (m : ℕ) {κ E : ℝ} (hκ : 0 < κ) :
    ∃ J : ℕ, ∃ A : ℝ, 0 ≤ A ∧ ∀ R D : ℝ, 1 ≤ R → 1 ≤ D → D ≤ R^2 →
      ∀ (T : Space (m+3) ≃ₗᵢ[ℝ] Space (m+3)) (z : Space (m+3)), z ≠ 0 →
      ‖T (normalize z)-(gnomonicChart (0 : Space (m+2)) : Space (m+3))‖ ≤ 1/8 →
      ∀ B : Space (m+3) → ℂ, ContDiff ℝ ∞ B →
      ∀ C : ℝ, 0 ≤ C →
      (∀ j ≤ 2*(J+1)+(m+2)+1, ∀ w : Sphere (m+3),
        ‖iteratedFDeriv ℝ j B w‖ ≤ C*D^j) →
      ∀ s r : ℝ, 0 < s → 1 ≤ r*‖z‖ → D^2/(r*‖z‖) ≤ R^(-κ) →
      ‖rotatedScaledWeightedInverseSum m J T s r z B -
          (((‖z‖/s)^(-(((m+2 : ℕ) : ℝ)/2)) : ℝ) : ℂ)*
            Complex.exp (Complex.I*((r*‖z‖ : ℝ) : ℂ))*B (normalize z)‖ ≤
        (‖z‖/s)^(-(((m+2 : ℕ) : ℝ)/2))*A*C*R^(-E) := by
  obtain ⟨J,A,hA,hi⟩ := exists_scaled_weighted_inverse_order hgnomonic hquadratic m (T := E) hκ
  refine ⟨J,A,hA,?_⟩
  intro R D hR hD hDR T z hz hnear B hB C hC hderiv s r hs hfreq hratio
  have hTz : T z ≠ 0 := by
    intro h
    exact hz (T.injective (h.trans T.map_zero.symm))
  have hb : ∀ j ≤ 2*(J+1)+(m+2)+1, ∀ w : Sphere (m+3),
      ‖iteratedFDeriv ℝ j (B ∘ T.symm) w‖ ≤ C*D^j := by
    intro j hj w
    rw [T.symm.norm_iteratedFDeriv_comp_right]
    exact hderiv j hj (sphereMap T.symm w)
  have he := hi R D hR hD hDR (T z) hTz
    (by simpa only [linearIsometryEquiv_normalize] using hnear)
    (B ∘ T.symm) (hB.comp T.symm.contDiff) C hC hb s r hs
    (by simpa only [T.norm_map] using hfreq) (by simpa only [T.norm_map] using hratio)
  simpa only [rotatedScaledWeightedInverseSum,T.norm_map,linearIsometryEquiv_normalize,
    Function.comp_apply,T.symm_apply_apply] using he

end Falconer

end OAI
