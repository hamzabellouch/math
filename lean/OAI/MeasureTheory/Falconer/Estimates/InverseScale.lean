import OAI.MeasureTheory.Falconer.Shells.DistanceInverse
import OAI.MeasureTheory.Falconer.Fourier.StationaryScales

namespace OAI

/-! # Arbitrary scale decay of the actual inverse remainder

One finite inverse order works uniformly at all large scales. Only the
ratio of the squared symbol scale to the oscillation parameter matters.
-/

namespace Falconer
open NormedSpace
open scoped ContDiff

theorem exists_displacement_inverse_order
    (hgnomonic : PublishedGnomonicSurface) (hquadratic : PublishedQuadraticStationary)
    (m : ℕ) {κ T : ℝ} (hκ : 0 < κ) :
    ∃ J : ℕ, ∃ A : ℝ, 0 ≤ A ∧ ∀ R D : ℝ, 1 ≤ R → 1 ≤ D → D ≤ R^2 →
      ∀ (z : Space (m+3)), z ≠ 0 →
      ‖normalize z-(gnomonicChart (0 : Space (m+2)) : Space (m+3))‖ ≤ 1/8 →
      ∀ B : Space (m+3) → ℂ, ContDiff ℝ ∞ B →
      ∀ C : ℝ, 0 ≤ C →
      (∀ j ≤ 2*(J+1)+(m+2)+1, ∀ w : Sphere (m+3),
        ‖iteratedFDeriv ℝ j B w‖ ≤ C*D^j) →
      ∀ r : ℝ, 1 ≤ r*‖z‖ → D^2/(r*‖z‖) ≤ R^(-κ) →
      ‖(((r*‖z‖)^(((m+2 : ℕ) : ℝ)/2) : ℝ) : ℂ)*inverseDisplacementSum m J r z B -
        Complex.exp (Complex.I*((r*‖z‖ : ℝ) : ℂ))*B (normalize z)‖ ≤ A*C*R^(-T) := by
  obtain ⟨L,hL,hscale⟩ := exists_stationary_remainder_order (m+1) (κ := κ) (T := T) hκ
  let J := L-1
  have hJL : J+1 = L := by dsimp [J]; omega
  obtain ⟨A,hA,hAb⟩ := displacement_inverse_expansion hgnomonic hquadratic m J
  refine ⟨J,A,hA,?_⟩
  intro R D hR hD hDu z hz he B hB C hC hb r hr hratio
  have hh := hAb z hz he B hB C D hC hD hb r hr
  have ht := hscale R D (r*‖z‖) hR (zero_le_one.trans hD)
    (zero_lt_one.trans_le hr) hDu hratio
  have hs : (r*‖z‖)^(-((J+1 : ℕ) : ℝ))*D^(2*(J+1)+(m+2)+1) ≤ R^(-T) := by
    simpa only [hJL,Real.rpow_neg_natCast,zpow_neg,zpow_natCast,inv_pow,
      Nat.add_assoc] using ht
  apply hh.trans
  calc
    _ = A*C*((r*‖z‖)^(-((J+1 : ℕ) : ℝ))*D^(2*(J+1)+(m+2)+1)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hs (mul_nonneg hA hC)

end Falconer

end OAI
