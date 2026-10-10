import OAI.MeasureTheory.Falconer.Angular.SphereInverse
import Mathlib.Analysis.Normed.Module.Normalize

namespace OAI

/-! # Inverse stationary phase for the original Euclidean displacement

The direction and oscillation parameter are exactly `z/‖z‖` and `r*‖z‖`.
No projected distance is substituted for the original distance.
-/

namespace Falconer
open Set Metric MeasureTheory NormedSpace
open scoped ContDiff

noncomputable def displacementDirection {d : ℕ} (z : Space d) (hz : z ≠ 0) : Sphere d :=
  ⟨normalize z,by rw [mem_sphere,dist_zero_right,norm_normalize hz]⟩

theorem sphereOscillation_displacement {d : ℕ} (r : ℝ) (z : Space d) (hz : z ≠ 0)
    (B : Sphere d → ℂ) :
    sphereOscillation (r*‖z‖) (displacementDirection z hz) B =
      ∫ w : Sphere d, Complex.exp (Complex.I*(r : ℂ)*(inner ℝ (w : Space d) z : ℂ))*B w
        ∂sphereMeasure d := by
  unfold sphereOscillation
  apply integral_congr_ae
  filter_upwards with w
  congr 2
  have hi : (r*‖z‖)*inner ℝ (w : Space d) (normalize z) = r*inner ℝ (w : Space d) z := by
    rw [mul_assoc,← real_inner_smul_right,norm_smul_normalize]
  have hc := congrArg (fun a : ℝ => (a : ℂ)) hi
  push_cast at hc
  push_cast
  change Complex.I*((r : ℂ)*(‖z‖ : ℂ))*(inner ℝ (w : Space d) (normalize z) : ℂ) = _
  calc
    _ = Complex.I*(((r : ℂ)*(‖z‖ : ℂ))*(inner ℝ (w : Space d) (normalize z) : ℂ)) := by ring
    _ = Complex.I*((r : ℂ)*(inner ℝ (w : Space d) z : ℂ)) := congrArg (fun a => Complex.I*a) hc
    _ = _ := by ring

noncomputable def inverseDisplacementSum (m J : ℕ) (r : ℝ) (z : Space (m+3))
    (B : Space (m+3) → ℂ) : ℂ :=
  ∑ j ∈ Finset.range (J+1), (((r*‖z‖)^(-(j : ℝ)) : ℝ) : ℂ)*
    ∫ w : Sphere (m+3), Complex.exp (Complex.I*(r : ℂ)*(inner ℝ (w : Space (m+3)) z : ℂ))*
      localInverseAmplitude m B j w ∂sphereMeasure (m+3)

theorem inverseSphereSum_displacement (m J : ℕ) (r : ℝ) (z : Space (m+3)) (hz : z ≠ 0)
    (B : Space (m+3) → ℂ) :
    inverseSphereSum m J (r*‖z‖) B (displacementDirection z hz) =
      inverseDisplacementSum m J r z B := by
  apply Finset.sum_congr rfl
  intro j _
  rw [sphereOscillation_displacement]

theorem displacement_inverse_expansion
    (hgnomonic : PublishedGnomonicSurface) (hquadratic : PublishedQuadraticStationary)
    (m J : ℕ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (z : Space (m+3)), z ≠ 0 →
      ‖normalize z-(gnomonicChart (0 : Space (m+2)) : Space (m+3))‖ ≤ 1/8 →
      ∀ B : Space (m+3) → ℂ, ContDiff ℝ ∞ B →
      ∀ C D : ℝ, 0 ≤ C → 1 ≤ D →
      (∀ j ≤ 2*(J+1)+(m+2)+1, ∀ w : Sphere (m+3),
        ‖iteratedFDeriv ℝ j B w‖ ≤ C*D^j) →
      ∀ r : ℝ, 1 ≤ r*‖z‖ →
      ‖(((r*‖z‖)^(((m+2 : ℕ) : ℝ)/2) : ℝ) : ℂ)*inverseDisplacementSum m J r z B -
        Complex.exp (Complex.I*((r*‖z‖ : ℝ) : ℂ))*B (normalize z)‖ ≤
        A*(r*‖z‖)^(-((J+1 : ℕ) : ℝ))*C*D^(2*(J+1)+(m+2)+1) := by
  obtain ⟨A,hA,hAb⟩ := sphere_inverse_expansion hgnomonic hquadratic m J
  refine ⟨A,hA,?_⟩
  intro z hz he B hB C D hC hD hb r hr
  have hh := hAb (displacementDirection z hz) he B hB C D hC hD hb (r*‖z‖) hr
  rw [inverseSphereSum_displacement] at hh
  exact hh

end Falconer

end OAI
