import OAI.Geometry.SurfaceImmersion.Primitive.PeriodicCoefficientProfiles

namespace OAI

/-! The longitudinal first derivative has a uniformly bounded oscillating
leading term and a remainder controlled by the actual coefficients. -/
noncomputable section
open scoped ContDiff
namespace ClosedSurfaceR4.PeriodicExpansion
open CovarianceCorrector
variable {A E : Type} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem longitudinal_profile_of_coefficients {F : A → E} (hF : ContDiff ℝ ∞ F)
    (U : ℕ → Family A E) (ℓ : A →L[ℝ] ℝ) (n : ℕ) {dx : A} (hx : ℓ dx = 1)
    {z C : ℝ} {p : A} (hz : 0 < z) (hz1 : z ≤ 1) (hC : 0 ≤ C)
    (hU : ∀ i < n+1, ‖((U i).slow dx).fastValue ℓ z p‖ ≤ C)
    (hA : ∀ i < n+1, ‖(U i).angle.fastValue ℓ z p‖ ≤ C) :
    ‖directionalMap (finiteAnsatz F U ℓ (n+1) z) dx p-
      (directionalMap F dx p+(U 0).angle.fastValue ℓ z p)‖ ≤ (2*(n+1)*C)*z := by
  have he : directionalMap (finiteAnsatz F U ℓ (n+1) z) dx p-
      (directionalMap F dx p+(U 0).angle.fastValue ℓ z p) =
      z • phaseSum (fun i => (U i).slow dx) ℓ (n+1) z p+
        (phaseSum (fun i => (U i).angle) ℓ (n+1) z p-(U 0).angle.fastValue ℓ z p) := by
    rw [finiteAnsatz_directional hF U ℓ (n+1) hz.ne' dx]
    simp only [hx,one_smul]
    abel
  rw [he]
  have hs := phaseSum_bound_of_coefficients (fun i => (U i).slow dx) ℓ (n+1) hz.le hz1 hC hU
  have ha := phaseSum_tail_bound_of_coefficients (fun i => (U i).angle) ℓ n hz.le hz1 hC hA
  calc
    _ ≤ ‖z • phaseSum (fun i => (U i).slow dx) ℓ (n+1) z p‖+
        ‖phaseSum (fun i => (U i).angle) ℓ (n+1) z p-(U 0).angle.fastValue ℓ z p‖ := norm_add_le _ _
    _ ≤ z*((n+1 : ℕ)*C)+(n*C)*z := by
      rw [norm_smul,Real.norm_eq_abs,abs_of_pos hz]
      exact add_le_add (mul_le_mul_of_nonneg_left hs hz.le) ha
    _ ≤ (2*(n+1)*C)*z := by
      push_cast
      nlinarith [mul_nonneg hC hz.le]

end ClosedSurfaceR4.PeriodicExpansion

end

end OAI
