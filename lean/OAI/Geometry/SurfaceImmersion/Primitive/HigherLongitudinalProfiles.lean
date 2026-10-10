import OAI.Geometry.SurfaceImmersion.Primitive.PeriodicCoefficientProfiles

namespace OAI

/-! The two remaining leading second derivative profiles, with constants
depending only on the displayed finite coefficient bounds. -/
noncomputable section
open scoped ContDiff
namespace ClosedSurfaceR4.PeriodicExpansion
open CovarianceCorrector
variable {A E : Type} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem mixed_profile_of_coefficients {F : A → E} (hF : ContDiff ℝ ∞ F)
    (U : ℕ → Family A E) (ℓ : A →L[ℝ] ℝ) (n : ℕ) {dx dy : A}
    (hx : ℓ dx = 1) (hy : ℓ dy = 0) {z C : ℝ} {p : A}
    (hz : 0 < z) (hz1 : z ≤ 1) (hC : 0 ≤ C)
    (hU : ∀ i < n+1, ‖(((U i).slow dx).slow dy).fastValue ℓ z p‖ ≤ C)
    (hA : ∀ i < n+1, ‖((U i).angle.slow dy).fastValue ℓ z p‖ ≤ C) :
    ‖directionalMap (directionalMap (finiteAnsatz F U ℓ (n+1) z) dx) dy p-
      (directionalMap (directionalMap F dx) dy p+((U 0).angle.slow dy).fastValue ℓ z p)‖ ≤
        (2*(n+1)*C)*z := by
  have he : directionalMap (directionalMap (finiteAnsatz F U ℓ (n+1) z) dx) dy p-
      (directionalMap (directionalMap F dx) dy p+((U 0).angle.slow dy).fastValue ℓ z p) =
      z • phaseSum (fun i => ((U i).slow dx).slow dy) ℓ (n+1) z p+
        (phaseSum (fun i => (U i).angle.slow dy) ℓ (n+1) z p-
          ((U 0).angle.slow dy).fastValue ℓ z p) := by
    rw [finiteAnsatz_second_transverse hF U ℓ (n+1) hz.ne' dx hy]
    simp only [hx,one_smul]
    abel
  rw [he]
  have hs := phaseSum_bound_of_coefficients (fun i => ((U i).slow dx).slow dy)
    ℓ (n+1) hz.le hz1 hC hU
  have ha := phaseSum_tail_bound_of_coefficients (fun i => (U i).angle.slow dy)
    ℓ n hz.le hz1 hC hA
  calc
    _ ≤ ‖z • phaseSum (fun i => ((U i).slow dx).slow dy) ℓ (n+1) z p‖+
        ‖phaseSum (fun i => (U i).angle.slow dy) ℓ (n+1) z p-
          ((U 0).angle.slow dy).fastValue ℓ z p‖ := norm_add_le _ _
    _ ≤ z*((n+1 : ℕ)*C)+(n*C)*z := by
      rw [norm_smul,Real.norm_eq_abs,abs_of_pos hz]
      exact add_le_add (mul_le_mul_of_nonneg_left hs hz.le) ha
    _ ≤ (2*(n+1)*C)*z := by
      push_cast
      nlinarith [mul_nonneg hC hz.le]

theorem scaled_longitudinal_profile_of_coefficients {F : A → E} (hF : ContDiff ℝ ∞ F)
    (U : ℕ → Family A E) (ℓ : A →L[ℝ] ℝ) (n : ℕ) {dx : A}
    (hx : ℓ dx = 1) {z C : ℝ} {p : A} (hz : 0 < z) (hz1 : z ≤ 1) (hC : 0 ≤ C)
    (hFxx : ‖directionalMap (directionalMap F dx) dx p‖ ≤ C)
    (hss : ∀ i < n+1, ‖(((U i).slow dx).slow dx).fastValue ℓ z p‖ ≤ C)
    (hsa : ∀ i < n+1, ‖((U i).slow dx).angle.fastValue ℓ z p‖ ≤ C)
    (has : ∀ i < n+1, ‖((U i).angle.slow dx).fastValue ℓ z p‖ ≤ C)
    (haa : ∀ i < n+1, ‖(U i).angle.angle.fastValue ℓ z p‖ ≤ C) :
    ‖z • directionalMap (directionalMap (finiteAnsatz F U ℓ (n+1) z) dx) dx p-
      (U 0).angle.angle.fastValue ℓ z p‖ ≤ (4*(n+1)*C)*z := by
  have hs := phaseSum_bound_of_coefficients (fun i => ((U i).slow dx).slow dx)
    ℓ (n+1) hz.le hz1 hC hss
  have ha := phaseSum_bound_of_coefficients (fun i => ((U i).slow dx).angle)
    ℓ (n+1) hz.le hz1 hC hsa
  have hb := phaseSum_bound_of_coefficients (fun i => (U i).angle.slow dx)
    ℓ (n+1) hz.le hz1 hC has
  have ht := phaseSum_tail_bound_of_coefficients (fun i => (U i).angle.angle)
    ℓ n hz.le hz1 hC haa
  simp only [Nat.cast_add,Nat.cast_one] at hs ha hb ht
  have hscaled : ‖z • phaseSum (fun i => ((U i).slow dx).slow dx) ℓ (n+1) z p‖ ≤ (n+1)*C := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos hz]
    exact (mul_le_mul_of_nonneg_left hs hz.le).trans
      (mul_le_of_le_one_left (mul_nonneg (show (0 : ℝ) ≤ (n : ℝ)+1 by positivity) hC) hz1)
  have hi : ‖directionalMap (directionalMap F dx) dx p+
      z • phaseSum (fun i => ((U i).slow dx).slow dx) ℓ (n+1) z p+
      phaseSum (fun i => ((U i).slow dx).angle) ℓ (n+1) z p+
      phaseSum (fun i => (U i).angle.slow dx) ℓ (n+1) z p‖ ≤ C+3*((n+1)*C) := by
    have hh := (norm_add_le _ _).trans (add_le_add
      ((norm_add_le _ _).trans (add_le_add
        ((norm_add_le _ _).trans (add_le_add hFxx hscaled)) ha)) hb)
    convert hh using 1
    ring
  have he : z • directionalMap (directionalMap (finiteAnsatz F U ℓ (n+1) z) dx) dx p-
      (U 0).angle.angle.fastValue ℓ z p =
      z • (directionalMap (directionalMap F dx) dx p+
        z • phaseSum (fun i => ((U i).slow dx).slow dx) ℓ (n+1) z p+
        phaseSum (fun i => ((U i).slow dx).angle) ℓ (n+1) z p+
        phaseSum (fun i => (U i).angle.slow dx) ℓ (n+1) z p)+
      (phaseSum (fun i => (U i).angle.angle) ℓ (n+1) z p-
        (U 0).angle.angle.fastValue ℓ z p) := by
    rw [finiteAnsatz_second_longitudinal hF U ℓ (n+1) hz.ne' hx]
    abel
  rw [he]
  calc
    _ ≤ ‖z • (directionalMap (directionalMap F dx) dx p+
        z • phaseSum (fun i => ((U i).slow dx).slow dx) ℓ (n+1) z p+
        phaseSum (fun i => ((U i).slow dx).angle) ℓ (n+1) z p+
        phaseSum (fun i => (U i).angle.slow dx) ℓ (n+1) z p)‖+
      ‖phaseSum (fun i => (U i).angle.angle) ℓ (n+1) z p-
        (U 0).angle.angle.fastValue ℓ z p‖ := norm_add_le _ _
    _ ≤ z*(C+3*((n+1)*C))+(n*C)*z := by
      rw [norm_smul,Real.norm_eq_abs,abs_of_pos hz]
      exact add_le_add (mul_le_mul_of_nonneg_left hi hz.le) ht
    _ = (4*(n+1)*C)*z := by ring

end ClosedSurfaceR4.PeriodicExpansion

end

end OAI
