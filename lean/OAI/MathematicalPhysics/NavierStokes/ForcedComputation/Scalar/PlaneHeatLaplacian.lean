import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.PlaneHeatTransfer

namespace OAI

/-! Cartesian integration by parts for the Euclidean Gaussian. -/

noncomputable section
namespace ForcedComputation.PlaneHeat
open Real MeasureTheory Set Filter ShearFlows
open scoped Topology ContDiff

variable (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem integral_cartesian (f : Plane → F) (hf : Integrable f) :
    (∫ x, f x) = ∫ r : ℝ, ∫ s : ℝ, f ![r,s] := by
  have hi := (volume_preserving_finTwoArrow ℝ).symm.integrable_comp_of_integrable hf
  calc
    _ = ∫ z : ℝ × ℝ, f ![z.1,z.2] := by
      convert! (volume_preserving_finTwoArrow ℝ).symm.integral_comp' f |>.symm using 1
    _ = _ := by
      exact integral_prod _ hi

theorem integral_cartesian_symm (f : Plane → F) (hf : Integrable f) :
    (∫ x, f x) = ∫ s : ℝ, ∫ r : ℝ, f ![r,s] := by
  have hi := (volume_preserving_finTwoArrow ℝ).symm.integrable_comp_of_integrable hf
  calc
    _ = ∫ z : ℝ × ℝ, f ![z.1,z.2] := by
      convert! (volume_preserving_finTwoArrow ℝ).symm.integral_comp' f |>.symm using 1
    _ = _ := by
      exact integral_prod_symm _ hi

private theorem product_data_integrable (w v : ℝ → ℝ) (hw : Integrable w)
    (hv : Integrable v) (f : Plane → F) (hf : Continuous f)
    (C : ℝ) (hC : ∀ x, ‖f x‖ ≤ C) :
    Integrable (fun x : Plane => (w (x 0) * v (x 1)) • f x) :=
  (product_integrable w v hw hv).smul_bdd C hf.aestronglyMeasurable (ae_of_all _ hC)

/-- Integration by parts in the second Cartesian coordinate; hypotheses refer to
the actual one-variable slices of the data. -/
theorem integral_second_one {t : ℝ} (ht : 0 < t) {f f' f'' : Plane → F}
    (hf : Continuous f) (hf'' : Continuous f'')
    (hd : ∀ r s, HasDerivAt (fun y => f ![r,y]) (f' ![r,s]) s)
    (hdd : ∀ r s, HasDerivAt (fun y => f' ![r,y]) (f'' ![r,s]) s)
    (C D E : ℝ) (hC : ∀ x, ‖f x‖ ≤ C) (hD : ∀ x, ‖f' x‖ ≤ D)
    (hE : ∀ x, ‖f'' x‖ ≤ E) :
    (∫ x : Plane, (oneDim t (x 0) * oneDimSecond t (x 1)) • f x) =
      ∫ x : Plane, kernel t x • f'' x := by
  rw [integral_cartesian F _ (product_data_integrable F _ _ (oneDim_integrable ht)
    (oneDimSecond_integrable ht) f hf C hC)]
  change _ = ∫ x : Plane, (oneDim t (x 0) * oneDim t (x 1)) • f'' x
  rw [integral_cartesian F _ (product_data_integrable F _ _ (oneDim_integrable ht)
    (oneDim_integrable ht) f'' hf'' E hE)]
  apply integral_congr_ae
  exact ae_of_all _ fun r => by
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, mul_smul]
    rw [integral_smul, integral_smul]
    congr 1
    apply gaussian_second_integral_by_parts F ht (hd r) (hdd r)
      (hf''.comp (by fun_prop)) C D E
    · intro s; exact hC ![r,s]
    · intro s; exact hD ![r,s]
    · intro s; exact hE ![r,s]

theorem integral_second_zero {t : ℝ} (ht : 0 < t) {f f' f'' : Plane → F}
    (hf : Continuous f) (hf'' : Continuous f'')
    (hd : ∀ r s, HasDerivAt (fun y => f ![y,s]) (f' ![r,s]) r)
    (hdd : ∀ r s, HasDerivAt (fun y => f' ![y,s]) (f'' ![r,s]) r)
    (C D E : ℝ) (hC : ∀ x, ‖f x‖ ≤ C) (hD : ∀ x, ‖f' x‖ ≤ D)
    (hE : ∀ x, ‖f'' x‖ ≤ E) :
    (∫ x : Plane, (oneDimSecond t (x 0) * oneDim t (x 1)) • f x) =
      ∫ x : Plane, kernel t x • f'' x := by
  rw [integral_cartesian_symm F _ (product_data_integrable F _ _ (oneDimSecond_integrable ht)
    (oneDim_integrable ht) f hf C hC)]
  change _ = ∫ x : Plane, (oneDim t (x 0) * oneDim t (x 1)) • f'' x
  rw [integral_cartesian_symm F _ (product_data_integrable F _ _ (oneDim_integrable ht)
    (oneDim_integrable ht) f'' hf'' E hE)]
  apply integral_congr_ae
  exact ae_of_all _ fun s => by
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one,
      mul_comm _ (oneDim t s), mul_smul]
    rw [integral_smul, integral_smul]
    congr 1
    apply gaussian_second_integral_by_parts F ht (fun r => hd r s) (fun r => hdd r s)
      (hf''.comp (by fun_prop)) C D E
    · intro r; exact hC ![r,s]
    · intro r; exact hD ![r,s]
    · intro r; exact hE ![r,s]

end ForcedComputation.PlaneHeat

end

end OAI
