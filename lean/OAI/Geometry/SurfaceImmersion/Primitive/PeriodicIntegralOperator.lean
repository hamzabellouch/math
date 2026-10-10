import OAI.Geometry.SurfaceImmersion.Primitive.PeriodicCalculus
import OAI.Geometry.SurfaceImmersion.Geometry.CovarianceParameter

namespace OAI

/-! Bounded linear operators underlying normalized periodic integration. -/

noncomputable section
open MeasureTheory
open scoped ContDiff

namespace ClosedSurfaceR4.PeriodicIntegralOperator

open CovarianceCorrector PeriodicPrimitive

variable {E P : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup P] [NormedSpace ℝ P]

omit [NormedSpace ℝ E] [CompleteSpace E] in
lemma continuous_lift (f : C(Period, E)) :
    Continuous (fun x : ℝ => f (x : Period)) :=
  f.continuous.comp (AddCircle.continuous_mk' 1)

/-- Integration from zero to a fixed real time is bounded on the space of
continuous periodic functions, even when that time is outside one period. -/
def rawIntegral (x : ℝ) : C(Period, E) →L[ℝ] E :=
  ({ toFun := fun f => ∫ t in 0..x, f (t : Period)
     map_add' := fun f g => intervalIntegral.integral_add
       ((continuous_lift f).intervalIntegrable 0 x)
       ((continuous_lift g).intervalIntegrable 0 x)
     map_smul' := fun a f => intervalIntegral.integral_smul a _ } :
    C(Period, E) →ₗ[ℝ] E).mkContinuous |x| (by
      intro f
      have hn := intervalIntegral.norm_integral_le_of_norm_le_const
        (a := 0) (b := x) (fun t _ => f.norm_coe_le_norm (t : Period))
      change ‖∫ t in 0..x, f (t : Period)‖ ≤ |x| * ‖f‖
      simpa only [sub_zero, mul_comm] using hn)

omit [CompleteSpace E] in
@[simp] lemma rawIntegral_apply (x : ℝ) (f : C(Period, E)) :
    rawIntegral x f = rawPrimitive (fun t : ℝ => f (t : Period)) x := rfl

lemma rawIntegral_continuous (f : C(Period, E)) :
    Continuous (fun t => rawIntegral t f) :=
  rawPrimitive_continuous (continuous_lift f)

omit [CompleteSpace E] in
lemma rawIntegral_norm_unit (f : C(Period, E)) {x : ℝ} (hx : x ∈ Set.Icc 0 1) :
    ‖rawIntegral x f‖ ≤ ‖f‖ := by
  have hn := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := 0) (b := x) (fun t _ => f.norm_coe_le_norm (t : Period))
  change ‖∫ t in 0..x, f (t : Period)‖ ≤ _
  rw [sub_zero, abs_of_nonneg hx.1] at hn
  exact hn.trans (mul_le_of_le_one_right (norm_nonneg f) hx.2)

/-- The mean of the unnormalized primitive is also a bounded linear map. -/
def primitiveMean : C(Period, E) →L[ℝ] E :=
  ({ toFun := fun f => ∫ t in 0..1, rawIntegral t f
     map_add' := by
       intro f g
       simp only [map_add]
       exact intervalIntegral.integral_add
         ((rawIntegral_continuous f).intervalIntegrable 0 1)
         ((rawIntegral_continuous g).intervalIntegrable 0 1)
     map_smul' := by
       intro a f
       simp only [map_smul]
       exact intervalIntegral.integral_smul a _ } : C(Period, E) →ₗ[ℝ] E).mkContinuous 1 (by
      intro f
      have hn := intervalIntegral.norm_integral_le_of_norm_le_const
        (a := 0) (b := 1) (fun t ht => rawIntegral_norm_unit f (by
          rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
          exact ⟨ht.1.le, ht.2⟩))
      simpa using hn)

/-- The normalized primitive at a fixed time, with its linear dependence on
all periodic input data made explicit. -/
def normalizedIntegral (x : ℝ) : C(Period, E) →L[ℝ] E :=
  rawIntegral x - primitiveMean

@[simp] lemma normalizedIntegral_apply (x : ℝ) (f : C(Period, E)) :
    normalizedIntegral x f = primitive (fun t : ℝ => f (t : Period)) x := rfl

lemma normalizedIntegral_norm_unit (f : C(Period, E)) {x : ℝ} (hx : x ∈ Set.Icc 0 1) :
    ‖normalizedIntegral x f‖ ≤ 2 * ‖f‖ := by
  calc
    _ ≤ ‖rawIntegral x f‖ + ‖primitiveMean f‖ := norm_sub_le _ _
    _ ≤ ‖f‖ + ‖f‖ := add_le_add (rawIntegral_norm_unit f hx) (by
      have hm := (primitiveMean (E := E)).le_opNorm f
      have hb : ‖primitiveMean (E := E)‖ ≤ 1 := by
        apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
        intro g
        exact intervalIntegral.norm_integral_le_of_norm_le_const
          (fun t ht => rawIntegral_norm_unit g (by
            rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
            exact ⟨ht.1.le, ht.2⟩)) |>.trans_eq (by simp)
      simpa using hm.trans (mul_le_mul_of_nonneg_right hb (norm_nonneg f)))
    _ = _ := by ring

/-- Smooth dependence on an external parameter follows from the proved
bounded linear operator, with no parameter-differentiation assumption. -/
theorem contDiff_normalizedIntegral {F : P → C(Period, E)}
    (hF : ContDiff ℝ ∞ F) (x : ℝ) :
    ContDiff ℝ ∞ (fun p => normalizedIntegral x (F p)) :=
  (normalizedIntegral (E := E) x).contDiff.comp hF

theorem normalizedIntegral_fderiv {F : P → C(Period, E)} {p : P}
    (hF : DifferentiableAt ℝ F p) (x : ℝ) :
    fderiv ℝ (fun q => normalizedIntegral x (F q)) p =
      (normalizedIntegral x).comp (fderiv ℝ F p) :=
  ((normalizedIntegral (E := E) x).hasFDerivAt.comp p hF.hasFDerivAt).fderiv

end ClosedSurfaceR4.PeriodicIntegralOperator

end

end OAI
