import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Integral.Pi
import OAI.NumberTheory.Catalan.Determinants.RealRowAmplitude
import OAI.NumberTheory.Catalan.Estimates.RealEnergyDiagonal
import OAI.NumberTheory.Catalan.Polynomial.MixedPolynomial
import OAI.NumberTheory.Catalan.Polynomial.ZetaPolynomial

namespace OAI

noncomputable section

namespace InternalCatalan

open MeasureTheory Set

def realPlaceMeasure : Measure ℝ :=
  (volume.restrict (Ioo (-1 : ℝ) 1)).withDensity
    (fun t => ENNReal.ofReal (|t| / Real.sqrt (1 - t ^ 2)))

private theorem realPlaceWeight_nonneg (t : ℝ) :
    0 ≤ |t| / Real.sqrt (1 - t ^ 2) :=
  div_nonneg (abs_nonneg _) (Real.sqrt_nonneg _)

private theorem measurable_realPlaceDensity :
    Measurable (fun t : ℝ => ENNReal.ofReal (|t| / Real.sqrt (1 - t ^ 2))) := by
  fun_prop

theorem integrable_realPlaceMeasure_iff (f : ℝ → ℝ) :
    Integrable f realPlaceMeasure ↔
      Integrable (fun t => (|t| / Real.sqrt (1 - t ^ 2)) * f t)
        (volume.restrict (Ioo (-1 : ℝ) 1)) := by
  simpa only [realPlaceMeasure, ENNReal.toReal_ofReal (realPlaceWeight_nonneg _),
    smul_eq_mul] using
    (integrable_withDensity_iff_integrable_smul' measurable_realPlaceDensity
      (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)) (g := f))

theorem integral_realPlaceMeasure (f : ℝ → ℝ) :
    (∫ t, f t ∂realPlaceMeasure) =
      ∫ t in Ioo (-1 : ℝ) 1, (|t| / Real.sqrt (1 - t ^ 2)) * f t := by
  simpa only [realPlaceMeasure, ENNReal.toReal_ofReal (realPlaceWeight_nonneg _),
    smul_eq_mul] using
    (integral_withDensity_eq_integral_toReal_smul measurable_realPlaceDensity
      (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)) f)

theorem realPlaceMeasure_univ : realPlaceMeasure univ = 2 := by
  have hi : Integrable (fun t : ℝ => |t| / Real.sqrt (1 - t ^ 2))
      (volume.restrict (Ioo (-1 : ℝ) 1)) := by
    have h := (intervalIntegrable_iff_integrableOn_Ioo_of_le
      (show (-1 : ℝ) ≤ 1 by norm_num)).mp (intervalIntegrable_scalarMoment 0)
    change Integrable (fun t : ℝ => t ^ 0 * (|t| / Real.sqrt (1 - t ^ 2)))
      (volume.restrict (Ioo (-1 : ℝ) 1)) at h
    simpa only [pow_zero, one_mul] using h
  have hv : (∫ t in Ioo (-1 : ℝ) 1, |t| / Real.sqrt (1 - t ^ 2)) = 2 := by
    simpa only [scalarMoment, pow_zero, one_mul,
      intervalIntegral.integral_of_le (show (-1 : ℝ) ≤ 1 by norm_num),
      integral_Ioc_eq_integral_Ioo] using scalarMoment_zero
  rw [realPlaceMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal hi
      (Filter.Eventually.of_forall realPlaceWeight_nonneg), hv]
  norm_num

instance : IsFiniteMeasure realPlaceMeasure where
  measure_univ_lt_top := by rw [realPlaceMeasure_univ]; norm_num

theorem integrable_realPlaceMeasure_prod_iff (f : ℝ × ℝ → ℝ) :
    Integrable f (realPlaceMeasure.prod (volume.restrict (Ioo (0 : ℝ) 1))) ↔
      Integrable (fun p => (|p.1| / Real.sqrt (1 - p.1 ^ 2)) * f p)
        ((volume.restrict (Ioo (-1 : ℝ) 1)).prod
          (volume.restrict (Ioo (0 : ℝ) 1))) := by
  unfold realPlaceMeasure
  rw [prod_withDensity_left measurable_realPlaceDensity]
  have hm : Measurable (fun p : ℝ × ℝ =>
      ENNReal.ofReal (|p.1| / Real.sqrt (1 - p.1 ^ 2))) :=
    measurable_realPlaceDensity.comp measurable_fst
  simpa only [ENNReal.toReal_ofReal (realPlaceWeight_nonneg _), smul_eq_mul] using
    (integrable_withDensity_iff_integrable_smul' hm
      (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)) (g := f))

theorem integral_realPlaceMeasure_prod (f : ℝ × ℝ → ℝ) :
    (∫ p, f p ∂realPlaceMeasure.prod (volume.restrict (Ioo (0 : ℝ) 1))) =
      ∫ p, (|p.1| / Real.sqrt (1 - p.1 ^ 2)) * f p
        ∂(volume.restrict (Ioo (-1 : ℝ) 1)).prod
          (volume.restrict (Ioo (0 : ℝ) 1)) := by
  unfold realPlaceMeasure
  rw [prod_withDensity_left measurable_realPlaceDensity]
  have hm : Measurable (fun p : ℝ × ℝ =>
      ENNReal.ofReal (|p.1| / Real.sqrt (1 - p.1 ^ 2))) :=
    measurable_realPlaceDensity.comp measurable_fst
  simpa only [ENNReal.toReal_ofReal (realPlaceWeight_nonneg _), smul_eq_mul] using
    (integral_withDensity_eq_integral_toReal_smul hm
      (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)) f)

section

open MeasureTheory Set Real

private theorem realCoordinateInv_deriv_nonneg {x : ℝ}
    (hx : x ∈ Ioo (-1 : ℝ) 1) :
    0 ≤ 2 * (1 - x ^ 2) / (1 + x ^ 2) ^ 2 := by
  have hp := mul_pos (sub_pos.mpr hx.2) (show (0 : ℝ) < 1 + x by linarith [hx.1])
  have hr : 0 < 1 - x ^ 2 := by nlinarith only [hp]
  exact div_nonneg (mul_nonneg (by norm_num) hr.le) (sq_nonneg _)

private theorem realCoordinate_weighted_comp (f : ℝ → ℝ) {x : ℝ}
    (hx : x ∈ Ioo (-1 : ℝ) 1) :
    ((|realCoordinateInv x| / sqrt (1 - realCoordinateInv x ^ 2)) *
      f (realCoordinateInv x)) * (2 * (1 - x ^ 2) / (1 + x ^ 2) ^ 2) =
        (4 * |x| / (1 + x ^ 2) ^ 2) * f (realCoordinateInv x) := by
  calc
    _ = ((|realCoordinateInv x| / sqrt (1 - realCoordinateInv x ^ 2)) *
      (2 * (1 - x ^ 2) / (1 + x ^ 2) ^ 2)) * f (realCoordinateInv x) := by ring
    _ = _ := by rw [realCoordinate_weight_jacobian hx]

theorem integral_realPlaceMeasure_coordinate (f : ℝ → ℝ) :
    (∫ t, f t ∂realPlaceMeasure) =
      ∫ x in Ioo (-1 : ℝ) 1,
        (4 * |x| / (1 + x ^ 2) ^ 2) * f (realCoordinateInv x) := by
  let g : ℝ → ℝ := fun t => (|t| / sqrt (1 - t ^ 2)) * f t
  have hsub := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
    (a := (-1 : ℝ)) (b := 1) (f := realCoordinateInv)
    (f' := fun x => 2 * (1 - x ^ 2) / (1 + x ^ 2) ^ 2) (g := g)
    continuous_realCoordinateInv.continuousOn (fun x _ => hasDerivAt_realCoordinateInv x)
    (by
      intro x hx
      apply realCoordinateInv_deriv_nonneg
      simpa only [min_eq_left (show (-1 : ℝ) ≤ 1 by norm_num),
        max_eq_right (show (-1 : ℝ) ≤ 1 by norm_num)] using hx)
  have he0 : realCoordinateInv (-1) = -1 := by norm_num [realCoordinateInv]
  have he1 : realCoordinateInv 1 = 1 := by norm_num [realCoordinateInv]
  rw [he0, he1] at hsub
  rw [integral_realPlaceMeasure]
  calc
    _ = ∫ t in (-1 : ℝ)..1, g t := by
      simp only [g, intervalIntegral.integral_of_le (show (-1 : ℝ) ≤ 1 by norm_num),
        integral_Ioc_eq_integral_Ioo]
    _ = ∫ x in (-1 : ℝ)..1,
        g (realCoordinateInv x) * (2 * (1 - x ^ 2) / (1 + x ^ 2) ^ 2) := hsub.symm
    _ = ∫ x in (-1 : ℝ)..1,
        (4 * |x| / (1 + x ^ 2) ^ 2) * f (realCoordinateInv x) := by
      apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
      intro x hx
      exact realCoordinate_weighted_comp f hx
    _ = _ := by
      rw [intervalIntegral.integral_of_le (show (-1 : ℝ) ≤ 1 by norm_num),
        integral_Ioc_eq_integral_Ioo]

theorem integrable_realPlaceMeasure_coordinate_iff (f : ℝ → ℝ) :
    Integrable f realPlaceMeasure ↔
      Integrable (fun x : ℝ => (4 * |x| / (1 + x ^ 2) ^ 2) * f (realCoordinateInv x))
        (volume.restrict (Ioo (-1 : ℝ) 1)) := by
  rw [integrable_realPlaceMeasure_iff]
  let g : ℝ → ℝ := fun t => (|t| / sqrt (1 - t ^ 2)) * f t
  have hsub := intervalIntegral.integrable_comp_mul_deriv_iff_of_deriv_nonneg
    (a := (-1 : ℝ)) (b := 1) (f := realCoordinateInv)
    (f' := fun x => 2 * (1 - x ^ 2) / (1 + x ^ 2) ^ 2) (g := g)
    continuous_realCoordinateInv.continuousOn (fun x _ => hasDerivAt_realCoordinateInv x)
    (by
      intro x hx
      apply realCoordinateInv_deriv_nonneg
      simpa only [min_eq_left (show (-1 : ℝ) ≤ 1 by norm_num),
        max_eq_right (show (-1 : ℝ) ≤ 1 by norm_num)] using hx)
  have he0 : realCoordinateInv (-1) = -1 := by norm_num [realCoordinateInv]
  have he1 : realCoordinateInv 1 = 1 := by norm_num [realCoordinateInv]
  rw [he0, he1] at hsub
  have hcongr := intervalIntegrable_congr_uIoo (μ := volume)
    (f := fun x : ℝ => g (realCoordinateInv x) * (2 * (1 - x ^ 2) / (1 + x ^ 2) ^ 2))
    (g := fun x : ℝ => (4 * |x| / (1 + x ^ 2) ^ 2) * f (realCoordinateInv x))
    (a := (-1 : ℝ)) (b := 1) (by
      intro x hx
      rw [uIoo_of_le (show (-1 : ℝ) ≤ 1 by norm_num)] at hx
      exact realCoordinate_weighted_comp f hx)
  have hiff := hsub.symm.trans hcongr
  have hOld : IntervalIntegrable g volume (-1) 1 ↔
      Integrable g (volume.restrict (Ioo (-1 : ℝ) 1)) :=
    intervalIntegrable_iff_integrableOn_Ioo_of_le (f := g)
      (show (-1 : ℝ) ≤ 1 by norm_num) (by finiteness) (by finiteness)
  have hNew :
      IntervalIntegrable (fun x : ℝ =>
        (4 * |x| / (1 + x ^ 2) ^ 2) * f (realCoordinateInv x)) volume (-1) 1 ↔
      Integrable (fun x : ℝ =>
        (4 * |x| / (1 + x ^ 2) ^ 2) * f (realCoordinateInv x))
          (volume.restrict (Ioo (-1 : ℝ) 1)) :=
    intervalIntegrable_iff_integrableOn_Ioo_of_le
      (f := fun x : ℝ => (4 * |x| / (1 + x ^ 2) ^ 2) * f (realCoordinateInv x))
      (show (-1 : ℝ) ≤ 1 by norm_num) (by finiteness) (by finiteness)
  exact hOld.symm.trans (hiff.trans hNew)

end

open MeasureTheory Set Polynomial

private theorem restrict_mixed_rectangle_positive :
    (((volume.restrict (Ioo (-1 : ℝ) 1)).prod
      (volume.restrict (Ioo (0 : ℝ) 1))).restrict
        (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ))) =
      (volume.restrict (Ioo (0 : ℝ) 1)).prod
        (volume.restrict (Ioo (0 : ℝ) 1)) := by
  rw [← Measure.restrict_prod_eq_prod_univ,
    Measure.restrict_restrict measurableSet_Ioi]
  have he : Ioi (0 : ℝ) ∩ Ioo (-1 : ℝ) 1 = Ioo (0 : ℝ) 1 := by
    ext x
    simp only [mem_inter_iff, mem_Ioi, mem_Ioo]
    constructor
    · rintro ⟨hx, _, h1⟩
      exact ⟨hx, h1⟩
    · rintro ⟨hx, h1⟩
      exact ⟨hx, by linarith, h1⟩
  rw [he]

theorem integrable_positive_zetaPolynomial (D Q : ℝ[X]) :
    Integrable (fun p : ℝ × ℝ =>
      if 0 < p.1 then D.eval p.1 * Q.eval p.2 / (1 - p.1 * p.2) else 0)
      ((volume.restrict (Ioo (-1 : ℝ) 1)).prod
        (volume.restrict (Ioo (0 : ℝ) 1))) := by
  have hfun : (fun p : ℝ × ℝ =>
      if 0 < p.1 then D.eval p.1 * Q.eval p.2 / (1 - p.1 * p.2) else 0) =
      (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)).indicator
        (fun p : ℝ × ℝ => D.eval p.1 * Q.eval p.2 / (1 - p.1 * p.2)) := by
    ext p
    simp only [indicator, mem_prod, mem_Ioi, mem_univ, and_true]
  rw [hfun, integrable_indicator_iff (measurableSet_Ioi.prod MeasurableSet.univ)]
  change Integrable _ _
  rw [restrict_mixed_rectangle_positive]
  exact integrable_zetaPolynomial D Q

theorem integral_positive_zetaPolynomial (D Q : ℝ[X]) :
    (∫ p : ℝ × ℝ,
      (if 0 < p.1 then D.eval p.1 * Q.eval p.2 / (1 - p.1 * p.2) else 0)
      ∂(volume.restrict (Ioo (-1 : ℝ) 1)).prod
        (volume.restrict (Ioo (0 : ℝ) 1))) = zetaMoment D Q := by
  have hfun : (fun p : ℝ × ℝ =>
      if 0 < p.1 then D.eval p.1 * Q.eval p.2 / (1 - p.1 * p.2) else 0) =
      (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)).indicator
        (fun p : ℝ × ℝ => D.eval p.1 * Q.eval p.2 / (1 - p.1 * p.2)) := by
    ext p
    simp only [indicator, mem_prod, mem_Ioi, mem_univ, and_true]
  rw [hfun, integral_indicator (measurableSet_Ioi.prod MeasurableSet.univ),
    restrict_mixed_rectangle_positive]
  exact (integral_prod_zetaPolynomial D Q).trans (zetaMoment_eq_sum D Q).symm

theorem integrable_realRowAmplitude (N r : ℕ) (Q : ℝ[X]) :
    Integrable (fun p : ℝ × ℝ =>
      (|p.1| / Real.sqrt (1 - p.1 ^ 2)) *
        (realRowAmplitude N r p.1 * Q.eval p.2) / (1 - p.1 * p.2))
      ((volume.restrict (Ioo (-1 : ℝ) 1)).prod
        (volume.restrict (Ioo (0 : ℝ) 1))) := by
  have hi := (integrable_mixedPolynomial (realPoly (rowP N r)) Q).sub
    ((integrable_positive_zetaPolynomial (realPoly (rowD N r)) Q).const_mul (3 / 2 : ℝ))
  apply hi.congr
  filter_upwards [ae_mem_mixed_rectangle] with p hp
  exact (realRowAmplitude_kernel_eq N r Q hp.1 p.2).symm

theorem integral_prod_realRowAmplitude (N r : ℕ) (Q : ℝ[X]) :
    (∫ p : ℝ × ℝ,
      (|p.1| / Real.sqrt (1 - p.1 ^ 2)) *
        (realRowAmplitude N r p.1 * Q.eval p.2) / (1 - p.1 * p.2)
      ∂(volume.restrict (Ioo (-1 : ℝ) 1)).prod
        (volume.restrict (Ioo (0 : ℝ) 1))) =
      mixedMoment (realPoly (rowP N r)) Q -
        (3 / 2 : ℝ) * zetaMoment (realPoly (rowD N r)) Q := by
  calc
    _ = ∫ p : ℝ × ℝ,
        ((|p.1| / Real.sqrt (1 - p.1 ^ 2)) *
          ((realPoly (rowP N r)).eval p.1 * Q.eval p.2) / (1 - p.1 * p.2) -
          (3 / 2 : ℝ) * (if 0 < p.1 then
            (realPoly (rowD N r)).eval p.1 * Q.eval p.2 / (1 - p.1 * p.2) else 0))
        ∂(volume.restrict (Ioo (-1 : ℝ) 1)).prod
          (volume.restrict (Ioo (0 : ℝ) 1)) := by
      apply integral_congr_ae
      filter_upwards [ae_mem_mixed_rectangle] with p hp
      exact realRowAmplitude_kernel_eq N r Q hp.1 p.2
    _ = _ := by
      rw [integral_sub (integrable_mixedPolynomial (realPoly (rowP N r)) Q)
        ((integrable_positive_zetaPolynomial (realPoly (rowD N r)) Q).const_mul (3 / 2 : ℝ)),
        integral_const_mul, integral_positive_zetaPolynomial]
      rw [integral_prod_mixedPolynomial, ← mixedMoment_eq_sum]

theorem determinantEntry_eq_realRow_integral (N r k : ℕ) :
    determinantEntry N r k =
      ∫ t in (-1 : ℝ)..1, ∫ s in (0 : ℝ)..1,
        (|t| / Real.sqrt (1 - t ^ 2)) *
          (realRowAmplitude N r t * (filteredColumn N k).eval s) / (1 - t * s) := by
  have h := integral_prod
    (fun p : ℝ × ℝ => (|p.1| / Real.sqrt (1 - p.1 ^ 2)) *
      (realRowAmplitude N r p.1 * (filteredColumn N k).eval p.2) / (1 - p.1 * p.2))
    (integrable_realRowAmplitude N r (filteredColumn N k))
  rw [integral_prod_realRowAmplitude] at h
  simpa only [determinantEntry,
    intervalIntegral.integral_of_le (show (-1 : ℝ) ≤ 1 by norm_num),
    intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num),
    integral_Ioc_eq_integral_Ioo] using h

theorem integrable_realPlaceRow (N r : ℕ) (Q : ℝ[X]) :
    Integrable (fun p : ℝ × ℝ =>
      realRowAmplitude N r p.1 * Q.eval p.2 / (1 - p.1 * p.2))
      (realPlaceMeasure.prod (volume.restrict (Ioo (0 : ℝ) 1))) := by
  apply (integrable_realPlaceMeasure_prod_iff _).mpr
  simpa only [mul_div_assoc] using integrable_realRowAmplitude N r Q

theorem determinantEntry_eq_realPlace_product (N r k : ℕ) :
    determinantEntry N r k =
      ∫ p : ℝ × ℝ,
        realRowAmplitude N r p.1 * (filteredColumn N k).eval p.2 / (1 - p.1 * p.2)
        ∂realPlaceMeasure.prod (volume.restrict (Ioo (0 : ℝ) 1)) := by
  rw [integral_realPlaceMeasure_prod]
  simpa only [determinantEntry, mul_div_assoc] using
    (integral_prod_realRowAmplitude N r (filteredColumn N k)).symm

theorem determinantEntry_eq_realPlace_integral (N r k : ℕ) :
    determinantEntry N r k =
      ∫ t, (∫ s in (0 : ℝ)..1,
        realRowAmplitude N r t * (filteredColumn N k).eval s / (1 - t * s))
        ∂realPlaceMeasure := by
  rw [determinantEntry_eq_realPlace_product]
  have h := integral_prod
    (fun p : ℝ × ℝ =>
      realRowAmplitude N r p.1 * (filteredColumn N k).eval p.2 / (1 - p.1 * p.2))
    (integrable_realPlaceRow N r (filteredColumn N k))
  simpa only [intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num),
    integral_Ioc_eq_integral_Ioo] using h

open MeasureTheory Set Polynomial
open scoped BigOperators

theorem integrable_pairedDeterminant (N : ℕ) :
    Integrable (fun z : Fin (n N) → ℝ × ℝ =>
      Matrix.det (Matrix.of fun r k : Fin (n N) =>
        realRowAmplitude N r.val (z k).1 * (filteredColumn N k.val).eval (z k).2 /
          (1 - (z k).1 * (z k).2)))
      (Measure.pi (fun _ : Fin (n N) =>
        realPlaceMeasure.prod (volume.restrict (Ioo (0 : ℝ) 1)))) := by
  classical
  simp_rw [Matrix.det_apply', Matrix.of_apply]
  apply integrable_finsetSum
  intro σ _
  exact (Integrable.fintype_prod (fun k : Fin (n N) =>
    integrable_realPlaceRow N (σ k).val (filteredColumn N k.val))).const_mul _

theorem determinant_eq_paired_integral (N : ℕ) :
    determinant N =
      ∫ z : Fin (n N) → ℝ × ℝ,
        Matrix.det (Matrix.of fun r k : Fin (n N) =>
          realRowAmplitude N r.val (z k).1 * (filteredColumn N k.val).eval (z k).2 /
            (1 - (z k).1 * (z k).2))
        ∂Measure.pi (fun _ : Fin (n N) =>
          realPlaceMeasure.prod (volume.restrict (Ioo (0 : ℝ) 1))) := by
  classical
  let μ : Measure (ℝ × ℝ) :=
    realPlaceMeasure.prod (volume.restrict (Ioo (0 : ℝ) 1))
  let F : Equiv.Perm (Fin (n N)) → (Fin (n N) → ℝ × ℝ) → ℝ := fun σ z =>
    ((Equiv.Perm.sign σ : ℤ) : ℝ) *
      ∏ k : Fin (n N), realRowAmplitude N (σ k).val (z k).1 *
        (filteredColumn N k.val).eval (z k).2 / (1 - (z k).1 * (z k).2)
  have hF (σ : Equiv.Perm (Fin (n N))) :
      Integrable (F σ) (Measure.pi (fun _ : Fin (n N) => μ)) := by
    exact (Integrable.fintype_prod
      (μ := fun _ : Fin (n N) => μ)
      (f := fun k : Fin (n N) => fun p : ℝ × ℝ =>
        realRowAmplitude N (σ k).val p.1 * (filteredColumn N k.val).eval p.2 /
          (1 - p.1 * p.2))
      (fun k => integrable_realPlaceRow N (σ k).val (filteredColumn N k.val))).const_mul
        (((Equiv.Perm.sign σ : ℤ) : ℝ))
  have hsplit := integral_finsetSum (μ := Measure.pi (fun _ : Fin (n N) => μ))
    (f := F) Finset.univ (fun σ _ => hF σ)
  unfold determinant
  change (Matrix.of (fun r k : Fin (n N) => determinantEntry N r.val k.val)).det = _
  simp_rw [Matrix.det_apply', Matrix.of_apply]
  change _ = ∫ z, ∑ σ : Equiv.Perm (Fin (n N)), F σ z
    ∂Measure.pi (fun _ : Fin (n N) => μ)
  rw [hsplit]
  apply Finset.sum_congr rfl
  intro σ _
  dsimp only [F]
  rw [integral_const_mul, integral_fintype_prod_eq_prod
    (fun k : Fin (n N) => fun p : ℝ × ℝ =>
      realRowAmplitude N (σ k).val p.1 * (filteredColumn N k.val).eval p.2 /
        (1 - p.1 * p.2))]
  congr 1
  apply Finset.prod_congr rfl
  intro k _
  exact determinantEntry_eq_realPlace_product N (σ k).val k.val

theorem pairedDeterminant_factor (N : ℕ) (z : Fin (n N) → ℝ × ℝ) :
    Matrix.det (Matrix.of fun r k : Fin (n N) =>
      realRowAmplitude N r.val (z k).1 * (filteredColumn N k.val).eval (z k).2 /
        (1 - (z k).1 * (z k).2)) =
      Matrix.det (Matrix.of fun r k : Fin (n N) => realRowAmplitude N r.val (z k).1) *
        ∏ k : Fin (n N), (filteredColumn N k.val).eval (z k).2 /
          (1 - (z k).1 * (z k).2) := by
  have h := Matrix.det_mul_row
    (fun k : Fin (n N) => (filteredColumn N k.val).eval (z k).2 /
      (1 - (z k).1 * (z k).2))
    (Matrix.of fun r k : Fin (n N) => realRowAmplitude N r.val (z k).1)
  convert h using 1
  · congr 1
    funext r k
    simp only [Matrix.of_apply]
    ring
  · exact _root_.mul_comm _ _

theorem determinant_eq_paired_factored_integral (N : ℕ) :
    determinant N =
      ∫ z : Fin (n N) → ℝ × ℝ,
        Matrix.det (Matrix.of fun r k : Fin (n N) => realRowAmplitude N r.val (z k).1) *
          ∏ k : Fin (n N), (filteredColumn N k.val).eval (z k).2 /
            (1 - (z k).1 * (z k).2)
        ∂Measure.pi (fun _ : Fin (n N) =>
          realPlaceMeasure.prod (volume.restrict (Ioo (0 : ℝ) 1))) := by
  rw [determinant_eq_paired_integral]
  apply integral_congr_ae
  filter_upwards with z
  exact pairedDeterminant_factor N z

end InternalCatalan

end

end OAI
