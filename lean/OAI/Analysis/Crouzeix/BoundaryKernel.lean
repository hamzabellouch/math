import Mathlib
import OAI.Analysis.Crouzeix.CircleCoordinate
import OAI.Analysis.Crouzeix.ExteriorKernel

namespace OAI

/-! Boundary Kernel. -/

noncomputable section

open Set Filter Metric Topology Function Complex ComplexConjugate MeasureTheory

namespace CrouzeixHilbert.Conformal

open Boundary

namespace ExteriorCollar

variable {U : Set ℂ} (C : ExteriorCollar U)

lemma closed_unit_subset_reciprocalDisk : closedBall (0 : ℂ) 1 ⊆ C.reciprocalDisk := by
  intro z hz
  rw [mem_ball_zero_iff]
  exact (mem_closedBall_zero_iff.mp hz).trans_lt
    ((one_lt_inv₀ C.radius_pos).mpr C.radius_lt_one)

lemma circle_inverse_mem (t : CircleSpace) : (circleCoordinate t)⁻¹ ∈ C.reciprocalDisk :=
  C.inverse_mem_reciprocalDisk (by rw [norm_circleCoordinate]; exact C.radius_lt_one)

def boundaryCorrection : C(CircleSpace × CircleSpace, ℂ) where
  toFun p := C.correction (circleCoordinate p.2)⁻¹ (circleCoordinate p.1)⁻¹
  continuous_toFun := C.continuousOn_correction.comp_continuous
    (((circleCoordinate.continuous.comp continuous_snd).inv₀
      (fun p => circleCoordinate_ne_zero p.2)).prodMk
      ((circleCoordinate.continuous.comp continuous_fst).inv₀
        (fun p => circleCoordinate_ne_zero p.1)))
    (fun p => ⟨C.circle_inverse_mem p.2, C.circle_inverse_mem p.1⟩)

def boundaryKernel : CircleKernel where
  toFun p := 1 + 2 * (C.boundaryCorrection p).re
  continuous_toFun := continuous_const.add
    (continuous_const.mul (continuous_re.comp C.boundaryCorrection.continuous))

lemma circle_real_quotient {t w : ℂ} (ht : ‖t‖ = 1) (hw : ‖w‖ = 1) (hne : t ≠ w) :
    2 * (t/(t-w)).re = 1 := by
  have hn : normSq (t-w) ≠ 0 := normSq_eq_zero.not.mpr (sub_ne_zero.mpr hne)
  have hts : t.re * t.re + t.im * t.im = 1 := by
    rw [← normSq_apply, normSq_eq_norm_sq, ht, one_pow]
  have hws : w.re * w.re + w.im * w.im = 1 := by
    rw [← normSq_apply, normSq_eq_norm_sq, hw, one_pow]
  rw [div_re, ← add_div]
  field_simp
  simp only [normSq_apply, sub_re, sub_im]
  nlinarith

lemma boundaryKernel_off_diagonal (hc : Convex ℝ U) {w t : CircleSpace} (hnt : t ≠ w) :
    0 ≤ C.boundaryKernel (w,t) := by
  have ht : C.radius < ‖circleCoordinate t‖ := by rw [norm_circleCoordinate]; exact C.radius_lt_one
  have hw : C.radius < ‖circleCoordinate w‖ := by rw [norm_circleCoordinate]; exact C.radius_lt_one
  have htw : circleCoordinate t ≠ circleCoordinate w := fun he => hnt (circleCoordinate_injective he)
  have hn := C.supporting_normal hc (norm_circleCoordinate t)
    (C.boundary.mapsTo (mem_sphere_zero_iff_norm.mpr (norm_circleCoordinate w))).1
  have hq : 0 ≤ (circleCoordinate t * deriv C.G (circleCoordinate t) /
      (C.G (circleCoordinate t) - C.G (circleCoordinate w))).re := by
    rw [div_re, ← add_div]
    apply div_nonneg _ (normSq_nonneg _)
    simpa only [mul_re, conj_re, conj_im, sub_neg_eq_add, neg_mul] using hn
  change 0 ≤ 1 + 2 * (C.correction _ _).re
  rw [C.correction_eq ht hw htw, sub_re]
  have he := circle_real_quotient (norm_circleCoordinate t) (norm_circleCoordinate w) htw
  linarith

lemma boundaryKernel_nonnegative (hc : Convex ℝ U) (p : CircleSpace × CircleSpace) :
    0 ≤ C.boundaryKernel p := by
  let : Nontrivial Circle := ⟨⟨1, -1, by
    intro h
    have h' := congrArg (fun z : Circle => (z : ℂ)) h
    norm_num at h'⟩⟩
  let : Nontrivial CircleSpace := (AddCircle.homeomorphCircle (T := 1) one_ne_zero).surjective.nontrivial
  apply (dense_compl_singleton p.1).induction (P := fun t => 0 ≤ C.boundaryKernel (p.1,t))
    (fun t ht => C.boundaryKernel_off_diagonal hc (by simpa using ht))
    (isClosed_le continuous_const
      (C.boundaryKernel.continuous.comp (continuous_const.prodMk continuous_id))) p.2

lemma boundaryCorrection_integral_right (w : CircleSpace) :
    (∫ t, C.boundaryCorrection (w,t) ∂circleMeasure) = 0 := by
  change (∫ t, C.correction (circleCoordinate t)⁻¹ (circleCoordinate w)⁻¹ ∂circleMeasure) = 0
  rw [integral_holomorphic_inverse_circleCoordinate
    ((C.differentiableOn_correction_left (C.circle_inverse_mem w)).mono C.closed_unit_subset_reciprocalDisk)]
  exact C.correction_zero_left _

lemma boundaryCorrection_integral_left (t : CircleSpace) :
    (∫ w, C.boundaryCorrection (w,t) ∂circleMeasure) = 0 := by
  change (∫ w, C.correction (circleCoordinate t)⁻¹ (circleCoordinate w)⁻¹ ∂circleMeasure) = 0
  rw [integral_holomorphic_inverse_circleCoordinate
    ((C.differentiableOn_correction_right (C.circle_inverse_mem t)).mono C.closed_unit_subset_reciprocalDisk)]
  exact C.correction_zero_right _

lemma boundaryKernel_integral_right (w : CircleSpace) :
    (∫ t, C.boundaryKernel (w,t) ∂circleMeasure) = 1 := by
  have hi : Integrable (fun t => C.boundaryCorrection (w,t)) circleMeasure :=
    (C.boundaryCorrection.continuous.comp (continuous_const.prodMk continuous_id)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  change (∫ t, 1 + 2 * (C.boundaryCorrection (w,t)).re ∂circleMeasure) = 1
  have hr : Integrable (fun t => (C.boundaryCorrection (w,t)).re) circleMeasure := hi.re
  rw [integral_add (integrable_const (1 : ℝ)) (hr.const_mul 2), integral_const_mul, show (∫ t, (C.boundaryCorrection (w,t)).re ∂circleMeasure) =
      (∫ t, C.boundaryCorrection (w,t) ∂circleMeasure).re from Complex.reCLM.integral_comp_comm hi,
    C.boundaryCorrection_integral_right, zero_re, mul_zero, add_zero, integral_const]
  simp

lemma boundaryKernel_integral_left (t : CircleSpace) :
    (∫ w, C.boundaryKernel (w,t) ∂circleMeasure) = 1 := by
  have hi : Integrable (fun w => C.boundaryCorrection (w,t)) circleMeasure :=
    (C.boundaryCorrection.continuous.comp (continuous_id.prodMk continuous_const)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  change (∫ w, 1 + 2 * (C.boundaryCorrection (w,t)).re ∂circleMeasure) = 1
  have hr : Integrable (fun w => (C.boundaryCorrection (w,t)).re) circleMeasure := hi.re
  rw [integral_add (integrable_const (1 : ℝ)) (hr.const_mul 2), integral_const_mul, show (∫ w, (C.boundaryCorrection (w,t)).re ∂circleMeasure) =
      (∫ w, C.boundaryCorrection (w,t) ∂circleMeasure).re from Complex.reCLM.integral_comp_comm hi,
    C.boundaryCorrection_integral_left, zero_re, mul_zero, add_zero, integral_const]
  simp

def boundaryOperator (hc : Convex ℝ U) (k : ℕ) : BoundaryL2 k →L[ℝ] BoundaryL2 k :=
  kernelOperator C.boundaryKernel (C.boundaryKernel_nonnegative hc)
    C.boundaryKernel_integral_right C.boundaryKernel_integral_left

lemma norm_boundaryOperator_le (hc : Convex ℝ U) (k : ℕ) :
    ‖C.boundaryOperator hc k‖ ≤ 1 :=
  norm_kernelOperator_le C.boundaryKernel (C.boundaryKernel_nonnegative hc)
    C.boundaryKernel_integral_right C.boundaryKernel_integral_left

end ExteriorCollar

end CrouzeixHilbert.Conformal

end

end OAI
