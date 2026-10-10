import Mathlib.Analysis.CStarAlgebra.Exponential
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.Hadamard
import Mathlib.Analysis.Complex.Schwarz

namespace OAI

/-! The entire conjugation path used in Kirchberg's Proposition 1,
J. Operator Theory 36 (1996), pp. 60--61. -/

noncomputable section
namespace KadisonSimilarity

open NormedSpace Complex Set

variable {B : Type*} [NormedRing B] [NormedAlgebra ℂ B] [StarRing B]
  [CStarRing B] [CompleteSpace B] [StarModule ℂ B]

local instance kirchbergConjugationRatAlgebra : NormedAlgebra ℚ B := NormedAlgebra.restrictScalars ℚ ℂ B

/-- The imaginary direction of this path is unitary conjugation. -/
def kirchbergPath (t a : B) (z : ℂ) : B :=
  exp (z • (-t)) * a * exp (z • t)

omit [StarRing B] [CStarRing B] [StarModule ℂ B] in
theorem differentiable_kirchbergPath (t a : B) :
    Differentiable ℂ (kirchbergPath t a) := by
  unfold kirchbergPath
  fun_prop

omit [StarRing B] [CStarRing B] [StarModule ℂ B] in
theorem kirchbergPath_hasDerivAt_zero (t a : B) :
    HasDerivAt (kirchbergPath t a) (a * t - t * a) 0 := by
  change HasDerivAt (fun z : ℂ => exp (z • (-t)) * a * exp (z • t)) _ _
  have h₁ := (hasDerivAt_exp_smul_const (-t) (0 : ℂ)).mul_const a
  have h₂ := h₁.mul (hasDerivAt_exp_smul_const t (0 : ℂ))
  simpa only [Pi.mul_def, zero_smul, NormedSpace.exp_zero, one_mul, mul_one,
    neg_mul, sub_eq_add_neg, add_comm] using h₂

theorem kirchbergPath_norm_re (t a : B) (ht : IsSelfAdjoint t) (z : ℂ) :
    ‖kirchbergPath t a z‖ = ‖kirchbergPath t a (z.re : ℂ)‖ := by
  have hcomm (s w : ℂ) : Commute (s • t) (w • t) :=
    ((Commute.refl t).smul_left s).smul_right w
  let U : unitary B := selfAdjoint.expUnitary (z.im • ⟨t, ht⟩)
  let V : unitary B := selfAdjoint.expUnitary ((-z.im) • ⟨t, ht⟩)
  have hz : z = (z.re : ℂ) + (z.im : ℂ) * I := by
    simpa only [mul_comm] using (re_add_im z).symm
  have hleft : exp (z • (-t)) =
      (V : B) * exp ((z.re : ℂ) • (-t)) := by
    conv_lhs => rw [hz, add_smul, add_comm]
    rw [exp_add_of_commute]
    · congr 1
      simp [V, selfAdjoint.expUnitary_coe, ← Complex.coe_smul, smul_smul, mul_comm]
    · exact ((Commute.refl (-t)).smul_left _).smul_right _
  have hright : exp (z • t) = exp ((z.re : ℂ) • t) * (U : B) := by
    conv_lhs => rw [hz, add_smul, exp_add_of_commute (hcomm _ _)]
    congr 1
    simp [U, selfAdjoint.expUnitary_coe, ← Complex.coe_smul, smul_smul, mul_comm]
  rw [kirchbergPath, hleft, hright]
  calc
    _ = ‖(V : B) * (exp ((z.re : ℂ) • (-t)) * a *
        exp ((z.re : ℂ) • t)) * (U : B)‖ := by simp only [mul_assoc]
    _ = _ := by rw [CStarRing.norm_mul_coe_unitary, CStarRing.norm_coe_unitary_mul]; rfl

/-- Compactness of the real interval gives boundedness on the infinite strip. -/
theorem kirchbergPath_strip_bddAbove (t a : B) (ht : IsSelfAdjoint t) :
    BddAbove ((norm ∘ kirchbergPath t a) ''
      Complex.HadamardThreeLines.verticalClosedStrip (-1) 1) := by
  have hc : Continuous (fun x : ℝ => ‖kirchbergPath t a (x : ℂ)‖) :=
    (differentiable_kirchbergPath t a).continuous.comp Complex.continuous_ofReal |>.norm
  obtain ⟨C, hC⟩ := (isCompact_Icc.image hc).bddAbove
  refine ⟨C, ?_⟩
  rintro y ⟨z, hz, rfl⟩
  rw [Function.comp_apply, kirchbergPath_norm_re t a ht z]
  exact hC ⟨z.re, hz, rfl⟩

omit [StarRing B] [CStarRing B] [CompleteSpace B] [StarModule ℂ B] in
@[simp] theorem kirchbergPath_zero (t a : B) : kirchbergPath t a 0 = a := by
  simp [kirchbergPath]

/-- The two boundary bounds control the whole strip, by three lines. -/
theorem kirchbergPath_norm_le (t a : B) (ht : IsSelfAdjoint t) {M : ℝ}
    (hM : 0 < M) (hleft : ‖kirchbergPath t a (-1)‖ ≤ M)
    (hright : ‖kirchbergPath t a 1‖ ≤ M) {z : ℂ}
    (hz : -1 ≤ z.re ∧ z.re ≤ 1) : ‖kirchbergPath t a z‖ ≤ M := by
  have h := Complex.HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip'
    (f := kirchbergPath t a) (a := M) (b := M) (by norm_num : (-1 : ℝ) < 1)
    hz (differentiable_kirchbergPath t a).diffContOnCl
    (kirchbergPath_strip_bddAbove t a ht) ?_ ?_
  · simpa only [← Real.rpow_add hM, sub_add_cancel, Real.rpow_one] using h
  · intro w hw
    rw [kirchbergPath_norm_re t a ht, show w.re = -1 from hw]
    simpa only [Complex.ofReal_neg, Complex.ofReal_one] using hleft
  · intro w hw
    rw [kirchbergPath_norm_re t a ht, show w.re = 1 from hw]
    exact hright

/-- Schwarz's lemma gives the scalar derivation bound on page 60. -/
theorem norm_commutator_le_of_kirchberg_bound (t a : B) (ht : IsSelfAdjoint t)
    {M : ℝ} (hM : 0 < M) (hleft : ‖kirchbergPath t a (-1)‖ ≤ M)
    (hright : ‖kirchbergPath t a 1‖ ≤ M) :
    ‖t * a - a * t‖ ≤ M + ‖a‖ := by
  have hmap : MapsTo (kirchbergPath t a) (Metric.ball 0 1)
      (Metric.closedBall (kirchbergPath t a 0) (M + ‖a‖)) := by
    intro z hz
    have hnz : ‖z‖ < 1 := by simpa only [Metric.mem_ball, dist_zero_right] using hz
    have hre : |z.re| ≤ 1 := (Complex.abs_re_le_norm z).trans hnz.le
    rw [Metric.mem_closedBall, dist_eq_norm, kirchbergPath_zero]
    exact (norm_sub_le _ _).trans (add_le_add
      (kirchbergPath_norm_le t a ht hM hleft hright (abs_le.mp hre)) le_rfl)
  have h := Complex.norm_deriv_le_div_of_mapsTo_ball
    (differentiable_kirchbergPath t a).differentiableOn hmap (by norm_num : (0 : ℝ) < 1)
  rw [(kirchbergPath_hasDerivAt_zero t a).deriv, div_one] at h
  simpa only [← neg_sub (a * t) (t * a), norm_neg] using h

end KadisonSimilarity

end

end OAI
