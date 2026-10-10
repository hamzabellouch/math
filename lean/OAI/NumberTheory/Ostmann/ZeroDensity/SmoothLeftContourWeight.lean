import OAI.NumberTheory.Ostmann.Characters.CharacterLogDerivativeLeft
import OAI.NumberTheory.Ostmann.ZeroDensity.SmoothContourResidue

namespace OAI

/-! # An integrable majorant for the left vertical contour -/

namespace Ostmann

open Complex MeasureTheory Filter
open scoped Topology

noncomputable def leftContourLine (t : ℝ) : ℂ := -(1 / 2) + (t : ℂ) * I

@[simp] theorem leftContourLine_re (t : ℝ) : (leftContourLine t).re = -(1 / 2 : ℝ) := by
  simp [leftContourLine]

@[simp] theorem leftContourLine_im (t : ℝ) : (leftContourLine t).im = t := by
  simp [leftContourLine]

@[fun_prop] theorem leftContourLine_continuous : Continuous leftContourLine := by
  unfold leftContourLine
  fun_prop

noncomputable def leftContourIntegrand (χ : PrimitiveComplexCharacter) (X t : ℝ) : ℂ :=
  (-deriv χ.L (leftContourLine t) / χ.L (leftContourLine t)) *
    smoothContourWeight X (leftContourLine t)

noncomputable def leftContourMajorant (t : ℝ) : ℝ := (1 + |t|) ^ (-(7 : ℝ))

theorem leftContourMajorant_nonneg (t : ℝ) : 0 ≤ leftContourMajorant t := Real.rpow_nonneg (by positivity) _

theorem leftContourMajorant_integrable : Integrable leftContourMajorant := by
  have hp : Integrable (fun t : ℝ => (1 + ‖t‖) ^ (-(7 : ℝ))) :=
    integrable_one_add_norm (μ := volume) (E := ℝ)
      (by norm_num : (Module.finrank ℝ ℝ : ℝ) < 7)
  change Integrable (fun t : ℝ => (1 + |t|) ^ (-(7 : ℝ)))
  simpa only [Real.norm_eq_abs] using hp

theorem leftContourWeight_norm (X t : ℝ) (hX : 0 < X) :
    ‖smoothContourWeight X (leftContourLine t)‖ =
      ‖primeMeanMellin (leftContourLine t)‖ / Real.sqrt X := by
  rw [smoothContourWeight, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hX,
    leftContourLine_re, Real.rpow_neg hX.le, ← Real.sqrt_eq_rpow]
  ring

theorem leftContourIntegrand_continuous (χ : PrimitiveComplexCharacter)
    (X : ℝ) (hX : 0 < X) : Continuous (leftContourIntegrand χ X) := by
  have hcL : Continuous χ.L := continuous_iff_continuousAt.mpr (fun z => (χ.L_analytic z).continuousAt)
  have hcd : Continuous (deriv χ.L) := continuous_iff_continuousAt.mpr (fun z => (χ.L_analytic z).deriv.continuousAt)
  have hn (t : ℝ) : χ.L (leftContourLine t) ≠ 0 := by
    apply χ.L_ne_zero_left_ne_origin _ (by simp) (by simp)
    intro he
    have hh := congrArg Complex.re he
    norm_num at hh
  exact ((hcd.comp leftContourLine_continuous).neg.div (hcL.comp leftContourLine_continuous) hn).mul
    ((smoothContourWeight_differentiable X hX).continuous.comp leftContourLine_continuous)

theorem leftContourIntegrand_bound : ∃ C : ℝ, 0 < C ∧
    ∀ (χ : PrimitiveComplexCharacter) (X : ℝ), 0 < X → ∀ t : ℝ,
      ‖leftContourIntegrand χ X t‖ ≤
        (C * (1 + Real.log (χ.modulus : ℝ)) / Real.sqrt X) * leftContourMajorant t := by
  obtain ⟨A, hA, hbound⟩ := character_logDeriv_left_bound
  obtain ⟨M, hM, hmellin⟩ := primeMeanMellin_decay
  refine ⟨A * M, mul_pos hA hM, ?_⟩
  intro χ X hX t
  have hq : 0 ≤ Real.log (χ.modulus : ℝ) := Real.log_nonneg (by exact_mod_cast χ.positive)
  have hl := hbound χ (leftContourLine t) (by simp)
  have hm := hmellin (leftContourLine t) (by norm_num) (by norm_num)
  simp only [leftContourLine_im] at hl hm
  have hscalar : 1 + Real.log (χ.modulus : ℝ) + |t| ≤
      (1 + Real.log (χ.modulus : ℝ)) * (1 + |t|) := by nlinarith [abs_nonneg t]
  have hexp : (1 + |t|) * Real.exp (-8 * Real.log (1 + |t|)) = leftContourMajorant t := by
    rw [leftContourMajorant, Real.rpow_def_of_pos (by positivity)]
    conv_lhs => arg 1; rw [← Real.exp_log (by positivity : 0 < 1 + |t|)]
    rw [← Real.exp_add]
    congr 1
    ring
  have hnorm : ‖leftContourIntegrand χ X t‖ =
      ‖logDeriv χ.L (leftContourLine t)‖ *
        (‖primeMeanMellin (leftContourLine t)‖ / Real.sqrt X) := by
    rw [leftContourIntegrand, norm_mul, leftContourWeight_norm X t hX]
    simp [logDeriv_apply, neg_div]
  rw [hnorm]
  calc
    _ ≤ (A * ((1 + Real.log (χ.modulus : ℝ)) * (1 + |t|))) *
        (M * Real.exp (-8 * Real.log (1 + |t|)) / Real.sqrt X) := by
      gcongr
      exact hl.trans (mul_le_mul_of_nonneg_left hscalar hA.le)
    _ = (A * M * (1 + Real.log (χ.modulus : ℝ)) / Real.sqrt X) * leftContourMajorant t := by
      rw [← hexp]
      ring

end Ostmann

end OAI
