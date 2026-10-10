import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import OAI.Geometry.NodalSets.Elliptic.CorrugationWellChoice

namespace OAI

namespace Yau.Geometry
open Real Set MeasureTheory
open scoped ContDiff
noncomputable section

def flatPrimitive (t : ℝ) : ℝ := ∫ s in (0:ℝ)..t, expNegInvGlue s

lemma flatPrimitive_hasDerivAt (t : ℝ) : HasDerivAt flatPrimitive (expNegInvGlue t) t := by
  have hc := (expNegInvGlue.contDiff (n := ⊤)).continuous
  exact intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 t)
    (hc.stronglyMeasurableAtFilter _ _) hc.continuousAt

lemma flatPrimitive_smooth : ContDiff ℝ ∞ flatPrimitive := by
  apply contDiff_infty_iff_deriv.mpr
  refine ⟨fun t ↦ (flatPrimitive_hasDerivAt t).differentiableAt,?_⟩
  have he : deriv flatPrimitive = expNegInvGlue := funext (fun t ↦ (flatPrimitive_hasDerivAt t).deriv)
  rw [he]
  exact expNegInvGlue.contDiff

lemma flatPrimitive_zero {t : ℝ} (ht : t ≤ 0) : flatPrimitive t = 0 := by
  unfold flatPrimitive
  calc
    (∫ s in (0:ℝ)..t, expNegInvGlue s) = ∫ s in (0:ℝ)..t, (0:ℝ) := by
      apply intervalIntegral.integral_congr
      intro s hs
      rw [uIcc_of_ge ht] at hs
      exact expNegInvGlue.zero_of_nonpos hs.2
    _ = 0 := by simp

def corrugationRadialPotential (a R r : ℝ) : ℝ := -(a/2)*flatPrimitive (R^2-r^2)

def corrugationDiskWell (a R : ℝ) (z : ℝ × ℝ) : ℝ :=
  -(a/2)*flatPrimitive (R^2-z.1^2-z.2^2)

lemma corrugationDiskWell_smooth (a R : ℝ) : ContDiff ℝ ∞ (corrugationDiskWell a R) :=
  contDiff_const.mul (flatPrimitive_smooth.comp
    ((contDiff_const.sub (contDiff_fst.pow 2)).sub (contDiff_snd.pow 2)))

lemma corrugationDiskWell_zero {a R : ℝ} {z : ℝ × ℝ} (hz : R^2 ≤ z.1^2+z.2^2) :
    corrugationDiskWell a R z = 0 := by
  unfold corrugationDiskWell
  rw [flatPrimitive_zero (by linarith),mul_zero]

lemma corrugationRadialPotential_hasDerivAt (a R r : ℝ) :
    HasDerivAt (corrugationRadialPotential a R) (corrugationSlope a R r) r := by
  have h := ((flatPrimitive_hasDerivAt (R^2-r^2)).comp r
    ((hasDerivAt_const r (R^2)).sub ((hasDerivAt_id r).pow 2))).const_mul (-(a/2))
  change HasDerivAt (corrugationRadialPotential a R) _ r at h
  convert h using 1
  simp [corrugationSlope]
  ring

lemma corrugationRadialPotential_rim (a R : ℝ) : corrugationRadialPotential a R R = 0 := by
  simp [corrugationRadialPotential,flatPrimitive_zero]

lemma corrugationRadialPotential_integral (a R r : ℝ) :
    corrugationRadialPotential a R r = -(∫ t in r..R, corrugationSlope a R t) := by
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ ↦ corrugationRadialPotential_hasDerivAt a R t)
    ((corrugationSlope_smooth a R).continuous.intervalIntegrable r R)
  rw [corrugationRadialPotential_rim,zero_sub] at h
  linarith

lemma corrugationDiskWell_radial (a R : ℝ) (z : ℝ × ℝ) :
    corrugationDiskWell a R z = corrugationRadialPotential a R (Real.sqrt (z.1^2+z.2^2)) := by
  rw [corrugationDiskWell,corrugationRadialPotential,Real.sq_sqrt (by positivity)]
  congr 2
  ring

lemma corrugationDiskWell_compactSupport (a : ℝ) {R : ℝ} (hR : 0 ≤ R) :
    HasCompactSupport (corrugationDiskWell a R) := by
  have hsub : Function.support (corrugationDiskWell a R) ⊆
      (Icc (-R) R) ×ˢ (Icc (-R) R) := by
    intro z hz
    have hn : z.1^2+z.2^2 < R^2 := by
      by_contra h
      exact hz (corrugationDiskWell_zero (le_of_not_gt h))
    constructor <;> constructor <;> nlinarith [sq_nonneg z.1,sq_nonneg z.2]
  exact (isCompact_Icc.prod isCompact_Icc).of_isClosed_subset isClosed_closure
    (closure_minimal hsub (isClosed_Icc.prod isClosed_Icc))

end
end Yau.Geometry

end OAI
