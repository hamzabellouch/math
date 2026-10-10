import OAI.Geometry.SurfaceImmersion.Correction.PolynomialRotationFrame

namespace OAI

/-! Rotation columns with an exterior constant shift. This allows the
twice-winding frame to have two separated simple zeros before filling. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

def axisNormalFrame (r y z : ℝ) : Base →L[ℝ] FrameTarget :=
  (ContinuousLinearMap.proj 0).smulRight (![r,0,0] : FrameTarget)+
    (ContinuousLinearMap.proj 1).smulRight (![0,y,z] : FrameTarget)

def shiftedRotationFrame (a b c e : ℝ) : Base →L[ℝ] FrameTarget :=
  polynomialRotationFrame a b c-
    (ContinuousLinearMap.proj 1).smulRight (![0,e,0] : FrameTarget)

lemma axisNormalFrame_injective {r y z : ℝ} (hr : r ≠ 0) (hn : y ≠ 0 ∨ z ≠ 0) :
    Function.Injective (axisNormalFrame r y z) := by
  intro u v he
  have h0 : u 0 = v 0 := by
    have hh := congrFun he 0
    simp [axisNormalFrame] at hh
    exact hh.resolve_right hr
  have h1 : u 1 = v 1 := by
    rcases hn with hn | hn
    · have hh := congrFun he 1
      simp [axisNormalFrame] at hh
      exact hh.resolve_right hn
    · have hh := congrFun he 2
      simp [axisNormalFrame] at hh
      exact hh.resolve_right hn
  ext i
  fin_cases i
  · exact h0
  · exact h1

lemma shiftedRotationFrame_zero_c (a b e : ℝ) :
    shiftedRotationFrame a b 0 e = axisNormalFrame (a^2+b^2) (a^2-b^2-e) (2*a*b) := by
  ext v i
  fin_cases i <;> simp [shiftedRotationFrame,axisNormalFrame,polynomialRotationFrame,
    rotationFirst,rotationSecond]
  all_goals ring

lemma shiftedRotationFrame_injective_exterior {a b e : ℝ} (hr : 1 < a^2+b^2)
    (he : e ∈ Icc (0:ℝ) 1) : Function.Injective (shiftedRotationFrame a b 0 e) := by
  rw [shiftedRotationFrame_zero_c]
  apply axisNormalFrame_injective (by linarith)
  by_contra hn
  push Not at hn
  have hab : a*b = 0 := by nlinarith [hn.2]
  rcases mul_eq_zero.mp hab with ha | hb
  · rw [ha] at hr hn
    simp only [zero_mul,mul_zero] at hr hn
    nlinarith [he.1,sq_nonneg b]
  · rw [hb] at hr hn
    simp only [mul_zero] at hr hn
    linarith [he.2]

lemma shiftedRotationFrame_injective {a b c e : ℝ} (hq : 0 < a^2+b^2+c^2)
    (hcase : e = 0 ∨ c = 0 ∧ 1 < a^2+b^2 ∧ e ∈ Icc (0:ℝ) 1) :
    Function.Injective (shiftedRotationFrame a b c e) := by
  rcases hcase with rfl | ⟨rfl,hr,he⟩
  · have hz : (ContinuousLinearMap.proj 1 : Base →L[ℝ] ℝ).smulRight
        (![0,(0:ℝ),0] : FrameTarget) = 0 := by
      ext v i
      fin_cases i <;> simp
    rw [shiftedRotationFrame,hz,sub_zero]
    exact polynomialRotationFrame_injective hq
  · exact shiftedRotationFrame_injective_exterior hr he

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
