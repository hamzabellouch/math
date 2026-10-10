import OAI.Geometry.SurfaceImmersion.Geometry.NormalPlaneFrame

namespace OAI

/-! Polynomial rotation columns from a three-coordinate quaternion.
They fill a twice-winding planar frame by allowing its first column to move. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

abbrev FrameTarget := Fin 3 → ℝ

def rotationFirst (a b c : ℝ) : FrameTarget :=
  ![a^2+b^2-c^2,2*b*c,-2*a*c]
def rotationSecond (a b c : ℝ) : FrameTarget :=
  ![2*b*c,a^2-b^2+c^2,2*a*b]
def polynomialRotationFrame (a b c : ℝ) : Base →L[ℝ] FrameTarget :=
  (ContinuousLinearMap.proj 0).smulRight (rotationFirst a b c) +
    (ContinuousLinearMap.proj 1).smulRight (rotationSecond a b c)

lemma polynomialRotationFrame_apply (a b c : ℝ) (v : Base) :
    polynomialRotationFrame a b c v =
      v 0 • rotationFirst a b c + v 1 • rotationSecond a b c := by
  rfl

lemma rotationFirst_sq (a b c : ℝ) :
    (rotationFirst a b c 0)^2+(rotationFirst a b c 1)^2+
      (rotationFirst a b c 2)^2 = (a^2+b^2+c^2)^2 := by
  dsimp [rotationFirst]
  ring
lemma rotationSecond_sq (a b c : ℝ) :
    (rotationSecond a b c 0)^2+(rotationSecond a b c 1)^2+
      (rotationSecond a b c 2)^2 = (a^2+b^2+c^2)^2 := by
  dsimp [rotationSecond]
  ring
lemma rotation_columns_orthogonal (a b c : ℝ) :
    rotationFirst a b c 0 * rotationSecond a b c 0+
      rotationFirst a b c 1 * rotationSecond a b c 1+
      rotationFirst a b c 2 * rotationSecond a b c 2 = 0 := by
  dsimp [rotationFirst,rotationSecond]
  ring

lemma polynomialRotationFrame_injective {a b c : ℝ} (hq : 0 < a^2+b^2+c^2) :
    Function.Injective (polynomialRotationFrame a b c) := by
  intro u v huv
  have he (i : Fin 3) :
      (u 0-v 0)*rotationFirst a b c i+(u 1-v 1)*rotationSecond a b c i = 0 := by
    have hi := congrFun huv i
    simp only [polynomialRotationFrame_apply,Pi.add_apply,Pi.smul_apply,smul_eq_mul] at hi
    linear_combination hi
  have hd0 : (u 0-v 0)*(a^2+b^2+c^2)^2 = 0 := by
    rw [←rotationFirst_sq a b c]
    linear_combination (rotationFirst a b c 0)*he 0+
      (rotationFirst a b c 1)*he 1+(rotationFirst a b c 2)*he 2-
      (u 1-v 1)*rotation_columns_orthogonal a b c
  have hd1 : (u 1-v 1)*(a^2+b^2+c^2)^2 = 0 := by
    rw [←rotationSecond_sq a b c]
    linear_combination (rotationSecond a b c 0)*he 0+
      (rotationSecond a b c 1)*he 1+(rotationSecond a b c 2)*he 2-
      (u 0-v 0)*rotation_columns_orthogonal a b c
  have hn : (a^2+b^2+c^2)^2 ≠ 0 := (sq_pos_of_pos hq).ne'
  have h0 := sub_eq_zero.mp ((mul_eq_zero.mp hd0).resolve_right hn)
  have h1 := sub_eq_zero.mp ((mul_eq_zero.mp hd1).resolve_right hn)
  ext i
  fin_cases i
  · exact h0
  · exact h1

lemma polynomialRotationFrame_smooth :
    ContDiff ℝ ∞ (fun q : FrameTarget => polynomialRotationFrame (q 0) (q 1) (q 2)) := by
  have hu : ContDiff ℝ ∞ (fun q : FrameTarget => rotationFirst (q 0) (q 1) (q 2)) := by
    apply contDiff_pi.mpr
    intro i
    fin_cases i <;> dsimp [rotationFirst] <;> fun_prop
  have hv : ContDiff ℝ ∞ (fun q : FrameTarget => rotationSecond (q 0) (q 1) (q 2)) := by
    apply contDiff_pi.mpr
    intro i
    fin_cases i <;> dsimp [rotationSecond] <;> fun_prop
  exact (contDiff_const.smulRight hu).add (contDiff_const.smulRight hv)

lemma polynomialRotationFrame_boundary (a b : ℝ) :
    polynomialRotationFrame a b 0 =
      (ContinuousLinearMap.proj 0).smulRight (![a^2+b^2,0,0] : FrameTarget)+
      (ContinuousLinearMap.proj 1).smulRight (![0,a^2-b^2,2*a*b] : FrameTarget) := by
  simp [polynomialRotationFrame,rotationFirst,rotationSecond]

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
