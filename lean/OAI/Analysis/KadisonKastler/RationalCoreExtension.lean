import OAI.Analysis.KadisonKastler.RationalComplexCore
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Topology.Instances.RealVectorSpace
import Mathlib.Analysis.Complex.Basic

namespace OAI

/-! # Bounded complex-linear extension from the rational core -/

namespace KadisonKastler

open TopologicalSpace

noncomputable section

variable {H F : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

local instance rationalHNormedSpace : NormedSpace ℚ H := NormedSpace.restrictScalars ℚ ℂ H
local instance rationalFNormedSpace : NormedSpace ℚ F := NormedSpace.restrictScalars ℚ ℂ F

/-- A continuous rational-linear map commuting with multiplication by i
is complex-linear. Real-linearity follows from continuity. -/
def complexifyRational (f : H →L[ℚ] F)
    (hI : ∀ x, f (Complex.I • x) = Complex.I • f x) : H →L[ℂ] F where
  toFun := f
  map_add' := f.map_add
  map_smul' c x := by
    have hdec (y : H) : c • y = c.re • y + c.im • (Complex.I • y) := by
      rw [← Complex.coe_smul, ← Complex.coe_smul, smul_smul, ← add_smul, Complex.re_add_im]
    have hdecF (y : F) : c • y = c.re • y + c.im • (Complex.I • y) := by
      rw [← Complex.coe_smul, ← Complex.coe_smul, smul_smul, ← add_smul, Complex.re_add_im]
    rw [hdec, f.map_add, map_real_smul f f.continuous, map_real_smul f f.continuous, hI,
      ← hdecF]
    rfl
  cont := f.continuous

@[simp]
theorem complexifyRational_apply (f : H →L[ℚ] F) (hI) (x : H) :
    complexifyRational f hI x = f x := rfl

namespace RationalComplexCore

variable [CompleteSpace F]
variable (C : RationalComplexCore H)

/-- Extend a bounded rational-linear map on the dense core. -/
def extendRational (f : C.space →ₗ[ℚ] F) : H →L[ℚ] F :=
  f.extendOfNorm C.space.subtype

/-- The extension agrees with every core value. -/
theorem extendRational_coe (f : C.space →ₗ[ℚ] F) {B : ℝ}
    (hb : ∀ x, ‖f x‖ ≤ B * ‖(x : H)‖) (x : C.space) :
    C.extendRational f (x : H) = f x :=
  LinearMap.extendOfNorm_eq C.dense.denseRange_val ⟨B, hb⟩ x

/-- The norm bound is unchanged by the dense extension. -/
theorem norm_extendRational_le (f : C.space →ₗ[ℚ] F) {B : ℝ}
    (hb : ∀ x, ‖f x‖ ≤ B * ‖(x : H)‖) (x : H) :
    ‖C.extendRational f x‖ ≤ B * ‖x‖ :=
  LinearMap.norm_extendOfNorm_apply_le C.dense.denseRange_val B hb x

/-- Commutation with i persists from the core to its norm completion. -/
theorem extendRational_mul_I (f : C.space →ₗ[ℚ] F) {B : ℝ}
    (hb : ∀ x, ‖f x‖ ≤ B * ‖(x : H)‖)
    (hI : ∀ x, f (C.mulI x) = Complex.I • f x) (x : H) :
    C.extendRational f (Complex.I • x) = Complex.I • C.extendRational f x := by
  have he : (fun x => C.extendRational f (Complex.I • x)) =
      fun x => Complex.I • C.extendRational f x := by
    have hd : DenseRange ((↑) : C.space → H) := C.dense.denseRange_val
    apply hd.equalizer
    · exact (C.extendRational f).continuous.comp (continuous_const.smul continuous_id)
    · exact continuous_const.smul (C.extendRational f).continuous
    · funext y
      change C.extendRational f ((C.mulI y : C.space) : H) =
        Complex.I • C.extendRational f (y : H)
      rw [C.extendRational_coe f hb, C.extendRational_coe f hb, hI]
  exact congrFun he x

/-- The final complex-linear extension, with no change of bound. -/
def extendComplex (f : C.space →ₗ[ℚ] F) {B : ℝ}
    (hb : ∀ x, ‖f x‖ ≤ B * ‖(x : H)‖)
    (hI : ∀ x, f (C.mulI x) = Complex.I • f x) : H →L[ℂ] F :=
  complexifyRational (C.extendRational f) (C.extendRational_mul_I f hb hI)

@[simp]
theorem extendComplex_coe (f : C.space →ₗ[ℚ] F) {B : ℝ}
    (hb : ∀ x, ‖f x‖ ≤ B * ‖(x : H)‖)
    (hI : ∀ x, f (C.mulI x) = Complex.I • f x) (x : C.space) :
    C.extendComplex f hb hI (x : H) = f x := C.extendRational_coe f hb x

theorem norm_extendComplex_le (f : C.space →ₗ[ℚ] F) {B : ℝ}
    (hb : ∀ x, ‖f x‖ ≤ B * ‖(x : H)‖)
    (hI : ∀ x, f (C.mulI x) = Complex.I • f x) (x : H) :
    ‖C.extendComplex f hb hI x‖ ≤ B * ‖x‖ := C.norm_extendRational_le f hb x

end RationalComplexCore

end

end KadisonKastler

end OAI
