import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralCoerciveInverse
import Mathlib.Analysis.Complex.Basic

namespace OAI

/-! The complex linear inverse of a real coercive form compatible with multiplication by i. -/

namespace DefocusingNLS
theorem spectralCompatibleInner_I {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [NormedSpace ℂ V] (u v : V) :
    inner ℝ (Complex.I • u) v = -inner ℝ u (Complex.I • v) := by
  have he : Complex.I • (u-Complex.I • v)=Complex.I • u+v := by
    simp [smul_sub,smul_smul]
  have hn : ‖Complex.I • u+v‖^2=‖u-Complex.I • v‖^2 := by
    rw [← he,norm_smul,Complex.norm_I,one_mul]
  have ha := norm_add_sq_real (Complex.I • u) v
  have hs := norm_sub_sq_real u (Complex.I • v)
  simp only [norm_smul,Complex.norm_I,one_mul] at ha hs
  linarith

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
noncomputable local instance : InnerProductSpace ℝ E := InnerProductSpace.complexToReal

theorem spectralInner_I (u v : E) :
    inner ℝ (Complex.I • u) v = -inner ℝ u (Complex.I • v) := by
  change (inner ℂ (Complex.I • u) v).re = -(inner ℂ u (Complex.I • v)).re
  simp [inner_smul_left,inner_smul_right]

noncomputable def spectralComplexLinearOfI (T : E →L[ℝ] E)
    (hI : ∀ u, T (Complex.I • u)=Complex.I • T u) : E →L[ℂ] E where
  toFun := T
  map_add' := T.map_add
  map_smul' := by
    intro c u
    change T (c • u)=c • T u
    calc
      T (c • u)=T (c.re • u+c.im • (Complex.I • u)) := by
        congr 1
        conv_lhs => rw [← c.re_add_im]
        simp only [add_smul,mul_smul,Complex.coe_smul]
      _=c.re • T u+c.im • (Complex.I • T u) := by
        rw [map_add,T.map_smul,T.map_smul,hI]
      _=c • T u := by
        conv_rhs => rw [← c.re_add_im]
        simp only [add_smul,mul_smul,Complex.coe_smul]
  cont := T.continuous

variable [CompleteSpace E]

noncomputable def spectralHermitianInverse (B : E →L[ℝ] E →L[ℝ] ℝ) (hB : IsCoercive B)
    (hI : ∀ u v, B (Complex.I • u) v = -B u (Complex.I • v)) : E →L[ℂ] E :=
  let T := (spectralCoerciveInverse B hB).comp
    (InnerProductSpace.toDual ℝ E).toContinuousLinearEquiv.toContinuousLinearMap
  spectralComplexLinearOfI T (by
    intro f
    apply Eq.symm
    apply spectralCoerciveInverse_unique B hB
    intro v
    rw [hI]
    have he := spectralCoerciveInverse_equation B hB
      (InnerProductSpace.toDual ℝ E f) (Complex.I • v)
    change B (T f) (Complex.I • v)=inner ℝ f (Complex.I • v) at he
    change -B (T f) (Complex.I • v)=inner ℝ (Complex.I • f) v
    rw [he,spectralInner_I])

end
end DefocusingNLS

end OAI
