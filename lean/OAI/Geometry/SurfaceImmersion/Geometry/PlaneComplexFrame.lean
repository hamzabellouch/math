import OAI.Geometry.SurfaceImmersion.Geometry.NormalPlaneFrame

namespace OAI

/-! A real coordinate frame from a nonzero vector in the normal plane. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

def planeComplexFrame (w : Base) : Base →L[ℝ] Base :=
  (ContinuousLinearMap.proj 0).smulRight w+
    (ContinuousLinearMap.proj 1).smulRight ![-w 1,w 0]

lemma planeComplexFrame_apply (w v : Base) :
    planeComplexFrame w v = ![w 0*v 0-w 1*v 1,w 1*v 0+w 0*v 1] := by
  ext i
  fin_cases i <;> simp [planeComplexFrame] <;> ring

lemma planeComplexFrame_smooth : ContDiff ℝ ∞ planeComplexFrame := by
  have hJ : ContDiff ℝ ∞ (fun w : Base => (![-w 1,w 0] : Base)) := by
    apply contDiff_pi.mpr
    intro i
    fin_cases i
    · exact (contDiff_apply ℝ ℝ 1).neg
    · exact contDiff_apply ℝ ℝ 0
  exact (contDiff_const.smulRight contDiff_id).add (contDiff_const.smulRight hJ)

lemma planeComplexFrame_injective {w : Base} (hw : w ≠ 0) :
    Function.Injective (planeComplexFrame w) := by
  have hs : (w 0)^2+(w 1)^2 ≠ 0 := by
    intro hz
    have h0 : w 0 = 0 := by nlinarith [sq_nonneg (w 0),sq_nonneg (w 1)]
    have h1 : w 1 = 0 := by nlinarith [sq_nonneg (w 0),sq_nonneg (w 1)]
    apply hw
    ext i
    fin_cases i
    · exact h0
    · exact h1
  intro u v he
  have h0 : w 0*u 0-w 1*u 1 = w 0*v 0-w 1*v 1 := by
    simpa only [planeComplexFrame_apply,Matrix.cons_val_zero] using congrFun he 0
  have h1 : w 1*u 0+w 0*u 1 = w 1*v 0+w 0*v 1 := by
    simpa only [planeComplexFrame_apply,Matrix.cons_val_one,Matrix.cons_val_zero] using congrFun he 1
  have hd0 : ((w 0)^2+(w 1)^2)*(u 0-v 0) = 0 := by
    linear_combination w 0*h0+w 1*h1
  have hd1 : ((w 0)^2+(w 1)^2)*(u 1-v 1) = 0 := by
    linear_combination w 0*h1-w 1*h0
  ext i
  fin_cases i
  · exact sub_eq_zero.mp ((mul_eq_zero.mp hd0).resolve_left hs)
  · exact sub_eq_zero.mp ((mul_eq_zero.mp hd1).resolve_left hs)

lemma planeComplexFrame_bijective {w : Base} (hw : w ≠ 0) :
    Function.Bijective (planeComplexFrame w) := by
  have hi := planeComplexFrame_injective hw
  exact ⟨hi,(LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (f := (planeComplexFrame w).toLinearMap) rfl).mp hi⟩

lemma planeComplexFrame_axis (w : Base) (r : ℝ) :
    planeComplexFrame w ![r,0] = r • w := by
  ext i
  fin_cases i <;> simp [planeComplexFrame_apply,mul_comm]

lemma planeComplexFrame_invertible {w : Base} (hw : w ≠ 0) :
    (planeComplexFrame w).IsInvertible := by
  have hb := planeComplexFrame_bijective hw
  exact ⟨ContinuousLinearEquiv.ofBijective (planeComplexFrame w)
    (LinearMap.ker_eq_bot.mpr hb.1) (LinearMap.range_eq_top.mpr hb.2),rfl⟩

lemma planeComplexFrame_inverse_axis {w : Base} (hw : w ≠ 0) (r : ℝ) :
    (planeComplexFrame w).inverse (r • w) = ![r,0] := by
  apply ((planeComplexFrame_invertible hw).inverse_apply_eq).mpr
  exact (planeComplexFrame_axis w r).symm

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
