import OAI.Geometry.SurfaceImmersion.Geometry.PlaneCurveGraph

namespace OAI

/-! A common linear plane coordinate is regular on either of two nonzero
curve velocities, including the case of collinear opposite velocities. -/
noncomputable section
open scoped ContDiff
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

def planeShearLinear (a : ℝ) : Base →L[ℝ] Base :=
  ContinuousLinearMap.pi ![ContinuousLinearMap.proj (0 : Fin 2) +
    a • ContinuousLinearMap.proj (1 : Fin 2),ContinuousLinearMap.proj (1 : Fin 2)]

lemma planeShearLinear_apply (a : ℝ) (v : Base) :
    planeShearLinear a v = ![v 0+a*v 1,v 1] := by
  ext i
  fin_cases i <;> rfl

lemma planeShearLinear_bijective (a : ℝ) : Function.Bijective (planeShearLinear a) := by
  constructor
  · intro v w he
    have h0 := congrFun he 0
    have h1 := congrFun he 1
    change v 0+a*v 1 = w 0+a*w 1 at h0
    change v 1 = w 1 at h1
    ext i
    fin_cases i
    · change v 0 = w 0
      rw [h1] at h0
      exact add_right_cancel h0
    · exact h1
  · intro w
    refine ⟨![w 0-a*w 1,w 1],?_⟩
    rw [planeShearLinear_apply]
    ext i
    fin_cases i <;> simp

def planeShearEquiv (a : ℝ) : Base ≃L[ℝ] Base :=
  ContinuousLinearEquiv.ofBijective (planeShearLinear a)
    (LinearMap.ker_eq_bot.mpr (planeShearLinear_bijective a).1)
    (LinearMap.range_eq_top.mpr (planeShearLinear_bijective a).2)

lemma plane_second_ne_zero {v : Base} (hv : v ≠ 0) (hv0 : v 0 = 0) : v 1 ≠ 0 := by
  intro hv1
  apply hv
  ext i
  fin_cases i
  · exact hv0
  · exact hv1

theorem exists_common_plane_parameter {v w : Base} (hv : v ≠ 0) (hw : w ≠ 0) :
    ∃ a : ℝ, v 0+a*v 1 ≠ 0 ∧ w 0+a*w 1 ≠ 0 := by
  by_cases hv0 : v 0 = 0
  · have hv1 := plane_second_ne_zero hv hv0
    by_cases hw0 : w 0 = 0
    · have hw1 := plane_second_ne_zero hw hw0
      exact ⟨1,by simpa only [hv0,zero_add,one_mul] using hv1,
        by simpa only [hw0,zero_add,one_mul] using hw1⟩
    · by_cases hw1 : w 0+w 1 = 0
      · refine ⟨2,?_,?_⟩
        · simpa only [hv0,zero_add] using mul_ne_zero (by norm_num : (2:ℝ) ≠ 0) hv1
        · intro h; apply hw0; linarith
      · exact ⟨1,by simpa only [hv0,zero_add,one_mul] using hv1,by simpa only [one_mul] using hw1⟩
  · by_cases hw0 : w 0 = 0
    · have hw1 := plane_second_ne_zero hw hw0
      by_cases hv1 : v 0+v 1 = 0
      · refine ⟨2,?_,?_⟩
        · intro h; apply hv0; linarith
        · simpa only [hw0,zero_add] using mul_ne_zero (by norm_num : (2:ℝ) ≠ 0) hw1
      · exact ⟨1,by simpa only [one_mul] using hv1,by simpa only [hw0,zero_add,one_mul] using hw1⟩
    · exact ⟨0,by simpa using hv0,by simpa using hw0⟩

theorem exists_common_plane_coordinate {v w : Base} (hv : v ≠ 0) (hw : w ≠ 0) :
    ∃ e : Base ≃L[ℝ] Base, (e v) 0 ≠ 0 ∧ (e w) 0 ≠ 0 := by
  obtain ⟨a,hv',hw'⟩ := exists_common_plane_parameter hv hw
  exact ⟨planeShearEquiv a,hv',hw'⟩

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
