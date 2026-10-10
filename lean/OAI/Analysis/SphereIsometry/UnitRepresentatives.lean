import OAI.Analysis.SphereIsometry.Basic

namespace OAI

/-!
# Unit representatives, including the zero vector

The fallback unit vector is used only at zero. The exact error identity permits
normalization of arbitrary representatives of a unit ultranorm class.
-/

noncomputable section
namespace Tingley

universe u
variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]

def unitize (e : UnitSphere X) (a : X) : UnitSphere X := by
  classical
  exact if ha : a = 0 then e else normalize a ha

@[simp] theorem unitize_zero (e : UnitSphere X) : unitize e 0 = e := by
  simp [unitize]

theorem unitize_of_ne_zero (e : UnitSphere X) {a : X} (ha : a ≠ 0) :
    unitize e a = normalize a ha := by
  simp [unitize, ha]

theorem norm_smul_unitize (e : UnitSphere X) (a : X) :
    ‖a‖ • (unitize e a : X) = a := by
  by_cases ha : a = 0
  · simp [ha]
  · rw [unitize_of_ne_zero e ha]
    exact norm_smul_normalize a ha

theorem sub_unitize (e : UnitSphere X) (a : X) :
    a - (unitize e a : X) = (‖a‖ - 1) • (unitize e a : X) := by
  rw [sub_smul, norm_smul_unitize, one_smul]

theorem norm_sub_unitize (e : UnitSphere X) (a : X) :
    ‖a - (unitize e a : X)‖ = |‖a‖ - 1| := by
  rw [sub_unitize, norm_smul, Real.norm_eq_abs, UnitSphere.norm_coe, mul_one]

end Tingley

end

end OAI
