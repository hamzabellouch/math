import OAI.Analysis.IrrationalRotation.Model.Spectral

namespace OAI

noncomputable section
namespace Invariant233
namespace TracialState
variable {A : Type*} [CStarAlgebra A]

theorem inverse_normSquare_first_term (τ : TracialState A) (a b : A)
    (ha : IsUnit a) :
    τ ((Ring.inverse a * star (Ring.inverse a)) * (star b * a)) =
      star (τ (Ring.inverse a * b)) := by
  calc
    τ ((Ring.inverse a * star (Ring.inverse a)) * (star b * a)) =
        τ (((Ring.inverse a * star (Ring.inverse a)) * star b) * a) := by
          simp only [mul_assoc]
    _ = τ (a * ((Ring.inverse a * star (Ring.inverse a)) * star b)) :=
      τ.tracial _ _
    _ = τ ((a * Ring.inverse a) * (star (Ring.inverse a) * star b)) := by
      simp only [mul_assoc]
    _ = τ (star (Ring.inverse a) * star b) := by
      rw [Ring.mul_inverse_cancel a ha, one_mul]
    _ = star (τ (b * Ring.inverse a)) := by rw [← star_mul, τ.map_star]
    _ = star (τ (Ring.inverse a * b)) := by rw [τ.tracial b (Ring.inverse a)]

theorem inverse_normSquare_second_term (a b : A) (ha : IsUnit a) :
    (Ring.inverse a * star (Ring.inverse a)) * (star a * b) =
      Ring.inverse a * b := by
  have hc : star (Ring.inverse a) * star a = 1 := by
    rw [← star_mul, Ring.mul_inverse_cancel a ha, star_one]
  calc
    (Ring.inverse a * star (Ring.inverse a)) * (star a * b) =
        Ring.inverse a * ((star (Ring.inverse a) * star a) * b) := by
          simp only [mul_assoc]
    _ = Ring.inverse a * b := by rw [hc, one_mul]

theorem re_inverse_normSquare_differential (τ : TracialState A) (a b : A)
    (ha : IsUnit a) :
    (τ (Ring.inverse (star a * a) * (star b * a + star a * b))).re =
      2 * (τ (Ring.inverse a * b)).re := by
  rw [Ring.inverse_mul (Or.inr ha), Ring.inverse_star, mul_add, map_add,
    τ.inverse_normSquare_first_term a b ha, inverse_normSquare_second_term a b ha]
  simp [Complex.add_re, two_mul]

theorem hasDerivAt_normSquare {f : ℝ → A} {f' : A} {t : ℝ}
    (hf : HasDerivAt f f' t) :
    HasDerivAt (fun s => star (f s) * f s)
      (star f' * f t + star (f t) * f') t := by
  exact hf.star.mul hf

end TracialState
end Invariant233

end

end OAI
