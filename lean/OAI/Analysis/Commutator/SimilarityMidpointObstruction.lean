import Mathlib

namespace OAI

noncomputable section

noncomputable section

namespace Kadison.SimilarityObstruction

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]

lemma midpoint_curvature (π : A →ₐ[ℂ] B) (a b : A) :
    2 • (π (a*b) + star (π (star (a*b)))) -
      (π a + star (π (star a))) * (π b + star (π (star b))) =
        (π a - star (π (star a))) * (π b - star (π (star b))) := by
  simp only [star_mul, map_mul, two_smul]
  noncomm_ring

lemma midpoint_multiplicative_iff_star (π : A →ₐ[ℂ] B) :
    (∀ a b : A, 2 • (π (a*b) + star (π (star (a*b)))) =
      (π a + star (π (star a))) * (π b + star (π (star b)))) ↔
      ∀ a : A, π (star a) = star (π a) := by
  constructor
  · intro h a
    have hz : (π a - star (π (star a))) * (π (star a) - star (π a)) = 0 := by
      have e := midpoint_curvature π a (star a)
      rw [h a (star a), sub_self] at e
      simpa only [star_star] using e.symm
    have hz' : (π a - star (π (star a))) * star (π a - star (π (star a))) = 0 := by
      have e : π (star a) - star (π a) = -star (π a - star (π (star a))) := by
        simp only [star_sub, star_star, neg_sub]
      rw [e, mul_neg, neg_eq_zero] at hz
      exact hz
    have he := (CStarRing.mul_star_self_eq_zero_iff _).mp hz'
    have he' := congrArg star (sub_eq_zero.mp he)
    simpa only [star_star] using he'.symm
  · intro h a b
    simp only [h, star_star, map_mul, two_smul]
    noncomm_ring

end Kadison.SimilarityObstruction
end
end

end OAI
