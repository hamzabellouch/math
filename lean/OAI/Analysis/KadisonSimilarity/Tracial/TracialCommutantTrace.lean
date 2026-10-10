import OAI.Analysis.KadisonSimilarity.Tracial.OppositeTracialGeometry

namespace OAI

/-! The vacuum trace on the left commutant, obtained directly from tracial
conjugation and the dense algebra vectors. -/

noncomputable section
namespace KadisonSimilarity
open Generator.Tracial UltrapowerBridge
namespace TracialCornerGeometry

variable {P H : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (G : TracialCornerGeometry P H)

theorem conjugation_involutive : Function.Involutive G.conjugation :=
  tracialConjugation_involutive G.trace G.vector G.inner_vector G.tracial G.dense_vector

theorem inner_conjugation_swap (x y : H) :
    inner ℂ (G.conjugation x) y = inner ℂ (G.conjugation y) x := by
  have h := inner_tracialConjugation G.trace G.vector G.inner_vector G.tracial
    G.dense_vector x (G.conjugation y)
  change inner ℂ (G.conjugation x) (G.conjugation (G.conjugation y)) =
    inner ℂ (G.conjugation y) x at h
  rwa [G.conjugation_involutive y] at h

/-- A left-module endomorphism has its adjoint vacuum vector given by tracial conjugation. -/
theorem commutant_conjugation_vector (Z : H →L[ℂ] H)
    (hZ : ∀ a, Z.comp (G.left a) = (G.left a).comp Z) :
    G.conjugation (Z (G.vector 1)) = star Z (G.vector 1) := by
  apply ext_inner_right ℂ
  intro ξ
  refine G.dense_vector.induction_on ξ (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro a
  rw [G.inner_conjugation_swap, G.conjugation_vector]
  have hleft : G.vector (star a) = (G.left a).adjoint (G.vector 1) := by
    rw [← ContinuousLinearMap.star_eq_adjoint, ← map_star, G.left_vector, mul_one]
  rw [hleft, ContinuousLinearMap.adjoint_inner_left]
  have hcomm := congrArg (fun T : H →L[ℂ] H => T (G.vector 1)) (hZ a)
  change Z (G.left a (G.vector 1)) = G.left a ((Z : H →L[ℂ] H) (G.vector 1)) at hcomm
  rw [← hcomm, G.left_vector, mul_one]
  exact (ContinuousLinearMap.adjoint_inner_left Z (G.vector a) (G.vector 1)).symm

theorem commutant_vector_trace (Z W : H →L[ℂ] H)
    (hZ : ∀ a, Z.comp (G.left a) = (G.left a).comp Z)
    (hW : ∀ a, W.comp (G.left a) = (G.left a).comp W) :
    inner ℂ (G.vector 1) (Z (W (G.vector 1))) =
      inner ℂ (G.vector 1) (W (Z (G.vector 1))) := by
  calc
    _ = inner ℂ (star Z (G.vector 1)) (W (G.vector 1)) :=
      (ContinuousLinearMap.adjoint_inner_left Z (W (G.vector 1)) (G.vector 1)).symm
    _ = inner ℂ (G.conjugation (Z (G.vector 1))) (W (G.vector 1)) := by
      rw [G.commutant_conjugation_vector Z hZ]
    _ = inner ℂ (G.conjugation (W (G.vector 1))) (Z (G.vector 1)) :=
      G.inner_conjugation_swap _ _
    _ = inner ℂ (star W (G.vector 1)) (Z (G.vector 1)) := by
      rw [G.commutant_conjugation_vector W hW]
    _ = _ := ContinuousLinearMap.adjoint_inner_left W (Z (G.vector 1)) (G.vector 1)

def leftCommutant : VonNeumannAlgebra H := starSubalgebraCommutant G.left.range

theorem mem_leftCommutant_iff (Z : H →L[ℂ] H) :
    Z ∈ G.leftCommutant ↔ ∀ a, Z.comp (G.left a) = (G.left a).comp Z := by
  change Z ∈ starSubalgebraCommutant G.left.range ↔ _
  rw [← SetLike.mem_coe, coe_starSubalgebraCommutant]
  constructor
  · intro hz a
    exact (hz (G.left a) ⟨a, rfl⟩).symm
  · intro hz
    rintro _ ⟨a, rfl⟩
    exact (hz a).symm

theorem leftCommutant_commutes (Z : G.leftCommutant.toStarSubalgebra) (a : P) :
    (Z : H →L[ℂ] H).comp (G.left a) = (G.left a).comp (Z : H →L[ℂ] H) :=
  (G.mem_leftCommutant_iff (Z : H →L[ℂ] H)).mp Z.property a

/-- The left commutant carries the faithful normal vacuum trace. -/
def commutantTracialRepresentation (h1 : G.trace 1 = 1) :
    TracialRepresentation G.leftCommutant where
  vector := G.vector 1
  norm_vector := G.norm_identityVector h1
  cyclic Z W := G.commutant_vector_trace Z W
    (G.leftCommutant_commutes Z) (G.leftCommutant_commutes W)
  separating Z hz := by
    ext ξ
    change (Z : H →L[ℂ] H) ξ = 0
    refine G.dense_vector.induction_on ξ (isClosed_eq (by fun_prop) (by fun_prop)) ?_
    intro a
    have h := congrArg (fun T : H →L[ℂ] H => T (G.vector 1)) (G.leftCommutant_commutes Z a)
    change (Z : H →L[ℂ] H) (G.left a (G.vector 1)) = G.left a ((Z : H →L[ℂ] H) (G.vector 1)) at h
    simpa only [G.left_vector, mul_one, hz, map_zero, zero_apply] using h

end TracialCornerGeometry
end KadisonSimilarity

end

end OAI
