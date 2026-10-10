import OAI.Combinatorics.EditApproximation.Refinement.PhysicalLocalOnlineKeys
import OAI.Combinatorics.EditApproximation.Geometry.BandDimension
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-! A single finite source range bounds every actual local online sampler,
independently of the incoming seed and queried state. -/

namespace EditApproximation

theorem keyedOnlineBandG_le {α : Type*} (source target : List α) {M : ℕ}
    (parent : TargetInterval source.length) (P exponent H b : ℕ) (hP : 0 < P) (tau : ℚ)
    (child : Fin M → TargetInterval target.length → ℚ) (r : TargetInterval target.length) :
    keyedOnlineBandG source target parent P exponent H b tau child r ≤
      H + M * (40 * P + 2) ^ 2 + 2 := by
  have hdimension := bandCoordinates_card_le parent r hP
    (representativeBandActions source target parent r b P tau ((2 : ℚ) ^ (-(exponent : ℤ))) child)
    (fun action ha => representativeBandActions_wide source target parent r b P tau _ child action ha)
  exact Nat.add_le_add_right (Nat.add_le_add_left hdimension H) 2



theorem physicalLocalOnlineMass_le {α : Type*} [DecidableEq α] {M J : ℕ}
    (source target : List α) (U : PhysicalEntry M J target.length → ℕ)
    (N P F : ℕ) (A : ℚ) (T exponent H : ℕ) (tau : ℚ) (hP : 0 < P)
    (key : PhysicalLocalOnlineKey M J N target.length) :
    physicalLocalOnlineMass source target U N P F A T exponent H tau key ≤ localOnlineMassBound M P H := by
  apply optimizerTriangularMass_monotone
  exact Nat.pow_le_pow_left (keyedOnlineBandG_le source target _ P exponent H _ hP tau _ _) 80

theorem localOnlineMassBound_positive (M P H : ℕ) : 0 < localOnlineMassBound M P H :=
  optimizerTriangularMass_positive _ (pow_pos (by omega) _)

end EditApproximation

end OAI
