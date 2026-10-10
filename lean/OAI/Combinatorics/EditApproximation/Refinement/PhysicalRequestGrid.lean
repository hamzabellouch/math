import OAI.Combinatorics.EditApproximation.Refinement.PhysicalLocalDenominator
import OAI.Combinatorics.EditApproximation.Geometry.ChargedGlobalQuery
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-! The canonical cache grid for every request, including terminal and
warmup branches.  This invariant holds for all incoming seeds and draws. -/

namespace EditApproximation



theorem localRequestValue_den_dvd {α : Type*} [DecidableEq α] {M J R : ℕ} [NeZero R]
    (source target : List α) (N P F exponent H Q T S copies ell : ℕ)
    (factor : ℕ → ℚ) (multiplier : ℕ → ℕ) (tau eta kappa : ℚ)
    (group : ℕ → ℕ → PhysicalInternalNode M J → Fin R → CellGroupDraws M F Q)
    (integer : ℕ → ℕ → PhysicalInternalNode M J → Fin R → ℕ → TargetInterval target.length → ℕ)
    (initial : PhysicalEntry M J target.length → ℕ) (hell : 0 < ell)
    (request : PhysicalTableRequest M J target.length) :
    (localRequestValue source target N P F exponent H Q T S copies factor multiplier
      tau eta kappa (1 / (ell : ℚ) ^ 10) group integer initial request).den ∣
      (ell ^ 10 + 1) ^ request.remainingDepth := by
  unfold localRequestValue unifiedPhysicalValue
  split
  · rw [physicalLocalWarmup_den_one]
    exact one_dvd _
  · exact physicalLocalOnlineRefinement_den_dvd source target _ N P F exponent H Q _ tau eta kappa
      T ell hell _ _ request.node (request.index - T) request.state

theorem chargedRequestValue_den_dvd {α : Type*} [DecidableEq α] {M J R : ℕ} [NeZero R]
    (source target : List α) (N P F exponent H Q T S passes copies ell : ℕ)
    (factor : ℕ → ℚ) (multiplier : ℕ → ℕ) (tau eta kappa : ℚ)
    (group : ℕ → ℕ → PhysicalInternalNode M J → Fin R → CellGroupDraws M F Q)
    (integer : ℕ → ℕ → PhysicalInternalNode M J → Fin R → ℕ → TargetInterval target.length → ℕ)
    (initial : PhysicalEntry M J target.length → ℕ) (hell : 0 < ell)
    (request : ChargedPhysicalRequest M J target.length passes copies T S) :
    (chargedRequestValue source target N P F exponent H Q T S passes copies factor multiplier
      tau eta kappa (1 / (ell : ℚ) ^ 10) group integer initial request).den ∣
      (ell ^ 10 + 1) ^ chargedPhysicalRemaining request := by
  cases request with
  | inl entry => simp only [chargedRequestValue, chargedPhysicalRemaining, Rat.den_natCast, one_dvd]
  | inr request =>
    exact localRequestValue_den_dvd (R := R) source target N P F exponent H Q T S copies ell
      factor multiplier tau eta kappa group integer initial hell request.val

end EditApproximation

end OAI
