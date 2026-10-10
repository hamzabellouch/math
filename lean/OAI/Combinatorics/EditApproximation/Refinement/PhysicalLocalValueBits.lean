import OAI.Combinatorics.EditApproximation.Refinement.PhysicalLocalDenominator
import OAI.Combinatorics.EditApproximation.Geometry.ChargedGlobalQuery
import OAI.Combinatorics.EditApproximation.Numerics.RationalIntermediateBits

namespace OAI

/-! Actual cached local values have short canonical rational encodings on
every seed, without an accuracy event. -/

namespace EditApproximation

 theorem unifiedPhysicalValue_encoding_bits {α : Type*} [DecidableEq α] {M J : ℕ}
    (source target : List α) (U : PhysicalEntry M J target.length → ℕ)
    (N P F exponent Q : ℕ) (A tau : ℚ) (hsize : source.length + target.length ≤ N)
    (T ell : ℕ) (hell : 0 < ell)
    (draw : PhysicalInternalNode M J → ℕ → CellGroupDraws M F Q)
    (online : PhysicalNode M J → PhysicalChildTables M target.length → ℕ →
      TargetInterval target.length → List (PhysicalRationalAction M target.length))
    (honline : ∀ node children t q action, action ∈ online node children t q → action.connection.den = 1)
    (node : PhysicalNode M J) (t : ℕ) (q : TargetInterval target.length) :
    rationalEncodingBits (unifiedPhysicalValue source target U N P F exponent Q A tau
      (1 / (ell : ℚ) ^ 10) T draw online node t q) ≤
      Nat.size ((32 * F + 1) * N) + 2 * (J - node.1.val) * Nat.size (ell ^ 10 + 1) + 3 := by
  unfold unifiedPhysicalValue
  split
  · exact (physicalLocalWarmup_encoding_bits source target U N P F A hsize t (node, q)).trans
      (by omega)
  · exact physicalLocalRefinement_encoding_bits source target U N P F exponent Q A tau hsize T ell hell
      draw online honline node (t - T) q

 theorem localRequestValue_encoding_bits {α : Type*} [DecidableEq α] {M J R : ℕ} [NeZero R]
    (source target : List α) (N P F exponent H Q T S copies ell : ℕ)
    (factor : ℕ → ℚ) (multiplier : ℕ → ℕ) (tau eta kappa : ℚ)
    (group : ℕ → ℕ → PhysicalInternalNode M J → Fin R → CellGroupDraws M F Q)
    (integer : ℕ → ℕ → PhysicalInternalNode M J → Fin R → ℕ → TargetInterval target.length → ℕ)
    (initial : PhysicalEntry M J target.length → ℕ) (hell : 0 < ell)
    (hsize : source.length + target.length ≤ N) (request : PhysicalTableRequest M J target.length) :
    rationalEncodingBits (localRequestValue source target N P F exponent H Q T S copies factor multiplier
      tau eta kappa (1 / (ell : ℚ) ^ 10) group integer initial request) ≤
      Nat.size ((32 * F + 1) * N) + 2 * J * Nat.size (ell ^ 10 + 1) + 3 := by
  unfold localRequestValue
  apply (unifiedPhysicalValue_encoding_bits source target _ N P F exponent Q _ tau hsize T ell hell _ _
    (physicalLocalOnline_connection_den source target _ N P F exponent H T _ tau eta kappa _)
    request.node request.index request.state).trans
  have hm := Nat.mul_le_mul_right (Nat.size (ell ^ 10 + 1))
    (Nat.mul_le_mul_left 2 (Nat.sub_le J request.node.1.val))
  omega

 theorem chargedRequestValue_encoding_bits {α : Type*} [DecidableEq α] {M J R : ℕ} [NeZero R]
    (source target : List α) (N P F exponent H Q T S passes copies ell : ℕ)
    (factor : ℕ → ℚ) (multiplier : ℕ → ℕ) (tau eta kappa : ℚ)
    (group : ℕ → ℕ → PhysicalInternalNode M J → Fin R → CellGroupDraws M F Q)
    (integer : ℕ → ℕ → PhysicalInternalNode M J → Fin R → ℕ → TargetInterval target.length → ℕ)
    (initial : PhysicalEntry M J target.length → ℕ) (hell : 0 < ell)
    (hsize : source.length + target.length ≤ N) (hinitial : ∀ entry, initial entry ≤ N)
    (request : ChargedPhysicalRequest M J target.length passes copies T S) :
    rationalEncodingBits (chargedRequestValue source target N P F exponent H Q T S passes copies
      factor multiplier tau eta kappa (1 / (ell : ℚ) ^ 10) group integer initial request) ≤
      Nat.size ((32 * F + 1) * N) + 2 * J * Nat.size (ell ^ 10 + 1) + 3 := by
  cases request with
  | inl entry =>
    change rationalEncodingBits (initial entry : ℚ) ≤ _
    rw [rationalEncodingBits_natCast]
    have hn : N ≤ (32 * F + 1) * N := by nlinarith
    have hs := Nat.size_le_size ((hinitial entry).trans hn)
    omega
  | inr request =>
    exact localRequestValue_encoding_bits source target N P F exponent H Q T S copies ell
      factor multiplier tau eta kappa group integer initial hell hsize request.val

end EditApproximation

end OAI
