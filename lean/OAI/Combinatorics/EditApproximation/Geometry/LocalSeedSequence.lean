import OAI.Combinatorics.EditApproximation.Geometry.UnifiedPhysicalTable
import OAI.Combinatorics.EditApproximation.Geometry.LocalOnlineProgram
import OAI.Combinatorics.EditApproximation.Refinement.PhysicalDependencyRank
import OAI.Combinatorics.EditApproximation.Probability.Median

namespace OAI

/-! Mathematical values for the actual local seed passes. This complete
function is a specification for the lazy program, not a table allocated
by the implementation. Copy streams are kept distinct at every pass. -/

namespace EditApproximation

section Sequence

variable {α : Type*} [DecidableEq α] {M J R : ℕ} [NeZero R]
  (source target : List α) (N P F exponent H Q T S copies : ℕ)
  (factor : ℕ → ℚ) (multiplier : ℕ → ℕ) (tau eta kappa delta : ℚ)
  (group : ℕ → ℕ → PhysicalInternalNode M J → Fin R → CellGroupDraws M F Q)
  (integer : ℕ → ℕ → PhysicalInternalNode M J → Fin R → ℕ → TargetInterval target.length → ℕ)

def localPassValue (seed : PhysicalEntry M J target.length → ℕ) (pass copy : ℕ)
    (node : PhysicalNode M J) (t : ℕ) (q : TargetInterval target.length) : ℚ :=
  physicalLocalRefinement source target seed N P F exponent Q (factor pass) tau delta T
    (fun node t => group pass copy node (Fin.ofNat R (t - 1)))
    (physicalLocalOnline source target seed N P F exponent H T (factor pass) tau eta kappa
      (integer pass copy)) node t q

def localSeedSequence (initial : PhysicalEntry M J target.length → ℕ) :
    ℕ → PhysicalEntry M J target.length → ℕ
  | 0 => initial
  | pass + 1 => fun state => min N (upperMedian (List.ofFn fun copy : Fin copies =>
      ⌈(multiplier pass : ℚ) * localPassValue source target N P F exponent H Q T factor
        tau eta kappa delta group integer (localSeedSequence initial pass) pass copy.val state.1 S state.2⌉₊))

theorem localSeedSequence_zero (initial : PhysicalEntry M J target.length → ℕ) :
    localSeedSequence source target N P F exponent H Q T S copies factor multiplier
      tau eta kappa delta group integer initial 0 = initial := rfl

theorem localSeedSequence_bounded (initial : PhysicalEntry M J target.length → ℕ)
    (hinitial : ∀ state, initial state ≤ N) (pass : ℕ) (state : PhysicalEntry M J target.length) :
    localSeedSequence source target N P F exponent H Q T S copies factor multiplier
      tau eta kappa delta group integer initial pass state ≤ N := by
  cases pass with
  | zero => exact hinitial state
  | succ pass => exact min_le_left _ _

def localRequestValue (initial : PhysicalEntry M J target.length → ℕ)
    (request : PhysicalTableRequest M J target.length) : ℚ :=
  let seed := localSeedSequence source target N P F exponent H Q T S copies factor multiplier
    tau eta kappa delta group integer initial request.pass
  unifiedPhysicalValue source target seed N P F exponent Q (factor request.pass) tau delta T
    (fun node t => group request.pass request.copy node (Fin.ofNat R (t - 1)))
    (physicalLocalOnline source target seed N P F exponent H T (factor request.pass) tau eta kappa
      (integer request.pass request.copy)) request.node request.index request.state

theorem localRequestValue_warmup (initial : PhysicalEntry M J target.length → ℕ)
    (pass copy : ℕ) (node : PhysicalNode M J) (j : ℕ) (hj : j ≤ T) (q : TargetInterval target.length) :
    localRequestValue source target N P F exponent H Q T S copies factor multiplier
      tau eta kappa delta group integer initial (PhysicalTableRequest.warmup pass copy node j q) =
    physicalLocalWarmup source target
      (localSeedSequence source target N P F exponent H Q T S copies factor multiplier
        tau eta kappa delta group integer initial pass) N P F (factor pass) j (node, q) :=
  unifiedPhysicalValue_warmup _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hj _

theorem localRequestValue_refinement (initial : PhysicalEntry M J target.length → ℕ)
    (pass copy : ℕ) (node : PhysicalNode M J) (t : ℕ) (q : TargetInterval target.length) :
    localRequestValue source target N P F exponent H Q T S copies factor multiplier
      tau eta kappa delta group integer initial (PhysicalTableRequest.refinement pass copy node T t q) =
    localPassValue source target N P F exponent H Q T factor tau eta kappa delta group integer
      (localSeedSequence source target N P F exponent H Q T S copies factor multiplier
        tau eta kappa delta group integer initial pass) pass copy node t q :=
  unifiedPhysicalValue_refinement _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _

end Sequence

end EditApproximation

end OAI
