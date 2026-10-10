import OAI.Combinatorics.EditApproximation.Binary.BinaryRefinementLists
import OAI.Combinatorics.EditApproximation.Binary.BinaryPhysicalContinuation

namespace OAI

/-! The nonterminal warmup step uses the same local representative grids,
but computes a single Bellman minimum and performs no online update. -/

namespace EditApproximation
namespace BinaryFraction

def localWarmupKernelWithWork {nx ny M : ℕ} (parent : TargetInterval nx)
    (N P F : ℕ) (a : BinaryFraction) (initial : TargetInterval ny → BinaryFraction)
    (child : Fin M × TargetInterval ny → BinaryFraction) (query : TargetInterval ny) :
    BinaryFraction × ℕ :=
  let representatives := localRepresentativesWithWork N P F a initial query
  let actions := wideActionsFromRepresentativesWithWork M parent representatives.1 P
  let L := canonicalMulWithWork (nat 128) (nat F)
  let result := bellmanWithWork endpointDistanceWithWork L.1 (initial query) child query actions.1
  (result.1, representatives.2 + actions.2 + L.2 + result.2 + 3)

theorem localWarmupKernelWithWork_value {nx ny M : ℕ} (parent : TargetInterval nx)
    (N P F : ℕ) (hP : 0 < P) (a : BinaryFraction) (initial : TargetInterval ny → BinaryFraction)
    (child : Fin M × TargetInterval ny → BinaryFraction) (query : TargetInterval ny) :
    (localWarmupKernelWithWork parent N P F a initial child query).1.value =
      rationalBellman (fun q => (initial q).value) (fun p q => (targetEndpointDistance p q : ℚ)) (128 * F)
        (rationalActualWideActions parent
          (localRefinementRepresentatives N P F a.value (fun q => (initial q).value) query) P)
        (fun is => (child is).value) query := by
  simp only [localWarmupKernelWithWork, bellmanWithWork_value,
    wideActionsFromRepresentativesWithWork_decode _ _ _ _ hP,
    localRepresentativesWithWork_value _ _ _ hP, canonicalMulWithWork_value,
    nat_value, endpointDistanceWithWork_value]
  rfl

end BinaryFraction
end EditApproximation

end OAI
