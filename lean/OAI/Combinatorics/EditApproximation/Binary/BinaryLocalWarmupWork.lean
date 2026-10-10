import OAI.Combinatorics.EditApproximation.Binary.BinaryPhysicalContinuationWork
import OAI.Combinatorics.EditApproximation.Binary.BinaryPreparedListBounds

namespace OAI

/-! The warmup branch constructs its actual local representative/action
lists and evaluates their finite Bellman minimum with counted arithmetic. -/

namespace EditApproximation
namespace BinaryFraction

def localWarmupWordBudget (M B : ℕ) : ℕ :=
  let W := physicalContinuationInputBudget M (B + 4)
  W + bellmanActionWordBudget M W

def localWarmupBitBudget (M P F B : ℕ) : ℕ :=
  let nr := (B + 1) * (64 * F * P + 2) ^ 2
  let W := physicalContinuationInputBudget M (B + 4)
  localRepresentativesBitBudget P F B + wideActionsBitBudget M P nr (B + 4) +
    2000 * (B + 5) ^ 2 + bellmanBitBudget M (nr * (40 * P + 2) ^ (2 * M)) W W
      (endpointDistanceBitBudget (B + 4)) + 3

private theorem wideWork_mono (M P n m B : ℕ) (h : n ≤ m) :
    wideActionsBitBudget M P n B ≤ wideActionsBitBudget M P m B := by
  unfold wideActionsBitBudget
  dsimp only
  exact Nat.mul_le_mul_right _ h

private theorem bellmanWork_mono (M n m B F C : ℕ) (h : n ≤ m) :
    bellmanBitBudget M n B F C ≤ bellmanBitBudget M m B F C := by
  unfold bellmanBitBudget
  gcongr

private theorem endpointDistance_uniform {n : ℕ} (q r : TargetInterval n) (B : ℕ)
    (hn : Nat.size n + 2 ≤ B) :
    (endpointDistanceWithWork q r).1.width ≤ endpointDistanceWordBudget B ∧
      (endpointDistanceWithWork q r).2 ≤ endpointDistanceBitBudget B :=
  endpointDistanceWithWork_bounds q r B
    ((Nat.add_le_add_right (Nat.size_le_size (q.ordered.trans q.valid)) 2).trans hn)
    ((Nat.add_le_add_right (Nat.size_le_size q.valid) 2).trans hn)
    ((Nat.add_le_add_right (Nat.size_le_size (r.ordered.trans r.valid)) 2).trans hn)
    ((Nat.add_le_add_right (Nat.size_le_size r.valid) 2).trans hn)

private theorem warmupCoefficient_bounds (F B : ℕ) (hB : 10 ≤ B)
    (hF : Nat.size F + 2 ≤ B) :
    (canonicalMulWithWork (nat 128) (nat F)).1.width ≤ 4 * (B + 4) + 2 ∧
      (canonicalMulWithWork (nat 128) (nat F)).2 ≤ 2000 * (B + 5) ^ 2 := by
  have h128 : (nat 128).width ≤ B + 4 :=
    (nat_width_le 128).trans (by change 10 ≤ B + 4; omega)
  have hFw : (nat F).width ≤ B + 4 := (nat_width_le F).trans (by omega)
  exact ⟨canonicalMulWithWork_width _ _ (B + 4) h128 hFw,
    canonicalMulWithWork_cost _ _ (B + 4) h128 hFw⟩

private theorem warmupBellman_bounds {ny M : ℕ} (F B : ℕ)
    (initial : TargetInterval ny → BinaryFraction)
    (child : Fin M × TargetInterval ny → BinaryFraction) (query : TargetInterval ny)
    (actions : List (BinaryBellmanAction (TargetInterval ny) (Fin M × TargetInterval ny) M))
    (hB : 10 ≤ B) (hny : Nat.size ny + 2 ≤ B) (hF : Nat.size F + 2 ≤ B)
    (hi : ∀ r, (initial r).width ≤ B) (hc : ∀ s, (child s).width ≤ B)
    (hconn : ∀ action ∈ actions, action.connection.width ≤ connectionWordBudget M (B + 4)) :
    (bellmanWithWork endpointDistanceWithWork (canonicalMulWithWork (nat 128) (nat F)).1
      (initial query) child query actions).1.width ≤ localWarmupWordBudget M B ∧
    (bellmanWithWork endpointDistanceWithWork (canonicalMulWithWork (nat 128) (nat F)).1
      (initial query) child query actions).2 ≤ bellmanBitBudget M actions.length
      (physicalContinuationInputBudget M (B + 4)) (physicalContinuationInputBudget M (B + 4))
        (endpointDistanceBitBudget (B + 4)) := by
  let W := physicalContinuationInputBudget M (B + 4)
  have hBW : B ≤ W := by dsimp only [W, physicalContinuationInputBudget]; omega
  have hL := (warmupCoefficient_bounds F B hB hF).1
  have hWcoefficient : 4 * (B + 4) + 2 ≤ W := by
    dsimp only [W, physicalContinuationInputBudget]; omega
  exact bellmanWithWork_bounds endpointDistanceWithWork _ (initial query) child query actions W W
    (endpointDistanceBitBudget (B + 4)) (hL.trans hWcoefficient) ((hi query).trans hBW)
    (fun action _ => (endpointDistance_uniform query action.center (B + 4) (by omega)).1.trans
      (by dsimp only [W, physicalContinuationInputBudget]; omega))
    (fun action _ => (endpointDistance_uniform query action.center (B + 4) (by omega)).2)
    (fun action ha => (hconn action ha).trans (by dsimp only [W, physicalContinuationInputBudget]; omega))
    (fun action _ i => (hc _).trans hBW)

private theorem warmupWide_bounds {nx ny M : ℕ} (parent : TargetInterval nx)
    (reps : List (ℕ × TargetInterval ny)) (P F B : ℕ) (hP : 0 < P)
    (initial : TargetInterval ny → BinaryFraction)
    (child : Fin M × TargetInterval ny → BinaryFraction) (query : TargetInterval ny)
    (hB : 10 ≤ B) (hnx : Nat.size nx + 2 ≤ B) (hny : Nat.size ny + 2 ≤ B)
    (hM : Nat.size M ≤ B) (hPbits : Nat.size P ≤ B) (hF : Nat.size F + 2 ≤ B)
    (hrep : ∀ br ∈ reps, Nat.size br.1 ≤ B + 4)
    (hi : ∀ r, (initial r).width ≤ B) (hc : ∀ s, (child s).width ≤ B) :
    (bellmanWithWork endpointDistanceWithWork (canonicalMulWithWork (nat 128) (nat F)).1
      (initial query) child query (wideActionsFromRepresentativesWithWork M parent reps P).1).1.width ≤
        localWarmupWordBudget M B ∧
    (wideActionsFromRepresentativesWithWork M parent reps P).2 +
      (canonicalMulWithWork (nat 128) (nat F)).2 +
      (bellmanWithWork endpointDistanceWithWork (canonicalMulWithWork (nat 128) (nat F)).1
        (initial query) child query (wideActionsFromRepresentativesWithWork M parent reps P).1).2 ≤
      wideActionsBitBudget M P reps.length (B + 4) + 2000 * (B + 5) ^ 2 +
      bellmanBitBudget M (reps.length * (40 * P + 2) ^ (2 * M))
        (physicalContinuationInputBudget M (B + 4)) (physicalContinuationInputBudget M (B + 4))
        (endpointDistanceBitBudget (B + 4)) := by
  have hw := wideActionsFromRepresentativesWithWork_bounds (M := M) parent reps P (B + 4) hP
    (by omega) (by omega) (by omega) (by omega) hrep
  have hb := warmupBellman_bounds F B initial child query _ hB hny hF hi hc hw.2.1
  have hbc := hb.2.trans (bellmanWork_mono M _ _ _ _ _ hw.1)
  exact ⟨hb.1, Nat.add_le_add (Nat.add_le_add hw.2.2 (warmupCoefficient_bounds F B hB hF).2) hbc⟩

attribute [local irreducible] localRepresentativesWithWork wideActionsFromRepresentativesWithWork

theorem localWarmupKernelWithWork_bounds {nx ny M : ℕ} (parent : TargetInterval nx)
    (N P F B : ℕ) (hP : 0 < P) (hFpos : 1 ≤ F) (a : BinaryFraction)
    (initial : TargetInterval ny → BinaryFraction) (child : Fin M × TargetInterval ny → BinaryFraction)
    (query : TargetInterval ny) (hB : 10 ≤ B) (hN : Nat.size N ≤ B)
    (hnx : Nat.size nx + 2 ≤ B) (hny : Nat.size ny + 2 ≤ B)
    (hM : Nat.size M ≤ B) (hPbits : Nat.size P ≤ B) (hF : Nat.size F + 2 ≤ B)
    (ha : a.width ≤ B) (hi : ∀ r, (initial r).width ≤ B) (hc : ∀ s, (child s).width ≤ B) :
    (localWarmupKernelWithWork parent N P F a initial child query).1.width ≤ localWarmupWordBudget M B ∧
      (localWarmupKernelWithWork parent N P F a initial child query).2 ≤ localWarmupBitBudget M P F B := by
  let reps := localRepresentativesWithWork N P F a initial query
  have hr := localRepresentativesWithWork_cost N P F B a initial query (by omega) hN hF hFpos
    hPbits hP (by omega) ha hi
  have hrl := localRepresentativesWithWork_length_le N P F B hP hFpos a initial query hN
  have htail := warmupWide_bounds parent reps.1 P F B hP initial child query hB hnx hny hM hPbits hF
    (fun br hbr => (localRepresentativesWithWork_scale_bits N P F B hP a initial query hN br hbr).trans (by omega)) hi hc
  have hwide := wideWork_mono M P _ ((B + 1) * (64 * F * P + 2) ^ 2) (B + 4) hrl
  have hbellman := bellmanWork_mono M _ _ (physicalContinuationInputBudget M (B + 4))
    (physicalContinuationInputBudget M (B + 4)) (endpointDistanceBitBudget (B + 4))
    (Nat.mul_le_mul_right ((40 * P + 2) ^ (2 * M)) hrl)
  refine ⟨htail.1, ?_⟩
  change reps.2 + _ + _ + _ + 3 ≤ _
  change reps.2 ≤ _ at hr
  unfold localWarmupBitBudget
  dsimp only
  simp only [reps] at htail hwide hbellman hr ⊢
  omega

end BinaryFraction
end EditApproximation

end OAI
