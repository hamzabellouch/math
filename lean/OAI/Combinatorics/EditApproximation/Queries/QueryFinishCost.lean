import OAI.Combinatorics.EditApproximation.Queries.QueryRefinementFinish
import OAI.Combinatorics.EditApproximation.Binary.BinaryPreparedKernelWork
import OAI.Combinatorics.EditApproximation.Binary.BinaryContinuationReadCosts

namespace OAI

namespace EditApproximation.BinaryFraction

private theorem continuationBudget_mono (M P nr ng no nr' ng' no' B : ℕ)
    (hr : nr ≤ nr') (hg : ng ≤ ng') (ho : no ≤ no') :
    physicalContinuationBitBudget M P nr ng no B ≤ physicalContinuationBitBudget M P nr' ng' no' B := by
  unfold physicalContinuationBitBudget wideActionsBitBudget localContinuationBitBudget bellmanBitBudget
  dsimp only
  gcongr

def queryRefinementFinishBitBudget (M P F B R G O : ℕ) : ℕ :=
  R + localRepresentativesBitBudget P F B * (R + 2) +
    physicalContinuationBitBudget M P ((B + 1) * (64 * F * P + 2) ^ 2) G O (B + 4) * tableReadFactor R + 2

theorem queryRefinementFinishWithWork_bounds {nx ny M : ℕ} (parent : TargetInterval nx)
    (N P F B R G O : ℕ) (a delta : BinaryFraction)
    (initial : TargetInterval ny → BinaryFraction × ℕ) (t : ℕ)
    (earlierKeys : List (Fin M × ℕ × TargetInterval ny)) (earlierWords : List BinaryFraction)
    (groups online : List (BinaryBellmanAction (TargetInterval ny) (Fin M × TargetInterval ny) M))
    (currentKeys : List (Fin M × TargetInterval ny)) (currentWords : List BinaryFraction)
    (q : TargetInterval ny) (hB : 10 ≤ B) (hP : 0 < P) (hFpos : 1 ≤ F)
    (hN : Nat.size N ≤ B) (hnx : Nat.size nx ≤ B) (hny : Nat.size ny + 2 ≤ B)
    (hM : Nat.size M ≤ B) (hPb : Nat.size P ≤ B) (hF : Nat.size F + 2 ≤ B)
    (ha : a.width ≤ B) (hd : delta.width ≤ B)
    (hi : ∀ r, (initial r).1.width ≤ B) (hR : ∀ r, (initial r).2 ≤ R)
    (he : ∀ input, (queryHistoryReadWithWork earlierKeys earlierWords (t - 1) input).1.width ≤ B)
    (heR : ∀ input, (queryHistoryReadWithWork earlierKeys earlierWords (t - 1) input).2 ≤ R)
    (hc : ∀ i r, (queryChildReadWithWork currentKeys currentWords i r).1.width ≤ B)
    (hcR : ∀ i r, (queryChildReadWithWork currentKeys currentWords i r).2 ≤ R)
    (hgroups : ∀ action ∈ groups, action.connection.width ≤ connectionWordBudget M (B + 4))
    (honline : ∀ action ∈ online, action.connection.width ≤ connectionWordBudget M (B + 4))
    (hglen : groups.length ≤ G) (holen : online.length ≤ O) :
    (queryRefinementFinishWithWork parent N P F a delta initial t earlierKeys earlierWords groups online
      currentKeys currentWords q).1.width ≤ preparedKernelWordBudget M B ∧
    (queryRefinementFinishWithWork parent N P F a delta initial t earlierKeys earlierWords groups online
      currentKeys currentWords q).2 ≤ queryRefinementFinishBitBudget M P F B R G O := by
  let reps := localRepresentativeReadWithWork N P F a initial q
  let old := queryHistoryReadWithWork earlierKeys earlierWords (t - 1)
  let current := fun input : Fin M × TargetInterval ny => queryChildReadWithWork currentKeys currentWords input.1 input.2
  have hr := localRepresentativeReadWithWork_eq_cost N P F a initial q R hR
  have hrCost := localRepresentativesWithWork_cost N P F B a (fun r => (initial r).1) q
    (by omega) hN hF hFpos hPb hP (by omega) ha hi
  have hrlen : reps.1.length ≤ (B + 1) * (64 * F * P + 2) ^ 2 := by
    rw [show reps.1 = (localRepresentativesWithWork N P F a (fun r => (initial r).1) q).1 from hr.1]
    exact localRepresentativesWithWork_length_le N P F B hP hFpos a (fun r => (initial r).1) q hN
  have hrwidth : ∀ br ∈ reps.1, Nat.size br.1 ≤ B + 4 := by
    intro br hbr
    rw [show reps.1 = (localRepresentativesWithWork N P F a (fun r => (initial r).1) q).1 from hr.1] at hbr
    exact (localRepresentativesWithWork_scale_bits N P F B hP a (fun r => (initial r).1) q hN br hbr).trans (by omega)
  have htail := physicalContinuationWithWork_bounds parent reps.1 P F (B + 4) delta (initial q).1
    (fun input => (old input).1) (fun input => (current input).1) groups online q hP (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) hrwidth (hd.trans (by omega))
    ((hi q).trans (by omega)) (fun input => (he input).trans (by omega))
    (fun input => (hc input.1 input.2).trans (by omega)) hgroups honline
  have htailValue := (physicalContinuationReadWithWork_eq_cost parent reps.1 P F delta (initial q).1
    old current groups online q R heR (fun input => hcR input.1 input.2)).1
  have htailRead := physicalContinuationReadWithWork_factor parent reps.1 P F delta (initial q).1
    old current groups online q R heR (fun input => hcR input.1 input.2)
  have htailCost := htail.2.trans (continuationBudget_mono M P _ _ _ _ _ _ (B + 4) hrlen hglen holen)
  have hrTotal : reps.2 ≤ localRepresentativesBitBudget P F B * (R + 2) :=
    hr.2.trans (Nat.mul_le_mul_right _ hrCost)
  have htTotal := htailRead.trans (Nat.mul_le_mul_right (tableReadFactor R) htailCost)
  constructor
  · change (physicalContinuationReadWithWork parent reps.1 P F delta (initial q).1 old current groups online q).1.width ≤ _
    rw [htailValue]
    exact htail.1
  · change (initial q).2 + reps.2 +
      (physicalContinuationReadWithWork parent reps.1 P F delta (initial q).1 old current groups online q).2 + 2 ≤ _
    have hq := hR q
    unfold queryRefinementFinishBitBudget
    omega

end EditApproximation.BinaryFraction

end OAI
