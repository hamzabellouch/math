import OAI.Combinatorics.EditApproximation.Binary.BinaryOnlineInputs
import OAI.Combinatorics.EditApproximation.Binary.BinaryBandInputWork

namespace OAI

/-! The finite optimistic-history builder uses only the charged Boolean
fraction instructions.  These bounds derive every intermediate width from
the stored table and mass widths. -/

namespace EditApproximation
namespace BinaryFraction

def gainBitBudget (Bm Bt : ℕ) : ℕ := 2100 * (Bm + Bt + 2) ^ 2 + 1

theorem gainWithWork_cost {β σ : Type*} (mass : β → BinaryFraction)
    (table : ℕ → β × σ → BinaryFraction) (s : ℕ) (i : β × σ) (Bm Bt : ℕ)
    (hm : (mass i.1).width ≤ Bm) (ht : (table s i).width ≤ Bt) :
    (gainWithWork mass table s i).2 ≤ gainBitBudget Bm Bt := by
  have h := divWithWork_cost (table s i).neg (mass i.1) (Bm + Bt)
    (by rw [neg_width]; omega) (by omega)
  exact Nat.add_le_add_right h 1

def decrementBitBudget (Bm Bt : ℕ) : ℕ :=
  6000 * (Bt + 1) ^ 2 + 2100 * (8 * Bt + Bm + 8) ^ 2 + 2

theorem decrementWithWork_cost {β σ : Type*} (mass : β → BinaryFraction)
    (table : ℕ → β × σ → BinaryFraction) (s : ℕ) (i : β × σ) (Bm Bt : ℕ)
    (hm : (mass i.1).width ≤ Bm) (ht : (table s i).width ≤ Bt)
    (ht' : (table (s + 1) i).width ≤ Bt) :
    (decrementWithWork mass table s i).2 ≤ decrementBitBudget Bm Bt := by
  have hs := subWithWork_cost (table s i) (table (s + 1) i) Bt ht ht'
  have hw := canonicalAddWithWork_self_width (table s i) (table (s + 1) i).neg
  change (subWithWork (table s i) (table (s + 1) i)).1.width ≤
    (subWithWork (table s i) (table (s + 1) i)).1.representation.storageBits at hw
  rw [subWithWork_representation] at hw
  have hraw := UnreducedRational.storageBits_sub (table s i).representation (table (s + 1) i).representation
  have ho := representation_storageBits_le (table s i)
  have hn := representation_storageBits_le (table (s + 1) i)
  have hd := divWithWork_cost (subWithWork (table s i) (table (s + 1) i)).1
    (mass i.1) (8 * Bt + Bm + 6) (by omega) (by omega)
  change (subWithWork (table s i) (table (s + 1) i)).2 +
    (divWithWork (subWithWork (table s i) (table (s + 1) i)).1 (mass i.1)).2 + 1 ≤ _
  rw [show 8 * Bt + Bm + 6 + 2 = 8 * Bt + Bm + 8 by omega] at hd
  unfold decrementBitBudget
  omega

def coefficientBitBudget (Bk : ℕ) : ℕ :=
  2000 * (Bk + 3) ^ 2 + 6000 * (2 * Bk + 7) ^ 2 + 2

theorem coefficientWithWork_cost (kappa : BinaryFraction) (Bk : ℕ)
    (hk : kappa.width ≤ Bk) :
    (coefficientWithWork kappa).2 ≤ coefficientBitBudget Bk := by
  have htwo : (nat 2).width = 2 := by decide
  have hm := canonicalMulWithWork_cost (nat 2) kappa (Bk + 2) (by omega) (by omega)
  have hw := canonicalMulWithWork_self_width (nat 2) kappa
  rw [canonicalMulWithWork_representation, nat_representation] at hw
  have hraw := UnreducedRational.storageBits_mul (UnreducedRational.nat 2) kappa.representation
  have hrawtwo : (UnreducedRational.nat 2).storageBits = 4 := by decide
  rw [hrawtwo] at hraw
  have hk' := representation_storageBits_le kappa
  have hs := subWithWork_cost one (canonicalMulWithWork (nat 2) kappa).1 (2 * Bk + 6)
    (by change 1 ≤ _; omega) (by omega)
  change (canonicalMulWithWork (nat 2) kappa).2 +
    (subWithWork one (canonicalMulWithWork (nat 2) kappa).1).2 + 1 ≤ _
  rw [show Bk + 2 + 1 = Bk + 3 by omega] at hm
  rw [show 2 * Bk + 6 + 1 = 2 * Bk + 7 by omega] at hs
  unfold coefficientBitBudget
  omega

def optimisticTermWordBudget (Bm Bt Bc : ℕ) : ℕ := 8 * Bt + 2 * Bm + 2 * Bc + 12

def optimisticTermBitBudget (Bm Bt Bc : ℕ) : ℕ :=
  gainBitBudget Bm Bt + decrementBitBudget Bm Bt +
    2000 * (optimisticTermWordBudget Bm Bt Bc + 1) ^ 2 +
    6000 * (optimisticTermWordBudget Bm Bt Bc + 1) ^ 2 + 2

theorem optimisticTermWithWork_cost {β σ : Type*} (mass : β → BinaryFraction)
    (table : ℕ → β × σ → BinaryFraction) (coefficient : BinaryFraction)
    (s : ℕ) (i : β × σ) (Bm Bt Bc : ℕ)
    (hm : (mass i.1).width ≤ Bm) (ht : (table s i).width ≤ Bt)
    (ht' : (table (s + 1) i).width ≤ Bt) (hc : coefficient.width ≤ Bc) :
    (optimisticTermWithWork mass table coefficient s i).2 ≤ optimisticTermBitBudget Bm Bt Bc := by
  let gain := (gainWithWork mass table s i).1
  let decrement := (decrementWithWork mass table s i).1
  let W := optimisticTermWordBudget Bm Bt Bc
  have hgs := gainWithWork_storage mass table s i Bm Bt hm ht
  have hds := decrementWithWork_storage mass table s i Bm Bt hm ht ht'
  have hgw := divWithWork_self_width (table s i).neg (mass i.1)
  change gain.width ≤ gain.representation.storageBits at hgw
  have hdw := divWithWork_self_width (subWithWork (table s i) (table (s + 1) i)).1 (mass i.1)
  change decrement.width ≤ decrement.representation.storageBits at hdw
  change gain.representation.storageBits ≤ _ at hgs
  change decrement.representation.storageBits ≤ _ at hds
  have hgW : gain.width ≤ W := by dsimp only [W, optimisticTermWordBudget]; omega
  have hdW : decrement.width ≤ W := by dsimp only [W, optimisticTermWordBudget]; omega
  have hcW : coefficient.width ≤ W := by dsimp only [W, optimisticTermWordBudget]; omega
  have hp := canonicalMulWithWork_cost coefficient decrement W hcW hdW
  have hpw := canonicalMulWithWork_self_width coefficient decrement
  rw [canonicalMulWithWork_representation] at hpw
  have hps := UnreducedRational.storageBits_mul coefficient.representation decrement.representation
  have hcs := representation_storageBits_le coefficient
  have hpW : (canonicalMulWithWork coefficient decrement).1.width ≤ W := by
    dsimp only [W, optimisticTermWordBudget]
    omega
  have ha := canonicalAddWithWork_cost gain (canonicalMulWithWork coefficient decrement).1 W hgW hpW
  have hg := gainWithWork_cost mass table s i Bm Bt hm ht
  have hd := decrementWithWork_cost mass table s i Bm Bt hm ht ht'
  change (gainWithWork mass table s i).2 + (decrementWithWork mass table s i).2 +
    (canonicalMulWithWork coefficient decrement).2 +
    (canonicalAddWithWork gain (canonicalMulWithWork coefficient decrement).1).2 + 2 ≤ _
  unfold optimisticTermBitBudget
  change _ ≤ gainBitBudget Bm Bt + decrementBitBudget Bm Bt +
    2000 * (W + 1) ^ 2 + 6000 * (W + 1) ^ 2 + 2
  omega

def onlineFinalWordBudget (Be Bk Bm Bt t : ℕ) : ℕ :=
  Be + bandMassTotalStorageBudget t (optimisticTermStorageBudget Bm Bt (4 * Bk + 18)) +
    (2 * Bt + 2 * Bm + 4) + 2

def onlineLinearBitBudget (Be Bk Bm Bt t : ℕ) : ℕ :=
  coefficientBitBudget Bk + t * (optimisticTermBitBudget Bm Bt (4 * Bk + 18) + 6) +
    storedSumBitBudget t (optimisticTermStorageBudget Bm Bt (4 * Bk + 18)) +
    gainBitBudget Bm Bt + 6000 * (onlineFinalWordBudget Be Bk Bm Bt t + 1) ^ 2 +
    2000 * (2 * onlineFinalWordBudget Be Bk Bm Bt t + 3) ^ 2 + 3

theorem onlineLinearWithWork_cost {β σ : Type*} (mass : β → BinaryFraction)
    (table : ℕ → β × σ → BinaryFraction) (eta kappa : BinaryFraction)
    (t : ℕ) (i : β × σ) (Be Bk Bm Bt : ℕ)
    (he : eta.width ≤ Be) (hk : kappa.width ≤ Bk) (hm : (mass i.1).width ≤ Bm)
    (ht : ∀ s ≤ t + 1, (table s i).width ≤ Bt) :
    (onlineLinearWithWork mass table eta kappa t i).2 ≤ onlineLinearBitBudget Be Bk Bm Bt t := by
  let coefficient := (coefficientWithWork kappa).1
  let terms := vectorMapWithWork t fun s => optimisticTermWithWork mass table coefficient s.val i
  let history := (bandMassTotalWithWork terms.1).1
  let current := (gainWithWork mass table t i).1
  let W := onlineFinalWordBudget Be Bk Bm Bt t
  have hcn := canonicalAddWithWork_self_width one (canonicalMulWithWork (nat 2) kappa).1.neg
  change coefficient.width ≤ coefficient.representation.storageBits at hcn
  have hc : coefficient.width ≤ 4 * Bk + 18 := hcn.trans (coefficientWithWork_storage kappa Bk hk)
  have hterms (s : Fin t) : (terms.1.get s).width ≤ optimisticTermStorageBudget Bm Bt (4 * Bk + 18) := by
    simp only [terms, vectorMapWithWork_value]
    exact (canonicalAddWithWork_self_width _ _).trans
      (optimisticTermWithWork_storage mass table coefficient s.val i Bm Bt (4 * Bk + 18)
        hm (ht s.val (by omega)) (ht (s.val + 1) (by omega)) hc)
  have htc := vectorMapWithWork_cost_le t
    (fun s => optimisticTermWithWork mass table coefficient s.val i)
    (optimisticTermBitBudget Bm Bt (4 * Bk + 18))
    (fun s => optimisticTermWithWork_cost mass table coefficient s.val i Bm Bt (4 * Bk + 18)
      hm (ht s.val (by omega)) (ht (s.val + 1) (by omega)) hc)
  have hhc := bandMassTotalWithWork_cost terms.1 (optimisticTermStorageBudget Bm Bt (4 * Bk + 18)) hterms
  have hhs := bandMassTotalWithWork_storage terms.1 (optimisticTermStorageBudget Bm Bt (4 * Bk + 18)) hterms
  change history.representation.storageBits ≤ _ at hhs
  have hhw := dotListWithWork_width_le_storageBits terms.1 (Vector.replicate t one) (List.finRange t)
  change history.width ≤ history.representation.storageBits at hhw
  have hgc := gainWithWork_cost mass table t i Bm Bt hm (ht t (by omega))
  have hgs := gainWithWork_storage mass table t i Bm Bt hm (ht t (by omega))
  change current.representation.storageBits ≤ _ at hgs
  have hgw := divWithWork_self_width (table t i).neg (mass i.1)
  change current.width ≤ current.representation.storageBits at hgw
  have hhW : history.width ≤ W := by dsimp only [W, onlineFinalWordBudget]; omega
  have hgW : current.width ≤ W := by dsimp only [W, onlineFinalWordBudget]; omega
  have hac := canonicalAddWithWork_cost history current W hhW hgW
  have haw := canonicalAddWithWork_self_width history current
  rw [canonicalAddWithWork_representation] at haw
  have has := UnreducedRational.storageBits_add history.representation current.representation
  have haW : (canonicalAddWithWork history current).1.width ≤ 2 * W + 2 := by
    dsimp only [W, onlineFinalWordBudget]
    omega
  have hmc := canonicalMulWithWork_cost eta (canonicalAddWithWork history current).1
    (2 * W + 2) (by dsimp only [W, onlineFinalWordBudget]; omega) haW
  rw [show 2 * W + 2 + 1 = 2 * W + 3 by omega] at hmc
  have hcc := coefficientWithWork_cost kappa Bk hk
  change (coefficientWithWork kappa).2 + terms.2 + (bandMassTotalWithWork terms.1).2 +
    (gainWithWork mass table t i).2 + (canonicalAddWithWork history current).2 +
    (canonicalMulWithWork eta (canonicalAddWithWork history current).1).2 + 3 ≤ _
  change terms.2 ≤ _ at htc
  unfold onlineLinearBitBudget
  change _ ≤ coefficientBitBudget Bk + t * (optimisticTermBitBudget Bm Bt (4 * Bk + 18) + 6) +
    storedSumBitBudget t (optimisticTermStorageBudget Bm Bt (4 * Bk + 18)) + gainBitBudget Bm Bt +
    6000 * (W + 1) ^ 2 + 2000 * (2 * W + 3) ^ 2 + 3
  omega

end BinaryFraction
end EditApproximation

end OAI
