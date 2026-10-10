import OAI.Combinatorics.EditApproximation.Binary.BinarySampledOnlineSpace
import OAI.Combinatorics.EditApproximation.Queries.QueryOnlineRangeSpace
import OAI.Combinatorics.EditApproximation.Binary.BinaryUnskippedSpace
import OAI.Combinatorics.EditApproximation.Binary.BinaryLocalOnlineSource
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

namespace EditApproximation



theorem reduceOnlineIntegerAllocation_le_work (K integer : ℕ) (hK : 0 < K) :
    reduceOnlineIntegerAllocation K integer ≤ (BinaryFraction.reduceOnlineIntegerWithWork K hK integer).2 := by
  have ht := triangularMassAllocation_le_work K
  have hd := bitDivModAllocation_le_work (bitWordValue (triangularMassWithWork K).1).bits integer.bits
  unfold reduceOnlineIntegerAllocation BinaryFraction.reduceOnlineIntegerWithWork binaryNaturalDivModWithWork
  dsimp only
  omega

/-- The only multiplicative allowance needed by the labeled optimizer. -/
theorem filterMapAllocation_le_three_work {α β : Type*} (f : α → Option β × ℕ)
    (allocation : α → ℕ) (xs : List α) (h : ∀ x ∈ xs, allocation x ≤ 3 * (f x).2) :
    filterMapAllocation f allocation xs ≤ 3 * (filterMapWithWork f xs).2 := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    have hx := h x List.mem_cons_self
    have ht := ih (fun y hy => h y (List.mem_cons_of_mem _ hy))
    simp only [filterMapAllocation, filterMapWithWork]
    cases he : (f x).1 <;> simp only [Option.isSome, Bool.false_eq_true, ↓reduceIte] <;> omega

namespace BinaryFraction
section Online
variable {α : Type*} (source target : List α) {M : ℕ}
  (parent : TargetInterval source.length) (P F exponent H b : ℕ) (hb : 0 < b) (hP : 0 < P)
  (tau eta kappa : BinaryFraction)
  (child initial : Fin M → TargetInterval target.length → BinaryFraction × ℕ)
  (table : ℕ → Fin M × TargetInterval target.length → BinaryFraction × ℕ)
  (R : ℕ) (hc : ∀ i q, (child i q).2 ≤ R) (hi : ∀ i q, (initial i q).2 ≤ R)
  (childAllocation initialAllocation : Fin M → TargetInterval target.length → ℕ)
  (tableAllocation : ℕ → Fin M × TargetInterval target.length → ℕ)

def preparedOnlineReadAllocation (t : ℕ) (center : TargetInterval target.length) (integer : ℕ) : ℕ :=
  let band := (preparedRepresentativeReadWithWork parent center (parent.hi - parent.lo) b P
    tau (inversePowerTwo exponent) child).1
  let G := (onlineIndexSetupWithWork H band).1
  let accepted := (reduceOnlineIntegerWithWork (G ^ 80) (by
    dsimp only [G]; rw [onlineIndexSetupWithWork_value]; positivity) integer).1
  preparedRepresentativeReadAllocation parent center (parent.hi - parent.lo) b P
    tau (inversePowerTwo exponent) child childAllocation +
    onlineIndexSetupAllocation H band + reduceOnlineIntegerAllocation (G ^ 80) integer +
    if hband : band = [] then 0 else
      preparedUnskippedReadAllocation parent center b P exponent tau (nat F)
        child initial childAllocation initialAllocation +
      if (preparedUnskippedReadWithWork source target parent b P exponent hb hP tau (nat F)
        child initial R R hc hi center).1.isSome then
        countedSampledOnlineAllocation center b initial initialAllocation table tableAllocation eta kappa
          band hband G (G ^ 80) t accepted + 1
      else 0

theorem preparedOnlineReadAllocation_le_work (t : ℕ) (center : TargetInterval target.length) (integer : ℕ)
    (hca : ∀ i q, childAllocation i q ≤ (child i q).2)
    (hia : ∀ i q, initialAllocation i q ≤ (initial i q).2)
    (hta : ∀ s q, tableAllocation s q ≤ (table s q).2) :
    preparedOnlineReadAllocation source target parent P F exponent H b hb hP tau eta kappa child initial table
      R hc hi childAllocation initialAllocation tableAllocation t center integer ≤
      3 * (preparedOnlineReadWithWork source target parent P F exponent H b hb hP tau eta kappa
        child initial table R hc hi t center integer).2 := by
  have emptyBound (b b' s s' r r' : ℕ) (hb : b ≤ b') (hs : s ≤ s') (hr : r ≤ r') :
      b + s + r + 0 ≤ 3 * (b' + s' + r' + 1) := by
    omega
  have selectedBound (b b' s s' r r' g g' a a' : ℕ)
      (hb : b ≤ b') (hs : s ≤ s') (hr : r ≤ r') (hg : g ≤ g') (ha : a ≤ 3 * a') :
      b + s + r + (g + (a + 1)) ≤ 3 * (b' + s' + r' + g' + a' + 2) := by
    omega
  have rejectedBound (b b' s s' r r' g g' : ℕ)
      (hb : b ≤ b') (hs : s ≤ s') (hr : r ≤ r') (hg : g ≤ g') :
      b + s + r + (g + 0) ≤ 3 * (b' + s' + r' + g' + 1) := by
    omega
  let band := (preparedRepresentativeReadWithWork parent center (parent.hi - parent.lo) b P
    tau (inversePowerTwo exponent) child).1
  let G := (onlineIndexSetupWithWork H band).1
  have hG : 0 < G ^ 80 := by dsimp only [G]; rw [onlineIndexSetupWithWork_value]; positivity
  let accepted := (reduceOnlineIntegerWithWork (G ^ 80) hG integer).1
  have hbnd := preparedRepresentativeReadAllocation_le_work parent center (parent.hi - parent.lo) b P
    tau (inversePowerTwo exponent) child childAllocation hca
  have hsetup := onlineIndexSetupAllocation_le_work H band
  have hreduce := reduceOnlineIntegerAllocation_le_work (G ^ 80) integer hG
  have hguard := preparedUnskippedReadAllocation_le_work source target parent center b P exponent hb hP
    tau (nat F) child initial childAllocation initialAllocation R R hc hi hca hia
  unfold preparedOnlineReadAllocation preparedOnlineReadWithWork
  dsimp only
  split_ifs with he hg
  · dsimp only [band, G] at hsetup hreduce
    exact emptyBound _ _ _ _ _ _ hbnd hsetup hreduce
  · have hsample := countedSampledOnlineAllocation_le_work center b initial initialAllocation table tableAllocation
      eta kappa band he G (G ^ 80) t accepted hia hta
    dsimp only [band, G, accepted] at hsetup hreduce hsample
    exact selectedBound _ _ _ _ _ _ _ _ _ _ hbnd hsetup hreduce hguard hsample
  · dsimp only [band, G] at hsetup hreduce
    exact rejectedBound _ _ _ _ _ _ _ _ hbnd hsetup hreduce hguard

end Online
end BinaryFraction
end EditApproximation

end OAI
