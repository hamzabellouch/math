import OAI.Combinatorics.ContingencyTables.Machines.PreparedTransitionCache
import OAI.Combinatorics.ContingencyTables.Transport.BooleanCountTransport

namespace OAI

/-! # Executed cached transitions have the actual walk's integer counts -/

namespace ContingencyTables.ProfilePrograms

lemma cachedWordCount_eq (p : ResidualParameters) (M : ℕ)
    (cache : List (Option DensePrograms.MatrixCode×ℕ)) (target : List ℕ×List ℕ)
    (bits : List Bool) :
    cachedWordCount (((p,(M,cache)),target),bits)=
      M*decisionWeightSum (((p,bits),target),cache) := rfl

end ContingencyTables.ProfilePrograms

namespace ContingencyTables.SmallGraphProfiles
open ProfilePrograms DensePrograms PhysicalCompletionFibres FirstPaperPhysicalMarginal
open SmallContextCoordinates CompletionCounts CompletionTranslation
open scoped BigOperators Classical
noncomputable section

variable {m n q : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)
variable (e : Fin q ≃ Cells (paperSmall r c))
variable (hr : 0<(largeIndices ((dimensionAllowance (I := Fin m) (J := Fin n))^20,List.ofFn r)).length)
variable (hc : 0<(largeIndices ((dimensionAllowance (I := Fin m) (J := Fin n))^20,List.ofFn c)).length)
variable (b h : ℕ) (hb : Nat.clog 2 (stateBound r c+2)≤b)
local notation "d" => dimensionAllowance (I := Fin m) (J := Fin n)
local notation "R" => listedRows r c (d^20) (d^12) (stateCapacity r c) hr
local notation "P" => listedColumns r c (d^20) (d^12) (stateCapacity r c) hc
local notation "s" => smallProposalBits (I := Fin m) (J := Fin n)
local notation "f" => 25*(d+b+h+1)^62

attribute [local irreducible] canonicalCounts listedStepCounts listedCompletionCounts
  normalizedDrawBits prepareTransitionCache stateCode stateCodeData listedRows listedColumns
  completionDecision transitionCount cachedWordCount cachedWordInput completionWeights decisionWeightSum

def listedUnpaddedCounts (x : PaperStates r c) :
    IntegerLaw (Table (R x) (P x)) (2^normalizedDrawBits (R x) (P x) d h) :=
  canonicalCounts (R x) (P x) (listed_dimension_fourteen r c hr hc)
    (listed_row_padding r c (d^20) (d^12) (stateCapacity r c) hr hc x)
    (listed_column_padding r c (d^20) (d^12) (stateCapacity r c) hr hc x)
    (listed_paper_totals r c hr hc x) h

def listedCompletionFactor (x : PaperStates r c) : ℕ :=
  2^(f-normalizedDrawBits (R x) (P x) d h)

def listedCachedDecision (x : PaperStates r c) (word : Fin s → Bool)
    (A : Table (R x) (P x)) : PaperStates r c :=
  completionDecision R P x (decodedCodeProposal r c e x word) A

attribute [local irreducible] listedUnpaddedCounts listedCompletionFactor listedCachedDecision

lemma listedCompletionCounts_count (x : PaperStates r c) (A : PaperFibre r c x) :
    (listedCompletionCounts r c hr hc b h hb x).count A=
      (listedUnpaddedCounts r c hr hc h x).count (paperListedEquiv r c hr hc x A)*
        listedCompletionFactor r c hr hc b h x := by
  unfold listedUnpaddedCounts listedCompletionFactor listedCompletionCounts
  rfl

lemma listedStepCounts_sum (x y : PaperStates r c) :
    (listedStepCounts r c e hr hc b h hb x).count y=
      ∑ word : Fin s → Bool,∑ A : Table (R x) (P x),
        if listedCachedDecision r c e hr hc x word A=y then
          (listedUnpaddedCounts r c hr hc h x).count A*
            listedCompletionFactor r c hr hc b h x else 0 := by
  have he := IntegerLaw.booleanFinish_equiv_count
    (listedCompletionCounts r c hr hc b h hb x) (listedUnpaddedCounts r c hr hc h x)
    (paperListedEquiv r c hr hc x) (listedCompletionFactor r c hr hc b h x)
    (listedCachedDecision r c e hr hc x)
    (listedCompletionCounts_count r c hr hc b h hb x) y
  simpa only [listedStepCounts,listedCachedDecision] using he

lemma decisionWeightSum_listed (htotal : ∑ i,r i=∑ j,c j)
    (x y : PaperStates r c) (word : Fin s → Bool) :
    decisionWeightSum ((encodedShortStep r c e h x word,stateCode r c e y),
      completionWeights ((marginCode (R x),marginCode (P x)),(d,h)))=
      ∑ A : Table (R x) (P x),if listedCachedDecision r c e hr hc x word A=y
        then (listedUnpaddedCounts r c hr hc h x).count A else 0 := by
  unfold listedCachedDecision listedUnpaddedCounts
  exact decisionWeightSum_actual r c e hr hc htotal h x y word

lemma transitionCount_actual (htotal : ∑ i,r i=∑ j,c j)
    (x y : PaperStates r c) (xs : List Bool) (hs : xs.length=s) :
    transitionCount ((prepareTransitionCache
      ((((stateCodeData r c e x,d^12),(d,h)),f)),stateCode r c e y),xs)=
      (listedStepCounts r c e hr hc b h hb x).count y := by
  rw [prepareTransitionCache_encoded r c e hr hc,transitionCount_words _ xs s hs,
    listedStepCounts_sum r c e hr hc b h hb x y]
  apply Finset.sum_congr rfl
  intro word _
  rw [cachedWordCount_eq]
  have he := decisionWeightSum_listed r c e hr hc h htotal x y word
  unfold encodedShortStep at he
  rw [he,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro A _
  unfold listedCompletionFactor
  split_ifs
  · exact Nat.mul_comm _ _
  · exact Nat.mul_zero _

end
end ContingencyTables.SmallGraphProfiles

end OAI
