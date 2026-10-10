import OAI.Combinatorics.ContingencyTables.Machines.CachedTerminalCount
import OAI.Combinatorics.ContingencyTables.Sampling.ProfileTransitionCountSemantics
import OAI.Combinatorics.ContingencyTables.Transport.IntegerPushTransport
import OAI.Combinatorics.ContingencyTables.Transport.ListedOutputSemantics

namespace OAI

/-! # Cached terminal success counts equal the actual completion law -/

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
local notation "f" => 25*(d+b+h+1)^62

attribute [local irreducible] canonicalCounts listedCompletionCounts listedUnpaddedCounts
  listedCompletionFactor stateCode stateCodeData completionWeights prepareTransitionCache
  terminalCount listedRows listedColumns

lemma tableCode_option_eq (o : Option (Table r c)) (T : Table r c) :
    o.map (fun X => matrixCode X.val)=some (matrixCode T.val) ↔ o=some T := by
  cases o with
  | none => simp
  | some X =>
    simp only [Option.map_some,Option.some.injEq]
    constructor
    · intro he
      exact Subtype.ext (matrixCode_injective he)
    · rintro rfl
      rfl

def listedTerminalDecision (x : PaperStates r c) (A : Table (R x) (P x)) :
    Option (Table r c) := stateTrial r c ⟨x,(paperListedEquiv r c hr hc x).symm A⟩

attribute [local irreducible] listedTerminalDecision

lemma terminal_completion_sum (x : PaperStates r c) (T : Table r c) :
    ((listedCompletionCounts r c hr hc b h hb x).push
      (fun A => stateTrial r c ⟨x,A⟩)).count (some T)=
      ∑ A : Table (R x) (P x),if listedTerminalDecision r c hr hc x A=some T
        then (listedUnpaddedCounts r c hr hc h x).count A*
          listedCompletionFactor r c hr hc b h x else 0 := by
  have he := IntegerLaw.push_equiv_count
    (listedCompletionCounts r c hr hc b h hb x) (listedUnpaddedCounts r c hr hc h x)
    (paperListedEquiv r c hr hc x) (listedCompletionFactor r c hr hc b h x)
    (listedTerminalDecision r c hr hc x)
    (listedCompletionCounts_count r c hr hc b h hb x) (some T)
  simpa only [listedTerminalDecision,Equiv.symm_apply_apply] using he

lemma terminal_cache_sum (x : PaperStates r c) (T : Table r c) :
    ((completionWeights ((marginCode (R x),marginCode (P x)),(d,h))).map
      (fun entry => entry.1.elim 0 (fun X =>
        if outerTrial ((stateCodeData r c e x,d^12),X)=some (matrixCode T.val)
        then entry.2 else 0))).sum=
      ∑ A : Table (R x) (P x),if listedTerminalDecision r c hr hc x A=some T
        then (listedUnpaddedCounts r c hr hc h x).count A else 0 := by
  let w : MatrixCode → ℕ := fun X =>
    if outerTrial ((stateCodeData r c e x,d^12),X)=some (matrixCode T.val) then 1 else 0
  have he : ((completionWeights ((marginCode (R x),marginCode (P x)),(d,h))).map
      (fun entry => entry.1.elim 0 (fun X =>
        if outerTrial ((stateCodeData r c e x,d^12),X)=some (matrixCode T.val)
        then entry.2 else 0))).sum=
      ((completionWeights ((marginCode (R x),marginCode (P x)),(d,h))).map
        (fun entry => entry.1.elim 0 (fun X => entry.2*w X))).sum := by
    congr 1
    apply List.map_congr_left
    rintro ⟨o,n⟩ _
    cases o with
    | none => rfl
    | some X => simp only [Option.elim_some,w]; split_ifs <;> simp
  rw [he,sum_completionWeights (R x) (P x) (listed_dimension_fourteen r c hr hc)
    (by simpa only [Fintype.card_prod,Fintype.card_fin] using (listed_dimensions r c hr hc).2.2)
    (listed_row_padding r c (d^20) (d^12) (stateCapacity r c) hr hc x)
    (listed_column_padding r c (d^20) (d^12) (stateCapacity r c) hr hc x)
    (listed_paper_totals r c hr hc x) h w]
  apply Finset.sum_congr rfl
  intro A _
  have ho := actualOuterTrial r c e hr hc x ((paperListedEquiv r c hr hc x).symm A)
  rw [Equiv.apply_symm_apply] at ho
  simp only [w,ho,tableCode_option_eq]
  unfold listedTerminalDecision listedUnpaddedCounts
  split_ifs <;> simp

lemma terminalCount_actual (x : PaperStates r c) (T : Table r c) :
    terminalCount (prepareTransitionCache
      ((((stateCodeData r c e x,d^12),(d,h)),f)),matrixCode T.val)=
      ((listedCompletionCounts r c hr hc b h hb x).push
        (fun A => stateTrial r c ⟨x,A⟩)).count (some T) := by
  rw [prepareTransitionCache_encoded r c e hr hc,terminalCount_eq,
    terminal_cache_sum r c e hr hc h x T,terminal_completion_sum r c hr hc b h hb x T,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro A _
  unfold listedCompletionFactor
  split_ifs
  · exact Nat.mul_comm _ _
  · exact Nat.mul_zero _

end
end ContingencyTables.SmallGraphProfiles

end OAI
