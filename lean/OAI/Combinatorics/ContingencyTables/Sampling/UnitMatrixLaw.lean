import OAI.Combinatorics.ContingencyTables.Sampling.UnitMatrixProgram
import OAI.Combinatorics.ContingencyTables.Sampling.UnitBoxLaw
import OAI.Combinatorics.ContingencyTables.Sampling.ProfileTerminalSemantics

namespace OAI

/-! # The all-small matrix computes its actual finite-word law -/

namespace ContingencyTables.IntegerLaw
open scoped BigOperators Classical

lemma push_push_count {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]
    [DecidableEq B] [DecidableEq C] {Q : ℕ} (p : IntegerLaw A Q)
    (f : A → B) (g : B → C) (c : C) :
    ((p.push f).push g).count c=(p.push (g ∘ f)).count c := by
  calc
    _ = ∑ b,(p.push f).count b*(if g b=c then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro b _
      by_cases h : g b=c <;> simp only [h,ite_true,ite_false,mul_one,mul_zero]
    _ = ∑ a,p.count a*(if g (f a)=c then 1 else 0) := sum_push_mul p f _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a _
      by_cases h : g (f a)=c <;> simp only [h,Function.comp_apply,ite_true,ite_false,mul_one,mul_zero]

lemma push_count_sum {A B : Type*} [Fintype A] [Fintype B] [DecidableEq B]
    {Q : ℕ} (p : IntegerLaw A Q) (f : A → B) (b : B) :
    (p.push f).count b=∑ a,if f a=b then p.count a else 0 := rfl

lemma boolean_push_count {B : Type*} [Fintype B] [DecidableEq B] (s : ℕ)
    (f : (Fin s → Bool) → B) (b : B) :
    ((boolean s).push f).count b=∑ bits,if f bits=b then 1 else 0 := rfl

end ContingencyTables.IntegerLaw

namespace ContingencyTables.SmallGraphProfiles
open ProfilePrograms DensePrograms PhysicalCompletionFibres FirstPaperPhysicalMarginal
open SmallContextCoordinates CompletionCounts
open scoped BigOperators Classical
noncomputable section

variable {m n q : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)
variable (e : Fin q ≃ Cells (paperSmall r c)) (b h : ℕ)
local notation "s" => smallProposalBits (I := Fin m) (J := Fin n)
local notation "BoxIndex" => ProfileIndex (m := m) (n := n) (q := q)

attribute [local irreducible] stateCode stateCodeData profileIndex profileAt matrixInput
  UnitCountPrograms.matrixEntry unitStepCounts

lemma unit_wordViews_actual (htotal : ∑ i,r i=∑ j,c j) (z x : PaperStates r c)
    (xs : List Bool) (v : List ℕ×List ℕ) (bits : Fin s → Bool) :
    UnitCountPrograms.wordViews ((matrixInput r c e b h z xs,(stateCode r c e x,v)),List.ofFn bits)=
      stateCode r c e (unitCodeBitStep r c e x bits) := by
  unfold UnitCountPrograms.wordViews
  rw [sourceData_input,candidate_stateCodeData,codeProposal_encoded r c e htotal x bits]
  cases hp : decodedCodeProposal r c e x bits <;>
    simp only [Option.map_none,Option.map_some,Option.getD_none,Option.getD_some,unitCodeBitStep,hp]

lemma unitStepCounts_push_count (x : PaperStates r c) (j : BoxIndex) :
    ((unitStepCounts r c e x).push (profileIndex r c e)).count j=
      ∑ bits : Fin s → Bool,if profileIndex r c e (unitCodeBitStep r c e x bits)=j then 1 else 0 := by
  unfold unitStepCounts
  rw [IntegerLaw.push_push_count]
  exact IntegerLaw.boolean_push_count s
    (profileIndex r c e ∘ unitCodeBitStep r c e x) j

lemma unit_wordCount_actual (htotal : ∑ i,r i=∑ j,c j) (z x : PaperStates r c)
    (xs : List Bool) (j : BoxIndex) (bits : Fin s → Bool) :
    UnitCountPrograms.wordCount
      ((matrixInput r c e b h z xs,(stateCode r c e x,boxCode j)),List.ofFn bits)=
      if profileIndex r c e (unitCodeBitStep r c e x bits)=j then 1 else 0 := by
  unfold UnitCountPrograms.wordCount
  rw [unit_wordViews_actual r c e b h htotal z x xs (boxCode j) bits,←boxCode_index r c e]
  have he (a b : BoxIndex) : boxCode a=boxCode b ↔ a=b :=
    (boxCode_injective (m := m) (n := n) (q := q)).eq_iff
  simp only [he]

lemma unit_validEntry_actual (htotal : ∑ i,r i=∑ j,c j) (z x : PaperStates r c)
    (xs : List Bool) (hs : xs.length=s) (j : BoxIndex) :
    UnitCountPrograms.validEntry (matrixInput r c e b h z xs,(stateCode r c e x,boxCode j))=
      ((unitStepCounts r c e x).push (profileIndex r c e)).count j := by
  unfold UnitCountPrograms.validEntry
  have hxs : (matrixInput r c e b h z xs).2=xs := by unfold matrixInput; rfl
  rw [hxs]
  change ((booleanWords xs).map (fun w => UnitCountPrograms.wordCount
    ((matrixInput r c e b h z xs,(stateCode r c e x,boxCode j)),w))).sum=_
  rw [sum_booleanWords xs s hs,unitStepCounts_push_count]
  apply Finset.sum_congr rfl
  intro bits _
  exact unit_wordCount_actual r c e b h htotal z x xs j bits

lemma unit_matrixEntry_actual (htotal : ∑ i,r i=∑ j,c j) (z : PaperStates r c)
    (xs : List Bool) (hs : xs.length=s) (i j : BoxIndex) :
    UnitCountPrograms.matrixEntry (matrixInput r c e b h z xs,(boxCode i,boxCode j))=
      (unitBoxStep r c e i).count j := by
  cases hi : profileAt r c e i with
  | none =>
    have hp := boxCode_test_false r c e htotal z i hi
    unfold UnitCountPrograms.matrixEntry
    rw [sourceData_input,hp]
    simp only [Bool.false_eq_true,ite_false]
    unfold UnitCountPrograms.diagonalEntry UnitCountPrograms.denominator
    unfold unitBoxStep
    rw [hi]
    simp only [Option.elim_none,IntegerLaw.point]
    unfold matrixInput
    rw [BinaryPowerPrograms.power_eq,hs]
    have he (a b : BoxIndex) : boxCode a=boxCode b ↔ a=b :=
      (boxCode_injective (m := m) (n := n) (q := q)).eq_iff
    simp only [he,eq_comm]
  | some x =>
    have hix : profileIndex r c e x=i := (profileAt_eq_some r c e i x).mp hi
    have hcode : boxCode i=stateCode r c e x := by rw [←hix,boxCode_index]
    rw [hcode]
    unfold UnitCountPrograms.matrixEntry
    rw [sourceData_input]
    have hx := (test_candidate_iff r c e htotal z (stateCode r c e x)).mpr ⟨x,rfl⟩
    rw [hx]
    simp only [ite_true]
    unfold unitBoxStep
    rw [hi]
    exact unit_validEntry_actual r c e b h htotal z x xs hs j

lemma unit_profileMatrix_actual (htotal : ∑ i,r i=∑ j,c j) (z : PaperStates r c)
    (xs : List Bool) (hs : xs.length=s) :
    UnitCountPrograms.profileMatrix (matrixInput r c e b h z xs)=
      List.ofFn (fun j : BoxIndex => List.ofFn (fun i : BoxIndex =>
        (unitBoxStep r c e i).count j)) := by
  have hv : profileBoxViews (matrixData (matrixInput r c e b h z xs))=
      List.ofFn (boxCode (m := m) (n := n) (q := q)) := by
    unfold matrixData matrixInput
    exact profileBoxViews_actual r c e z
  unfold UnitCountPrograms.profileMatrix
  rw [hv,List.map_ofFn]
  apply congrArg List.ofFn
  funext j
  dsimp only [Function.comp_apply]
  unfold UnitCountPrograms.matrixColumn
  dsimp only [Prod.fst]
  rw [hv,List.map_ofFn]
  apply congrArg List.ofFn
  funext i
  exact unit_matrixEntry_actual r c e b h htotal z xs hs i j

end
end ContingencyTables.SmallGraphProfiles

end OAI
