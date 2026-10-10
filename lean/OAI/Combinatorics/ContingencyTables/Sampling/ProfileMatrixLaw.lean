import OAI.Combinatorics.ContingencyTables.Sampling.ProfileMatrixSemantics
import OAI.Combinatorics.ContingencyTables.Sampling.ProfileMatrixProgram

namespace OAI

/-! # Every entry of the computed profile matrix has its exact integer law -/

namespace ContingencyTables.IntegerLaw
open scoped BigOperators Classical

lemma push_count_not_range {A B : Type*} [Fintype A] [Fintype B] [DecidableEq B]
    {Q : ℕ} (p : IntegerLaw A Q) (f : A → B) (b : B) (hb : ∀ a,f a≠b) :
    (p.push f).count b=0 := by
  change (∑ a,if f a=b then p.count a else 0)=0
  simp only [hb,ite_false,Finset.sum_const_zero]

end ContingencyTables.IntegerLaw

namespace ContingencyTables.SmallGraphProfiles
open ProfilePrograms DensePrograms PhysicalCompletionFibres FirstPaperPhysicalMarginal
open SmallContextCoordinates CompletionCounts
open scoped BigOperators Classical
noncomputable section

variable {m n q : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)
variable (e : Fin q ≃ Cells (paperSmall r c))
variable (hr : 0<(largeIndices ((dimensionAllowance (I := Fin m) (J := Fin n))^20,List.ofFn r)).length)
variable (hc : 0<(largeIndices ((dimensionAllowance (I := Fin m) (J := Fin n))^20,List.ofFn c)).length)
variable (b h : ℕ) (hb : Nat.clog 2 (stateBound r c+2)≤b)
local notation "d" => dimensionAllowance (I := Fin m) (J := Fin n)
local notation "s" => smallProposalBits (I := Fin m) (J := Fin n)
local notation "f" => 25*(d+b+h+1)^62
local notation "BoxIndex" => ProfileIndex (m := m) (n := n) (q := q)

attribute [local irreducible] stateCode stateCodeData listedStepCounts prepareTransitionCache
  profileIndex profileAt ProfilePrograms.matrixEntry matrixInput IntegerLaw.push listedWalkCounts

lemma boxCode_test_false (htotal : ∑ i,r i=∑ j,c j) (z : PaperStates r c)
    (k : BoxIndex) (hk : profileAt r c e k=none) :
    profileTest (candidateData (stateCodeData r c e z,boxCode k))=false := by
  apply Bool.eq_false_iff.mpr
  intro ht
  obtain ⟨x,hx⟩ := (test_candidate_iff r c e htotal z _).mp ht
  have hd : profileAt r c e k=some x := by
    unfold profileAt
    exact (decodeStateCode_eq_some_iff r c e _ x).mpr hx
  rw [hk] at hd
  cases hd

lemma matrixDenominator_actual (z : PaperStates r c) (xs : List Bool) (hs : xs.length=s) :
    matrixDenominator (matrixInput r c e b h z xs)=2^(s+f) := by
  unfold matrixDenominator matrixInput
  rw [BinaryPowerPrograms.power_eq,hs]

lemma sourceData_input (z : PaperStates r c) (xs : List Bool) (u v : List ℕ×List ℕ) :
    sourceData (matrixInput r c e b h z xs,(u,v))=candidateData (stateCodeData r c e z,u) := by
  unfold sourceData matrixData matrixInput
  rfl

lemma targetData_input (z : PaperStates r c) (xs : List Bool) (u v : List ℕ×List ℕ) :
    targetData (matrixInput r c e b h z xs,(u,v))=candidateData (stateCodeData r c e z,v) := by
  unfold targetData matrixData matrixInput
  rfl

lemma matrixEntry_invalid_source (htotal : ∑ i,r i=∑ j,c j) (z : PaperStates r c)
    (xs : List Bool) (hs : xs.length=s) (i j : BoxIndex)
    (hi : profileAt r c e i=none) :
    ProfilePrograms.matrixEntry (matrixInput r c e b h z xs,(boxCode i,boxCode j))=
      if j=i then 2^(s+f) else 0 := by
  have hp := boxCode_test_false r c e htotal z i hi
  unfold ProfilePrograms.matrixEntry
  rw [sourceData_input,hp]
  simp only [Bool.false_eq_true,ite_false]
  unfold diagonalMatrixEntry
  rw [matrixDenominator_actual r c e b h z xs hs]
  have hij : boxCode i=boxCode j ↔ i=j :=
    (boxCode_injective (m := m) (n := n) (q := q)).eq_iff
  simp only [hij,eq_comm]

lemma matrixEntry_invalid_target (htotal : ∑ i,r i=∑ j,c j) (z x : PaperStates r c)
    (xs : List Bool) (j : BoxIndex) (hj : profileAt r c e j=none) :
    ProfilePrograms.matrixEntry (matrixInput r c e b h z xs,(stateCode r c e x,boxCode j))=0 := by
  have hx := (test_candidate_iff r c e htotal z (stateCode r c e x)).mpr ⟨x,rfl⟩
  have hj' := boxCode_test_false r c e htotal z j hj
  unfold ProfilePrograms.matrixEntry
  rw [sourceData_input,targetData_input,hx,hj']
  simp only [ite_true,Bool.false_eq_true,ite_false]

lemma matrixEntry_actual (htotal : ∑ i,r i=∑ j,c j) (z : PaperStates r c)
    (xs : List Bool) (hs : xs.length=s) (i j : BoxIndex) :
    ProfilePrograms.matrixEntry (matrixInput r c e b h z xs,(boxCode i,boxCode j))=
      (profileBoxStep r c e hr hc b h hb i).count j := by
  cases hi : profileAt r c e i with
  | none =>
    rw [matrixEntry_invalid_source r c e b h htotal z xs hs i j hi]
    unfold profileBoxStep
    rw [hi]
    rfl
  | some x =>
    have hix : profileIndex r c e x=i := (profileAt_eq_some r c e i x).mp hi
    have hcode : boxCode i=stateCode r c e x := by rw [←hix,boxCode_index]
    rw [hcode]
    unfold profileBoxStep
    rw [hi]
    simp only [Option.elim_some]
    cases hj : profileAt r c e j with
    | none =>
      rw [matrixEntry_invalid_target r c e b h htotal z x xs j hj]
      symm
      apply IntegerLaw.push_count_not_range
      intro a hindex
      rw [←hindex,profileAt_index] at hj
      cases hj
    | some y =>
      have hjy : profileIndex r c e y=j := (profileAt_eq_some r c e j y).mp hj
      rw [←hjy,boxCode_index,
        IntegerLaw.push_count_injective _ _ (profileIndex_injective r c e)]
      exact matrixEntry_codes r c e hr hc b h hb htotal z x y xs hs

lemma profileMatrix_actual (htotal : ∑ i,r i=∑ j,c j) (z : PaperStates r c)
    (xs : List Bool) (hs : xs.length=s) :
    profileMatrix (matrixInput r c e b h z xs)=
      List.ofFn (fun j : BoxIndex => List.ofFn (fun i : BoxIndex =>
        (profileBoxStep r c e hr hc b h hb i).count j)) := by
  have hv : profileBoxViews (matrixData (matrixInput r c e b h z xs))=
      List.ofFn (boxCode (m := m) (n := n) (q := q)) :=
    by
      unfold matrixData matrixInput
      exact profileBoxViews_actual r c e z
  unfold profileMatrix
  rw [hv,List.map_ofFn]
  apply congrArg List.ofFn
  funext j
  dsimp only [Function.comp_apply]
  unfold matrixColumn
  dsimp only [Prod.fst]
  rw [hv,List.map_ofFn]
  apply congrArg List.ofFn
  funext i
  exact matrixEntry_actual r c e hr hc b h hb htotal z xs hs i j

lemma profileMatrix_walk (htotal : ∑ i,r i=∑ j,c j) (z : PaperStates r c)
    (xs : List Bool) (hs : xs.length=s) (N : ℕ) :
    IntegerMatrixPrograms.iterate (N,(profileMatrix (matrixInput r c e b h z xs),
      List.ofFn (fun k : BoxIndex => if k=profileIndex r c e z then 1 else 0)))=
      List.ofFn (fun k : BoxIndex =>
        ((listedWalkCounts r c e hr hc b h hb z N).push (profileIndex r c e)).count k) := by
  rw [profileMatrix_actual r c e hr hc b h hb htotal z xs hs]
  exact profileBox_iterate r c e hr hc b h hb z N

end
end ContingencyTables.SmallGraphProfiles

end OAI
