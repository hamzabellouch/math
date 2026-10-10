import OAI.Combinatorics.ContingencyTables.Sampling.ProfileMatrixEntry
import OAI.Combinatorics.ContingencyTables.Sampling.ProfileTransitionCountSemantics
import OAI.Combinatorics.ContingencyTables.Sampling.ProfileBoxLaw

namespace OAI

/-! # The computed matrix is the actual profile transition law -/

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
local notation "s" => smallProposalBits (I := Fin m) (J := Fin n)
local notation "f" => 25*(d+b+h+1)^62
local notation "BoxIndex" => ProfileIndex (m := m) (n := n) (q := q)

attribute [local irreducible] stateCode stateCodeData prepareTransitionCache transitionCount
  ProfilePrograms.matrixEntry validMatrixEntry listedStepCounts listedCompletionCounts

def matrixInput (x : PaperStates r c) (xs : List Bool) : MatrixParameters :=
  ((((stateCodeData r c e x,d^12),(d,h)),f),xs)

def boxCode (k : BoxIndex) : List ℕ×List ℕ :=
  splitViews (q,List.ofFn
    (fun i => ((finFunctionFinEquiv.symm k : ProfileBox (m := m) (n := n) (q := q)) i).val))

lemma boxCode_injective : Function.Injective (boxCode (m := m) (n := n) (q := q)) := by
  intro k l hkl
  have hv := congrArg flattenViews hkl
  simp only [boxCode,splitViews,flattenViews,List.take_append_drop] at hv
  have he : (finFunctionFinEquiv.symm k : ProfileBox (m := m) (n := n) (q := q))=
      finFunctionFinEquiv.symm l := by
    funext i
    exact Fin.ext (congrFun (List.ofFn_injective hv) i)
  exact finFunctionFinEquiv.symm.injective he

lemma boxCode_index (x : PaperStates r c) :
    boxCode (profileIndex r c e x)=stateCode r c e x := by
  exact ((decodeStateCode_eq_some_iff r c e _ x).mp (profileAt_index r c e x)).symm

lemma candidate_stateCodeData (x y : PaperStates r c) :
    candidateData (stateCodeData r c e x,stateCode r c e y)=stateCodeData r c e y := by
  unfold candidateData stateCodeData codeCheckData
  rfl

lemma test_candidate_iff (htotal : ∑ i,r i=∑ j,c j) (x : PaperStates r c)
    (v : List ℕ×List ℕ) :
    profileTest (candidateData (stateCodeData r c e x,v))=true ↔
      ∃ y : PaperStates r c,stateCode r c e y=v := by
  simpa only [candidateData,stateCodeData,codeCheckData,stateCode] using
    (profileTest_code_iff r c htotal e v)

lemma matrixEntry_codes (htotal : ∑ i,r i=∑ j,c j) (z x y : PaperStates r c)
    (xs : List Bool) (hs : xs.length=s) :
    ProfilePrograms.matrixEntry (matrixInput r c e b h z xs,(stateCode r c e x,stateCode r c e y))=
      (listedStepCounts r c e hr hc b h hb x).count y := by
  have hx : profileTest (candidateData (stateCodeData r c e z,stateCode r c e x))=true :=
    (test_candidate_iff r c e htotal z _).mpr ⟨x,rfl⟩
  have hy : profileTest (candidateData (stateCodeData r c e z,stateCode r c e y))=true :=
    (test_candidate_iff r c e htotal z _).mpr ⟨y,rfl⟩
  unfold ProfilePrograms.matrixEntry sourceData targetData matrixData matrixInput
  rw [hx,hy]
  simp only [ite_true]
  unfold validMatrixEntry entryQuery entryCacheParameters
  dsimp only [sourceData,matrixData]
  rw [candidate_stateCodeData]
  exact transitionCount_actual r c e hr hc b h hb htotal x y xs hs

end
end ContingencyTables.SmallGraphProfiles

end OAI
