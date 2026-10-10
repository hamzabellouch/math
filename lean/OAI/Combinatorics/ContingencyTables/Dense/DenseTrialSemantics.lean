import OAI.Combinatorics.ContingencyTables.Dense.DenseTrialProgram
import OAI.Combinatorics.ContingencyTables.Dense.DenseBooleanTrial
import OAI.Combinatorics.ContingencyTables.Dense.DenseBoundedRejection

namespace OAI

/-! # The complete trial program uses the manuscript's finite-bit experiment -/

namespace ContingencyTables.DensePrograms
open GridBoundary FairBits
open scoped BigOperators Classical

noncomputable section

def trialInput {m n d : ℕ} (R : Option (Fin m) → ℕ) (P : Option (Fin n) → ℕ)
    (h : ℕ) (a : Grid (I := Fin (m*n)) (4*d^8)) (bits : List Bool) : DenseTrialData :=
  (((((marginCode R,marginCode P),gridNatCode a),d),h),bits)

lemma flatToGridData_code {m n K : ℕ} (R : Option (Fin m) → ℕ) (P : Option (Fin n) → ℕ)
    (d : ℕ) (a : Grid (I := Fin (m*n)) K) :
    flatToGridData (((marginCode R,marginCode P),gridNatCode a),d)=
      exponentDataCode R P d (fun i j => (corner a (finProdFinEquiv (i,j))).toNat) := by
  unfold flatToGridData gridNatCode
  rw [unflattenGrid_code]
  rfl

lemma trialGrid_code {m n d : ℕ} (hd : 0 < d)
    (R : Option (Fin m) → ℕ) (P : Option (Fin n) → ℕ) (h : ℕ)
    (a : Grid (I := Fin (m*n)) (4*d^8))
    (bits : Fin (denseTrialBits R P d finProdFinEquiv h) → Bool) :
    trialGrid (trialInput R P h a (List.ofFn bits))=
      exponentDataCode R P d (fun i j =>
        (corner (denseBooleanWalk R P d finProdFinEquiv a (d^50*(h+1)^2)
          (trialWordEquiv R P d finProdFinEquiv h bits).1) (finProdFinEquiv (i,j))).toNat) := by
  dsimp only [trialGrid,trialInput,trialWalkBits]
  have ht := ofFn_split_take (p := (d^50*(h+1)^2)*denseStepBits d)
    (k := ∑ j : Fin (m*n),offsetBitLength (integerWidth R P d (finProdFinEquiv.symm j)) h d) bits
  have he := congrArg (fun w => flatToGridData
    (flatWordWalk ((((marginCode R,marginCode P),gridNatCode a),d),w))) ht
  refine he.trans ?_
  rw [flatWordWalk_code hd]
  exact flatToGridData_code R P d _

lemma trialOffsets_code {m n d : ℕ} (hd : 0 < d)
    (R : Option (Fin m) → ℕ) (P : Option (Fin n) → ℕ) (h : ℕ)
    (a : Grid (I := Fin (m*n)) (4*d^8))
    (bits : Fin (denseTrialBits R P d finProdFinEquiv h) → Bool) :
    trialOffsets (trialInput R P h a (List.ofFn bits))=
      List.ofFn (fun j => List.ofFn ((trialWordEquiv R P d finProdFinEquiv h bits).2 j)) := by
  unfold trialOffsets
  rw [trialGrid_code hd,offsetLengths_code]
  dsimp only [trialInput,trialWalkBits]
  have ht := ofFn_split_drop (p := (d^50*(h+1)^2)*denseStepBits d)
    (k := ∑ j : Fin (m*n),offsetBitLength (integerWidth R P d (finProdFinEquiv.symm j)) h d) bits
  have he := congrArg (fun w => dependentChunks
    (List.ofFn (fun j : Fin (m*n) => offsetBitLength
      (integerWidth R P d (finProdFinEquiv.symm j)) h d),w)) ht
  refine he.trans ?_
  rw [dependentChunks_ofFn]
  rfl

theorem trialCompletion_code {m n d : ℕ}
    (R : Option (Fin m) → ℕ) (P : Option (Fin n) → ℕ)
    (hd : 14 ≤ d) (hR : ∀ i,d^12 ≤ R i) (hP : ∀ j,d^12 ≤ P j) (h : ℕ)
    (a : Grid (I := Fin (m*n)) (4*d^8))
    (bits : Fin (denseTrialBits R P d finProdFinEquiv h) → Bool) :
    trialCompletion (trialInput R P h a (List.ofFn bits))=
      ((marginCode R,marginCode P),matrixCode (fun i j => trialFree R P d finProdFinEquiv
        (denseBooleanTrial R P d hd hR hP finProdFinEquiv h a bits) (i,j))) := by
  have hd0 : 0 < d := by omega
  unfold trialCompletion
  rw [trialGrid_code hd0,trialOffsets_code hd0]
  apply Prod.ext
  · rfl
  · exact offsetMatrix_trialFree R P (integerWidth_pos R P d hd hR hP) h _ _

def tableOutput {m n : ℕ} {R : Option (Fin m) → ℕ} {P : Option (Fin n) → ℕ}
    (X : Table R P) : MatrixCode :=
  matrixCode (fun i : Fin (m+1) => fun j : Fin (n+1) =>
    X.val (finSuccEquiv m i) (finSuccEquiv n j))

lemma acceptCompletion_trialFree {m n d : ℕ}
    (R : Option (Fin m) → ℕ) (P : Option (Fin n) → ℕ)
    (htotal : ∑ i,R i=∑ j,P j) (t : DenseTrial R P d (m*n)) :
    acceptCompletion ((marginCode R,marginCode P),
      matrixCode (fun i j => trialFree R P d finProdFinEquiv t (i,j)))=
      (trialSuccess R P d finProdFinEquiv htotal t).map tableOutput := by
  have hv := completionValid_code R P (fun i j => trialFree R P d finProdFinEquiv t (i,j))
  by_cases ht : TrialAccepted R P d finProdFinEquiv t
  · have hc := hv.mpr ht
    simp only [acceptCompletion,hc,ite_true,trialSuccess,dite_eq_left ht,Option.map_some]
    rw [completedMatrix_code]
    rfl
  · have hc : completionValid ((marginCode R,marginCode P),
        matrixCode (fun i j => trialFree R P d finProdFinEquiv t (i,j)))≠true := by
      intro h
      exact ht (hv.mp h)
    simp only [acceptCompletion,hc,Bool.false_eq_true,ite_false,trialSuccess,dite_eq_right ht,Option.map_none]

/-- The physical binary program returns exactly the successful table of the
declared finite Boolean experiment, with the same rejection event. -/
theorem denseTrialCode_eq {m n d : ℕ}
    (R : Option (Fin m) → ℕ) (P : Option (Fin n) → ℕ)
    (hd : 14 ≤ d) (hR : ∀ i,d^12 ≤ R i) (hP : ∀ j,d^12 ≤ P j)
    (htotal : ∑ i,R i=∑ j,P j) (h : ℕ)
    (a : Grid (I := Fin (m*n)) (4*d^8))
    (bits : Fin (denseTrialBits R P d finProdFinEquiv h) → Bool) :
    denseTrialCode (trialInput R P h a (List.ofFn bits))=
      (trialSuccess R P d finProdFinEquiv htotal
        (denseBooleanTrial R P d hd hR hP finProdFinEquiv h a bits)).map tableOutput := by
  unfold denseTrialCode
  rw [trialCompletion_code R P hd hR hP]
  exact acceptCompletion_trialFree R P htotal _

end
end ContingencyTables.DensePrograms

end OAI
