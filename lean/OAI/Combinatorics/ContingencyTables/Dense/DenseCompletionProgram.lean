import OAI.Combinatorics.ContingencyTables.Dense.DenseIntegerProgram
import OAI.Combinatorics.ContingencyTables.Dense.DenseExponentArithmetic

namespace OAI

/-! # Signed dependent entries from binary margin and matrix lists -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS.TreeTyped
open scoped BigOperators

abbrev CompletionData := (List ℕ×List ℕ)×MatrixCode
abbrev CompletionCell := CompletionData×(ℕ×ℕ)

/-- Index zero denotes the distinguished dependent row or column. -/
def completionParts (z : CompletionCell) : ℕ×ℕ :=
  if z.2.1=0 then
    if z.2.2=0 then
      (z.1.1.1.headD 0+matrixTotal z.1.2,z.1.1.2.tail.sum)
    else (z.1.1.2.getD z.2.2 0,columnTotal (z.1.2,z.2.2-1))
  else if z.2.2=0 then
    (z.1.1.1.getD z.2.1 0,rowTotal (z.1.2,z.2.1-1))
  else (matrixEntry (z.1.2,(z.2.1-1,z.2.2-1)),0)

def completionPartsRealizer : Realizer completionParts := by
  let R : Realizer (fun z : CompletionCell => z.1.1.1) :=
    composition (composition first first) first
  let C : Realizer (fun z : CompletionCell => z.1.1.2) :=
    composition (composition first first) second
  let Z : Realizer (fun z : CompletionCell => z.1.2) := composition first second
  let I : Realizer (fun z : CompletionCell => z.2.1) := composition second first
  let J : Realizer (fun z : CompletionCell => z.2.2) := composition second second
  let Im := composition (pair I (constant 1)) subtract
  let Jm := composition (pair J (constant 1)) subtract
  let Rval := composition (pair R I) (getDFast 0)
  let Cval := composition (pair C J) (getDFast 0)
  let Rsum := composition (pair Z Im) rowTotalRealizer
  let Csum := composition (pair Z Jm) columnTotalRealizer
  let total := pair
    (composition (pair (composition R (head 0)) (composition Z matrixTotalRealizer)) add)
    (composition (composition C tail) listSum)
  let entry := pair (composition (pair Z (pair Im Jm)) matrixEntryRealizer) (constant 0)
  exact (choose (composition (pair I (constant 0)) natEqual)
    (choose (composition (pair J (constant 0)) natEqual) total (pair Cval Csum))
    (choose (composition (pair J (constant 0)) natEqual) (pair Rval Rsum) entry)).congr
      (by intro z; simp only [Function.comp_apply,decide_eq_true_eq,completionParts])

theorem polynomial_completionParts : PolynomialTime completionPartsRealizer := by
  have hR : PolynomialTime (composition
      (composition (first (A := CompletionData) (B := ℕ×ℕ)) first) first) :=
    polynomial_composition (polynomial_composition polynomial_first polynomial_first) polynomial_first
  have hC : PolynomialTime (composition
      (composition (first (A := CompletionData) (B := ℕ×ℕ)) first) second) :=
    polynomial_composition (polynomial_composition polynomial_first polynomial_first) polynomial_second
  have hZ : PolynomialTime (composition
      (first (A := CompletionData) (B := ℕ×ℕ)) second) :=
    polynomial_composition polynomial_first polynomial_second
  have hI : PolynomialTime (composition
      (second (A := CompletionData) (B := ℕ×ℕ)) first) :=
    polynomial_composition polynomial_second polynomial_first
  have hJ : PolynomialTime (composition
      (second (A := CompletionData) (B := ℕ×ℕ)) second) :=
    polynomial_composition polynomial_second polynomial_second
  have hi := polynomial_composition (polynomial_pair hI (polynomial_constant 0)) polynomial_natEqual
  have hj := polynomial_composition (polynomial_pair hJ (polynomial_constant 0)) polynomial_natEqual
  have him := polynomial_composition (polynomial_pair hI (polynomial_constant 1)) polynomial_subtract
  have hjm := polynomial_composition (polynomial_pair hJ (polynomial_constant 1)) polynomial_subtract
  have hr := polynomial_composition (polynomial_pair hR hI) (polynomial_getDFast 0)
  have hc := polynomial_composition (polynomial_pair hC hJ) (polynomial_getDFast 0)
  have hrs := polynomial_composition (polynomial_pair hZ him) polynomial_rowTotal
  have hcs := polynomial_composition (polynomial_pair hZ hjm) polynomial_columnTotal
  have ht := polynomial_pair (polynomial_composition (polynomial_pair
    (polynomial_composition hR (polynomial_head 0))
    (polynomial_composition hZ polynomial_matrixTotal)) polynomial_add)
    (polynomial_composition (polynomial_composition hC polynomial_tail) polynomial_listSum)
  have he := polynomial_pair (polynomial_composition
    (polynomial_pair hZ (polynomial_pair him hjm)) polynomial_matrixEntry) (polynomial_constant 0)
  unfold completionPartsRealizer
  exact polynomial_congr _ (polynomial_choose hi (polynomial_choose hj ht
    (polynomial_pair hc hcs)) (polynomial_choose hj (polynomial_pair hr hrs) he))

def marginCode {m : ℕ} (R : Option (Fin m) → ℕ) : List ℕ :=
  R none::List.ofFn (fun i => R (some i))

def optionIndex {m : ℕ} : Option (Fin m) → ℕ
  | none => 0
  | some i => i.val+1

lemma marginCode_getD {m : ℕ} (R : Option (Fin m) → ℕ) (i : Option (Fin m)) :
    (marginCode R).getD (optionIndex i) 0=R i := by
  cases i with
  | none => rfl
  | some i =>
    simp only [marginCode,optionIndex,List.getD_eq_getElem?_getD,List.getElem?_cons_succ,
      List.getElem?_ofFn,i.isLt,dite_true,Option.getD_some,Fin.eta]

theorem completionParts_code {m n : ℕ} (R : Option (Fin m) → ℕ)
    (P : Option (Fin n) → ℕ) (z : Fin m → Fin n → ℕ)
    (i : Option (Fin m)) (j : Option (Fin n)) :
    completionParts (((marginCode R,marginCode P),matrixCode z),(optionIndex i,optionIndex j))=
      GridBoundary.integerParts R P (fun p => z p.1 p.2) i j := by
  cases i with
  | none =>
    cases j with
    | none =>
      simp only [completionParts,optionIndex,ite_true,marginCode,List.headD_cons,
        List.tail_cons,List.sum_ofFn,matrixTotal_code,GridBoundary.integerParts]
    | some j =>
      simp only [completionParts,optionIndex,ite_true,Nat.add_one_ne_zero,ite_false,
        Nat.add_sub_cancel,columnTotal_code,GridBoundary.integerParts]
      exact congrArg (fun a => (a,∑ i,z i j)) (marginCode_getD P (some j))
  | some i =>
    cases j with
    | none =>
      simp only [completionParts,optionIndex,Nat.add_one_ne_zero,ite_false,ite_true,
        Nat.add_sub_cancel,rowTotal_code,GridBoundary.integerParts]
      exact congrArg (fun a => (a,∑ j,z i j)) (marginCode_getD R (some i))
    | some j =>
      simp only [completionParts,optionIndex,Nat.add_one_ne_zero,ite_false,
        Nat.add_sub_cancel,matrixEntry_code,GridBoundary.integerParts]

/-- The difference of the computed pair is the exact signed completion entry. -/
theorem completionParts_signed {m n : ℕ} (R : Option (Fin m) → ℕ)
    (P : Option (Fin n) → ℕ) (z : Fin m → Fin n → ℕ)
    (i : Option (Fin m)) (j : Option (Fin n)) :
    let p := completionParts
      (((marginCode R,marginCode P),matrixCode z),(optionIndex i,optionIndex j))
    (p.1 : ℤ)-p.2=DenseAffine.integerTable R P (fun ij => z ij.1 ij.2) i j := by
  dsimp only
  rw [completionParts_code]
  exact GridBoundary.integerParts_sub R P _ i j

end ContingencyTables.DensePrograms

end OAI
