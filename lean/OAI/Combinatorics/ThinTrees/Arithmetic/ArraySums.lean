import Mathlib
import OAI.Combinatorics.ThinTrees.Metric.CenteredMatrices

namespace OAI

/-! Array sums. -/

section

namespace CurrentKS.Realization
open CleanRoutine Matrix
open scoped BigOperators

def matrixSumData (p : ℕ×List MatrixData) : MatrixData :=
  weightedSumData (p.1,(List.replicate p.2.length 1,p.2))
def matrixSum : Realizes (prodCode natCode (listCode matrixCode)) matrixCode matrixSumData :=
  let n := first natCode (listCode matrixCode)
  let xs := second natCode (listCode matrixCode)
  let ones := ((constant _ ratCode 1).both (xs.then (lengthList matrixCode))).then (replicateList ratCode)
  (n.both (ones.both xs)).then weightedSum
instance poly_matrixSum : PolyTime matrixSum := by
  unfold matrixSum
  apply poly_then
lemma matrixSum_data {n m : ℕ} (A : Fin m → Matrix (Fin n) (Fin n) ℚ) :
    matrixSumData (n,List.ofFn (fun i => matrixData (A i)))=matrixData (∑i,A i) := by
  unfold matrixSumData
  rw [List.length_ofFn,←List.ofFn_const (n:=m) (1:ℚ),weightedSum_data]
  simp

variable {α β : Type*} {ea : α → Word} {eb : β → Word}
def Realizes.sumFinMatrices {n d : α → ℕ}
    {A : (a : α) → Fin (n a) → Matrix (Fin (d a)) (Fin (d a)) ℚ}
    (r : Realizes (finFamilyCode ea n) matrixCode (fun a => matrixData (A a.1 a.2)))
    (rn : Realizes ea natCode n) (rd : Realizes ea natCode d) :
    Realizes ea matrixCode (fun a => matrixData (∑i,A a i)) :=
  (rd.both (r.tabulateFin rn)).then matrixSum |>.congr (fun a => matrixSum_data (A a))
instance poly_sumFinMatrices {n d : α → ℕ}
    {A : (a : α) → Fin (n a) → Matrix (Fin (d a)) (Fin (d a)) ℚ}
    (r : Realizes (finFamilyCode ea n) matrixCode (fun a => matrixData (A a.1 a.2)))
    (rn : Realizes ea natCode n) (rd : Realizes ea natCode d)
    [PolyTime r] [PolyTime rn] [PolyTime rd] : PolyTime (r.sumFinMatrices rn rd) := by
  unfold Realizes.sumFinMatrices;infer_instance

def Realizes.sumFin {n : α → ℕ} {f : (a : α) → Fin (n a) → ℚ}
    (r : Realizes (finFamilyCode ea n) ratCode (fun a => f a.1 a.2))
    (rn : Realizes ea natCode n) : Realizes ea ratCode (fun a => ∑i,f a i) :=
  ((r.tabulateFin rn).then sumRationals).congr (fun _ => List.sum_ofFn)
instance poly_sumFin {n : α → ℕ} {f : (a : α) → Fin (n a) → ℚ}
    (r : Realizes (finFamilyCode ea n) ratCode (fun a => f a.1 a.2))
    (rn : Realizes ea natCode n) [PolyTime r] [PolyTime rn] : PolyTime (r.sumFin rn) := by
  unfold Realizes.sumFin;infer_instance
end CurrentKS.Realization
end

end OAI
