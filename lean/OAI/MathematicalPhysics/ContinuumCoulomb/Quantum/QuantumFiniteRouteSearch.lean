import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumRouteCandidates
import OAI.Computability.QuantumFactoring.BitStackListOps
import OAI.Computability.QuantumFactoring.BitStackListIndex
import OAI.Computability.QuantumFactoring.BitStackAdder

namespace OAI

/-! The 140-candidate route search uses a literal fixed-size scan. Its input
predicate can be supplied by the finite physical geometry table. -/

namespace ContinuumCoulomb.QuantumFiniteRouteSearch
open ExactQuantumFactoring.BitStackProgram

def firstTrue : ℕ → List Bool → ℕ
  | 0, _ => 0
  | k+1, bs => if bs.headD false then 0 else 1+firstTrue k bs.tail

theorem firstTrue_le (k : ℕ) (bs : List Bool) : firstTrue k bs ≤ k := by
  induction k generalizing bs with
  | zero => rfl
  | succ k ih =>
    simp only [firstTrue]
    split
    · omega
    · have h := ih bs.tail
      omega

theorem firstTrue_eq_findIdx {k : ℕ} {bs : List Bool} (h : bs.length = k) :
    firstTrue k bs = bs.findIdx id := by
  induction bs generalizing k with
  | nil => subst k; rfl
  | cons b bs ih =>
    have hk : k ≠ 0 := by simp only [List.length_cons] at h; omega
    obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
    have ht : bs.length = k := by simpa using h
    cases b <;> simp [firstTrue,List.findIdx_cons,ih ht,Nat.add_comm]

theorem drop_findIdx_headD {α : Type} (xs : List α) (p : α → Bool) (default : α) :
    (xs.drop (xs.findIdx p)).headD default = (xs.find? p).getD default := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    by_cases h : p a
    · simp [List.findIdx_cons,h]
    · simpa [List.findIdx_cons,List.find?_cons,h,Nat.add_comm] using ih

def selectValue {α : Type} (default : α) (p : α → Bool) (xs : List α) : α :=
  (xs.drop (firstTrue 140 (xs.map p))).headD default

theorem selectValue_eq_find {α : Type} (default : α) (p : α → Bool) (xs : List α)
    (hlen : xs.length = 140) : selectValue default p xs = (xs.find? p).getD default := by
  have hi : firstTrue 140 (xs.map p) = xs.findIdx p := by
    rw [firstTrue_eq_findIdx (by simpa using hlen),List.findIdx_map]
    rfl
  rw [selectValue,hi,drop_findIdx_headD]

theorem selectValue_eq_of_find {α : Type} (default : α) (p : α → Bool) (xs : List α)
    (hlen : xs.length = 140) {v : α} (hv : xs.find? p = some v) :
    selectValue default p xs = v := by
  rw [selectValue_eq_find default p xs hlen,hv]
  rfl

noncomputable section

noncomputable def indexProgram (k : ℕ) :
    Procedure (listCode Procedure.boolCode) Nat.bits (firstTrue k) := by
  induction k with
  | zero => exact Procedure.constant _ _ 0
  | succ k ih =>
    let head := Procedure.listHead Procedure.boolCode false
    let tail := Procedure.listTail Procedure.boolCode
    let next := Procedure.binaryAdd.comp
      ((Procedure.constant (listCode Procedure.boolCode) Nat.bits 1).pair (ih.comp tail))
    exact (Procedure.conditional head (Procedure.constant _ _ 0) next).congrFun (by intro bs; rfl)

noncomputable def indexCertificate : Turing.TM2ComputableInPolyTime
    (listCode Procedure.boolCode) Nat.bits (firstTrue 140) := (indexProgram 140).toTM2

noncomputable def predicateIndexProgram {α : Type} (ea : α → List Bool) (default : α)
    {p : α → Bool} (test : Procedure ea Procedure.boolCode p) :
    Procedure (listCode ea) Nat.bits (fun xs => firstTrue 140 (xs.map p)) :=
  (indexProgram 140).comp (Procedure.listMap default false test)

noncomputable def selectProgram {α : Type} (ea : α → List Bool) (default : α)
    {p : α → Bool} (test : Procedure ea Procedure.boolCode p) :
    Procedure (listCode ea) ea
      (fun xs => (xs.drop (firstTrue 140 (xs.map p))).headD default) :=
  (Procedure.listGet ea default).comp
    ((predicateIndexProgram ea default test).pair (Procedure.identity _))

end
end ContinuumCoulomb.QuantumFiniteRouteSearch

end OAI
