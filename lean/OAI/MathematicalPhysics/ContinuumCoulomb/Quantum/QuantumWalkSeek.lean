import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumWalkErasure
import OAI.Computability.QuantumFactoring.BitStackIteration

namespace OAI

/-! A bounded scan finds the first occurrence of a cell in a route list.
It only removes list heads, so the machine state never grows. -/

noncomputable section
open scoped List
namespace ContinuumCoulomb.QuantumWalkSeek
open ExactQuantumFactoring.BitStackProgram
variable {α : Type} [DecidableEq α]

def scan (d : α) (x : α × List α) : α × List α :=
  if x.1 = x.2.headD d then x else (x.1,x.2.tail)

@[simp] theorem scan_first (d : α) (x : α × List α) : (scan d x).1 = x.1 := by
  unfold scan
  split <;> rfl

theorem scan_sublist (d : α) (x : α × List α) : (scan d x).2 <+ x.2 := by
  unfold scan
  split
  · exact List.Sublist.refl _
  · exact List.tail_sublist _

theorem iterate_first (d : α) (x : α × List α) (n : ℕ) : ((scan d)^[n] x).1 = x.1 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply',scan_first,ih]

theorem iterate_sublist (d : α) (x : α × List α) (n : ℕ) : ((scan d)^[n] x).2 <+ x.2 := by
  induction n with
  | zero => exact List.Sublist.refl _
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact (scan_sublist d _).trans ih

theorem scan_drop_idx (d a : α) (xs : List α) (n : ℕ) (hn : xs.length ≤ n) :
    ((scan d)^[n] (a,xs)).2 = xs.drop (xs.idxOf a) := by
  induction n generalizing xs with
  | zero =>
    have h : xs = [] := List.length_eq_zero_iff.mp (by omega)
    subst xs
    rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply]
    cases xs with
    | nil =>
      have h : scan d (a,[]) = (a,[]) := by unfold scan; split <;> rfl
      have hi : ((scan d)^[n] (a,[])) = (a,[]) := by
        exact Function.iterate_fixed h n
      rw [h,hi]
      rfl
    | cons b xs =>
      by_cases hab : a=b
      · subst b
        have h : scan d (a,a::xs) = (a,a::xs) := by simp [scan]
        rw [h,Function.iterate_fixed h n]
        simp
      · have hlen : xs.length ≤ n := by simpa using hn
        simpa [scan,hab,List.idxOf_cons,beq_iff_eq,eq_comm] using ih xs hlen

noncomputable def scanProgram (ea : α → List Bool) (d : α)
    (eqp : Procedure (prodCode ea ea) Procedure.boolCode (fun x => decide (x.1=x.2))) :
    Procedure (prodCode ea (listCode ea)) (prodCode ea (listCode ea)) (scan d) := by
  let a := Procedure.first ea (listCode ea)
  let xs := Procedure.second ea (listCode ea)
  let same := eqp.comp (a.pair ((Procedure.listHead ea d).comp xs))
  exact (Procedure.conditional same (Procedure.identity _) (a.pair ((Procedure.listTail ea).comp xs))).congrFun
    (by intro x; simp only [Function.comp_apply,scan,decide_eq_true_eq,id_eq])

noncomputable def program (ea : α → List Bool) (d : α)
    (eqp : Procedure (prodCode ea ea) Procedure.boolCode (fun x => decide (x.1=x.2))) :
    Procedure (prodCode ea (listCode ea)) (listCode ea) (fun x => x.2.drop (x.2.idxOf x.1)) := by
  let rep := (scanProgram ea d eqp).iterate Polynomial.X (by
    intro n x i _
    simp only [prodCode,pairBits_length,Polynomial.eval_X,iterate_first]
    have h := QuantumWalkErasure.listCode_length_sublist ea (iterate_sublist d x i)
    omega)
  let count := (Procedure.length.precompose (listCode ea)).comp (Procedure.second ea (listCode ea))
  exact ((Procedure.second ea (listCode ea)).comp
    (rep.comp (count.pair (Procedure.identity _)))).congrFun (by
      intro x
      exact scan_drop_idx d x.1 x.2 _ (list_length_le_code ea x.2))

end ContinuumCoulomb.QuantumWalkSeek

end

end OAI
