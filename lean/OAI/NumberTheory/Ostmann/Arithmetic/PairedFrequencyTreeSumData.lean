import OAI.NumberTheory.Ostmann.Arithmetic.PairedFrequencyTreeSum
import OAI.NumberTheory.Ostmann.Characters.FrequencyExposureLeaves

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.PairedFrequencyTreeSum
open Characters
open FrequencyTreeSum

def defaultData (Q : ℕ) : FrequencyExposure.Data Q :=
  ⟨1,1,1,1,1,1,by simp,by simp⟩

variable {Q : ℕ} (S : List Bool → Finset (ℤ × ℤ))
  (hdiv : ∀ p s, s ∈ S p → s.1.natAbs ∣ Q ∧ s.2.natAbs ∣ Q)

def assignmentDataForward : {k : ℕ} → {p : List Bool} →
    Assignment S k p → List Bool → FrequencyExposure.Data Q
  | 0,_,_,_ => defaultData Q
  | _+1,p,x,[] =>
      ⟨x.1.val.1,x.1.val.2,(root S x.2.1).1,(root S x.2.2).1,
        (root S x.2.1).2,(root S x.2.2).2,
        (hdiv p x.1.val x.1.property).1,(hdiv p x.1.val x.1.property).2⟩
  | _+1,_,x,false::q => assignmentDataForward x.2.1 q
  | _+1,_,x,true::q => assignmentDataForward x.2.2 q

def assignmentData {k : ℕ} {p : List Bool} (x : Assignment S k p)
    (q : List Bool) : FrequencyExposure.Data Q :=
  assignmentDataForward S hdiv x q.reverse

theorem assignmentData_left {k : ℕ} {p : List Bool} (x : Assignment S (k+1) p)
    (q : List Bool) :
    assignmentData S hdiv x (q ++ [false]) = assignmentData S hdiv x.2.1 q := by
  simp [assignmentData, List.reverse_append, assignmentDataForward]

theorem assignmentData_right {k : ℕ} {p : List Bool} (x : Assignment S (k+1) p)
    (q : List Bool) :
    assignmentData S hdiv x (q ++ [true]) = assignmentData S hdiv x.2.2 q := by
  simp [assignmentData, List.reverse_append, assignmentDataForward]

theorem budget_eq_weight_shift (C : NNReal) (ε : ℝ) {k : ℕ} {p : List Bool}
    (x : Assignment S k p) (d : List Bool → FrequencyExposure.Data Q) (r : List Bool)
    (hd : ∀ q, d (q ++ r) = assignmentData S hdiv x q) :
    ((FrequencyExposure.budget C ε d k r).value : ℝ) =
      weight S (factor (C : ℝ) ε) x := by
  induction k generalizing p r with
  | zero => rfl
  | succ k ih =>
    have hleft : ∀ q, d (q ++ false :: r) = assignmentData S hdiv x.2.1 q := by
      intro q
      calc
        _ = d ((q ++ [false]) ++ r) := by simp only [List.append_assoc, List.cons_append, List.nil_append]
        _ = assignmentData S hdiv x (q ++ [false]) := hd _
        _ = _ := assignmentData_left S hdiv x q
    have hright : ∀ q, d (q ++ true :: r) = assignmentData S hdiv x.2.2 q := by
      intro q
      calc
        _ = d ((q ++ [true]) ++ r) := by simp only [List.append_assoc, List.cons_append, List.nil_append]
        _ = assignmentData S hdiv x (q ++ [true]) := hd _
        _ = _ := assignmentData_right S hdiv x q
    have hroot : d r = assignmentData S hdiv x [] := by simpa using hd []
    change ((C : ℝ) * (FrequencyExposure.reducedPair (d r) : ℝ) ^ (ε - 1)) *
      ((FrequencyExposure.budget C ε d k (false :: r)).value : ℝ) *
      ((FrequencyExposure.budget C ε d k (true :: r)).value : ℝ) = _
    rw [ih x.2.1 (false :: r) hleft, ih x.2.2 (true :: r) hright, hroot]
    rfl

theorem budget_eq_weight (C : NNReal) (ε : ℝ) {k : ℕ} {p : List Bool}
    (x : Assignment S k p) :
    ((FrequencyExposure.budget C ε (assignmentData S hdiv x) k []).value : ℝ) =
      weight S (factor (C : ℝ) ε) x :=
  budget_eq_weight_shift S hdiv C ε x _ [] (fun q => by rw [List.append_nil])

end Ostmann.Arithmetic.PairedFrequencyTreeSum

end

end OAI
