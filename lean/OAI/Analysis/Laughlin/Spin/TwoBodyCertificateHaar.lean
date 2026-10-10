import OAI.Analysis.Laughlin.Operators.Certificate
import OAI.Analysis.Laughlin.Pair.FockHaar

namespace OAI

namespace Laughlin.Fock
open Rotation MeasureTheory
open scoped BigOperators Matrix

noncomputable def physicalPairRowMatrix (Q : ℕ) (row : ℕ × ℤ × List (ℕ × ℕ × ℤ)) :
    Matrix (Fin (2*Q-2+1)) (Fin (2*Q-2+1)) ℂ :=
  fun i j => if i.val=row.1 ∧ j.val=row.1 then ((row.2.1 : ℂ)/10^7)^2 else 0

noncomputable def physicalTwoBodyMatrix (Q : ℕ) :
    Matrix (Fin (2*Q-2+1)) (Fin (2*Q-2+1)) ℂ :=
  (Certificate.rows.map (physicalPairRowMatrix Q)).sum

theorem physicalTwoBodyMatrix_trace (Q : ℕ) (hQ : 5 ≤ Q) :
    Matrix.trace (physicalTwoBodyMatrix Q) = (93527408868499/10^14 : ℂ) := by
  have htr (row : ℕ × ℤ × List (ℕ × ℕ × ℤ)) (hr : row ∈ Certificate.rows) :
      Matrix.trace (physicalPairRowMatrix Q row) =
      ((row.2.1 : ℂ)/10^7)^2 := by
    have ht : row.1 ≤ 7 := (show ∀ row ∈ Certificate.rows, row.1 ≤ 7 from by decide) row hr
    let p : Fin (2*Q-2+1) := ⟨row.1,by omega⟩
    have he (i : Fin (2*Q-2+1)) : i.val=row.1 ↔ i=p := by
      constructor
      · intro h; exact Fin.ext h
      · intro h; subst i; rfl
    simp only [Matrix.trace,Matrix.diag,physicalPairRowMatrix,he,and_self,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  have hsum (l : List (Matrix (Fin (2*Q-2+1)) (Fin (2*Q-2+1)) ℂ)) :
      Matrix.trace l.sum = (l.map Matrix.trace).sum := by
    induction l with
    | nil => simp
    | cons a l ih => simp only [List.sum_cons,List.map_cons,Matrix.trace_add,ih]
  rw [physicalTwoBodyMatrix,hsum,List.map_map]
  have he : Certificate.rows.map (fun row => Matrix.trace (physicalPairRowMatrix Q row)) =
      Certificate.rows.map (fun row => ((row.2.1 : ℂ)/10^7)^2) := List.map_congr_left htr
  change (Certificate.rows.map (fun row => Matrix.trace (physicalPairRowMatrix Q row))).sum = _
  rw [he]
  have hl (l : List (ℕ × ℤ × List (ℕ × ℕ × ℤ))) :
      (l.map (fun row => ((row.2.1 : ℂ)/10^7)^2)).sum =
        ((l.map (fun row => row.2.1^2)).sum : ℤ)/(10^14 : ℂ) := by
    induction l with
    | nil => simp
    | cons a l ih =>
      simp only [List.map_cons,List.sum_cons,Int.cast_add,Int.cast_pow,ih]
      ring
  rw [hl,Certificate.eta_numerator]
  norm_num

theorem physical_twoBody_certificate_haar (Q : ℕ) (hQ : 5 ≤ Q) (x : Space Q) :
    ((2*Q-2+1 : ℕ) : ℂ) * (∫ g, contractionForm Q
      (fun p : Fin (2*Q-2+1) => sourcePairEnd Q p.val) (physicalTwoBodyMatrix Q)
      (exteriorRotation Q g⁻¹ x) ∂sourceHaar) =
      (93527408868499/10^14 : ℂ) * (sourceFockEnergy Q x : ℂ) := by
  rw [physical_pairFock_haar Q (by omega),physicalTwoBodyMatrix_trace Q hQ]
  have hd : ((2*Q-2+1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (2*Q-2)
  field_simp

end Laughlin.Fock

end OAI
