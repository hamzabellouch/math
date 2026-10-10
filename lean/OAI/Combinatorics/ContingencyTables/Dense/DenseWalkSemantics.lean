import OAI.Combinatorics.ContingencyTables.Dense.DenseWalkProgram
import OAI.Combinatorics.ContingencyTables.Dense.DenseMetropolisSemantics
import OAI.Combinatorics.ContingencyTables.Dense.DenseBooleanWalk

namespace OAI

/-! # Pointwise agreement of the binary dense loop and the finite walk -/

namespace ContingencyTables.DensePrograms
open GridBoundary FirstSuccess
open scoped Classical

noncomputable section

lemma advance_code {m n d : ℕ}
    (R : Option (Fin m) → ℕ) (P : Option (Fin n) → ℕ)
    (a : Grid (I := Fin (m*n)) (4*d^8)) (bits : Fin (denseStepBits d) → Bool) :
    advance (List.ofFn bits,(((marginCode R,marginCode P),gridNatCode a),d))=
      (((marginCode R,marginCode P),
        gridNatCode (denseBitStep R P d finProdFinEquiv a bits)),d) := by
  unfold advance replaceFlat
  rw [flatWordStep_code]

theorem walkWords_ofFn {m n d : ℕ}
    (R : Option (Fin m) → ℕ) (P : Option (Fin n) → ℕ)
    (a : Grid (I := Fin (m*n)) (4*d^8)) (steps : ℕ)
    (bits : Fin steps → Fin (denseStepBits d) → Bool) :
    walkWords ((((marginCode R,marginCode P),gridNatCode a),d),
      List.ofFn (fun i => List.ofFn (bits i)))=
      (((marginCode R,marginCode P),
        gridNatCode (wordWalk (denseBitStep R P d finProdFinEquiv) a steps bits)),d) := by
  induction steps with
  | zero => rfl
  | succ steps ih =>
    unfold walkWords at ih ⊢
    rw [List.ofFn_succ',List.concat_eq_append,List.foldl_append]
    change advance (List.ofFn (bits (Fin.last steps)),
      (List.ofFn (fun i => List.ofFn ((Fin.init bits) i))).foldl
        (fun data bits => advance (bits,data)) (((marginCode R,marginCode P),gridNatCode a),d)) = _
    rw [ih (Fin.init bits)]
    exact advance_code R P _ _

end
end ContingencyTables.DensePrograms

end OAI
