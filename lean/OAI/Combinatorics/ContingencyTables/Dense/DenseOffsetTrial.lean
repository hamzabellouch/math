import OAI.Combinatorics.ContingencyTables.Dense.DenseOffsetSemantics
import OAI.Combinatorics.ContingencyTables.Dense.DenseTrial

namespace OAI

/-! # The quotient program computes the full free part of a dense trial -/

namespace ContingencyTables.DensePrograms
open GridBoundary ProfilePrograms
open scoped Classical

noncomputable section

private lemma fin_transport_val {α : Sort*} {n : α → ℕ} {a b : α}
    (h : a=b) (x : Fin (n a)) : ((h ▸ x) : Fin (n b)).val=x.val := by
  cases h
  rfl

lemma drawOffsetWords_value {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] {q : ℕ}
    (e : I×J ≃ Fin q) (w : I×J → ℕ) (hw : ∀ p,0<w p) (h d : ℕ)
    (bits : OffsetWords e w h d) (p : I×J) :
    (drawOffsetWords e w hw h d bits p).val=
      scaledWordValue (w p,List.ofFn (bits (e p))) := by
  rw [scaledWordValue_ofFn _ _ (hw p)]
  simp only [drawOffsetWords,offsetCoordinateEquiv,Equiv.piCongrLeft'_symm_apply,
    fin_transport_val,FairBits.scaledBitInteger,FairBits.scaledInteger]
  congr 2
  exact congrArg w (e.symm_apply_apply p)

theorem offsetMatrix_trialFree {m n d : ℕ}
    (R : Option (Fin m) → ℕ) (P : Option (Fin n) → ℕ)
    (hw : ∀ p,0 < integerWidth R P d p) (h : ℕ)
    (a : Grid (I := Fin (m*n)) (4*d^8))
    (bits : OffsetWords finProdFinEquiv (integerWidth R P d) h d) :
    offsetMatrix (exponentDataCode R P d
      (fun i j => (corner a (finProdFinEquiv (i,j))).toNat),
        List.ofFn (fun i => List.ofFn (bits i)))=
      matrixCode (fun i j => trialFree R P d finProdFinEquiv
        (a,drawOffsetWords finProdFinEquiv (integerWidth R P d) hw h d bits) (i,j)) := by
  rw [offsetMatrix_code]
  apply congrArg matrixCode
  funext i j
  rw [trialFree,trialBoxEquiv_val,drawOffsetWords_value]
  simp only [cornerFree]
  exact Nat.add_comm _ _

end
end ContingencyTables.DensePrograms

end OAI
