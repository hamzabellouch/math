import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumSwapConjugation

namespace OAI

/-! A linear-size adjacent-CNOT program for one arbitrarily separated CNOT. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped Classical

def qmaAdjacentCnot (work : ℕ) : (a d : ℕ) → a+d+1 < work+1 → Bool → List QMAGate
  | a,0,_,forward => [qmaOrderedCnot a (a+1) forward]
  | a,d+1,h,forward =>
      qmaWireSwapGates (⟨a,by omega⟩ : Fin (work+1)) ⟨a+1,by omega⟩ ++
      qmaAdjacentCnot work (a+1) d (by omega) forward ++
      qmaWireSwapGates (⟨a,by omega⟩ : Fin (work+1)) ⟨a+1,by omega⟩

theorem qmaAdjacentCnot_length (work a d : ℕ) (h : a+d+1 < work+1) (b : Bool) :
    (qmaAdjacentCnot work a d h b).length = 6*d+1 := by
  induction d generalizing a with
  | zero => rfl
  | succ d ih => simp [qmaAdjacentCnot,qmaWireSwapGates,ih]; omega

theorem qmaAdjacentCnot_matrix (work a d : ℕ) (h : a+d+1 < work+1) (b : Bool) :
    qmaGateProduct work (qmaAdjacentCnot work a d h b) =
      qmaGateMatrix work (qmaOrderedCnot a (a+d+1) b) := by
  induction d generalizing a with
  | zero => exact qmaGateProduct_singleton _ _
  | succ d ih =>
    let i : Fin (work+1) := ⟨a,by omega⟩
    let j : Fin (work+1) := ⟨a+1,by omega⟩
    let k : Fin (work+1) := ⟨a+(d+1)+1,h⟩
    have hij : i ≠ j := by intro he; have := congrArg Fin.val he; simp [i,j] at this
    have hki : k ≠ i := by intro he; have := congrArg Fin.val he; dsimp [k,i] at this; omega
    have hkj : k ≠ j := by intro he; have := congrArg Fin.val he; dsimp [k,j] at this; omega
    simp only [qmaAdjacentCnot,qmaGateProduct_append,ih]
    rw [←mul_assoc]
    have he : a+1+d+1 = k.val := by dsimp [k]; omega
    rw [he]
    exact (qmaWireSwap_conjugate i j hij (qmaOrderedCnot j.val k.val b)).trans
      (congrArg (qmaGateMatrix work) (qmaSwap_relabels_ordered i j k hki hkj b))

end ContinuumCoulomb

end

end OAI
