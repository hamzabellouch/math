import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumDistributedInput

namespace OAI

/-! Exact three-CNOT transfers for a circuit whose active wires move through a grid. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical

def qmaWirePermutation {n : ℕ} (f : SourceSpinBasis n → SourceSpinBasis n) :
    Matrix (SourceSpinBasis n) (SourceSpinBasis n) ℂ := fun s t => if s = f t then 1 else 0

theorem qmaWirePermutation_mul {n : ℕ} (f g : SourceSpinBasis n → SourceSpinBasis n) :
    qmaWirePermutation f*qmaWirePermutation g = qmaWirePermutation (f ∘ g) := by
  ext s t
  simp only [qmaWirePermutation,Matrix.mul_apply,mul_ite,mul_zero]
  rw [Finset.sum_eq_single (g t)]
  · simp
  · intro b _ hb
    simp [hb]
  · simp

theorem qmaControlledNot_swap (work : ℕ) (i j : Fin (work+1)) (hij : i ≠ j)
    (s : SourceSpinBasis (work+1)) :
    qmaControlledNot work i j (qmaControlledNot work j i (qmaControlledNot work i j s)) =
      s ∘ Equiv.swap i j := by
  funext k
  by_cases hki : k = i
  · subst k
    generalize hi : s i = a
    generalize hj : s j = b
    fin_cases a <;> fin_cases b <;>
      simp [qmaControlledNot,hij,hi,hj]
  by_cases hkj : k = j
  · subst k
    generalize hi : s i = a
    generalize hj : s j = b
    fin_cases a <;> fin_cases b <;>
      simp [qmaControlledNot,hij,Ne.symm hij,hi,hj]
  · simp [qmaControlledNot,hki,hkj,Equiv.swap_apply_def]

def qmaWireSwapGates {work : ℕ} (i j : Fin (work+1)) : List QMAGate :=
  [.controlledNot i.val j.val,.controlledNot j.val i.val,.controlledNot i.val j.val]

theorem qmaWireSwapGates_wellFormed {work : ℕ} (i j : Fin (work+1)) (hij : i ≠ j) :
    ∀ g ∈ qmaWireSwapGates i j, g.WellFormed (work+1) := by
  intro g hg
  have hval : i.val ≠ j.val := fun h => hij (Fin.ext h)
  simp only [qmaWireSwapGates,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact ⟨i.isLt,j.isLt,hval⟩
  · exact ⟨j.isLt,i.isLt,hval.symm⟩
  · exact ⟨i.isLt,j.isLt,hval⟩

theorem qmaQubit_fin {work : ℕ} (i : Fin (work+1)) : qmaQubit work i.val = i := by
  apply Fin.ext
  exact Nat.mod_eq_of_lt i.isLt

theorem qmaGateMatrix_cnot_fin {work : ℕ} (i j : Fin (work+1)) :
    qmaGateMatrix work (.controlledNot i.val j.val) = qmaWirePermutation (qmaControlledNot work i j) := by
  rw [qmaGateMatrix,qmaQubit_fin,qmaQubit_fin]
  rfl

theorem qmaWireSwap_matrix {work : ℕ} (i j : Fin (work+1)) (hij : i ≠ j) :
    qmaCircuitMatrix ⟨work,0,qmaWireSwapGates i j⟩ =
      qmaWirePermutation (fun s => s ∘ Equiv.swap i j) := by
  simp only [qmaCircuitMatrix,qmaWireSwapGates,List.foldl_cons,List.foldl_nil,
    qmaGateMatrix_cnot_fin,mul_one]
  rw [qmaWirePermutation_mul,qmaWirePermutation_mul]
  congr 1
  funext s
  exact qmaControlledNot_swap work i j hij s

end ContinuumCoulomb

end

end OAI
