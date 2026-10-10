import Mathlib
import OAI.Analysis.MatrixSigning.Arithmetic.CleanRationalCompare
import OAI.Analysis.MatrixSigning.Arithmetic.SparseScalarNodes

namespace OAI

namespace KS.W19.SparseCoefficientStage
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators
open KS.W15.ComplexMachine

def ports : Fin 28 ↪ Fin 35 :=
  ⟨![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,19,20,21,22,24,25,17,23,27,28,26,18], by decide⟩
def arithmetic : Program 35 := liftPorts SparseScalarNodes.program ports

def put (s : Fin 35 → List Bool) (p : Fin 35) (q : ℚ) : Fin 35 → List Bool :=
  Function.update s p (KS.W01.encodeRat q)
def after (s : Fin 35 → List Bool) (a b : ℚ) : Fin 35 → List Bool :=
  put (put (put (put (put (put s 24 1) 25 2) 21 (a+1)) 22 (2*b)) 27 (-(a+1)))
    28 (SparseScalarNodes.coefficient a b)

theorem arithmetic_spec (s : Fin 35 → List Bool) (a b : ℚ)
    (hc : ∀ i, i.val < 16 → s i = [])
    (ha : s 19 = KS.W01.encodeRat a) (hb : s 20 = KS.W01.encodeRat b)
    (h21 : s 21 = []) (h22 : s 22 = []) (h24 : s 24 = []) (h25 : s 25 = [])
    (h27 : s 27 = []) (h28 : s 28 = []) :
    RunSpec arithmetic s (after s a b) (SparseScalarNodes.ticks a b) := by
  let small := fun i => s (ports i)
  have hcore : CoreEmpty small := by
    intro i
    apply hc
    fin_cases i <;> decide
  have h := SparseScalarNodes.coefficient_spec small a b hcore ha hb h21 h22 h24 h25 h27 h28
  apply KS.W01.FixedPortRunSpec.lift_runSpec _ ports _ _ _ _ _ h
  · intro i; rfl
  · intro i; fin_cases i <;> simp [after,put,SparseScalarNodes.after,SparseScalarNodes.put,small,ports]
  · intro i hi
    have h24' := hi 20
    have h25' := hi 21
    have h21' := hi 18
    have h22' := hi 19
    have h27' := hi 24
    have h28' := hi 25
    change i ≠ 24 at h24'
    change i ≠ 25 at h25'
    change i ≠ 21 at h21'
    change i ≠ 22 at h22'
    change i ≠ 27 at h27'
    change i ≠ 28 at h28'
    simp [after,put,Function.update_of_ne,h24',h25',h21',h22',h27',h28']

def cleanupPorts : List (Fin 35) := [19,20,21,22,24,25,27,33]
def cleanup : Program 35 := KS.W04.CleanRationalCompare.clearListProgram 28 cleanupPorts
def program : Program 35 := compose arithmetic cleanup

def ticks (s : Fin 35 → List Bool) (a b : ℚ) : ℕ := SparseScalarNodes.ticks a b +
  KS.W04.CleanRationalCompare.clearListTicks cleanupPorts (after s a b)

def result (s : Fin 35 → List Bool) (a b : ℚ) : Fin 35 → List Bool :=
  Function.update (KS.W04.CleanRationalCompare.clearListState cleanupPorts s) 28
    (KS.W01.encodeRat (SparseScalarNodes.coefficient a b))

theorem full_spec (s : Fin 35 → List Bool) (a b : ℚ)
    (hc : ∀ i, i.val < 16 → s i = [])
    (ha : s 19 = KS.W01.encodeRat a) (hb : s 20 = KS.W01.encodeRat b)
    (h21 : s 21 = []) (h22 : s 22 = []) (h24 : s 24 = []) (h25 : s 25 = [])
    (h27 : s 27 = []) (h28 : s 28 = []) :
    RunSpec program s (result s a b) (ticks s a b) := by
  have h := arithmetic_spec s a b hc ha hb h21 h22 h24 h25 h27 h28
  have hclean := KS.W04.CleanRationalCompare.clearList_spec (28 : Fin 35) cleanupPorts (after s a b)
  have he : KS.W04.CleanRationalCompare.clearListState cleanupPorts (after s a b) = result s a b := by
    funext i
    fin_cases i <;> simp [result,cleanupPorts,after,put,
      KS.W04.CleanRationalCompare.clearListState,KS.W04.CleanRationalCompare.clearState]
  rw [he] at hclean
  exact h.compose hclean

end KS.W19.SparseCoefficientStage

end OAI
