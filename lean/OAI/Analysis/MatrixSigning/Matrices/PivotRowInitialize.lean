import Mathlib
import OAI.Analysis.MatrixSigning.Matrices.PivotRowLoop
import OAI.Analysis.MatrixSigning.Machines.SchurDimension

namespace OAI

section

namespace KS.W17.PivotRowLoop
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators KS.W07

def initial {n : ℕ} (M : DenseRatMatrix (n+1)) : Fin 32 → List Bool := state M 0 0 false

def «initialize» : Program 32 := compose
  (compose (compose SchurDimension.predecessor (SchurDimension.unaryProgram true))
    (KS.W04.BinaryStackMoves.clearProgram 30)) (SchurCounters.pushProgram 28 true)

def initializeTicks (n : ℕ) : ℕ :=
  SchurDimension.predecessorTicks n + (4*n+6*(Computability.encodeNat n).length+4) +
    ((Computability.encodeNat n).length+1) + 1

theorem initialize_spec {n : ℕ} (M : DenseRatMatrix (n+1)) :
    RunSpec «initialize» (initial M) (state M 1 n false) (initializeTicks n) := by
  let s := initial M
  let t := Function.update s 30 (Computability.encodeNat n)
  let u := Function.update t 25 (List.replicate n true)
  have h1 := SchurDimension.predecessor_spec s n rfl rfl rfl rfl rfl rfl
  have h2 := SchurDimension.unary_spec true t n rfl rfl rfl rfl rfl
  have h3 := KS.W04.CleanRationalCompare.clear_spec (30 : Fin 32) u
  have he : KS.W04.CleanRationalCompare.clearState 30 u = state M 0 n false := by
    funext j; fin_cases j <;> simp [KS.W04.CleanRationalCompare.clearState,u,t,s,initial,state,Function.update]
  rw [he] at h3
  have h4 := SchurCounters.push_spec (28 : Fin 32) true (state M 0 n false)
  have he4 : Function.update (state M 0 n false) 28 (true :: state M 0 n false 28) =
      state M 1 n false := by
    funext j; fin_cases j <;> simp [state,Function.update,Computability.encodeNat,Computability.encodeNum,Computability.encodePosNum]
  rw [he4] at h4
  exact ((h1.compose h2).compose h3).compose h4

def offDiagonalProgram : Program 32 := compose «initialize» program

theorem offDiagonal_spec {n : ℕ} (M : DenseRatMatrix (n+1)) (b : ℕ)
    (hnum : ∀ i j, (DenseRatMatrix.decode M i j).num.natAbs ≤ 2^b)
    (hden : ∀ i j, (DenseRatMatrix.decode M i j).den ≤ 2^b) :
    RunSpec offDiagonalProgram (initial M)
      (state M (outcome M 1 n).index (outcome M 1 n).remaining (outcome M 1 n).found)
      (initializeTicks n + ticks M b 1 n) := by
  have h : RunSpec program (state M 1 n false)
      (state M (outcome M 1 n).index (outcome M 1 n).remaining (outcome M 1 n).found)
      (ticks M b 1 n) := by
    intro bits hb
    exact run_scan M b 1 n (by omega) hnum hden bits hb.ge
  exact (initialize_spec M).compose h

end KS.W17.PivotRowLoop

end

end OAI
