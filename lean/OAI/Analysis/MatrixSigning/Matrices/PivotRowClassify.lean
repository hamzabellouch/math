import Mathlib
import OAI.Analysis.MatrixSigning.Matrices.PivotRowRead
import OAI.Analysis.MatrixSigning.Arithmetic.RationalSignClassifier

namespace OAI

section

namespace KS.W17.PivotRowClassify
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators KS.W07
open KS.W07.SchurReadStage

def classifierPorts : Fin 13 ↪ Fin 32 := Fin.castLEEmb (by decide)
def classifier : Program 32 := liftPorts KS.W06.RationalSignClassifier.program classifierPorts

def program : Program 32 := compose (compose PivotRowRead.program classifier)
  (KS.W07.WireAppend.program 9 29 16)

def ticks {n : ℕ} (M : DenseRatMatrix (n+1)) (b : ℕ) (j : Fin (n+1)) : ℕ :=
  ((2*(Computability.encodeNat j.val).length+2) +
    (2*(Computability.encodeNat (n+1)).length+2) + 1024*(n+2)^2*(b+1)) +
  256*(KS.W01.ratLength (DenseRatMatrix.decode M 0 j)+1) +
  (2*(KS.W06.RationalSignClassifier.outputCode (DenseRatMatrix.decode M 0 j)).length+2)

theorem full_spec {n : ℕ} (M : DenseRatMatrix (n+1)) (b : ℕ)
    (hnum : ∀ i j, (DenseRatMatrix.decode M i j).num.natAbs ≤ 2^b)
    (hden : ∀ i j, (DenseRatMatrix.decode M i j).den ≤ 2^b)
    (j : Fin (n+1)) (before : Fin 32 → List Bool) (hw : WorkClear before)
    (hm : before 31 = KS.W08.denseMatrixTape M)
    (hd : before 26 = Computability.encodeNat (n+1))
    (hj : before 28 = Computability.encodeNat j.val) (hf : before 29 = []) :
    RunSpec program before
      (Function.update before 29 (KS.W06.RationalSignClassifier.outputCode (DenseRatMatrix.decode M 0 j)))
      (ticks M b j) := by
  let q := DenseRatMatrix.decode M 0 j
  let code := KS.W06.RationalSignClassifier.outputCode q
  have hread := PivotRowRead.full_spec M b hnum hden j before hw hm hd hj
  have hclass : RunSpec classifier (Function.update before 0 (KS.W01.encodeRat q))
      (Function.update before 9 code) (256*(KS.W01.ratLength q+1)) := by
    apply KS.W01.FixedPortRunSpec.lift_runSpec
      KS.W06.RationalSignClassifier.program classifierPorts
      (KS.W06.SingleRationalParser.inputState (KS.W01.encodeRat q))
      (KS.W06.RationalSignClassifier.outputState q) _ _ _
      (KS.W06.RationalSignClassifier.canonical_spec q)
    · intro i
      have hi : before (classifierPorts i) = [] := hw _ (by have := i.isLt; simp [classifierPorts]; omega)
      fin_cases i <;> simp_all [classifierPorts, KS.W06.SingleRationalParser.inputState, Function.update]
    · intro i
      have hi : before (classifierPorts i) = [] := hw _ (by have := i.isLt; simp [classifierPorts]; omega)
      fin_cases i <;> simp_all [classifierPorts, KS.W06.RationalSignClassifier.outputState,
        Function.update, code]
    · intro i hi
      have h0 : i ≠ 0 := by simpa [classifierPorts] using hi 0
      have h9 : i ≠ 9 := by simpa [classifierPorts] using hi 9
      simp [Function.update, h0, h9]
  have hmoving := KS.W07.WireAppend.spec (9 : Fin 32) 29 16 (by decide) (by decide) (by decide)
    (Function.update before 9 code) (by simpa using hw 16 (by decide))
  have he : KS.W07.WireAppend.after 9 29 (Function.update before 9 code) =
      Function.update before 29 code := by
    have h9 := hw 9 (by decide)
    funext i; fin_cases i <;> simp [KS.W07.WireAppend.after, Function.update, hf, h9]
  rw [he] at hmoving
  exact (hread.compose hclass).compose hmoving

end KS.W17.PivotRowClassify

end

end OAI
