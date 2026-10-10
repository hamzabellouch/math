import Mathlib
import OAI.Analysis.MatrixSigning.Machines.SchurReadStage

namespace OAI

section

namespace KS.W17.PivotRowRead
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators KS.W07
open KS.W07.SchurReadStage

def program : Program 32 := compose
  (compose (copyProgram 28 0 (by decide) (by decide) (by decide))
    (copyProgram 26 2 (by decide) (by decide) (by decide))) reader

theorem full_spec {n : ℕ} (M : DenseRatMatrix (n+1)) (b : ℕ)
    (hnum : ∀ i j, (DenseRatMatrix.decode M i j).num.natAbs ≤ 2^b)
    (hden : ∀ i j, (DenseRatMatrix.decode M i j).den ≤ 2^b)
    (j : Fin (n+1)) (before : Fin 32 → List Bool) (hw : WorkClear before)
    (hm : before 31 = KS.W08.denseMatrixTape M)
    (hd : before 26 = Computability.encodeNat (n+1))
    (hj : before 28 = Computability.encodeNat j.val) :
    RunSpec program before (Function.update before 0 (KS.W01.encodeRat (DenseRatMatrix.decode M 0 j)))
      ((2*(Computability.encodeNat j.val).length+2) +
        (2*(Computability.encodeNat (n+1)).length+2) + 1024*(n+2)^2*(b+1)) := by
  have h0 := hw 0 (by decide)
  have h1 := hw 1 (by decide)
  have h2 := hw 2 (by decide)
  have h16 := hw 16 (by decide)
  have hc := copy_spec (28 : Fin 32) 0 (by decide) (by decide) (by decide) before h0 h16
  rw [hj] at hc
  have hd2 := copy_spec (26 : Fin 32) 2 (by decide) (by decide) (by decide)
    (Function.update before 0 (Computability.encodeNat j.val))
    (by simpa using h2) (by simpa using h16)
  simp only [Function.update_of_ne (show (26 : Fin 32) ≠ 0 by decide), hd] at hd2
  have hr := reader_spec M b hnum hden 0 j before hw hm
  have he : Function.update (Function.update before 0 (Computability.encodeNat j.val)) 2
      (Computability.encodeNat (n+1)) =
      readPrepared before (Computability.encodeNat j.val) (Computability.encodeNat (0 : ℕ))
        (Computability.encodeNat (n+1)) := by
    funext k
    fin_cases k <;> simp [readPrepared, h1, Computability.encodeNat, Computability.encodeNum, Function.update]
  rw [he] at hd2
  exact (hc.compose hd2).compose hr

end KS.W17.PivotRowRead

end

end OAI
