import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes0
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes1
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes2
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes3
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes5
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes10

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw544 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 1, -1], ![3, -3, 0]]

def raw544step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]

theorem canonical544 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw544 = injectiveMoment H node93 := by
  calc
    injectiveMoment H raw544 = injectiveMoment H raw544step0 := by
      have heq : raw544step0 = (fun i j => raw544 (permutation11 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw544 permutation11 permutation3
    _ = injectiveMoment H node93 := by rfl

def raw545 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -3, 2], ![1, 0, -1], ![1, 1, -2]]

theorem canonical545 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw545 = injectiveMoment H node350 := by
  rfl

def raw546 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -3, 2], ![1, 1, -2], ![1, 0, -1]]

def raw546step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -3, 2], ![1, 0, -1], ![1, 1, -2]]

theorem canonical546 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw546 = injectiveMoment H node350 := by
  calc
    injectiveMoment H raw546 = injectiveMoment H raw546step0 := by
      have heq : raw546step0 = (fun i j => raw546 (permutation34 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw546 permutation34 permutation3
    _ = injectiveMoment H node350 := by rfl

def raw547 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -3, 2], ![2, 1, -3]]

theorem canonical547 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw547 = injectiveMoment H node96 := by
  rfl

def raw548 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]

theorem canonical548 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw548 = injectiveMoment H node351 := by
  rfl

def raw549 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]

def raw549step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]

def raw549step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, -1, 1], ![0, 3, -3], ![2, -1, -1]]

theorem canonical549 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw549 = injectiveMoment H node651 := by
  calc
    injectiveMoment H raw549 = injectiveMoment H raw549step0 := by
      have heq : raw549step0 = -raw549 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw549).symm
    injectiveMoment H raw549step0 = injectiveMoment H raw549step1 := by
      have heq : raw549step1 = (fun i j => raw549step0 (permutation72 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw549step0 permutation72 permutation5
    _ = injectiveMoment H node651 := by rfl

def raw550 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]

def raw550step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-1, 2, -1], ![-2, 0, 2]]

def raw550step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 3, -3], ![2, -1, -1]]

theorem canonical550 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw550 = injectiveMoment H node198 := by
  calc
    injectiveMoment H raw550 = injectiveMoment H raw550step0 := by
      have heq : raw550step0 = -raw550 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw550).symm
    injectiveMoment H raw550step0 = injectiveMoment H raw550step1 := by
      have heq : raw550step1 = (fun i j => raw550step0 (permutation19 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw550step0 permutation19 permutation5
    _ = injectiveMoment H node198 := by rfl

def raw551 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]

def raw551step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]

def raw551step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0]]

theorem canonical551 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw551 = injectiveMoment H node663 := by
  calc
    injectiveMoment H raw551 = injectiveMoment H raw551step0 := by
      have heq : raw551step0 = -raw551 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw551).symm
    injectiveMoment H raw551step0 = injectiveMoment H raw551step1 := by
      have heq : raw551step1 = (fun i j => raw551step0 (permutation74 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw551step0 permutation74 permutation5
    _ = injectiveMoment H node663 := by rfl

def raw552 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]

def raw552step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]

def raw552step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![1, -2, 1], ![1, -1, 0]]

theorem canonical552 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw552 = injectiveMoment H node215 := by
  calc
    injectiveMoment H raw552 = injectiveMoment H raw552step0 := by
      have heq : raw552step0 = -raw552 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw552).symm
    injectiveMoment H raw552step0 = injectiveMoment H raw552step1 := by
      have heq : raw552step1 = (fun i j => raw552step0 (permutation16 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw552step0 permutation16 permutation5
    _ = injectiveMoment H node215 := by rfl

def raw553 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]

def raw553step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 3, -3], ![2, -2, 0]]

theorem canonical553 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw553 = injectiveMoment H node204 := by
  calc
    injectiveMoment H raw553 = injectiveMoment H raw553step0 := by
      have heq : raw553step0 = (fun i j => raw553 (permutation31 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw553 permutation31 permutation6
    _ = injectiveMoment H node204 := by rfl

def raw554 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 1, -2], ![2, -3, 1]]

theorem canonical554 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw554 = injectiveMoment H node97 := by
  rfl

def raw555 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![2, -3, 1], ![1, 1, -2]]

def raw555step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 1, -2], ![2, -3, 1]]

theorem canonical555 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw555 = injectiveMoment H node97 := by
  calc
    injectiveMoment H raw555 = injectiveMoment H raw555step0 := by
      have heq : raw555step0 = (fun i j => raw555 (permutation10 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw555 permutation10 permutation3
    _ = injectiveMoment H node97 := by rfl

def raw556 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![3, -2, -1]]

def raw556step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 3, -3], ![2, -2, 0]]

theorem canonical556 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw556 = injectiveMoment H node37 := by
  calc
    injectiveMoment H raw556 = injectiveMoment H raw556step0 := by
      have heq : raw556step0 = (fun i j => raw556 (permutation7 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw556 permutation7 permutation6
    _ = injectiveMoment H node37 := by rfl

def raw557 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1]]

def raw557step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -3, 3], ![-1, 3, -2], ![-1, 0, 1], ![-1, 0, 1]]

def raw557step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 3, -3], ![3, -1, -2]]

theorem canonical557 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw557 = injectiveMoment H node333 := by
  calc
    injectiveMoment H raw557 = injectiveMoment H raw557step0 := by
      have heq : raw557step0 = -raw557 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw557).symm
    injectiveMoment H raw557step0 = injectiveMoment H raw557step1 := by
      have heq : raw557step1 = (fun i j => raw557step0 (permutation72 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw557step0 permutation72 permutation5
    _ = injectiveMoment H node333 := by rfl

def raw558 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![1, -3, 2], ![2, 0, -2]]

def raw558step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -3, 3], ![-1, 3, -2], ![-2, 0, 2]]

def raw558step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 3, -3], ![3, -1, -2]]

theorem canonical558 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw558 = injectiveMoment H node91 := by
  calc
    injectiveMoment H raw558 = injectiveMoment H raw558step0 := by
      have heq : raw558step0 = -raw558 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw558).symm
    injectiveMoment H raw558step0 = injectiveMoment H raw558step1 := by
      have heq : raw558step1 = (fun i j => raw558step0 (permutation19 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw558step0 permutation19 permutation5
    _ = injectiveMoment H node91 := by rfl

def raw559 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]

def raw559step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -3, 3], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]

def raw559step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![2, -1, -1]]

theorem canonical559 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw559 = injectiveMoment H node339 := by
  calc
    injectiveMoment H raw559 = injectiveMoment H raw559step0 := by
      have heq : raw559step0 = -raw559 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw559).symm
    injectiveMoment H raw559step0 = injectiveMoment H raw559step1 := by
      have heq : raw559step1 = (fun i j => raw559step0 (permutation75 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw559step0 permutation75 permutation5
    _ = injectiveMoment H node339 := by rfl

def raw560 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![1, -2, 1], ![2, -1, -1]]

theorem canonical560 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw560 = injectiveMoment H node98 := by
  rfl

def raw561 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![1, -1, 0], ![1, -2, 1], ![1, 0, -1]]

def raw561step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -3, 3], ![-1, 1, 0], ![-1, 2, -1], ![-1, 0, 1]]

def raw561step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![2, -1, -1]]

theorem canonical561 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw561 = injectiveMoment H node339 := by
  calc
    injectiveMoment H raw561 = injectiveMoment H raw561step0 := by
      have heq : raw561step0 = -raw561 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw561).symm
    injectiveMoment H raw561step0 = injectiveMoment H raw561step1 := by
      have heq : raw561step1 = (fun i j => raw561step0 (permutation74 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw561step0 permutation74 permutation5
    _ = injectiveMoment H node339 := by rfl

def raw562 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]

def raw562step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]

theorem canonical562 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw562 = injectiveMoment H node341 := by
  calc
    injectiveMoment H raw562 = injectiveMoment H raw562step0 := by
      have heq : raw562step0 = (fun i j => raw562 (permutation65 i) (permutation7 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw562 permutation65 permutation7
    _ = injectiveMoment H node341 := by rfl

def raw563 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![1, -1, 0], ![2, -2, 0]]

def raw563step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]

theorem canonical563 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw563 = injectiveMoment H node93 := by
  calc
    injectiveMoment H raw563 = injectiveMoment H raw563step0 := by
      have heq : raw563step0 = (fun i j => raw563 (permutation18 i) (permutation7 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw563 permutation18 permutation7
    _ = injectiveMoment H node93 := by rfl

def raw564 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![1, 0, -1], ![2, -3, 1]]

def raw564step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -3, 3], ![-1, 0, 1], ![-2, 3, -1]]

def raw564step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 3, -3], ![3, -2, -1]]

theorem canonical564 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw564 = injectiveMoment H node92 := by
  calc
    injectiveMoment H raw564 = injectiveMoment H raw564step0 := by
      have heq : raw564step0 = -raw564 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw564).symm
    injectiveMoment H raw564step0 = injectiveMoment H raw564step1 := by
      have heq : raw564step1 = (fun i j => raw564step0 (permutation17 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw564step0 permutation17 permutation5
    _ = injectiveMoment H node92 := by rfl

def raw565 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![3, -3, 0]]

theorem canonical565 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw565 = injectiveMoment H node19 := by
  rfl

def raw566 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -3, 2], ![0, 2, -2], ![1, 0, -1], ![1, 1, -2]]

def raw566step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -3, 2], ![1, 0, -1], ![1, 1, -2]]

theorem canonical566 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw566 = injectiveMoment H node350 := by
  calc
    injectiveMoment H raw566 = injectiveMoment H raw566step0 := by
      have heq : raw566step0 = (fun i j => raw566 (permutation39 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw566 permutation39 permutation3
    _ = injectiveMoment H node350 := by rfl

def raw567 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -3, 2], ![0, 2, -2], ![2, 1, -3]]

def raw567step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -3, 2], ![2, 1, -3]]

theorem canonical567 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw567 = injectiveMoment H node96 := by
  calc
    injectiveMoment H raw567 = injectiveMoment H raw567step0 := by
      have heq : raw567step0 = (fun i j => raw567 (permutation11 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw567 permutation11 permutation3
    _ = injectiveMoment H node96 := by rfl

def raw568 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -3, 2], ![0, 3, -3], ![1, 0, -1], ![1, 0, -1]]

def raw568step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![-1, 3, -2], ![0, -3, 3], ![-1, 0, 1], ![-1, 0, 1]]

def raw568step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 3, -3], ![3, -1, -2]]

theorem canonical568 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw568 = injectiveMoment H node333 := by
  calc
    injectiveMoment H raw568 = injectiveMoment H raw568step0 := by
      have heq : raw568step0 = -raw568 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw568).symm
    injectiveMoment H raw568step0 = injectiveMoment H raw568step1 := by
      have heq : raw568step1 = (fun i j => raw568step0 (permutation96 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw568step0 permutation96 permutation5
    _ = injectiveMoment H node333 := by rfl

def raw569 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -3, 2], ![0, 3, -3], ![2, 0, -2]]

def raw569step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![-1, 3, -2], ![0, -3, 3], ![-2, 0, 2]]

def raw569step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 3, -3], ![3, -1, -2]]

theorem canonical569 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw569 = injectiveMoment H node91 := by
  calc
    injectiveMoment H raw569 = injectiveMoment H raw569step0 := by
      have heq : raw569step0 = -raw569 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw569).symm
    injectiveMoment H raw569step0 = injectiveMoment H raw569step1 := by
      have heq : raw569step1 = (fun i j => raw569step0 (permutation25 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw569step0 permutation25 permutation5
    _ = injectiveMoment H node91 := by rfl

def raw570 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -3, 2], ![1, 0, -1], ![1, 3, -4]]

def raw570step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![-1, 3, -2], ![-1, 0, 1], ![-1, -3, 4]]

def raw570step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 3, -3], ![3, -1, -2]]

theorem canonical570 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw570 = injectiveMoment H node79 := by
  calc
    injectiveMoment H raw570 = injectiveMoment H raw570step0 := by
      have heq : raw570step0 = -raw570 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw570).symm
    injectiveMoment H raw570step0 = injectiveMoment H raw570step1 := by
      have heq : raw570step1 = (fun i j => raw570step0 (permutation31 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw570step0 permutation31 permutation5
    _ = injectiveMoment H node79 := by rfl

def raw571 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -3, 2], ![1, 1, -2], ![1, 2, -3]]

theorem canonical571 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw571 = injectiveMoment H node100 := by
  rfl

def raw572 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -3, 2], ![2, 3, -5]]

def raw572step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 0, -3], ![-1, 3, -2], ![-2, -3, 5]]

def raw572step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 3, -3], ![3, -1, -2]]

theorem canonical572 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw572 = injectiveMoment H node17 := by
  calc
    injectiveMoment H raw572 = injectiveMoment H raw572step0 := by
      have heq : raw572step0 = -raw572 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw572).symm
    injectiveMoment H raw572step0 = injectiveMoment H raw572step1 := by
      have heq : raw572step1 = (fun i j => raw572step0 (permutation7 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw572step0 permutation7 permutation5
    _ = injectiveMoment H node17 := by rfl

def raw573 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -2, 1], ![0, 3, -3], ![2, -1, -1]]

def raw573step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![1, -2, 1], ![2, -1, -1]]

theorem canonical573 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw573 = injectiveMoment H node98 := by
  calc
    injectiveMoment H raw573 = injectiveMoment H raw573step0 := by
      have heq : raw573step0 = (fun i j => raw573 (permutation11 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw573 permutation11 permutation3
    _ = injectiveMoment H node98 := by rfl

def raw574 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -2, 1], ![1, -1, 0], ![1, 3, -4]]

def raw574step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![-1, 2, -1], ![-1, 1, 0], ![-1, -3, 4]]

def raw574step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, -1, 0], ![2, -1, -1]]

theorem canonical574 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw574 = injectiveMoment H node87 := by
  calc
    injectiveMoment H raw574 = injectiveMoment H raw574step0 := by
      have heq : raw574step0 = -raw574 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw574).symm
    injectiveMoment H raw574step0 = injectiveMoment H raw574step1 := by
      have heq : raw574step1 = (fun i j => raw574step0 (permutation28 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw574step0 permutation28 permutation5
    _ = injectiveMoment H node87 := by rfl

def raw575 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]

def raw575step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![-1, 2, -1], ![-1, 0, 1], ![-1, -2, 3]]

def raw575step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 3, -3], ![2, -1, -1]]

theorem canonical575 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw575 = injectiveMoment H node170 := by
  calc
    injectiveMoment H raw575 = injectiveMoment H raw575step0 := by
      have heq : raw575step0 = -raw575 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw575).symm
    injectiveMoment H raw575step0 = injectiveMoment H raw575step1 := by
      have heq : raw575step1 = (fun i j => raw575step0 (permutation31 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw575step0 permutation31 permutation5
    _ = injectiveMoment H node170 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
