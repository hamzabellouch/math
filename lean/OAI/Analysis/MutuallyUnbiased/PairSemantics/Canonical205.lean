import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes2
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes3
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes4
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes17
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes21
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes31
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes40
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes44

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw6560 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 2, 2, -4], ![1, -1, -2, 2]]

def raw6560step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 2, -1], ![0, 2, -2], ![2, -4, 2]]

def raw6560step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![1, -2, 1], ![0, -2, 2], ![-2, 4, -2]]

def raw6560step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![1, -1, 0], ![1, 1, -2]]

theorem canonical6560 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6560 = injectiveMoment H node153 := by
  calc
    injectiveMoment H raw6560 = injectiveMoment H raw6560step0 := by
      have heq : raw6560step0 = raw6560.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6560).symm
    injectiveMoment H raw6560step0 = injectiveMoment H raw6560step1 := by
      have heq : raw6560step1 = -raw6560step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6560step0).symm
    injectiveMoment H raw6560step1 = injectiveMoment H raw6560step2 := by
      have heq : raw6560step2 = (fun i j => raw6560step1 (permutation31 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6560step1 permutation31 permutation4
    _ = injectiveMoment H node153 := by rfl

def raw6561 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![1, -1, -2, 2], ![0, 2, 2, -4]]

def raw6561step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, -2, 2], ![2, 2, -4]]

def raw6561step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -1, 0], ![1, 1, -2], ![0, 2, -2], ![-2, -2, 4]]

def raw6561step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![1, -1, 0], ![1, 1, -2]]

theorem canonical6561 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6561 = injectiveMoment H node153 := by
  calc
    injectiveMoment H raw6561 = injectiveMoment H raw6561step0 := by
      have heq : raw6561step0 = raw6561.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6561).symm
    injectiveMoment H raw6561step0 = injectiveMoment H raw6561step1 := by
      have heq : raw6561step1 = -raw6561step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6561step0).symm
    injectiveMoment H raw6561step1 = injectiveMoment H raw6561step2 := by
      have heq : raw6561step2 = (fun i j => raw6561step1 (permutation31 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6561step1 permutation31 permutation3
    _ = injectiveMoment H node153 := by rfl

def raw6562 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![1, -1, 1, -1], ![0, 2, -1, -1]]

def raw6562step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 1, -1], ![2, -1, -1]]

def raw6562step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -1, 0], ![1, 1, -2], ![0, -1, 1], ![-2, 1, 1]]

def raw6562step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]

theorem canonical6562 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6562 = injectiveMoment H node230 := by
  calc
    injectiveMoment H raw6562 = injectiveMoment H raw6562step0 := by
      have heq : raw6562step0 = raw6562.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6562).symm
    injectiveMoment H raw6562step0 = injectiveMoment H raw6562step1 := by
      have heq : raw6562step1 = -raw6562step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6562step0).symm
    injectiveMoment H raw6562step1 = injectiveMoment H raw6562step2 := by
      have heq : raw6562step2 = (fun i j => raw6562step1 (permutation31 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6562step1 permutation31 permutation3
    _ = injectiveMoment H node230 := by rfl

def raw6563 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![1, -1, 2, -2], ![0, 2, -2, 0]]

def raw6563step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 2, -2], ![2, -2, 0]]

def raw6563step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]

theorem canonical6563 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6563 = injectiveMoment H node203 := by
  calc
    injectiveMoment H raw6563 = injectiveMoment H raw6563step0 := by
      have heq : raw6563step0 = raw6563.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6563).symm
    injectiveMoment H raw6563step0 = injectiveMoment H raw6563step1 := by
      have heq : raw6563step1 = (fun i j => raw6563step0 (permutation22 i) (permutation7 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6563step0 permutation22 permutation7
    _ = injectiveMoment H node203 := by rfl

def raw6564 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![1, -1, 3, -3], ![0, 2, -3, 1]]

def raw6564step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 3, -3], ![2, -3, 1]]

def raw6564step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -1, 0], ![1, 1, -2], ![0, -3, 3], ![-2, 3, -1]]

def raw6564step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 3, -3], ![1, -2, 1], ![1, 0, -1]]

theorem canonical6564 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6564 = injectiveMoment H node187 := by
  calc
    injectiveMoment H raw6564 = injectiveMoment H raw6564step0 := by
      have heq : raw6564step0 = raw6564.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6564).symm
    injectiveMoment H raw6564step0 = injectiveMoment H raw6564step1 := by
      have heq : raw6564step1 = -raw6564step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6564step0).symm
    injectiveMoment H raw6564step1 = injectiveMoment H raw6564step2 := by
      have heq : raw6564step2 = (fun i j => raw6564step1 (permutation32 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6564step1 permutation32 permutation4
    _ = injectiveMoment H node187 := by rfl

def raw6565 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![1, 0, -3, 2], ![0, 1, 3, -4]]

def raw6565step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, -3, 3], ![2, 2, -4]]

def raw6565step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -1, 0], ![1, 0, -1], ![0, 3, -3], ![-2, -2, 4]]

def raw6565step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1]]

theorem canonical6565 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6565 = injectiveMoment H node155 := by
  calc
    injectiveMoment H raw6565 = injectiveMoment H raw6565step0 := by
      have heq : raw6565step0 = raw6565.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6565).symm
    injectiveMoment H raw6565step0 = injectiveMoment H raw6565step1 := by
      have heq : raw6565step1 = -raw6565step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6565step0).symm
    injectiveMoment H raw6565step1 = injectiveMoment H raw6565step2 := by
      have heq : raw6565step2 = (fun i j => raw6565step1 (permutation31 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6565step1 permutation31 permutation3
    _ = injectiveMoment H node155 := by rfl

def raw6566 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![1, 0, -2, 1], ![0, 1, 2, -3]]

def raw6566step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, -2, 2], ![2, 1, -3]]

def raw6566step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -1, 0], ![1, 0, -1], ![0, 2, -2], ![-2, -1, 3]]

def raw6566step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]

theorem canonical6566 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6566 = injectiveMoment H node185 := by
  calc
    injectiveMoment H raw6566 = injectiveMoment H raw6566step0 := by
      have heq : raw6566step0 = raw6566.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6566).symm
    injectiveMoment H raw6566step0 = injectiveMoment H raw6566step1 := by
      have heq : raw6566step1 = -raw6566step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6566step0).symm
    injectiveMoment H raw6566step1 = injectiveMoment H raw6566step2 := by
      have heq : raw6566step2 = (fun i j => raw6566step1 (permutation31 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6566step1 permutation31 permutation3
    _ = injectiveMoment H node185 := by rfl

def raw6567 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![1, 0, 2, -3], ![0, 1, -2, 1]]

def raw6567step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, 2, -2], ![2, -3, 1]]

def raw6567step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -1, 0], ![1, 0, -1], ![0, -2, 2], ![-2, 3, -1]]

def raw6567step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]

theorem canonical6567 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6567 = injectiveMoment H node185 := by
  calc
    injectiveMoment H raw6567 = injectiveMoment H raw6567step0 := by
      have heq : raw6567step0 = raw6567.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6567).symm
    injectiveMoment H raw6567step0 = injectiveMoment H raw6567step1 := by
      have heq : raw6567step1 = -raw6567step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6567step0).symm
    injectiveMoment H raw6567step1 = injectiveMoment H raw6567step2 := by
      have heq : raw6567step2 = (fun i j => raw6567step1 (permutation32 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6567step1 permutation32 permutation4
    _ = injectiveMoment H node185 := by rfl

def raw6568 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![1, 0, 3, -4], ![0, 1, -3, 2]]

def raw6568step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, 3, -3], ![2, -4, 2]]

def raw6568step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -1, 0], ![1, 0, -1], ![0, -3, 3], ![-2, 4, -2]]

def raw6568step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1]]

theorem canonical6568 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6568 = injectiveMoment H node155 := by
  calc
    injectiveMoment H raw6568 = injectiveMoment H raw6568step0 := by
      have heq : raw6568step0 = raw6568.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6568).symm
    injectiveMoment H raw6568step0 = injectiveMoment H raw6568step1 := by
      have heq : raw6568step1 = -raw6568step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6568step0).symm
    injectiveMoment H raw6568step1 = injectiveMoment H raw6568step2 := by
      have heq : raw6568step2 = (fun i j => raw6568step1 (permutation32 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6568step1 permutation32 permutation4
    _ = injectiveMoment H node155 := by rfl

def raw6569 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![-4, 2, 1, 1], ![5, -1, -2, -2]]

def raw6569step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -4, 5], ![-1, 2, -1], ![1, 1, -2], ![1, 1, -2]]

theorem canonical6569 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6569 = injectiveMoment H node234 := by
  calc
    injectiveMoment H raw6569 = injectiveMoment H raw6569step0 := by
      have heq : raw6569step0 = raw6569.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6569).symm
    _ = injectiveMoment H node234 := by rfl

def raw6570 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![-3, 2, 1, 0], ![4, -1, -2, -1]]

def raw6570step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 2, -1], ![1, 1, -2], ![1, 0, -1]]

def raw6570step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 2, -1], ![1, 0, -1], ![1, 1, -2]]

theorem canonical6570 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6570 = injectiveMoment H node246 := by
  calc
    injectiveMoment H raw6570 = injectiveMoment H raw6570step0 := by
      have heq : raw6570step0 = raw6570.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6570).symm
    injectiveMoment H raw6570step0 = injectiveMoment H raw6570step1 := by
      have heq : raw6570step1 = (fun i j => raw6570step0 (permutation10 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6570step0 permutation10 permutation3
    _ = injectiveMoment H node246 := by rfl

def raw6571 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![-3, 3, 1, -1], ![4, -2, -2, 0]]

def raw6571step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 3, -2], ![1, 1, -2], ![1, -1, 0]]

def raw6571step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 3, -2], ![1, -1, 0], ![1, 1, -2]]

theorem canonical6571 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6571 = injectiveMoment H node247 := by
  calc
    injectiveMoment H raw6571 = injectiveMoment H raw6571step0 := by
      have heq : raw6571step0 = raw6571.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6571).symm
    injectiveMoment H raw6571step0 = injectiveMoment H raw6571step1 := by
      have heq : raw6571step1 = (fun i j => raw6571step0 (permutation10 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6571step0 permutation10 permutation3
    _ = injectiveMoment H node247 := by rfl

def raw6572 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![-2, -1, 1, 2], ![3, 2, -2, -3]]

def raw6572step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, -1, 2], ![1, 1, -2], ![1, 2, -3]]

theorem canonical6572 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6572 = injectiveMoment H node258 := by
  calc
    injectiveMoment H raw6572 = injectiveMoment H raw6572step0 := by
      have heq : raw6572step0 = raw6572.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6572).symm
    _ = injectiveMoment H node258 := by rfl

def raw6573 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![-2, -1, 2, 1], ![3, 2, -3, -2]]

def raw6573step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, -1, 2], ![1, 2, -3], ![1, 1, -2]]

def raw6573step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, -1, 2], ![1, 1, -2], ![1, 2, -3]]

theorem canonical6573 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6573 = injectiveMoment H node258 := by
  calc
    injectiveMoment H raw6573 = injectiveMoment H raw6573step0 := by
      have heq : raw6573step0 = raw6573.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6573).symm
    injectiveMoment H raw6573step0 = injectiveMoment H raw6573step1 := by
      have heq : raw6573step1 = (fun i j => raw6573step0 (permutation10 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6573step0 permutation10 permutation3
    _ = injectiveMoment H node258 := by rfl

def raw6574 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![-2, 2, -2, 2], ![3, -1, 1, -3]]

def raw6574step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 2, -3]]

theorem canonical6574 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6574 = injectiveMoment H node260 := by
  calc
    injectiveMoment H raw6574 = injectiveMoment H raw6574step0 := by
      have heq : raw6574step0 = raw6574.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6574).symm
    _ = injectiveMoment H node260 := by rfl

def raw6575 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![-2, 2, 1, -1], ![3, -1, -2, 0]]

def raw6575step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 2, -1], ![1, 1, -2], ![1, -1, 0]]

def raw6575step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2]]

theorem canonical6575 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6575 = injectiveMoment H node261 := by
  calc
    injectiveMoment H raw6575 = injectiveMoment H raw6575step0 := by
      have heq : raw6575step0 = raw6575.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6575).symm
    injectiveMoment H raw6575step0 = injectiveMoment H raw6575step1 := by
      have heq : raw6575step1 = (fun i j => raw6575step0 (permutation10 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6575step0 permutation10 permutation3
    _ = injectiveMoment H node261 := by rfl

def raw6576 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![-2, 3, -2, 1], ![3, -2, 1, -2]]

def raw6576step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 3, -2], ![1, -2, 1], ![1, 1, -2]]

theorem canonical6576 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6576 = injectiveMoment H node262 := by
  calc
    injectiveMoment H raw6576 = injectiveMoment H raw6576step0 := by
      have heq : raw6576step0 = raw6576.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6576).symm
    _ = injectiveMoment H node262 := by rfl

def raw6577 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![-2, 3, 1, -2], ![3, -2, -2, 1]]

def raw6577step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 3, -2], ![1, 1, -2], ![1, -2, 1]]

def raw6577step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 3, -2], ![1, -2, 1], ![1, 1, -2]]

theorem canonical6577 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6577 = injectiveMoment H node262 := by
  calc
    injectiveMoment H raw6577 = injectiveMoment H raw6577step0 := by
      have heq : raw6577step0 = raw6577.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6577).symm
    injectiveMoment H raw6577step0 = injectiveMoment H raw6577step1 := by
      have heq : raw6577step1 = (fun i j => raw6577step0 (permutation10 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6577step0 permutation10 permutation3
    _ = injectiveMoment H node262 := by rfl

def raw6578 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![-1, -2, 2, 1], ![2, 3, -3, -2]]

def raw6578step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -2, 3], ![1, 2, -3], ![1, 1, -2]]

def raw6578step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, -1, 2], ![1, 1, -2], ![1, 2, -3]]

theorem canonical6578 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6578 = injectiveMoment H node258 := by
  calc
    injectiveMoment H raw6578 = injectiveMoment H raw6578step0 := by
      have heq : raw6578step0 = raw6578.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6578).symm
    injectiveMoment H raw6578step0 = injectiveMoment H raw6578step1 := by
      have heq : raw6578step1 = (fun i j => raw6578step0 (permutation16 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6578step0 permutation16 permutation3
    _ = injectiveMoment H node258 := by rfl

def raw6579 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![-1, -2, 3, 0], ![2, 3, -4, -1]]

def raw6579step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -2, 3], ![1, 3, -4], ![1, 0, -1]]

def raw6579step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![1, 2, -3], ![-1, -3, 4], ![-1, 0, 1]]

def raw6579step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 0, 1], ![1, 1, -2], ![1, 2, -3]]

theorem canonical6579 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6579 = injectiveMoment H node241 := by
  calc
    injectiveMoment H raw6579 = injectiveMoment H raw6579step0 := by
      have heq : raw6579step0 = raw6579.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6579).symm
    injectiveMoment H raw6579step0 = injectiveMoment H raw6579step1 := by
      have heq : raw6579step1 = -raw6579step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6579step0).symm
    injectiveMoment H raw6579step1 = injectiveMoment H raw6579step2 := by
      have heq : raw6579step2 = (fun i j => raw6579step1 (permutation25 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6579step1 permutation25 permutation3
    _ = injectiveMoment H node241 := by rfl

def raw6580 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![-1, -1, 1, 1], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 1, -1, -1]]

theorem canonical6580 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6580 = injectiveMoment H node2618 := by
  rfl

def raw6581 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![-1, -1, 1, 1], ![0, 1, -1, 0], ![1, 1, -1, -1], ![1, 0, 0, -1]]

def raw6581step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![-1, -1, 1, 1], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 1, -1, -1]]

theorem canonical6581 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6581 = injectiveMoment H node2618 := by
  calc
    injectiveMoment H raw6581 = injectiveMoment H raw6581step0 := by
      have heq : raw6581step0 = (fun i j => raw6581 (permutation34 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6581 permutation34 permutation9
    _ = injectiveMoment H node2618 := by rfl

def raw6582 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![-1, -1, 1, 1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 1, -1, -1]]

def raw6582step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![-1, -1, 1, 1], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 1, -1, -1]]

theorem canonical6582 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6582 = injectiveMoment H node2618 := by
  calc
    injectiveMoment H raw6582 = injectiveMoment H raw6582step0 := by
      have heq : raw6582step0 = (fun i j => raw6582 (permutation33 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6582 permutation33 permutation10
    _ = injectiveMoment H node2618 := by rfl

def raw6583 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![-1, -1, 1, 1], ![0, 2, -2, 0], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def raw6583step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 1, 0], ![0, -1, 1, 0], ![1, 1, -1, -1], ![1, 1, -1, -1]]

theorem canonical6583 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6583 = injectiveMoment H node2014 := by
  calc
    injectiveMoment H raw6583 = injectiveMoment H raw6583step0 := by
      have heq : raw6583step0 = (fun i j => raw6583 (permutation96 i) (permutation25 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6583 permutation96 permutation25
    _ = injectiveMoment H node2014 := by rfl

def raw6584 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![-1, -1, 1, 1], ![1, 0, 0, -1], ![1, 2, -2, -1]]

def raw6584step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![-1, -1, 0, 2], ![1, 1, 0, -2], ![1, 1, -1, -1]]

def raw6584step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, 1, -1], ![0, -1, -1, 2], ![0, 1, 1, -2], ![1, -1, -1, 1]]

theorem canonical6584 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6584 = injectiveMoment H node1360 := by
  calc
    injectiveMoment H raw6584 = injectiveMoment H raw6584step0 := by
      have heq : raw6584step0 = raw6584.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6584).symm
    injectiveMoment H raw6584step0 = injectiveMoment H raw6584step1 := by
      have heq : raw6584step1 = (fun i j => raw6584step0 (permutation30 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6584step0 permutation30 permutation21
    _ = injectiveMoment H node1360 := by rfl

def raw6585 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![-1, -1, 1, 1], ![1, 1, -1, -1], ![1, 1, -1, -1]]

theorem canonical6585 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6585 = injectiveMoment H node1088 := by
  rfl

def raw6586 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![-1, -1, 1, 1], ![2, 2, -2, -2]]

def raw6586step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![1, 1, -2], ![1, 1, -2]]

theorem canonical6586 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6586 = injectiveMoment H node275 := by
  calc
    injectiveMoment H raw6586 = injectiveMoment H raw6586step0 := by
      have heq : raw6586step0 = raw6586.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6586).symm
    _ = injectiveMoment H node275 := by rfl

def raw6587 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![-1, -1, 2, 0], ![2, 2, -3, -1]]

def raw6587step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![1, 2, -3], ![1, 0, -1]]

def raw6587step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![1, 1, -2], ![-1, -2, 3], ![-1, 0, 1]]

def raw6587step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![1, 1, -2], ![1, 1, -2]]

theorem canonical6587 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6587 = injectiveMoment H node175 := by
  calc
    injectiveMoment H raw6587 = injectiveMoment H raw6587step0 := by
      have heq : raw6587step0 = raw6587.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6587).symm
    injectiveMoment H raw6587step0 = injectiveMoment H raw6587step1 := by
      have heq : raw6587step1 = -raw6587step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6587step0).symm
    injectiveMoment H raw6587step1 = injectiveMoment H raw6587step2 := by
      have heq : raw6587step2 = (fun i j => raw6587step1 (permutation25 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6587step1 permutation25 permutation5
    _ = injectiveMoment H node175 := by rfl

def raw6588 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![-1, -1, 3, -1], ![2, 2, -4, 0]]

def raw6588step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![1, 3, -4], ![1, -1, 0]]

def raw6588step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![1, 1, -2], ![-1, -3, 4], ![-1, 1, 0]]

def raw6588step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 1, 0], ![1, 1, -2], ![1, 1, -2]]

theorem canonical6588 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6588 = injectiveMoment H node244 := by
  calc
    injectiveMoment H raw6588 = injectiveMoment H raw6588step0 := by
      have heq : raw6588step0 = raw6588.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6588).symm
    injectiveMoment H raw6588step0 = injectiveMoment H raw6588step1 := by
      have heq : raw6588step1 = -raw6588step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6588step0).symm
    injectiveMoment H raw6588step1 = injectiveMoment H raw6588step2 := by
      have heq : raw6588step2 = (fun i j => raw6588step1 (permutation25 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6588step1 permutation25 permutation3
    _ = injectiveMoment H node244 := by rfl

def raw6589 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![-1, 0, 0, 1], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def raw6589step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, 0, 0]]

theorem canonical6589 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6589 = injectiveMoment H node2846 := by
  calc
    injectiveMoment H raw6589 = injectiveMoment H raw6589step0 := by
      have heq : raw6589step0 = (fun i j => raw6589 (permutation36 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6589 permutation36 permutation17
    _ = injectiveMoment H node2846 := by rfl

def raw6590 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![-1, 0, 0, 1], ![1, 0, 0, -1], ![1, 1, -1, -1]]

def raw6590step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 1, -1]]

theorem canonical6590 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6590 = injectiveMoment H node1349 := by
  calc
    injectiveMoment H raw6590 = injectiveMoment H raw6590step0 := by
      have heq : raw6590step0 = (fun i j => raw6590 (permutation9 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6590 permutation9 permutation17
    _ = injectiveMoment H node1349 := by rfl

def raw6591 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![-1, 2, -2, 1], ![2, -1, 1, -2]]

def raw6591step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 1, -2]]

theorem canonical6591 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6591 = injectiveMoment H node276 := by
  calc
    injectiveMoment H raw6591 = injectiveMoment H raw6591step0 := by
      have heq : raw6591step0 = raw6591.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6591).symm
    _ = injectiveMoment H node276 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
