import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes2
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes3
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes4
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes13
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes17
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes18
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes19
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes20
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes21
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes31
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes40
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes44

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw7808 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -2, 2], ![0, -2, 0, 2], ![0, 1, 3, -4], ![1, 0, -1, 0]]

def raw7808step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![1, -2, 1, 0], ![-2, 0, 3, -1], ![2, 2, -4, 0]]

def raw7808step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -2, 1, 1], ![0, 2, 2, -4], ![1, 0, -1, 0]]

theorem canonical7808 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7808 = injectiveMoment H node1189 := by
  calc
    injectiveMoment H raw7808 = injectiveMoment H raw7808step0 := by
      have heq : raw7808step0 = raw7808.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7808).symm
    injectiveMoment H raw7808step0 = injectiveMoment H raw7808step1 := by
      have heq : raw7808step1 = (fun i j => raw7808step0 (permutation24 i) (permutation29 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7808step0 permutation24 permutation29
    _ = injectiveMoment H node1189 := by rfl

def raw7809 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -2, 2], ![0, -2, 1, 1], ![0, 1, 2, -3], ![1, 0, -1, 0]]

def raw7809step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, -1, 2, -2], ![0, 2, -1, -1], ![0, -1, -2, 3], ![-1, 0, 1, 0]]

def raw7809step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 3, -2], ![0, 2, -1, -1], ![1, -1, -2, 2]]

theorem canonical7809 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7809 = injectiveMoment H node1283 := by
  calc
    injectiveMoment H raw7809 = injectiveMoment H raw7809step0 := by
      have heq : raw7809step0 = -raw7809 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7809).symm
    injectiveMoment H raw7809step0 = injectiveMoment H raw7809step1 := by
      have heq : raw7809step1 = (fun i j => raw7809step0 (permutation32 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7809step0 permutation32 permutation10
    _ = injectiveMoment H node1283 := by rfl

def raw7810 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -2, 2], ![0, -2, 3, -1], ![0, 1, 0, -1], ![1, 0, -1, 0]]

def raw7810step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![1, -2, 1, 0], ![-2, 3, 0, -1], ![2, -1, -1, 0]]

def raw7810step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 2, -1], ![0, 1, 1, -2], ![1, 0, -1, 0]]

theorem canonical7810 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7810 = injectiveMoment H node1207 := by
  calc
    injectiveMoment H raw7810 = injectiveMoment H raw7810step0 := by
      have heq : raw7810step0 = raw7810.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7810).symm
    injectiveMoment H raw7810step0 = injectiveMoment H raw7810step1 := by
      have heq : raw7810step1 = (fun i j => raw7810step0 (permutation26 i) (permutation31 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7810step0 permutation26 permutation31
    _ = injectiveMoment H node1207 := by rfl

def raw7811 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -2, 2], ![0, -1, -1, 2], ![0, 0, 2, -2], ![1, 0, 1, -2]]

def raw7811step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, -1, 2, -2], ![0, 1, 1, -2], ![0, 0, -2, 2], ![-1, 0, -1, 2]]

def raw7811step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, -2, 2], ![0, 1, 1, -2], ![1, -1, 2, -2]]

theorem canonical7811 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7811 = injectiveMoment H node1253 := by
  calc
    injectiveMoment H raw7811 = injectiveMoment H raw7811step0 := by
      have heq : raw7811step0 = -raw7811 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7811).symm
    injectiveMoment H raw7811step0 = injectiveMoment H raw7811step1 := by
      have heq : raw7811step1 = (fun i j => raw7811step0 (permutation32 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7811step0 permutation32 permutation9
    _ = injectiveMoment H node1253 := by rfl

def raw7812 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -2, 2], ![0, -1, -1, 2], ![0, 1, 3, -4], ![1, -1, 0, 0]]

def raw7812step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![1, -1, 1, -1], ![-2, -1, 3, 0], ![2, 2, -4, 0]]

def raw7812step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, -2, 3], ![0, 2, 2, -4], ![1, 0, -1, 0]]

theorem canonical7812 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7812 = injectiveMoment H node1095 := by
  calc
    injectiveMoment H raw7812 = injectiveMoment H raw7812step0 := by
      have heq : raw7812step0 = raw7812.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7812).symm
    injectiveMoment H raw7812step0 = injectiveMoment H raw7812step1 := by
      have heq : raw7812step1 = (fun i j => raw7812step0 (permutation18 i) (permutation29 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7812step0 permutation18 permutation29
    _ = injectiveMoment H node1095 := by rfl

def raw7813 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -2, 2], ![0, -1, 2, -1], ![0, 1, 1, -2], ![1, -1, -1, 1]]

theorem canonical7813 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7813 = injectiveMoment H node1333 := by
  rfl

def raw7814 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 1, -2, 2], ![0, -1, 2, -1], ![1, 0, 0, -1]]

def raw7814step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![1, -1, 0], ![-2, 2, 0], ![2, -1, -1]]

def raw7814step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1]]

theorem canonical7814 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7814 = injectiveMoment H node284 := by
  calc
    injectiveMoment H raw7814 = injectiveMoment H raw7814step0 := by
      have heq : raw7814step0 = raw7814.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7814).symm
    injectiveMoment H raw7814step0 = injectiveMoment H raw7814step1 := by
      have heq : raw7814step1 = (fun i j => raw7814step0 (permutation30 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7814step0 permutation30 permutation8
    _ = injectiveMoment H node284 := by rfl

def raw7815 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 1, -2, 2], ![0, -1, 3, -2], ![1, 0, -1, 0]]

def raw7815step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![1, -1, 0], ![-2, 3, -1], ![2, -2, 0]]

def raw7815step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0]]

theorem canonical7815 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7815 = injectiveMoment H node272 := by
  calc
    injectiveMoment H raw7815 = injectiveMoment H raw7815step0 := by
      have heq : raw7815step0 = raw7815.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7815).symm
    injectiveMoment H raw7815step0 = injectiveMoment H raw7815step1 := by
      have heq : raw7815step1 = (fun i j => raw7815step0 (permutation24 i) (permutation7 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7815step0 permutation24 permutation7
    _ = injectiveMoment H node272 := by rfl

def raw7816 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -2, 2], ![0, 0, -1, 1], ![0, 0, 2, -2], ![1, -1, 1, -1]]

theorem canonical7816 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7816 = injectiveMoment H node1335 := by
  rfl

def raw7817 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -2, 2], ![0, 0, -1, 1], ![0, 0, 3, -3], ![1, -1, 0, 0]]

def raw7817step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![1, 0, 0, -1], ![-2, -1, 3, 0], ![2, 1, -3, 0]]

def raw7817step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 1, 0], ![0, 1, -1, 0], ![1, 0, 2, -3]]

theorem canonical7817 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7817 = injectiveMoment H node1201 := by
  calc
    injectiveMoment H raw7817 = injectiveMoment H raw7817step0 := by
      have heq : raw7817step0 = raw7817.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7817).symm
    injectiveMoment H raw7817step0 = injectiveMoment H raw7817step1 := by
      have heq : raw7817step1 = (fun i j => raw7817step0 (permutation23 i) (permutation19 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7817step0 permutation23 permutation19
    _ = injectiveMoment H node1201 := by rfl

def raw7818 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -2, 2], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -2, 3, -2]]

def raw7818step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![1, 0, 1, -2], ![-2, -1, 0, 3], ![2, 1, -1, -2]]

def raw7818step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 0, -1, 1], ![0, 1, 1, -2], ![1, -1, 2, -2]]

theorem canonical7818 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7818 = injectiveMoment H node1216 := by
  calc
    injectiveMoment H raw7818 = injectiveMoment H raw7818step0 := by
      have heq : raw7818step0 = raw7818.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7818).symm
    injectiveMoment H raw7818step0 = injectiveMoment H raw7818step1 := by
      have heq : raw7818step1 = (fun i j => raw7818step0 (permutation21 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7818step0 permutation21 permutation17
    _ = injectiveMoment H node1216 := by rfl

def raw7819 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -2, 2], ![0, 0, -1, 1], ![0, 1, 2, -3], ![1, -2, 1, 0]]

def raw7819step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![1, 0, 1, -2], ![-2, -1, 2, 1], ![2, 1, -3, 0]]

def raw7819step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 0, -1], ![-1, 0, -1, 2], ![2, 1, -2, -1], ![-2, -1, 3, 0]]

def raw7819step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 1, 0], ![0, 2, -1, -1], ![1, -1, 2, -2]]

theorem canonical7819 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7819 = injectiveMoment H node1204 := by
  calc
    injectiveMoment H raw7819 = injectiveMoment H raw7819step0 := by
      have heq : raw7819step0 = raw7819.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7819).symm
    injectiveMoment H raw7819step0 = injectiveMoment H raw7819step1 := by
      have heq : raw7819step1 = -raw7819step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7819step0).symm
    injectiveMoment H raw7819step1 = injectiveMoment H raw7819step2 := by
      have heq : raw7819step2 = (fun i j => raw7819step1 (permutation27 i) (permutation19 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7819step1 permutation27 permutation19
    _ = injectiveMoment H node1204 := by rfl

def raw7820 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -2, 2], ![0, 0, -1, 1], ![0, 1, 3, -4], ![1, -2, 0, 1]]

def raw7820step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![1, 0, 1, -2], ![-2, -1, 3, 0], ![2, 1, -4, 1]]

def raw7820step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 0, -1], ![-1, 0, -1, 2], ![2, 1, -3, 0], ![-2, -1, 4, -1]]

def raw7820step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, -1, 1, 0], ![0, 2, -1, -1], ![1, 0, 2, -3]]

theorem canonical7820 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7820 = injectiveMoment H node892 := by
  calc
    injectiveMoment H raw7820 = injectiveMoment H raw7820step0 := by
      have heq : raw7820step0 = raw7820.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7820).symm
    injectiveMoment H raw7820step0 = injectiveMoment H raw7820step1 := by
      have heq : raw7820step1 = -raw7820step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7820step0).symm
    injectiveMoment H raw7820step1 = injectiveMoment H raw7820step2 := by
      have heq : raw7820step2 = (fun i j => raw7820step1 (permutation27 i) (permutation19 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7820step1 permutation27 permutation19
    _ = injectiveMoment H node892 := by rfl

def raw7821 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -2, 2], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, 0, 0]]

def raw7821step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![1, 0, 0, -1], ![-2, 1, 1, 0], ![2, -1, -1, 0]]

def raw7821step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, 1, 0, -2]]

theorem canonical7821 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7821 = injectiveMoment H node1039 := by
  calc
    injectiveMoment H raw7821 = injectiveMoment H raw7821step0 := by
      have heq : raw7821step0 = raw7821.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7821).symm
    injectiveMoment H raw7821step0 = injectiveMoment H raw7821step1 := by
      have heq : raw7821step1 = (fun i j => raw7821step0 (permutation29 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7821step0 permutation29 permutation18
    _ = injectiveMoment H node1039 := by rfl

def raw7822 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -2, 2], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -2, 1, 0]]

def raw7822step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![1, 0, 1, -2], ![-2, 1, 0, 1], ![2, -1, -1, 0]]

def raw7822step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 1, -1], ![0, 1, -2, 1], ![1, 0, 1, -2]]

theorem canonical7822 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7822 = injectiveMoment H node1047 := by
  calc
    injectiveMoment H raw7822 = injectiveMoment H raw7822step0 := by
      have heq : raw7822step0 = raw7822.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7822).symm
    injectiveMoment H raw7822step0 = injectiveMoment H raw7822step1 := by
      have heq : raw7822step1 = (fun i j => raw7822step0 (permutation27 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7822step0 permutation27 permutation18
    _ = injectiveMoment H node1047 := by rfl

def raw7823 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 1, -2, 2], ![0, 0, 1, -1], ![1, -1, 1, -1]]

def raw7823step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![1, 0, -1], ![-2, 1, 1], ![2, -1, -1]]

def raw7823step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2]]

theorem canonical7823 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7823 = injectiveMoment H node283 := by
  calc
    injectiveMoment H raw7823 = injectiveMoment H raw7823step0 := by
      have heq : raw7823step0 = raw7823.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7823).symm
    injectiveMoment H raw7823step0 = injectiveMoment H raw7823step1 := by
      have heq : raw7823step1 = (fun i j => raw7823step0 (permutation29 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7823step0 permutation29 permutation6
    _ = injectiveMoment H node283 := by rfl

def raw7824 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 1, -2, 2], ![0, 0, 2, -2], ![1, -1, 0, 0]]

def raw7824step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![1, 0, -1], ![-2, 2, 0], ![2, -2, 0]]

def raw7824step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1]]

theorem canonical7824 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7824 = injectiveMoment H node291 := by
  calc
    injectiveMoment H raw7824 = injectiveMoment H raw7824step0 := by
      have heq : raw7824step0 = raw7824.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7824).symm
    injectiveMoment H raw7824step0 = injectiveMoment H raw7824step1 := by
      have heq : raw7824step1 = (fun i j => raw7824step0 (permutation20 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7824step0 permutation20 permutation8
    _ = injectiveMoment H node291 := by rfl

def raw7825 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -2, 2], ![0, 0, 3, -3], ![0, 1, -1, 0], ![1, -2, 0, 1]]

def raw7825step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![1, 0, 1, -2], ![-2, 3, -1, 0], ![2, -3, 0, 1]]

def raw7825step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, -2, 1, 0]]

theorem canonical7825 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7825 = injectiveMoment H node1231 := by
  calc
    injectiveMoment H raw7825 = injectiveMoment H raw7825step0 := by
      have heq : raw7825step0 = raw7825.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7825).symm
    injectiveMoment H raw7825step0 = injectiveMoment H raw7825step1 := by
      have heq : raw7825step1 = (fun i j => raw7825step0 (permutation22 i) (permutation25 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7825step0 permutation22 permutation25
    _ = injectiveMoment H node1231 := by rfl

def raw7826 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -2, 2], ![0, 0, 3, -3], ![0, 1, 0, -1], ![1, -2, -1, 2]]

theorem canonical7826 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7826 = injectiveMoment H node1337 := by
  rfl

def raw7827 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 1, -2, 2], ![0, 0, 3, -3], ![1, -1, -1, 1]]

def raw7827step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![1, 0, -1], ![-2, 3, -1], ![2, -3, 1]]

def raw7827step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 2, -3]]

theorem canonical7827 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7827 = injectiveMoment H node259 := by
  calc
    injectiveMoment H raw7827 = injectiveMoment H raw7827step0 := by
      have heq : raw7827step0 = raw7827.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7827).symm
    injectiveMoment H raw7827step0 = injectiveMoment H raw7827step1 := by
      have heq : raw7827step1 = (fun i j => raw7827step0 (permutation23 i) (permutation7 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7827step0 permutation23 permutation7
    _ = injectiveMoment H node259 := by rfl

def raw7828 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 1, -2, 2], ![0, 1, 0, -1], ![1, -2, 2, -1]]

def raw7828step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![1, 1, -2], ![-2, 0, 2], ![2, -1, -1]]

def raw7828step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1]]

theorem canonical7828 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7828 = injectiveMoment H node288 := by
  calc
    injectiveMoment H raw7828 = injectiveMoment H raw7828step0 := by
      have heq : raw7828step0 = raw7828.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7828).symm
    injectiveMoment H raw7828step0 = injectiveMoment H raw7828step1 := by
      have heq : raw7828step1 = (fun i j => raw7828step0 (permutation28 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7828step0 permutation28 permutation6
    _ = injectiveMoment H node288 := by rfl

def raw7829 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 1, -2, 2], ![0, 1, 1, -2], ![1, -2, 1, 0]]

def raw7829step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![1, 1, -2], ![-2, 1, 1], ![2, -2, 0]]

def raw7829step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]

theorem canonical7829 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7829 = injectiveMoment H node210 := by
  calc
    injectiveMoment H raw7829 = injectiveMoment H raw7829step0 := by
      have heq : raw7829step0 = raw7829.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7829).symm
    injectiveMoment H raw7829step0 = injectiveMoment H raw7829step1 := by
      have heq : raw7829step1 = (fun i j => raw7829step0 (permutation27 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7829step0 permutation27 permutation6
    _ = injectiveMoment H node210 := by rfl

def raw7830 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 1, -2, 2], ![0, 1, 3, -4], ![1, -2, -1, 2]]

def raw7830step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![1, 1, -2], ![-2, 3, -1], ![2, -4, 2]]

def raw7830step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![-1, -1, 2], ![2, -3, 1], ![-2, 4, -2]]

def raw7830step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 2, -3], ![2, -1, -1]]

theorem canonical7830 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7830 = injectiveMoment H node132 := by
  calc
    injectiveMoment H raw7830 = injectiveMoment H raw7830step0 := by
      have heq : raw7830step0 = raw7830.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7830).symm
    injectiveMoment H raw7830step0 = injectiveMoment H raw7830step1 := by
      have heq : raw7830step1 = -raw7830step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7830step0).symm
    injectiveMoment H raw7830step1 = injectiveMoment H raw7830step2 := by
      have heq : raw7830step2 = (fun i j => raw7830step1 (permutation28 i) (permutation7 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7830step1 permutation28 permutation7
    _ = injectiveMoment H node132 := by rfl

def raw7831 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![-1, 1, -1, 1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, -1, 1, -1]]

def raw7831step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![-1, -1, 1, 1], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 1, -1, -1]]

theorem canonical7831 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7831 = injectiveMoment H node2618 := by
  calc
    injectiveMoment H raw7831 = injectiveMoment H raw7831step0 := by
      have heq : raw7831step0 = (fun i j => raw7831 (permutation33 i) (permutation12 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7831 permutation33 permutation12
    _ = injectiveMoment H node2618 := by rfl

def raw7832 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![-1, 1, -1, 1], ![0, 0, 2, -2], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def raw7832step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 1, 0], ![0, -1, 1, 0], ![1, 1, -1, -1], ![1, 1, -1, -1]]

theorem canonical7832 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7832 = injectiveMoment H node2014 := by
  calc
    injectiveMoment H raw7832 = injectiveMoment H raw7832step0 := by
      have heq : raw7832step0 = (fun i j => raw7832 (permutation96 i) (permutation29 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7832 permutation96 permutation29
    _ = injectiveMoment H node2014 := by rfl

def raw7833 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![-1, 1, -1, 1], ![1, -1, 0, 0], ![1, -1, 2, -2]]

def raw7833step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![1, 1, -1, -1], ![-1, -1, 0, 2], ![1, 1, 0, -2]]

def raw7833step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, 1, -1], ![0, -1, -1, 2], ![0, 1, 1, -2], ![1, -1, -1, 1]]

theorem canonical7833 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7833 = injectiveMoment H node1360 := by
  calc
    injectiveMoment H raw7833 = injectiveMoment H raw7833step0 := by
      have heq : raw7833step0 = raw7833.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7833).symm
    injectiveMoment H raw7833step0 = injectiveMoment H raw7833step1 := by
      have heq : raw7833step1 = (fun i j => raw7833step0 (permutation18 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7833step0 permutation18 permutation21
    _ = injectiveMoment H node1360 := by rfl

def raw7834 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![-1, 1, -1, 1], ![1, -1, 1, -1], ![1, -1, 1, -1]]

def raw7834step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![-1, -1, 1, 1], ![1, 1, -1, -1], ![1, 1, -1, -1]]

theorem canonical7834 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7834 = injectiveMoment H node1088 := by
  calc
    injectiveMoment H raw7834 = injectiveMoment H raw7834step0 := by
      have heq : raw7834step0 = (fun i j => raw7834 (permutation9 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7834 permutation9 permutation11
    _ = injectiveMoment H node1088 := by rfl

def raw7835 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, -2, 3, -1], ![0, 1, -2, 1], ![1, 0, 0, -1]]

def raw7835step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, -1, 1, -1], ![0, 2, -3, 1], ![0, -1, 2, -1], ![-1, 0, 0, 1]]

def raw7835step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -1, -1, 2], ![0, 2, 1, -3], ![1, -1, -1, 1]]

theorem canonical7835 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7835 = injectiveMoment H node1299 := by
  calc
    injectiveMoment H raw7835 = injectiveMoment H raw7835step0 := by
      have heq : raw7835step0 = -raw7835 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7835).symm
    injectiveMoment H raw7835step0 = injectiveMoment H raw7835step1 := by
      have heq : raw7835step1 = (fun i j => raw7835step0 (permutation32 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7835step0 permutation32 permutation10
    _ = injectiveMoment H node1299 := by rfl

def raw7836 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, -1, -2, 3], ![0, 1, 3, -4], ![1, -1, 0, 0]]

theorem canonical7836 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7836 = injectiveMoment H node1340 := by
  rfl

def raw7837 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, -1, -2, 3], ![1, 0, 3, -4]]

def raw7837step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![1, -1, 0], ![-1, -2, 3], ![1, 3, -4]]

def raw7837step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![-1, 1, 0], ![1, 2, -3], ![-1, -3, 4]]

def raw7837step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 1, 0], ![1, 0, -1], ![1, 2, -3]]

theorem canonical7837 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7837 = injectiveMoment H node243 := by
  calc
    injectiveMoment H raw7837 = injectiveMoment H raw7837step0 := by
      have heq : raw7837step0 = raw7837.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7837).symm
    injectiveMoment H raw7837step0 = injectiveMoment H raw7837step1 := by
      have heq : raw7837step1 = -raw7837step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7837step0).symm
    injectiveMoment H raw7837step1 = injectiveMoment H raw7837step2 := by
      have heq : raw7837step2 = (fun i j => raw7837step1 (permutation29 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7837step1 permutation29 permutation3
    _ = injectiveMoment H node243 := by rfl

def raw7838 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, -1, -1, 2], ![0, 0, -1, 1], ![0, 1, 3, -4], ![1, -1, 0, 0]]

theorem canonical7838 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7838 = injectiveMoment H node2841 := by
  rfl

def raw7839 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, -1, -1, 2], ![0, 1, 2, -3], ![1, -1, 0, 0]]

def raw7839step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, -1, 2], ![0, 2, 1, -3], ![1, 0, -1, 0]]

theorem canonical7839 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7839 = injectiveMoment H node1099 := by
  calc
    injectiveMoment H raw7839 = injectiveMoment H raw7839step0 := by
      have heq : raw7839step0 = (fun i j => raw7839 (permutation9 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7839 permutation9 permutation11
    _ = injectiveMoment H node1099 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
