import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes1
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes2
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes3
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes4
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes11
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes12
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes14
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes15
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes18
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes19
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes20
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes42
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes44

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw7552 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -2, 0, 2], ![0, 2, 0, -2], ![1, 0, -2, 1]]

theorem canonical7552 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7552 = injectiveMoment H node1304 := by
  rfl

def raw7553 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -2, 0, 2], ![0, 2, 1, -3], ![1, 0, -3, 2]]

theorem canonical7553 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7553 = injectiveMoment H node1305 := by
  rfl

def raw7554 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -2, 0, 2], ![1, 2, -2, -1]]

def raw7554step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -2, 2], ![2, 0, -2], ![-1, 2, -1]]

def raw7554step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]

theorem canonical7554 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7554 = injectiveMoment H node203 := by
  calc
    injectiveMoment H raw7554 = injectiveMoment H raw7554step0 := by
      have heq : raw7554step0 = raw7554.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7554).symm
    injectiveMoment H raw7554step0 = injectiveMoment H raw7554step1 := by
      have heq : raw7554step1 = (fun i j => raw7554step0 (permutation15 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7554step0 permutation15 permutation5
    _ = injectiveMoment H node203 := by rfl

def raw7555 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -2, 1, 1], ![1, 2, -3, 0]]

def raw7555step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -2, 2], ![2, 1, -3], ![-1, 1, 0]]

def raw7555step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![0, 2, -2], ![-2, -1, 3], ![1, -1, 0]]

def raw7555step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]

theorem canonical7555 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7555 = injectiveMoment H node185 := by
  calc
    injectiveMoment H raw7555 = injectiveMoment H raw7555step0 := by
      have heq : raw7555step0 = raw7555.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7555).symm
    injectiveMoment H raw7555step0 = injectiveMoment H raw7555step1 := by
      have heq : raw7555step1 = -raw7555step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7555step0).symm
    injectiveMoment H raw7555step1 = injectiveMoment H raw7555step2 := by
      have heq : raw7555step2 = (fun i j => raw7555step1 (permutation24 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7555step1 permutation24 permutation3
    _ = injectiveMoment H node185 := by rfl

def raw7556 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -2, 2, 0], ![1, 2, -4, 1]]

def raw7556step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -2, 2], ![2, 2, -4], ![-1, 0, 1]]

def raw7556step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![0, 2, -2], ![-2, -2, 4], ![1, 0, -1]]

def raw7556step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 1, -1], ![2, 0, -2]]

theorem canonical7556 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7556 = injectiveMoment H node145 := by
  calc
    injectiveMoment H raw7556 = injectiveMoment H raw7556step0 := by
      have heq : raw7556step0 = raw7556.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7556).symm
    injectiveMoment H raw7556step0 = injectiveMoment H raw7556step1 := by
      have heq : raw7556step1 = -raw7556step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7556step0).symm
    injectiveMoment H raw7556step1 = injectiveMoment H raw7556step2 := by
      have heq : raw7556step2 = (fun i j => raw7556step1 (permutation22 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7556step1 permutation22 permutation5
    _ = injectiveMoment H node145 := by rfl

def raw7557 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -2, 3, -1], ![1, 2, -5, 2]]

def raw7557step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -2, 2], ![2, 3, -5], ![-1, -1, 2]]

def raw7557step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![0, 2, -2], ![-2, -3, 5], ![1, 1, -2]]

def raw7557step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 2, -2], ![1, 0, -1], ![1, 1, -2]]

theorem canonical7557 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7557 = injectiveMoment H node127 := by
  calc
    injectiveMoment H raw7557 = injectiveMoment H raw7557step0 := by
      have heq : raw7557step0 = raw7557.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7557).symm
    injectiveMoment H raw7557step0 = injectiveMoment H raw7557step1 := by
      have heq : raw7557step1 = -raw7557step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7557step0).symm
    injectiveMoment H raw7557step1 = injectiveMoment H raw7557step2 := by
      have heq : raw7557step2 = (fun i j => raw7557step1 (permutation23 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7557step1 permutation23 permutation3
    _ = injectiveMoment H node127 := by rfl

def raw7558 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -1, -3, 4], ![0, 1, 1, -2], ![1, 0, 0, -1]]

def raw7558step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, -1, 2, -1], ![0, 1, 0, -1], ![1, 0, 1, -2]]

theorem canonical7558 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7558 = injectiveMoment H node1170 := by
  calc
    injectiveMoment H raw7558 = injectiveMoment H raw7558step0 := by
      have heq : raw7558step0 = (fun i j => raw7558 (permutation16 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7558 permutation16 permutation15
    _ = injectiveMoment H node1170 := by rfl

def raw7559 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -1, -3, 4], ![0, 2, 0, -2], ![1, -1, 1, -1]]

theorem canonical7559 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7559 = injectiveMoment H node1306 := by
  rfl

def raw7560 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -1, -3, 4], ![0, 2, 1, -3], ![1, -1, 0, 0]]

theorem canonical7560 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7560 = injectiveMoment H node1307 := by
  rfl

def raw7561 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -1, -3, 4], ![1, 1, 1, -3]]

def raw7561step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![2, -3, 1], ![-1, 4, -3]]

def raw7561step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![0, 1, -1], ![-2, 3, -1], ![1, -4, 3]]

def raw7561step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 3, -4]]

theorem canonical7561 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7561 = injectiveMoment H node173 := by
  calc
    injectiveMoment H raw7561 = injectiveMoment H raw7561step0 := by
      have heq : raw7561step0 = raw7561.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7561).symm
    injectiveMoment H raw7561step0 = injectiveMoment H raw7561step1 := by
      have heq : raw7561step1 = -raw7561step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7561step0).symm
    injectiveMoment H raw7561step1 = injectiveMoment H raw7561step2 := by
      have heq : raw7561step2 = (fun i j => raw7561step1 (permutation23 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7561step1 permutation23 permutation4
    _ = injectiveMoment H node173 := by rfl

def raw7562 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -1, -2, 3], ![0, 1, 0, -1], ![1, 0, 0, -1]]

def raw7562step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 1, 0], ![2, -2, 0, 0], ![-1, 3, -1, -1]]

def raw7562step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, 0, 0, -1]]

theorem canonical7562 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7562 = injectiveMoment H node974 := by
  calc
    injectiveMoment H raw7562 = injectiveMoment H raw7562step0 := by
      have heq : raw7562step0 = raw7562.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7562).symm
    injectiveMoment H raw7562step0 = injectiveMoment H raw7562step1 := by
      have heq : raw7562step1 = (fun i j => raw7562step0 (permutation31 i) (permutation25 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7562step0 permutation31 permutation25
    _ = injectiveMoment H node974 := by rfl

def raw7563 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -1, -2, 3], ![0, 2, 0, -2], ![1, -1, 0, 0]]

def raw7563step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, -2, 1], ![0, 1, 2, -3], ![0, -2, 0, 2], ![-1, 1, 0, 0]]

def raw7563step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, 0, -2, 2], ![0, 2, 1, -3], ![1, -2, 0, 1]]

theorem canonical7563 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7563 = injectiveMoment H node1301 := by
  calc
    injectiveMoment H raw7563 = injectiveMoment H raw7563step0 := by
      have heq : raw7563step0 = -raw7563 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7563).symm
    injectiveMoment H raw7563step0 = injectiveMoment H raw7563step1 := by
      have heq : raw7563step1 = (fun i j => raw7563step0 (permutation32 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7563step0 permutation32 permutation11
    _ = injectiveMoment H node1301 := by rfl

def raw7564 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -1, -1, 2], ![0, 2, 0, -2], ![1, -1, -1, 1]]

theorem canonical7564 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7564 = injectiveMoment H node1309 := by
  rfl

def raw7565 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -1, 0, 1], ![0, 1, 0, -1], ![1, 0, -2, 1]]

def raw7565step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 1, 0], ![0, 1, -1, 0], ![1, 0, 1, -2]]

theorem canonical7565 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7565 = injectiveMoment H node1241 := by
  calc
    injectiveMoment H raw7565 = injectiveMoment H raw7565step0 := by
      have heq : raw7565step0 = (fun i j => raw7565 (permutation9 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7565 permutation9 permutation10
    _ = injectiveMoment H node1241 := by rfl

def raw7566 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -1, 0, 1], ![0, 1, 1, -2], ![1, 0, -3, 2]]

def raw7566step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, -2, 1], ![0, 1, 0, -1], ![0, -1, -1, 2], ![-1, 0, 3, -2]]

def raw7566step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 2, -1], ![0, 1, -1, 0], ![1, 0, 1, -2]]

theorem canonical7566 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7566 = injectiveMoment H node1206 := by
  calc
    injectiveMoment H raw7566 = injectiveMoment H raw7566step0 := by
      have heq : raw7566step0 = -raw7566 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7566).symm
    injectiveMoment H raw7566step0 = injectiveMoment H raw7566step1 := by
      have heq : raw7566step1 = (fun i j => raw7566step0 (permutation32 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7566step0 permutation32 permutation10
    _ = injectiveMoment H node1206 := by rfl

def raw7567 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -1, 0, 1], ![0, 2, 1, -3], ![1, -1, -3, 3]]

theorem canonical7567 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7567 = injectiveMoment H node1312 := by
  rfl

def raw7568 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -1, 1, 0], ![0, 2, 0, -2], ![1, -1, -3, 3]]

def raw7568step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 2, -1], ![2, 1, 0, -3], ![-1, 0, -2, 3]]

def raw7568step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 0, -1], ![0, 1, -2, 1], ![-2, -1, 0, 3], ![1, 0, 2, -3]]

def raw7568step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 1, 0, -1], ![0, 1, 2, -3], ![1, 0, -2, 1]]

theorem canonical7568 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7568 = injectiveMoment H node819 := by
  calc
    injectiveMoment H raw7568 = injectiveMoment H raw7568step0 := by
      have heq : raw7568step0 = raw7568.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7568).symm
    injectiveMoment H raw7568step0 = injectiveMoment H raw7568step1 := by
      have heq : raw7568step1 = -raw7568step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7568step0).symm
    injectiveMoment H raw7568step1 = injectiveMoment H raw7568step2 := by
      have heq : raw7568step2 = (fun i j => raw7568step1 (permutation22 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7568step1 permutation22 permutation15
    _ = injectiveMoment H node819 := by rfl

def raw7569 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, 0, -3, 3], ![0, 1, 1, -2], ![1, -1, 0, 0]]

def raw7569step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, 3, -3], ![0, 1, -2, 1], ![1, -1, 0, 0]]

theorem canonical7569 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7569 = injectiveMoment H node1267 := by
  calc
    injectiveMoment H raw7569 = injectiveMoment H raw7569step0 := by
      have heq : raw7569step0 = (fun i j => raw7569 (permutation9 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7569 permutation9 permutation10
    _ = injectiveMoment H node1267 := by rfl

def raw7570 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, 0, -3, 3], ![0, 2, 1, -3], ![1, -2, 0, 1]]

theorem canonical7570 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7570 = injectiveMoment H node1313 := by
  rfl

def raw7571 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -1, -1, 1]]

def raw7571step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 1, -1]]

theorem canonical7571 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7571 = injectiveMoment H node1262 := by
  calc
    injectiveMoment H raw7571 = injectiveMoment H raw7571step0 := by
      have heq : raw7571step0 = (fun i j => raw7571 (permutation9 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7571 permutation9 permutation10
    _ = injectiveMoment H node1262 := by rfl

def raw7572 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, 0, -1, 1], ![0, 2, 0, -2], ![1, -2, -1, 2]]

theorem canonical7572 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7572 = injectiveMoment H node1316 := by
  rfl

def raw7573 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, 0, 0, 0], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -2, -2, 3]]

def raw7573step0 : Matrix (Fin 4) (Fin 5) ℤ := ![![-1, 0, 0, 0, 1], ![0, 0, 1, 1, -2], ![2, 0, 0, 0, -2], ![-1, 0, -1, -1, 3]]

def raw7573step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 1, 1, -2], ![2, 0, 0, -2], ![-1, -1, -1, 3]]

def raw7573step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, -1, 1], ![0, 0, 2, -2], ![1, 1, 0, -2]]

theorem canonical7573 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7573 = injectiveMoment H node959 := by
  calc
    injectiveMoment H raw7573 = injectiveMoment H raw7573step0 := by
      have heq : raw7573step0 = raw7573.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7573).symm
    injectiveMoment H raw7573step0 = injectiveMoment H raw7573step1 := by
      have hz : ∀ i, raw7573step0 i (permutation57 0) = 0 := by decide +kernel
      have heq : raw7573step1 = (fun i j => raw7573step0 i (permutation57 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw7573step0 permutation57 hz
    injectiveMoment H raw7573step1 = injectiveMoment H raw7573step2 := by
      have heq : raw7573step2 = (fun i j => raw7573step1 (permutation28 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7573step1 permutation28 permutation17
    _ = injectiveMoment H node959 := by rfl

def raw7574 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, 0, 0, 0], ![0, 1, 0, -1], ![1, -1, -2, 2]]

def raw7574step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, 1, -1], ![2, 0, 0, -2], ![-1, 0, -1, 2]]

def raw7574step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 1, -1], ![2, 0, -2], ![-1, -1, 2]]

def raw7574step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1]]

theorem canonical7574 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7574 = injectiveMoment H node284 := by
  calc
    injectiveMoment H raw7574 = injectiveMoment H raw7574step0 := by
      have heq : raw7574step0 = raw7574.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7574).symm
    injectiveMoment H raw7574step0 = injectiveMoment H raw7574step1 := by
      have hz : ∀ i, raw7574step0 i (permutation15 0) = 0 := by decide +kernel
      have heq : raw7574step1 = (fun i j => raw7574step0 i (permutation15 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw7574step0 permutation15 hz
    injectiveMoment H raw7574step1 = injectiveMoment H raw7574step2 := by
      have heq : raw7574step2 = (fun i j => raw7574step1 (permutation28 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7574step1 permutation28 permutation5
    _ = injectiveMoment H node284 := by rfl

def raw7575 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -2, -2, 3]]

def raw7575step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -2, 3, -2]]

theorem canonical7575 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7575 = injectiveMoment H node2731 := by
  calc
    injectiveMoment H raw7575 = injectiveMoment H raw7575step0 := by
      have heq : raw7575step0 = (fun i j => raw7575 (permutation35 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7575 permutation35 permutation10
    _ = injectiveMoment H node2731 := by rfl

def raw7576 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, -1, 0], ![1, -2, -2, 3]]

def raw7576step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -2, 3, -2]]

theorem canonical7576 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7576 = injectiveMoment H node2731 := by
  calc
    injectiveMoment H raw7576 = injectiveMoment H raw7576step0 := by
      have heq : raw7576step0 = (fun i j => raw7576 (permutation33 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7576 permutation33 permutation10
    _ = injectiveMoment H node2731 := by rfl

def raw7577 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -2, -3, 4]]

theorem canonical7577 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7577 = injectiveMoment H node2832 := by
  rfl

def raw7578 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, -3, 3]]

def raw7578step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, 1, -1], ![2, 1, 0, -3], ![-1, -1, -1, 3]]

def raw7578step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, 0, 2, -3]]

theorem canonical7578 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7578 = injectiveMoment H node963 := by
  calc
    injectiveMoment H raw7578 = injectiveMoment H raw7578step0 := by
      have heq : raw7578step0 = raw7578.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7578).symm
    injectiveMoment H raw7578step0 = injectiveMoment H raw7578step1 := by
      have heq : raw7578step1 = (fun i j => raw7578step0 (permutation27 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7578step0 permutation27 permutation17
    _ = injectiveMoment H node963 := by rfl

def raw7579 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -2, -3, 4]]

def raw7579step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, 2, -2], ![2, 1, 0, -3], ![-1, -1, -2, 4]]

def raw7579step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, -1, 1], ![0, 2, 0, -2], ![1, 0, 2, -3]]

theorem canonical7579 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7579 = injectiveMoment H node763 := by
  calc
    injectiveMoment H raw7579 = injectiveMoment H raw7579step0 := by
      have heq : raw7579step0 = raw7579.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7579).symm
    injectiveMoment H raw7579step0 = injectiveMoment H raw7579step1 := by
      have heq : raw7579step1 = (fun i j => raw7579step0 (permutation27 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7579step0 permutation27 permutation17
    _ = injectiveMoment H node763 := by rfl

def raw7580 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -2, -1, 2]]

def raw7580step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 1, 1, -2], ![2, -1, 0, -1], ![-1, 0, -1, 2]]

def raw7580step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 0, -1], ![0, -1, -1, 2], ![-2, 1, 0, 1], ![1, 0, 1, -2]]

def raw7580step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 1, -1], ![0, 1, -2, 1], ![1, 0, 1, -2]]

theorem canonical7580 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7580 = injectiveMoment H node1047 := by
  calc
    injectiveMoment H raw7580 = injectiveMoment H raw7580step0 := by
      have heq : raw7580step0 = raw7580.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7580).symm
    injectiveMoment H raw7580step0 = injectiveMoment H raw7580step1 := by
      have heq : raw7580step1 = -raw7580step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7580step0).symm
    injectiveMoment H raw7580step1 = injectiveMoment H raw7580step2 := by
      have heq : raw7580step2 = (fun i j => raw7580step1 (permutation15 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7580step1 permutation15 permutation23
    _ = injectiveMoment H node1047 := by rfl

def raw7581 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, 1, 0, -1], ![0, 0, 0, 0], ![1, -1, -2, 2]]

def raw7581step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 1, 0, -1], ![2, 0, 0, -2], ![-1, -1, 0, 2]]

def raw7581step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 1, -1], ![2, 0, -2], ![-1, -1, 2]]

def raw7581step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1]]

theorem canonical7581 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7581 = injectiveMoment H node284 := by
  calc
    injectiveMoment H raw7581 = injectiveMoment H raw7581step0 := by
      have heq : raw7581step0 = raw7581.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7581).symm
    injectiveMoment H raw7581step0 = injectiveMoment H raw7581step1 := by
      have hz : ∀ i, raw7581step0 i (permutation21 0) = 0 := by decide +kernel
      have heq : raw7581step1 = (fun i j => raw7581step0 i (permutation21 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw7581step0 permutation21 hz
    injectiveMoment H raw7581step1 = injectiveMoment H raw7581step2 := by
      have heq : raw7581step2 = (fun i j => raw7581step1 (permutation28 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7581step1 permutation28 permutation5
    _ = injectiveMoment H node284 := by rfl

def raw7582 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, 1, 0, -1], ![0, 1, -1, 0], ![1, -2, -1, 2]]

def raw7582step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 1, 1, -2], ![2, 0, -1, -1], ![-1, -1, 0, 2]]

def raw7582step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 0, -1], ![0, -1, -1, 2], ![-2, 0, 1, 1], ![1, 1, 0, -2]]

def raw7582step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 1, -1], ![0, 1, -2, 1], ![1, 0, 1, -2]]

theorem canonical7582 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7582 = injectiveMoment H node1047 := by
  calc
    injectiveMoment H raw7582 = injectiveMoment H raw7582step0 := by
      have heq : raw7582step0 = raw7582.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7582).symm
    injectiveMoment H raw7582step0 = injectiveMoment H raw7582step1 := by
      have heq : raw7582step1 = -raw7582step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7582step0).symm
    injectiveMoment H raw7582step1 = injectiveMoment H raw7582step2 := by
      have heq : raw7582step2 = (fun i j => raw7582step1 (permutation15 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7582step1 permutation15 permutation17
    _ = injectiveMoment H node1047 := by rfl

def raw7583 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -2, -2, 3]]

def raw7583step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 1, 1, -2], ![2, 0, 0, -2], ![-1, -1, -1, 3]]

def raw7583step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, -1, 1], ![0, 0, 2, -2], ![1, 1, 0, -2]]

theorem canonical7583 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7583 = injectiveMoment H node959 := by
  calc
    injectiveMoment H raw7583 = injectiveMoment H raw7583step0 := by
      have heq : raw7583step0 = raw7583.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7583).symm
    injectiveMoment H raw7583step0 = injectiveMoment H raw7583step1 := by
      have heq : raw7583step1 = (fun i j => raw7583step0 (permutation28 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7583step0 permutation28 permutation17
    _ = injectiveMoment H node959 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
