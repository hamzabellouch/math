import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes0
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes4
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes8
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes10
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes11
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes13
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes17
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes20
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes29
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes38
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes41
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes43

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw8672 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0], ![-3, 3, 0]]

def raw8672step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0]]

theorem canonical8672 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8672 = injectiveMoment H node2791 := by
  calc
    injectiveMoment H raw8672 = injectiveMoment H raw8672step0 := by
      have heq : raw8672step0 = (fun i j => raw8672 (permutation231 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8672 permutation231 permutation8
    _ = injectiveMoment H node2791 := by rfl

def raw8673 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![-3, 2, 1]]

def raw8673step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![3, -2, -1]]

def raw8673step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]

theorem canonical8673 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8673 = injectiveMoment H node1891 := by
  calc
    injectiveMoment H raw8673 = injectiveMoment H raw8673step0 := by
      have heq : raw8673step0 = -raw8673 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8673).symm
    injectiveMoment H raw8673step0 = injectiveMoment H raw8673step1 := by
      have heq : raw8673step1 = (fun i j => raw8673step0 (permutation366 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8673step0 permutation366 permutation6
    _ = injectiveMoment H node1891 := by rfl

def raw8674 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![-2, 1, 1], ![-1, -1, 2], ![3, 0, -3]]

def raw8674step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![-2, 1, 1], ![-1, -1, 2], ![3, 0, -3]]

def raw8674step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, 3, -3], ![1, -2, 1], ![1, 0, -1]]

theorem canonical8674 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8674 = injectiveMoment H node1138 := by
  calc
    injectiveMoment H raw8674 = injectiveMoment H raw8674step0 := by
      have hz : ∀ j, raw8674 (permutation202 0) j = 0 := by decide +kernel
      have heq : raw8674step0 = (fun i j => raw8674 (permutation202 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8674 permutation202 hz
    injectiveMoment H raw8674step0 = injectiveMoment H raw8674step1 := by
      have heq : raw8674step1 = (fun i j => raw8674step0 (permutation109 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8674step0 permutation109 permutation5
    _ = injectiveMoment H node1138 := by rfl

def raw8675 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![-3, 0, 3], ![2, 1, -3]]

def raw8675step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![-1, 1, 0], ![3, 0, -3], ![-2, -1, 3]]

def raw8675step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![3, 0, -3], ![-2, -1, 3]]

def raw8675step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 0, 1], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1]]

theorem canonical8675 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8675 = injectiveMoment H node864 := by
  calc
    injectiveMoment H raw8675 = injectiveMoment H raw8675step0 := by
      have heq : raw8675step0 = -raw8675 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8675).symm
    injectiveMoment H raw8675step0 = injectiveMoment H raw8675step1 := by
      have hz : ∀ j, raw8675step0 (permutation202 0) j = 0 := by decide +kernel
      have heq : raw8675step1 = (fun i j => raw8675step0 (permutation202 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8675step0 permutation202 hz
    injectiveMoment H raw8675step1 = injectiveMoment H raw8675step2 := by
      have heq : raw8675step2 = (fun i j => raw8675step1 (permutation138 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8675step1 permutation138 permutation5
    _ = injectiveMoment H node864 := by rfl

def raw8676 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![-2, -1, 3], ![1, 2, -3]]

def raw8676step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![-2, -1, 3], ![1, 2, -3]]

def raw8676step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 2, -3]]

theorem canonical8676 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8676 = injectiveMoment H node559 := by
  calc
    injectiveMoment H raw8676 = injectiveMoment H raw8676step0 := by
      have hz : ∀ j, raw8676 (permutation202 0) j = 0 := by decide +kernel
      have heq : raw8676step0 = (fun i j => raw8676 (permutation202 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8676 permutation202 hz
    injectiveMoment H raw8676step0 = injectiveMoment H raw8676step1 := by
      have heq : raw8676step1 = (fun i j => raw8676step0 (permutation104 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8676step0 permutation104 permutation3
    _ = injectiveMoment H node559 := by rfl

def raw8677 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![-2, 1, 1]]

def raw8677step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![-2, 1, 1]]

def raw8677step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

theorem canonical8677 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8677 = injectiveMoment H node711 := by
  calc
    injectiveMoment H raw8677 = injectiveMoment H raw8677step0 := by
      have hz : ∀ j, raw8677 (permutation202 0) j = 0 := by decide +kernel
      have heq : raw8677step0 = (fun i j => raw8677 (permutation202 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8677 permutation202 hz
    injectiveMoment H raw8677step0 = injectiveMoment H raw8677step1 := by
      have heq : raw8677step1 = (fun i j => raw8677step0 (permutation128 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8677step0 permutation128 permutation3
    _ = injectiveMoment H node711 := by rfl

def raw8678 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2], ![-3, 1, 2]]

def raw8678step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2], ![3, -1, -2]]

def raw8678step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2], ![3, -1, -2]]

def raw8678step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]

theorem canonical8678 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8678 = injectiveMoment H node869 := by
  calc
    injectiveMoment H raw8678 = injectiveMoment H raw8678step0 := by
      have heq : raw8678step0 = -raw8678 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8678).symm
    injectiveMoment H raw8678step0 = injectiveMoment H raw8678step1 := by
      have hz : ∀ j, raw8678step0 (permutation202 0) j = 0 := by decide +kernel
      have heq : raw8678step1 = (fun i j => raw8678step0 (permutation202 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8678step0 permutation202 hz
    injectiveMoment H raw8678step1 = injectiveMoment H raw8678step2 := by
      have heq : raw8678step2 = (fun i j => raw8678step1 (permutation137 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8678step1 permutation137 permutation6
    _ = injectiveMoment H node869 := by rfl

def raw8679 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![-2, 0, 2]]

def raw8679step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![-2, 0, 2]]

def raw8679step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1]]

theorem canonical8679 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8679 = injectiveMoment H node1291 := by
  calc
    injectiveMoment H raw8679 = injectiveMoment H raw8679step0 := by
      have hz : ∀ j, raw8679 (permutation202 0) j = 0 := by decide +kernel
      have heq : raw8679step0 = (fun i j => raw8679 (permutation202 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8679 permutation202 hz
    injectiveMoment H raw8679step0 = injectiveMoment H raw8679step1 := by
      have heq : raw8679step1 = (fun i j => raw8679step0 (permutation54 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8679step0 permutation54 permutation5
    _ = injectiveMoment H node1291 := by rfl

def raw8680 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![-2, -1, 3]]

def raw8680step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![-2, -1, 3]]

def raw8680step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]

theorem canonical8680 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8680 = injectiveMoment H node560 := by
  calc
    injectiveMoment H raw8680 = injectiveMoment H raw8680step0 := by
      have hz : ∀ j, raw8680 (permutation202 0) j = 0 := by decide +kernel
      have heq : raw8680step0 = (fun i j => raw8680 (permutation202 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8680 permutation202 hz
    injectiveMoment H raw8680step0 = injectiveMoment H raw8680step1 := by
      have heq : raw8680step1 = (fun i j => raw8680step0 (permutation128 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8680step0 permutation128 permutation3
    _ = injectiveMoment H node560 := by rfl

def raw8681 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![-3, 1, 2]]

def raw8681step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1], ![3, -1, -2]]

def raw8681step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1], ![3, -1, -2]]

def raw8681step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

theorem canonical8681 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8681 = injectiveMoment H node868 := by
  calc
    injectiveMoment H raw8681 = injectiveMoment H raw8681step0 := by
      have heq : raw8681step0 = -raw8681 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8681).symm
    injectiveMoment H raw8681step0 = injectiveMoment H raw8681step1 := by
      have hz : ∀ j, raw8681step0 (permutation202 0) j = 0 := by decide +kernel
      have heq : raw8681step1 = (fun i j => raw8681step0 (permutation202 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8681step0 permutation202 hz
    injectiveMoment H raw8681step1 = injectiveMoment H raw8681step2 := by
      have heq : raw8681step2 = (fun i j => raw8681step1 (permutation135 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8681step1 permutation135 permutation6
    _ = injectiveMoment H node868 := by rfl

def raw8682 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-2, 0, 2], ![0, 3, -3]]

def raw8682step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![-2, 0, 2], ![0, 3, -3]]

def raw8682step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0]]

theorem canonical8682 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8682 = injectiveMoment H node663 := by
  calc
    injectiveMoment H raw8682 = injectiveMoment H raw8682step0 := by
      have hz : ∀ j, raw8682 (permutation202 0) j = 0 := by decide +kernel
      have heq : raw8682step0 = (fun i j => raw8682 (permutation202 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8682 permutation202 hz
    injectiveMoment H raw8682step0 = injectiveMoment H raw8682step1 := by
      have heq : raw8682step1 = (fun i j => raw8682step0 (permutation108 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8682step0 permutation108 permutation3
    _ = injectiveMoment H node663 := by rfl

def raw8683 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![-3, 0, 3], ![1, 2, -3]]

def raw8683step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![3, 0, -3], ![-1, -2, 3]]

def raw8683step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![3, 0, -3], ![-1, -2, 3]]

def raw8683step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1]]

theorem canonical8683 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8683 = injectiveMoment H node563 := by
  calc
    injectiveMoment H raw8683 = injectiveMoment H raw8683step0 := by
      have heq : raw8683step0 = -raw8683 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8683).symm
    injectiveMoment H raw8683step0 = injectiveMoment H raw8683step1 := by
      have hz : ∀ j, raw8683step0 (permutation202 0) j = 0 := by decide +kernel
      have heq : raw8683step1 = (fun i j => raw8683step0 (permutation202 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8683step0 permutation202 hz
    injectiveMoment H raw8683step1 = injectiveMoment H raw8683step2 := by
      have heq : raw8683step2 = (fun i j => raw8683step1 (permutation144 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8683step1 permutation144 permutation5
    _ = injectiveMoment H node563 := by rfl

def raw8684 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![-2, -1, 3], ![0, 3, -3]]

def raw8684step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![-2, -1, 3], ![0, 3, -3]]

def raw8684step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1]]

theorem canonical8684 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8684 = injectiveMoment H node563 := by
  calc
    injectiveMoment H raw8684 = injectiveMoment H raw8684step0 := by
      have hz : ∀ j, raw8684 (permutation202 0) j = 0 := by decide +kernel
      have heq : raw8684step0 = (fun i j => raw8684 (permutation202 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8684 permutation202 hz
    injectiveMoment H raw8684step0 = injectiveMoment H raw8684step1 := by
      have heq : raw8684step1 = (fun i j => raw8684step0 (permutation108 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8684step0 permutation108 permutation3
    _ = injectiveMoment H node563 := by rfl

def raw8685 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![-1, -1, 2], ![-1, 3, -2]]

def raw8685step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![-1, -1, 2], ![-1, 3, -2]]

def raw8685step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

theorem canonical8685 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8685 = injectiveMoment H node872 := by
  calc
    injectiveMoment H raw8685 = injectiveMoment H raw8685step0 := by
      have hz : ∀ j, raw8685 (permutation202 0) j = 0 := by decide +kernel
      have heq : raw8685step0 = (fun i j => raw8685 (permutation202 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8685 permutation202 hz
    injectiveMoment H raw8685step0 = injectiveMoment H raw8685step1 := by
      have heq : raw8685step1 = (fun i j => raw8685step0 (permutation146 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8685step0 permutation146 permutation4
    _ = injectiveMoment H node872 := by rfl

def raw8686 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![-3, 2, 1]]

def raw8686step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![3, -2, -1]]

def raw8686step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![3, -2, -1]]

def raw8686step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

theorem canonical8686 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8686 = injectiveMoment H node570 := by
  calc
    injectiveMoment H raw8686 = injectiveMoment H raw8686step0 := by
      have heq : raw8686step0 = -raw8686 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8686).symm
    injectiveMoment H raw8686step0 = injectiveMoment H raw8686step1 := by
      have hz : ∀ j, raw8686step0 (permutation202 0) j = 0 := by decide +kernel
      have heq : raw8686step1 = (fun i j => raw8686step0 (permutation202 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8686step0 permutation202 hz
    injectiveMoment H raw8686step1 = injectiveMoment H raw8686step2 := by
      have heq : raw8686step2 = (fun i j => raw8686step1 (permutation143 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8686step1 permutation143 permutation6
    _ = injectiveMoment H node570 := by rfl

def raw8687 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![-3, 1, 2]]

def raw8687step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2], ![3, -1, -2]]

def raw8687step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2], ![3, -1, -2]]

def raw8687step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

theorem canonical8687 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8687 = injectiveMoment H node872 := by
  calc
    injectiveMoment H raw8687 = injectiveMoment H raw8687step0 := by
      have heq : raw8687step0 = -raw8687 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8687).symm
    injectiveMoment H raw8687step0 = injectiveMoment H raw8687step1 := by
      have hz : ∀ j, raw8687step0 (permutation202 0) j = 0 := by decide +kernel
      have heq : raw8687step1 = (fun i j => raw8687step0 (permutation202 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8687step0 permutation202 hz
    injectiveMoment H raw8687step1 = injectiveMoment H raw8687step2 := by
      have heq : raw8687step2 = (fun i j => raw8687step1 (permutation149 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8687step1 permutation149 permutation6
    _ = injectiveMoment H node872 := by rfl

def raw8688 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![-2, 0, 2], ![-1, 2, -1], ![2, -1, -1]]

def raw8688step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2], ![1, -2, 1], ![-2, 1, 1]]

def raw8688step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-1, 0, 1], ![2, 0, -2], ![1, -2, 1], ![-2, 1, 1]]

def raw8688step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

theorem canonical8688 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8688 = injectiveMoment H node705 := by
  calc
    injectiveMoment H raw8688 = injectiveMoment H raw8688step0 := by
      have heq : raw8688step0 = -raw8688 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8688).symm
    injectiveMoment H raw8688step0 = injectiveMoment H raw8688step1 := by
      have hz : ∀ j, raw8688step0 (permutation202 0) j = 0 := by decide +kernel
      have heq : raw8688step1 = (fun i j => raw8688step0 (permutation202 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8688step0 permutation202 hz
    injectiveMoment H raw8688step1 = injectiveMoment H raw8688step2 := by
      have heq : raw8688step2 = (fun i j => raw8688step1 (permutation118 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8688step1 permutation118 permutation6
    _ = injectiveMoment H node705 := by rfl

def raw8689 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![-2, 2, 0], ![-1, -1, 2], ![2, 0, -2]]

def raw8689step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![0, 0, 0], ![-1, 0, 1], ![2, -2, 0], ![1, 1, -2], ![-2, 0, 2]]

def raw8689step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-1, 0, 1], ![2, -2, 0], ![1, 1, -2], ![-2, 0, 2]]

def raw8689step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0]]

theorem canonical8689 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8689 = injectiveMoment H node670 := by
  calc
    injectiveMoment H raw8689 = injectiveMoment H raw8689step0 := by
      have heq : raw8689step0 = -raw8689 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8689).symm
    injectiveMoment H raw8689step0 = injectiveMoment H raw8689step1 := by
      have hz : ∀ j, raw8689step0 (permutation202 0) j = 0 := by decide +kernel
      have heq : raw8689step1 = (fun i j => raw8689step0 (permutation202 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8689step0 permutation202 hz
    injectiveMoment H raw8689step1 = injectiveMoment H raw8689step2 := by
      have heq : raw8689step2 = (fun i j => raw8689step1 (permutation91 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8689step1 permutation91 permutation6
    _ = injectiveMoment H node670 := by rfl

def raw8690 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![-1, 2, -1], ![2, 0, -2], ![-2, -1, 3]]

def raw8690step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![0, 0, 0], ![-1, 0, 1], ![1, -2, 1], ![-2, 0, 2], ![2, 1, -3]]

def raw8690step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-1, 0, 1], ![1, -2, 1], ![-2, 0, 2], ![2, 1, -3]]

def raw8690step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 2, -3]]

theorem canonical8690 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8690 = injectiveMoment H node702 := by
  calc
    injectiveMoment H raw8690 = injectiveMoment H raw8690step0 := by
      have heq : raw8690step0 = -raw8690 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8690).symm
    injectiveMoment H raw8690step0 = injectiveMoment H raw8690step1 := by
      have hz : ∀ j, raw8690step0 (permutation202 0) j = 0 := by decide +kernel
      have heq : raw8690step1 = (fun i j => raw8690step0 (permutation202 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8690step0 permutation202 hz
    injectiveMoment H raw8690step1 = injectiveMoment H raw8690step2 := by
      have heq : raw8690step2 = (fun i j => raw8690step1 (permutation94 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8690step1 permutation94 permutation5
    _ = injectiveMoment H node702 := by rfl

def raw8691 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![-1, -2, 3], ![-1, 3, -2]]

def raw8691step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![-1, -2, 3], ![-1, 3, -2]]

def raw8691step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 3, -2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]

theorem canonical8691 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8691 = injectiveMoment H node876 := by
  calc
    injectiveMoment H raw8691 = injectiveMoment H raw8691step0 := by
      have hz : ∀ j, raw8691 (permutation202 0) j = 0 := by decide +kernel
      have heq : raw8691step0 = (fun i j => raw8691 (permutation202 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8691 permutation202 hz
    injectiveMoment H raw8691step0 = injectiveMoment H raw8691step1 := by
      have heq : raw8691step1 = (fun i j => raw8691step0 (permutation122 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8691step0 permutation122 permutation3
    _ = injectiveMoment H node876 := by rfl

def raw8692 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0]]

def raw8692step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1]]

theorem canonical8692 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8692 = injectiveMoment H node293 := by
  calc
    injectiveMoment H raw8692 = injectiveMoment H raw8692step0 := by
      have heq : raw8692step0 = (fun i j => raw8692 (permutation23 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8692 permutation23 permutation4
    _ = injectiveMoment H node293 := by rfl

def raw8693 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![-2, -1, 3], ![2, 1, -3]]

def raw8693step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]

theorem canonical8693 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8693 = injectiveMoment H node1858 := by
  calc
    injectiveMoment H raw8693 = injectiveMoment H raw8693step0 := by
      have heq : raw8693step0 = (fun i j => raw8693 (permutation283 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8693 permutation283 permutation3
    _ = injectiveMoment H node1858 := by rfl

def raw8694 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![-1, -2, 3], ![1, 2, -3]]

def raw8694step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 2, -3]]

theorem canonical8694 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8694 = injectiveMoment H node2465 := by
  calc
    injectiveMoment H raw8694 = injectiveMoment H raw8694step0 := by
      have heq : raw8694step0 = (fun i j => raw8694 (permutation283 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8694 permutation283 permutation3
    _ = injectiveMoment H node2465 := by rfl

def raw8695 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![-1, -1, 2]]

def raw8695step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

theorem canonical8695 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8695 = injectiveMoment H node2660 := by
  calc
    injectiveMoment H raw8695 = injectiveMoment H raw8695step0 := by
      have heq : raw8695step0 = (fun i j => raw8695 (permutation325 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8695 permutation325 permutation5
    _ = injectiveMoment H node2660 := by rfl

def raw8696 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![-1, -2, 3], ![0, 3, -3]]

def raw8696step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 3, -3], ![1, 0, -1]]

theorem canonical8696 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8696 = injectiveMoment H node2477 := by
  calc
    injectiveMoment H raw8696 = injectiveMoment H raw8696step0 := by
      have heq : raw8696step0 = (fun i j => raw8696 (permutation265 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8696 permutation265 permutation3
    _ = injectiveMoment H node2477 := by rfl

def raw8697 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![0, 0, 0]]

def raw8697step0 : Matrix (Fin 2) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1]]

def raw8697step1 : Matrix (Fin 2) (Fin 2) ℤ := ![![-1, 1], ![1, -1]]

theorem canonical8697 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8697 = injectiveMoment H node5 := by
  calc
    injectiveMoment H raw8697 = injectiveMoment H raw8697step0 := by
      have hz : ∀ j, raw8697 (permutation7 0) j = 0 := by decide +kernel
      have heq : raw8697step0 = (fun i j => raw8697 (permutation7 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8697 permutation7 hz
    injectiveMoment H raw8697step0 = injectiveMoment H raw8697step1 := by
      have hz : ∀ i, raw8697step0 i (permutation3 0) = 0 := by decide +kernel
      have heq : raw8697step1 = (fun i j => raw8697step0 i (permutation3 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8697step0 permutation3 hz
    _ = injectiveMoment H node5 := by rfl

def raw8698 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![0, 0, 0], ![-2, 1, 1], ![-1, -1, 2], ![3, 0, -3]]

def raw8698step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![-2, 1, 1], ![-1, -1, 2], ![3, 0, -3]]

def raw8698step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, 3, -3], ![1, -2, 1], ![1, 0, -1]]

theorem canonical8698 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8698 = injectiveMoment H node1138 := by
  calc
    injectiveMoment H raw8698 = injectiveMoment H raw8698step0 := by
      have hz : ∀ j, raw8698 (permutation221 0) j = 0 := by decide +kernel
      have heq : raw8698step0 = (fun i j => raw8698 (permutation221 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8698 permutation221 hz
    injectiveMoment H raw8698step0 = injectiveMoment H raw8698step1 := by
      have heq : raw8698step1 = (fun i j => raw8698step0 (permutation109 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8698step0 permutation109 permutation5
    _ = injectiveMoment H node1138 := by rfl

def raw8699 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![-3, 0, 3], ![2, 1, -3]]

def raw8699step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![0, -1, 1], ![0, 0, 0], ![-1, 1, 0], ![3, 0, -3], ![-2, -1, 3]]

def raw8699step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![3, 0, -3], ![-2, -1, 3]]

def raw8699step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 0, 1], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1]]

theorem canonical8699 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8699 = injectiveMoment H node864 := by
  calc
    injectiveMoment H raw8699 = injectiveMoment H raw8699step0 := by
      have heq : raw8699step0 = -raw8699 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8699).symm
    injectiveMoment H raw8699step0 = injectiveMoment H raw8699step1 := by
      have hz : ∀ j, raw8699step0 (permutation221 0) j = 0 := by decide +kernel
      have heq : raw8699step1 = (fun i j => raw8699step0 (permutation221 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8699step0 permutation221 hz
    injectiveMoment H raw8699step1 = injectiveMoment H raw8699step2 := by
      have heq : raw8699step2 = (fun i j => raw8699step1 (permutation138 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8699step1 permutation138 permutation5
    _ = injectiveMoment H node864 := by rfl

def raw8700 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![-2, -1, 3], ![1, 2, -3]]

def raw8700step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![-2, -1, 3], ![1, 2, -3]]

def raw8700step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 2, -3]]

theorem canonical8700 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8700 = injectiveMoment H node559 := by
  calc
    injectiveMoment H raw8700 = injectiveMoment H raw8700step0 := by
      have hz : ∀ j, raw8700 (permutation221 0) j = 0 := by decide +kernel
      have heq : raw8700step0 = (fun i j => raw8700 (permutation221 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8700 permutation221 hz
    injectiveMoment H raw8700step0 = injectiveMoment H raw8700step1 := by
      have heq : raw8700step1 = (fun i j => raw8700step0 (permutation104 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8700step0 permutation104 permutation3
    _ = injectiveMoment H node559 := by rfl

def raw8701 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![-2, 1, 1]]

def raw8701step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![-2, 1, 1]]

def raw8701step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

theorem canonical8701 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8701 = injectiveMoment H node711 := by
  calc
    injectiveMoment H raw8701 = injectiveMoment H raw8701step0 := by
      have hz : ∀ j, raw8701 (permutation221 0) j = 0 := by decide +kernel
      have heq : raw8701step0 = (fun i j => raw8701 (permutation221 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8701 permutation221 hz
    injectiveMoment H raw8701step0 = injectiveMoment H raw8701step1 := by
      have heq : raw8701step1 = (fun i j => raw8701step0 (permutation128 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8701step0 permutation128 permutation3
    _ = injectiveMoment H node711 := by rfl

def raw8702 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![-3, 1, 2]]

def raw8702step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![0, -1, 1], ![0, 0, 0], ![-1, 1, 0], ![-2, 0, 2], ![3, -1, -2]]

def raw8702step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2], ![3, -1, -2]]

def raw8702step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]

theorem canonical8702 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8702 = injectiveMoment H node869 := by
  calc
    injectiveMoment H raw8702 = injectiveMoment H raw8702step0 := by
      have heq : raw8702step0 = -raw8702 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8702).symm
    injectiveMoment H raw8702step0 = injectiveMoment H raw8702step1 := by
      have hz : ∀ j, raw8702step0 (permutation221 0) j = 0 := by decide +kernel
      have heq : raw8702step1 = (fun i j => raw8702step0 (permutation221 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8702step0 permutation221 hz
    injectiveMoment H raw8702step1 = injectiveMoment H raw8702step2 := by
      have heq : raw8702step2 = (fun i j => raw8702step1 (permutation137 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8702step1 permutation137 permutation6
    _ = injectiveMoment H node869 := by rfl

def raw8703 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![-2, 3, -1], ![1, -3, 2]]

def raw8703step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![-2, 3, -1], ![1, -3, 2]]

def raw8703step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 2, -3]]

theorem canonical8703 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8703 = injectiveMoment H node559 := by
  calc
    injectiveMoment H raw8703 = injectiveMoment H raw8703step0 := by
      have hz : ∀ j, raw8703 (permutation221 0) j = 0 := by decide +kernel
      have heq : raw8703step0 = (fun i j => raw8703 (permutation221 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8703 permutation221 hz
    injectiveMoment H raw8703step0 = injectiveMoment H raw8703step1 := by
      have heq : raw8703step1 = (fun i j => raw8703step0 (permutation110 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8703step0 permutation110 permutation4
    _ = injectiveMoment H node559 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
