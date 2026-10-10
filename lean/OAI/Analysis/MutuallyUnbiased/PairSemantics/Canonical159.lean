import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes0
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes1
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes3
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes4
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes5
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes9
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes11
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes14
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes19
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes33
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes34
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes36
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes44

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw5088 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 3, -2], ![0, -1, -1, 2], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, 0, 0, -1]]

def raw5088step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, -1, 2, -1], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 0, -1, 0]]

theorem canonical5088 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5088 = injectiveMoment H node2171 := by
  calc
    injectiveMoment H raw5088 = injectiveMoment H raw5088step0 := by
      have heq : raw5088step0 = (fun i j => raw5088 (permutation33 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5088 permutation33 permutation10
    _ = injectiveMoment H node2171 := by rfl

def raw5089 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 3, -2], ![0, -1, -1, 2], ![0, 1, 0, -1], ![1, -1, -2, 2], ![1, 0, 0, -1]]

theorem canonical5089 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5089 = injectiveMoment H node2327 := by
  rfl

def raw5090 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 3, -2], ![0, -1, -1, 2], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 0, -1, 0]]

def raw5090step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, -1, 2, -1], ![0, 1, -1, 0], ![1, -1, 1, -1], ![1, 0, 0, -1]]

theorem canonical5090 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5090 = injectiveMoment H node2169 := by
  calc
    injectiveMoment H raw5090 = injectiveMoment H raw5090step0 := by
      have heq : raw5090step0 = (fun i j => raw5090 (permutation33 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5090 permutation33 permutation10
    _ = injectiveMoment H node2169 := by rfl

def raw5091 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 3, -2], ![0, -1, -1, 2], ![1, -1, -2, 2], ![1, 1, 0, -2]]

theorem canonical5091 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5091 = injectiveMoment H node714 := by
  rfl

def raw5092 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 3, -2], ![0, -1, -1, 2], ![1, 0, -2, 1], ![1, 0, 0, -1]]

def raw5092step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, -1, 0, 0], ![3, -1, -2, 0], ![-2, 2, 1, -1]]

def raw5092step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, 1, 0, 0], ![-3, 1, 2, 0], ![2, -2, -1, 1]]

def raw5092step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 1, -1], ![0, 2, 1, -3], ![1, -1, -2, 2]]

theorem canonical5092 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw5092 = injectiveMoment H node1050 := by
  calc
    injectiveMoment H raw5092 = injectiveMoment H raw5092step0 := by
      have heq : raw5092step0 = raw5092.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5092).symm
    injectiveMoment H raw5092step0 = injectiveMoment H raw5092step1 := by
      have heq : raw5092step1 = -raw5092step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw5092step0).symm
    injectiveMoment H raw5092step1 = injectiveMoment H raw5092step2 := by
      have heq : raw5092step2 = (fun i j => raw5092step1 (permutation9 i) (permutation32 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5092step1 permutation9 permutation32
    _ = injectiveMoment H node1050 := by rfl

def raw5093 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 3, -2], ![0, 0, -3, 3], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw5093step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 0, -1, 0], ![3, -3, 0, 0], ![-2, 3, 0, -1]]

def raw5093step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, 0, 1, 0], ![-3, 3, 0, 0], ![2, -3, 0, 1]]

def raw5093step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 3, -3], ![0, 1, -3, 2], ![1, 0, 0, -1]]

theorem canonical5093 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw5093 = injectiveMoment H node1062 := by
  calc
    injectiveMoment H raw5093 = injectiveMoment H raw5093step0 := by
      have heq : raw5093step0 = raw5093.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5093).symm
    injectiveMoment H raw5093step0 = injectiveMoment H raw5093step1 := by
      have heq : raw5093step1 = -raw5093step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw5093step0).symm
    injectiveMoment H raw5093step1 = injectiveMoment H raw5093step2 := by
      have heq : raw5093step2 = (fun i j => raw5093step1 (permutation12 i) (permutation26 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5093step1 permutation12 permutation26
    _ = injectiveMoment H node1062 := by rfl

def raw5094 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 3, -2], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, -2, -1, 2], ![1, 0, 0, -1]]

def raw5094step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, -2, 3, -2], ![1, 0, 0, -1]]

theorem canonical5094 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5094 = injectiveMoment H node2216 := by
  calc
    injectiveMoment H raw5094 = injectiveMoment H raw5094step0 := by
      have heq : raw5094step0 = (fun i j => raw5094 (permutation114 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5094 permutation114 permutation15
    _ = injectiveMoment H node2216 := by rfl

def raw5095 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 3, -2], ![0, 0, -2, 2], ![1, -2, -1, 2], ![1, 1, 0, -2]]

def raw5095step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 0, -2, 1], ![3, -2, -1, 0], ![-2, 2, 2, -2]]

def raw5095step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -2, 1], ![0, 1, 1, -2], ![2, -2, 2, -2]]

theorem canonical5095 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5095 = injectiveMoment H node593 := by
  calc
    injectiveMoment H raw5095 = injectiveMoment H raw5095step0 := by
      have heq : raw5095step0 = raw5095.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5095).symm
    injectiveMoment H raw5095step0 = injectiveMoment H raw5095step1 := by
      have heq : raw5095step1 = (fun i j => raw5095step0 (permutation23 i) (permutation20 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5095step0 permutation23 permutation20
    _ = injectiveMoment H node593 := by rfl

def raw5096 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 3, -2], ![0, 0, -2, 2], ![1, -1, -1, 1], ![1, 0, 0, -1]]

def raw5096step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 0, -1, 0], ![3, -2, -1, 0], ![-2, 2, 1, -1]]

def raw5096step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, 0, 1, 0], ![-3, 2, 1, 0], ![2, -2, -1, 1]]

def raw5096step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, 0, -1], ![0, 1, 2, -3], ![1, -1, -2, 2]]

theorem canonical5096 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw5096 = injectiveMoment H node1083 := by
  calc
    injectiveMoment H raw5096 = injectiveMoment H raw5096step0 := by
      have heq : raw5096step0 = raw5096.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5096).symm
    injectiveMoment H raw5096step0 = injectiveMoment H raw5096step1 := by
      have heq : raw5096step1 = -raw5096step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw5096step0).symm
    injectiveMoment H raw5096step1 = injectiveMoment H raw5096step2 := by
      have heq : raw5096step2 = (fun i j => raw5096step1 (permutation9 i) (permutation32 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5096step1 permutation9 permutation32
    _ = injectiveMoment H node1083 := by rfl

def raw5097 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 3, -2], ![0, 0, -1, 1], ![0, 0, -2, 2], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw5097step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 1, 0, 0], ![0, 0, -2, 2], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -2, 3, -2]]

theorem canonical5097 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5097 = injectiveMoment H node2850 := by
  calc
    injectiveMoment H raw5097 = injectiveMoment H raw5097step0 := by
      have heq : raw5097step0 = (fun i j => raw5097 (permutation119 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5097 permutation119 permutation15
    _ = injectiveMoment H node2850 := by rfl

def raw5098 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 3, -2], ![0, 0, -1, 1], ![1, -1, -2, 2], ![1, 0, 0, -1]]

def raw5098step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 0, -1, 0], ![3, -1, -2, 0], ![-2, 1, 2, -1]]

def raw5098step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 0, -1, 1], ![0, 1, 1, -2], ![1, -1, 2, -2]]

theorem canonical5098 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5098 = injectiveMoment H node1216 := by
  calc
    injectiveMoment H raw5098 = injectiveMoment H raw5098step0 := by
      have heq : raw5098step0 = raw5098.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5098).symm
    injectiveMoment H raw5098step0 = injectiveMoment H raw5098step1 := by
      have heq : raw5098step1 = (fun i j => raw5098step0 (permutation23 i) (permutation20 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5098step0 permutation23 permutation20
    _ = injectiveMoment H node1216 := by rfl

def raw5099 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 3, -2], ![0, 1, 0, -1], ![1, -2, -3, 4], ![1, 0, 0, -1]]

def raw5099step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 1, -2, 0], ![3, 0, -3, 0], ![-2, -1, 4, -1]]

def raw5099step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 3, -3], ![0, 1, -2, 1], ![1, 0, 1, -2]]

theorem canonical5099 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5099 = injectiveMoment H node918 := by
  calc
    injectiveMoment H raw5099 = injectiveMoment H raw5099step0 := by
      have heq : raw5099step0 = raw5099.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5099).symm
    injectiveMoment H raw5099step0 = injectiveMoment H raw5099step1 := by
      have heq : raw5099step1 = (fun i j => raw5099step0 (permutation31 i) (permutation19 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5099step0 permutation31 permutation19
    _ = injectiveMoment H node918 := by rfl

def raw5100 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 3, -2], ![1, -2, -1, 2], ![0, 0, -2, 2], ![1, 1, 0, -2]]

def raw5100step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![1, -2, 0, 1], ![3, -1, -2, 0], ![-2, 2, 2, -2]]

def raw5100step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -2, 1], ![0, 1, 1, -2], ![2, -2, 2, -2]]

theorem canonical5100 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5100 = injectiveMoment H node593 := by
  calc
    injectiveMoment H raw5100 = injectiveMoment H raw5100step0 := by
      have heq : raw5100step0 = raw5100.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5100).symm
    injectiveMoment H raw5100step0 = injectiveMoment H raw5100step1 := by
      have heq : raw5100step1 = (fun i j => raw5100step0 (permutation23 i) (permutation26 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5100step0 permutation23 permutation26
    _ = injectiveMoment H node593 := by rfl

def raw5101 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-3, 3], ![1, -1], ![2, -2], ![2, -2]]

def raw5101step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-2, 2], ![1, -1], ![2, -2], ![2, -2]]

theorem canonical5101 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5101 = injectiveMoment H node117 := by
  calc
    injectiveMoment H raw5101 = injectiveMoment H raw5101step0 := by
      have heq : raw5101step0 = (fun i j => raw5101 (permutation57 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5101 permutation57 permutation1
    _ = injectiveMoment H node117 := by rfl

def raw5102 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![-1, 1], ![1, -1], ![2, -2], ![2, -2]]

theorem canonical5102 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5102 = injectiveMoment H node715 := by
  rfl

def raw5103 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![-1, 1], ![2, -2], ![1, -1], ![2, -2]]

def raw5103step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![-1, 1], ![1, -1], ![2, -2], ![2, -2]]

theorem canonical5103 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5103 = injectiveMoment H node715 := by
  calc
    injectiveMoment H raw5103 = injectiveMoment H raw5103step0 := by
      have heq : raw5103step0 = (fun i j => raw5103 (permutation153 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5103 permutation153 permutation1
    _ = injectiveMoment H node715 := by rfl

def raw5104 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![0, 0], ![0, 0], ![2, -2], ![2, -2]]

def raw5104step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![0, 0], ![2, -2], ![2, -2]]

def raw5104step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![2, -2], ![2, -2]]

theorem canonical5104 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5104 = injectiveMoment H node45 := by
  calc
    injectiveMoment H raw5104 = injectiveMoment H raw5104step0 := by
      have hz : ∀ j, raw5104 (permutation241 0) j = 0 := by decide +kernel
      have heq : raw5104step0 = (fun i j => raw5104 (permutation241 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5104 permutation241 hz
    injectiveMoment H raw5104step0 = injectiveMoment H raw5104step1 := by
      have hz : ∀ j, raw5104step0 (permutation80 0) j = 0 := by decide +kernel
      have heq : raw5104step1 = (fun i j => raw5104step0 (permutation80 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5104step0 permutation80 hz
    _ = injectiveMoment H node45 := by rfl

def raw5105 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![0, 0], ![1, -1], ![1, -1], ![2, -2]]

def raw5105step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![1, -1], ![1, -1], ![2, -2]]

theorem canonical5105 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5105 = injectiveMoment H node231 := by
  calc
    injectiveMoment H raw5105 = injectiveMoment H raw5105step0 := by
      have hz : ∀ j, raw5105 (permutation221 0) j = 0 := by decide +kernel
      have heq : raw5105step0 = (fun i j => raw5105 (permutation221 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5105 permutation221 hz
    _ = injectiveMoment H node231 := by rfl

def raw5106 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![0, 0], ![2, -2], ![2, -2]]

def raw5106step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![2, -2], ![2, -2]]

theorem canonical5106 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5106 = injectiveMoment H node45 := by
  calc
    injectiveMoment H raw5106 = injectiveMoment H raw5106step0 := by
      have hz : ∀ j, raw5106 (permutation80 0) j = 0 := by decide +kernel
      have heq : raw5106step0 = (fun i j => raw5106 (permutation80 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5106 permutation80 hz
    _ = injectiveMoment H node45 := by rfl

def raw5107 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![1, -1], ![0, 0], ![1, -1], ![2, -2]]

def raw5107step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![1, -1], ![1, -1], ![2, -2]]

theorem canonical5107 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5107 = injectiveMoment H node231 := by
  calc
    injectiveMoment H raw5107 = injectiveMoment H raw5107step0 := by
      have hz : ∀ j, raw5107 (permutation241 0) j = 0 := by decide +kernel
      have heq : raw5107step0 = (fun i j => raw5107 (permutation241 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5107 permutation241 hz
    _ = injectiveMoment H node231 := by rfl

def raw5108 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![1, -1], ![1, -1], ![0, 0], ![2, -2]]

def raw5108step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![1, -1], ![1, -1], ![2, -2]]

theorem canonical5108 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5108 = injectiveMoment H node231 := by
  calc
    injectiveMoment H raw5108 = injectiveMoment H raw5108step0 := by
      have hz : ∀ j, raw5108 (permutation258 0) j = 0 := by decide +kernel
      have heq : raw5108step0 = (fun i j => raw5108 (permutation258 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5108 permutation258 hz
    _ = injectiveMoment H node231 := by rfl

def raw5109 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![1, -1], ![1, -1], ![1, -1], ![1, -1]]

theorem canonical5109 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5109 = injectiveMoment H node716 := by
  rfl

def raw5110 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![1, -1], ![1, -1], ![2, -2]]

theorem canonical5110 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5110 = injectiveMoment H node231 := by
  rfl

def raw5111 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![1, -1], ![2, -2], ![1, -1]]

def raw5111step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![1, -1], ![1, -1], ![2, -2]]

theorem canonical5111 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5111 = injectiveMoment H node231 := by
  calc
    injectiveMoment H raw5111 = injectiveMoment H raw5111step0 := by
      have heq : raw5111step0 = (fun i j => raw5111 (permutation34 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5111 permutation34 permutation1
    _ = injectiveMoment H node231 := by rfl

def raw5112 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![1, -1], ![3, -3]]

def raw5112step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![2, -2], ![2, -2]]

theorem canonical5112 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5112 = injectiveMoment H node25 := by
  calc
    injectiveMoment H raw5112 = injectiveMoment H raw5112step0 := by
      have heq : raw5112step0 = (fun i j => raw5112 (permutation31 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5112 permutation31 permutation2
    _ = injectiveMoment H node25 := by rfl

def raw5113 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![2, -2], ![0, 0], ![1, -1], ![1, -1]]

def raw5113step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![2, -2], ![1, -1], ![1, -1]]

def raw5113step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![1, -1], ![1, -1], ![2, -2]]

theorem canonical5113 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5113 = injectiveMoment H node231 := by
  calc
    injectiveMoment H raw5113 = injectiveMoment H raw5113step0 := by
      have hz : ∀ j, raw5113 (permutation241 0) j = 0 := by decide +kernel
      have heq : raw5113step0 = (fun i j => raw5113 (permutation241 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5113 permutation241 hz
    injectiveMoment H raw5113step0 = injectiveMoment H raw5113step1 := by
      have heq : raw5113step1 = (fun i j => raw5113step0 (permutation36 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5113step0 permutation36 permutation1
    _ = injectiveMoment H node231 := by rfl

def raw5114 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![2, -2], ![0, 0], ![2, -2]]

def raw5114step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![2, -2], ![2, -2]]

theorem canonical5114 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5114 = injectiveMoment H node45 := by
  calc
    injectiveMoment H raw5114 = injectiveMoment H raw5114step0 := by
      have hz : ∀ j, raw5114 (permutation104 0) j = 0 := by decide +kernel
      have heq : raw5114step0 = (fun i j => raw5114 (permutation104 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5114 permutation104 hz
    _ = injectiveMoment H node45 := by rfl

def raw5115 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![2, -2], ![1, -1], ![1, -1]]

def raw5115step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![1, -1], ![1, -1], ![2, -2]]

theorem canonical5115 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5115 = injectiveMoment H node231 := by
  calc
    injectiveMoment H raw5115 = injectiveMoment H raw5115step0 := by
      have heq : raw5115step0 = (fun i j => raw5115 (permutation36 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5115 permutation36 permutation1
    _ = injectiveMoment H node231 := by rfl

def raw5116 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![2, -2], ![2, -2]]

theorem canonical5116 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5116 = injectiveMoment H node45 := by
  rfl

def raw5117 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![-1, 1], ![-1, 1], ![1, -1], ![4, -4]]

def raw5117step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![-4, 4], ![-1, 1], ![1, -1], ![1, -1], ![1, -1], ![2, -2]]

theorem canonical5117 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5117 = injectiveMoment H node296 := by
  calc
    injectiveMoment H raw5117 = injectiveMoment H raw5117step0 := by
      have heq : raw5117step0 = (fun i j => raw5117 (permutation401 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5117 permutation401 permutation2
    _ = injectiveMoment H node296 := by rfl

def raw5118 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![-1, 1], ![-1, 1], ![2, -2], ![3, -3]]

def raw5118step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![-2, 2], ![1, -1], ![1, -1], ![1, -1], ![2, -2]]

theorem canonical5118 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5118 = injectiveMoment H node380 := by
  calc
    injectiveMoment H raw5118 = injectiveMoment H raw5118step0 := by
      have heq : raw5118step0 = (fun i j => raw5118 (permutation401 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5118 permutation401 permutation2
    _ = injectiveMoment H node380 := by rfl

def raw5119 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![-1, 1], ![0, 0], ![2, -2], ![2, -2]]

def raw5119step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![-1, 1], ![2, -2], ![2, -2]]

def raw5119step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![1, -1], ![1, -1], ![2, -2]]

theorem canonical5119 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5119 = injectiveMoment H node231 := by
  calc
    injectiveMoment H raw5119 = injectiveMoment H raw5119step0 := by
      have hz : ∀ j, raw5119 (permutation241 0) j = 0 := by decide +kernel
      have heq : raw5119step0 = (fun i j => raw5119 (permutation241 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5119 permutation241 hz
    injectiveMoment H raw5119step0 = injectiveMoment H raw5119step1 := by
      have heq : raw5119step1 = (fun i j => raw5119step0 (permutation125 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5119step0 permutation125 permutation2
    _ = injectiveMoment H node231 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
