import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes0
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes2
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes3
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes4
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes10
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes11
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes20
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes38
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes41
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes42
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes43
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes45
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes48
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes49

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw8064 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -2, 0, 2], ![-1, 1, -1, 1], ![0, 1, 2, -3], ![1, 0, -1, 0]]

def raw8064step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, 1, 1, 0], ![0, -1, 2, -1], ![2, 1, -3, 0]]

def raw8064step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, -2, 1], ![0, 1, 2, -3], ![1, -1, 0, 0]]

theorem canonical8064 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8064 = injectiveMoment H node1079 := by
  calc
    injectiveMoment H raw8064 = injectiveMoment H raw8064step0 := by
      have heq : raw8064step0 = raw8064.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw8064).symm
    injectiveMoment H raw8064step0 = injectiveMoment H raw8064step1 := by
      have heq : raw8064step1 = (fun i j => raw8064step0 (permutation24 i) (permutation29 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8064step0 permutation24 permutation29
    _ = injectiveMoment H node1079 := by rfl

def raw8065 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -2, 0, 2], ![-1, 1, -1, 1], ![0, 1, 3, -4], ![1, 0, -2, 1]]

def raw8065step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 2, 0, -2], ![1, -1, 1, -1], ![0, -1, -3, 4], ![-1, 0, 2, -1]]

def raw8065step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -1, -3, 4], ![0, 2, 0, -2], ![1, -1, 1, -1]]

theorem canonical8065 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8065 = injectiveMoment H node1306 := by
  calc
    injectiveMoment H raw8065 = injectiveMoment H raw8065step0 := by
      have heq : raw8065step0 = -raw8065 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8065).symm
    injectiveMoment H raw8065step0 = injectiveMoment H raw8065step1 := by
      have heq : raw8065step1 = (fun i j => raw8065step0 (permutation31 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8065step0 permutation31 permutation9
    _ = injectiveMoment H node1306 := by rfl

def raw8066 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -2, 0, 2], ![-1, 1, 1, -1], ![0, 1, 1, -2], ![1, 0, -2, 1]]

def raw8066step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 2, 0, -2], ![1, -1, -1, 1], ![0, -1, -1, 2], ![-1, 0, 2, -1]]

def raw8066step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -1, -1, 2], ![0, 2, 0, -2], ![1, -1, -1, 1]]

theorem canonical8066 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8066 = injectiveMoment H node1309 := by
  calc
    injectiveMoment H raw8066 = injectiveMoment H raw8066step0 := by
      have heq : raw8066step0 = -raw8066 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8066).symm
    injectiveMoment H raw8066step0 = injectiveMoment H raw8066step1 := by
      have heq : raw8066step1 = (fun i j => raw8066step0 (permutation31 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8066step0 permutation31 permutation9
    _ = injectiveMoment H node1309 := by rfl

def raw8067 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -2, 0, 2], ![-1, 2, 2, -3], ![1, 0, -2, 1]]

def raw8067step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![-2, 2, 0], ![0, 2, -2], ![2, -3, 1]]

def raw8067step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 1, -1], ![2, -2, 0], ![0, -2, 2], ![-2, 3, -1]]

def raw8067step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 2, -2], ![2, 0, -2]]

theorem canonical8067 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8067 = injectiveMoment H node169 := by
  calc
    injectiveMoment H raw8067 = injectiveMoment H raw8067step0 := by
      have heq : raw8067step0 = raw8067.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw8067).symm
    injectiveMoment H raw8067step0 = injectiveMoment H raw8067step1 := by
      have heq : raw8067step1 = -raw8067step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8067step0).symm
    injectiveMoment H raw8067step1 = injectiveMoment H raw8067step2 := by
      have heq : raw8067step2 = (fun i j => raw8067step1 (permutation28 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8067step1 permutation28 permutation4
    _ = injectiveMoment H node169 := by rfl

def raw8068 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -2, 0, 2], ![-1, 2, 3, -4], ![1, 0, -3, 2]]

def raw8068step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![-2, 2, 0], ![0, 3, -3], ![2, -4, 2]]

def raw8068step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 1, -1], ![2, -2, 0], ![0, -3, 3], ![-2, 4, -2]]

def raw8068step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, -1, 1], ![0, 3, -3], ![2, 0, -2]]

theorem canonical8068 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8068 = injectiveMoment H node141 := by
  calc
    injectiveMoment H raw8068 = injectiveMoment H raw8068step0 := by
      have heq : raw8068step0 = raw8068.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw8068).symm
    injectiveMoment H raw8068step0 = injectiveMoment H raw8068step1 := by
      have heq : raw8068step1 = -raw8068step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8068step0).symm
    injectiveMoment H raw8068step1 = injectiveMoment H raw8068step2 := by
      have heq : raw8068step2 = (fun i j => raw8068step1 (permutation28 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8068step1 permutation28 permutation4
    _ = injectiveMoment H node141 := by rfl

def raw8069 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -2, 0, 2], ![0, 0, -2, 2], ![0, 2, 2, -4]]

def raw8069step0 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 2, 0, -2], ![0, 0, 2, -2], ![0, -2, -2, 4]]

def raw8069step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 0, -2], ![0, 2, -2], ![-2, -2, 4]]

def raw8069step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![2, 0, -2]]

theorem canonical8069 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8069 = injectiveMoment H node31 := by
  calc
    injectiveMoment H raw8069 = injectiveMoment H raw8069step0 := by
      have heq : raw8069step0 = -raw8069 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8069).symm
    injectiveMoment H raw8069step0 = injectiveMoment H raw8069step1 := by
      have hz : ∀ i, raw8069step0 i (permutation9 0) = 0 := by decide +kernel
      have heq : raw8069step1 = (fun i j => raw8069step0 i (permutation9 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8069step0 permutation9 hz
    injectiveMoment H raw8069step1 = injectiveMoment H raw8069step2 := by
      have heq : raw8069step2 = (fun i j => raw8069step1 (permutation8 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8069step1 permutation8 permutation3
    _ = injectiveMoment H node31 := by rfl

def raw8070 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, 0, 2], ![0, 0, -1, 1], ![-1, 1, -1, 1], ![0, 1, 3, -4], ![1, 0, -1, 0]]

def raw8070step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 2, 0, -2], ![0, 0, 1, -1], ![1, -1, 1, -1], ![0, -1, -3, 4], ![-1, 0, 1, 0]]

def raw8070step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -1, -3, 4], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -1, 1, -1]]

theorem canonical8070 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8070 = injectiveMoment H node2807 := by
  calc
    injectiveMoment H raw8070 = injectiveMoment H raw8070step0 := by
      have heq : raw8070step0 = -raw8070 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8070).symm
    injectiveMoment H raw8070step0 = injectiveMoment H raw8070step1 := by
      have heq : raw8070step1 = (fun i j => raw8070step0 (permutation147 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8070step0 permutation147 permutation9
    _ = injectiveMoment H node2807 := by rfl

def raw8071 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -2, 0, 2], ![0, 0, -1, 1], ![-1, 2, 2, -3], ![1, 0, -1, 0]]

def raw8071step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 0, 2, 0], ![0, -1, 2, -1], ![2, 1, -3, 0]]

def raw8071step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, 0, 2, -3]]

theorem canonical8071 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8071 = injectiveMoment H node1032 := by
  calc
    injectiveMoment H raw8071 = injectiveMoment H raw8071step0 := by
      have heq : raw8071step0 = raw8071.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw8071).symm
    injectiveMoment H raw8071step0 = injectiveMoment H raw8071step1 := by
      have heq : raw8071step1 = (fun i j => raw8071step0 (permutation23 i) (permutation19 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8071step0 permutation23 permutation19
    _ = injectiveMoment H node1032 := by rfl

def raw8072 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -2, 0, 2], ![0, 0, -1, 1], ![-1, 2, 3, -4], ![1, 0, -2, 1]]

def raw8072step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 0, 2, 0], ![0, -1, 3, -2], ![2, 1, -4, 1]]

def raw8072step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, 1, -1], ![2, 0, -2, 0], ![0, 1, -3, 2], ![-2, -1, 4, -1]]

def raw8072step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, -1, 1], ![0, 2, 0, -2], ![1, 0, 2, -3]]

theorem canonical8072 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8072 = injectiveMoment H node763 := by
  calc
    injectiveMoment H raw8072 = injectiveMoment H raw8072step0 := by
      have heq : raw8072step0 = raw8072.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw8072).symm
    injectiveMoment H raw8072step0 = injectiveMoment H raw8072step1 := by
      have heq : raw8072step1 = -raw8072step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8072step0).symm
    injectiveMoment H raw8072step1 = injectiveMoment H raw8072step2 := by
      have heq : raw8072step2 = (fun i j => raw8072step1 (permutation27 i) (permutation16 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8072step1 permutation27 permutation16
    _ = injectiveMoment H node763 := by rfl

def raw8073 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -2, 0, 2], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![-2, 0, 2, 0], ![2, 1, 1, -4]]

def raw8073step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 2, 0, -2], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, -1, 1, 0], ![2, 0, -2, 0], ![-2, -1, -1, 4]]

def raw8073step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, 0, -2], ![2, 0, -2, 0]]

theorem canonical8073 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8073 = injectiveMoment H node2904 := by
  calc
    injectiveMoment H raw8073 = injectiveMoment H raw8073step0 := by
      have heq : raw8073step0 = -raw8073 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8073).symm
    injectiveMoment H raw8073step0 = injectiveMoment H raw8073step1 := by
      have heq : raw8073step1 = (fun i j => raw8073step0 (permutation379 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8073step0 permutation379 permutation9
    _ = injectiveMoment H node2904 := by rfl

def raw8074 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -2, 0, 2], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, 0, -1, 0], ![-2, 0, 2, 0], ![1, 2, 1, -4]]

def raw8074step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 2, 0, -2], ![0, 0, 1, -1], ![0, 0, 1, -1], ![-1, 0, 1, 0], ![2, 0, -2, 0], ![-1, -2, -1, 4]]

def raw8074step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -2, 0], ![2, 0, 0, -2]]

theorem canonical8074 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8074 = injectiveMoment H node2902 := by
  calc
    injectiveMoment H raw8074 = injectiveMoment H raw8074step0 := by
      have heq : raw8074step0 = -raw8074 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8074).symm
    injectiveMoment H raw8074step0 = injectiveMoment H raw8074step1 := by
      have heq : raw8074step1 = (fun i j => raw8074step0 (permutation380 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8074step0 permutation380 permutation15
    _ = injectiveMoment H node2902 := by rfl

def raw8075 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -2, 0, 2], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, 0, -1, 0], ![-2, 1, 1, 0], ![1, 1, 2, -4]]

def raw8075step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -2, 1, 0], ![1, 1, 2, -4]]

theorem canonical8075 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8075 = injectiveMoment H node3179 := by
  calc
    injectiveMoment H raw8075 = injectiveMoment H raw8075step0 := by
      have heq : raw8075step0 = (fun i j => raw8075 (permutation151 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8075 permutation151 permutation15
    _ = injectiveMoment H node3179 := by rfl

def raw8076 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -2, 0, 2], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, 0, -1, 0], ![-2, 2, 0, 0], ![1, 0, 3, -4]]

def raw8076step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 3, -4], ![2, -2, 0, 0]]

theorem canonical8076 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8076 = injectiveMoment H node3178 := by
  calc
    injectiveMoment H raw8076 = injectiveMoment H raw8076step0 := by
      have heq : raw8076step0 = (fun i j => raw8076 (permutation152 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8076 permutation152 permutation15
    _ = injectiveMoment H node3178 := by rfl

def raw8077 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, 0, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![-1, 1, 3, -3], ![1, 0, -1, 0]]

def raw8077step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 2, 0, -2], ![0, 0, 1, -1], ![0, -1, 1, 0], ![1, -1, -3, 3], ![-1, 0, 1, 0]]

def raw8077step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 2, -2, 0], ![1, -1, 3, -3]]

theorem canonical8077 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8077 = injectiveMoment H node2754 := by
  calc
    injectiveMoment H raw8077 = injectiveMoment H raw8077step0 := by
      have heq : raw8077step0 = -raw8077 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8077).symm
    injectiveMoment H raw8077step0 = injectiveMoment H raw8077step1 := by
      have heq : raw8077step1 = (fun i j => raw8077step0 (permutation141 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8077step0 permutation141 permutation10
    _ = injectiveMoment H node2754 := by rfl

def raw8078 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -2, 0, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![-2, 0, 1, 1], ![2, 0, 2, -4]]

def raw8078step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 2, 0, -2], ![0, 0, 1, -1], ![0, -1, 1, 0], ![0, -1, 1, 0], ![2, 0, -1, -1], ![-2, 0, -2, 4]]

def raw8078step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -1, 1, 0], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 2, 0, -2], ![2, 0, -1, -1]]

theorem canonical8078 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8078 = injectiveMoment H node3102 := by
  calc
    injectiveMoment H raw8078 = injectiveMoment H raw8078step0 := by
      have heq : raw8078step0 = -raw8078 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8078).symm
    injectiveMoment H raw8078step0 = injectiveMoment H raw8078step1 := by
      have heq : raw8078step1 = (fun i j => raw8078step0 (permutation364 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8078step0 permutation364 permutation9
    _ = injectiveMoment H node3102 := by rfl

def raw8079 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, 0, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 3, -4], ![0, 0, -1, 1]]

def raw8079step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![1, -1, 0], ![1, 3, -4], ![0, -1, 1]]

def raw8079step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 3, -4]]

theorem canonical8079 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8079 = injectiveMoment H node653 := by
  calc
    injectiveMoment H raw8079 = injectiveMoment H raw8079step0 := by
      have hz : ∀ i, raw8079 i (permutation9 0) = 0 := by decide +kernel
      have heq : raw8079step0 = (fun i j => raw8079 i (permutation9 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8079 permutation9 hz
    injectiveMoment H raw8079step0 = injectiveMoment H raw8079step1 := by
      have heq : raw8079step1 = (fun i j => raw8079step0 (permutation37 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8079step0 permutation37 permutation3
    _ = injectiveMoment H node653 := by rfl

def raw8080 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -2, 0, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, 0, -1, 0], ![-2, 0, 1, 1], ![1, 1, 2, -4]]

def raw8080step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 1, 2, -4]]

theorem canonical8080 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8080 = injectiveMoment H node3151 := by
  calc
    injectiveMoment H raw8080 = injectiveMoment H raw8080step0 := by
      have heq : raw8080step0 = (fun i j => raw8080 (permutation183 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8080 permutation183 permutation15
    _ = injectiveMoment H node3151 := by rfl

def raw8081 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -2, 0, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, 0, -1, 0], ![-2, 1, 0, 1], ![1, 0, 3, -4]]

def raw8081step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, -2, 0, 1], ![1, 0, -1, 0]]

theorem canonical8081 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8081 = injectiveMoment H node3191 := by
  calc
    injectiveMoment H raw8081 = injectiveMoment H raw8081step0 := by
      have heq : raw8081step0 = (fun i j => raw8081 (permutation161 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8081 permutation161 permutation15
    _ = injectiveMoment H node3191 := by rfl

def raw8082 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -2, 0, 2], ![0, 0, -1, 1], ![0, 2, 2, -4], ![0, 0, -1, 1]]

def raw8082step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 2, 0, -2], ![0, 0, 1, -1], ![0, -2, -2, 4], ![0, 0, 1, -1]]

def raw8082step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![-2, -2, 4], ![0, 1, -1]]

def raw8082step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 1, -1], ![2, 0, -2]]

theorem canonical8082 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8082 = injectiveMoment H node145 := by
  calc
    injectiveMoment H raw8082 = injectiveMoment H raw8082step0 := by
      have heq : raw8082step0 = -raw8082 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8082).symm
    injectiveMoment H raw8082step0 = injectiveMoment H raw8082step1 := by
      have hz : ∀ i, raw8082step0 i (permutation9 0) = 0 := by decide +kernel
      have heq : raw8082step1 = (fun i j => raw8082step0 i (permutation9 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8082step0 permutation9 hz
    injectiveMoment H raw8082step1 = injectiveMoment H raw8082step2 := by
      have heq : raw8082step2 = (fun i j => raw8082step1 (permutation24 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8082step1 permutation24 permutation3
    _ = injectiveMoment H node145 := by rfl

def raw8083 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -2, 0, 2], ![0, 0, -1, 1], ![1, 0, -1, 0], ![1, 0, -1, 0], ![-2, 0, 1, 1], ![0, 2, 2, -4]]

def raw8083step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 2, 0, -2], ![0, 0, 1, -1], ![-1, 0, 1, 0], ![-1, 0, 1, 0], ![2, 0, -1, -1], ![0, -2, -2, 4]]

def raw8083step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -1, 1, 0], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 2, -1, -1], ![2, 0, 0, -2]]

theorem canonical8083 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8083 = injectiveMoment H node3101 := by
  calc
    injectiveMoment H raw8083 = injectiveMoment H raw8083step0 := by
      have heq : raw8083step0 = -raw8083 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8083).symm
    injectiveMoment H raw8083step0 = injectiveMoment H raw8083step1 := by
      have heq : raw8083step1 = (fun i j => raw8083step0 (permutation365 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8083step0 permutation365 permutation15
    _ = injectiveMoment H node3101 := by rfl

def raw8084 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -2, 0, 2], ![0, 0, -1, 1], ![1, 0, -1, 0], ![1, 0, -1, 0], ![-2, 1, 0, 1], ![0, 1, 3, -4]]

def raw8084step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -2, 0, 1], ![1, 0, 3, -4]]

theorem canonical8084 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8084 = injectiveMoment H node3185 := by
  calc
    injectiveMoment H raw8084 = injectiveMoment H raw8084step0 := by
      have heq : raw8084step0 = (fun i j => raw8084 (permutation151 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8084 permutation151 permutation15
    _ = injectiveMoment H node3185 := by rfl

def raw8085 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, 0, 2], ![0, 0, 1, -1], ![-1, 0, 1, 0], ![0, 2, -2, 0], ![1, 0, 0, -1]]

def raw8085step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 2, 0], ![0, 0, -1, 1], ![0, 2, 0, -2], ![1, 0, -1, 0]]

theorem canonical8085 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8085 = injectiveMoment H node2745 := by
  calc
    injectiveMoment H raw8085 = injectiveMoment H raw8085step0 := by
      have heq : raw8085step0 = (fun i j => raw8085 (permutation80 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8085 permutation80 permutation10
    _ = injectiveMoment H node2745 := by rfl

def raw8086 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -2, 0, 2], ![0, 0, 1, -1], ![-1, 2, 1, -2], ![1, 0, -2, 1]]

def raw8086step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 2, 0, -2], ![0, 0, -1, 1], ![1, -2, -1, 2], ![-1, 0, 2, -1]]

def raw8086step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, 0, -1, 1], ![0, 2, 0, -2], ![1, -2, -1, 2]]

theorem canonical8086 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8086 = injectiveMoment H node1316 := by
  calc
    injectiveMoment H raw8086 = injectiveMoment H raw8086step0 := by
      have heq : raw8086step0 = -raw8086 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8086).symm
    injectiveMoment H raw8086step0 = injectiveMoment H raw8086step1 := by
      have heq : raw8086step1 = (fun i j => raw8086step0 (permutation29 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8086step0 permutation29 permutation9
    _ = injectiveMoment H node1316 := by rfl

def raw8087 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, 0, 2], ![0, 0, 1, -1], ![0, 0, 1, -1], ![-1, 2, -2, 1], ![1, 0, 0, -1]]

def raw8087step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 2, 1], ![0, 0, -2, 2], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, 0, -1]]

theorem canonical8087 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8087 = injectiveMoment H node2453 := by
  calc
    injectiveMoment H raw8087 = injectiveMoment H raw8087step0 := by
      have heq : raw8087step0 = (fun i j => raw8087 (permutation104 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8087 permutation104 permutation11
    _ = injectiveMoment H node2453 := by rfl

def raw8088 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, 0, 2], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -2, 0], ![0, 0, 0, 0]]

def raw8088step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -2, 0, 2], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -2, 0]]

def raw8088step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]

theorem canonical8088 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8088 = injectiveMoment H node207 := by
  calc
    injectiveMoment H raw8088 = injectiveMoment H raw8088step0 := by
      have hz : ∀ j, raw8088 (permutation128 0) j = 0 := by decide +kernel
      have heq : raw8088step0 = (fun i j => raw8088 (permutation128 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8088 permutation128 hz
    injectiveMoment H raw8088step0 = injectiveMoment H raw8088step1 := by
      have hz : ∀ i, raw8088step0 i (permutation9 0) = 0 := by decide +kernel
      have heq : raw8088step1 = (fun i j => raw8088step0 i (permutation9 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8088step0 permutation9 hz
    _ = injectiveMoment H node207 := by rfl

def raw8089 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -2, 0, 2], ![0, 0, 1, -1], ![0, 2, 0, -2], ![0, 0, -1, 1]]

def raw8089step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![2, 0, -2], ![0, -1, 1]]

def raw8089step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1]]

theorem canonical8089 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8089 = injectiveMoment H node291 := by
  calc
    injectiveMoment H raw8089 = injectiveMoment H raw8089step0 := by
      have hz : ∀ i, raw8089 i (permutation9 0) = 0 := by decide +kernel
      have heq : raw8089step0 = (fun i j => raw8089 i (permutation9 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8089 permutation9 hz
    injectiveMoment H raw8089step0 = injectiveMoment H raw8089step1 := by
      have heq : raw8089step1 = (fun i j => raw8089step0 (permutation28 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8089step0 permutation28 permutation5
    _ = injectiveMoment H node291 := by rfl

def raw8090 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, 0, 2], ![0, 0, 2, -2], ![-1, 1, -1, 1], ![0, 1, -1, 0], ![1, 0, 0, -1]]

def raw8090step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, 1, 0], ![0, 0, -2, 2], ![0, 2, 0, -2], ![1, 0, 0, -1]]

theorem canonical8090 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8090 = injectiveMoment H node2633 := by
  calc
    injectiveMoment H raw8090 = injectiveMoment H raw8090step0 := by
      have heq : raw8090step0 = (fun i j => raw8090 (permutation92 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8090 permutation92 permutation11
    _ = injectiveMoment H node2633 := by rfl

def raw8091 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, 0, 2], ![0, 0, 2, -2], ![0, 1, -1, 0], ![-1, 1, -1, 1], ![1, 0, 0, -1]]

def raw8091step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, 1, 0], ![0, 0, -2, 2], ![0, 2, 0, -2], ![1, 0, 0, -1]]

theorem canonical8091 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8091 = injectiveMoment H node2633 := by
  calc
    injectiveMoment H raw8091 = injectiveMoment H raw8091step0 := by
      have heq : raw8091step0 = (fun i j => raw8091 (permutation116 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8091 permutation116 permutation11
    _ = injectiveMoment H node2633 := by rfl

def raw8092 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, 0, 2], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![0, 0, 0, 0]]

def raw8092step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -2, 0, 2], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, -1, 0]]

def raw8092step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]

def raw8092step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]

theorem canonical8092 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8092 = injectiveMoment H node207 := by
  calc
    injectiveMoment H raw8092 = injectiveMoment H raw8092step0 := by
      have hz : ∀ j, raw8092 (permutation128 0) j = 0 := by decide +kernel
      have heq : raw8092step0 = (fun i j => raw8092 (permutation128 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8092 permutation128 hz
    injectiveMoment H raw8092step0 = injectiveMoment H raw8092step1 := by
      have hz : ∀ i, raw8092step0 i (permutation9 0) = 0 := by decide +kernel
      have heq : raw8092step1 = (fun i j => raw8092step0 i (permutation9 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8092step0 permutation9 hz
    injectiveMoment H raw8092step1 = injectiveMoment H raw8092step2 := by
      have heq : raw8092step2 = (fun i j => raw8092step1 (permutation18 i) (permutation7 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8092step1 permutation18 permutation7
    _ = injectiveMoment H node207 := by rfl

def raw8093 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -2, 0, 2], ![0, 0, 2, -2], ![0, 2, -2, 0]]

def raw8093step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![2, -2, 0]]

theorem canonical8093 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8093 = injectiveMoment H node41 := by
  calc
    injectiveMoment H raw8093 = injectiveMoment H raw8093step0 := by
      have hz : ∀ i, raw8093 i (permutation9 0) = 0 := by decide +kernel
      have heq : raw8093step0 = (fun i j => raw8093 i (permutation9 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8093 permutation9 hz
    _ = injectiveMoment H node41 := by rfl

def raw8094 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, 0, 2], ![0, 0, 3, -3], ![-1, 1, -1, 1], ![0, 1, -1, 0], ![1, 0, -1, 0]]

def raw8094step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 2, 0, -2], ![0, 0, -3, 3], ![1, -1, 1, -1], ![0, -1, 1, 0], ![-1, 0, 1, 0]]

def raw8094step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, 0, 3, -3], ![0, 2, -2, 0], ![1, -1, -1, 1]]

theorem canonical8094 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8094 = injectiveMoment H node2764 := by
  calc
    injectiveMoment H raw8094 = injectiveMoment H raw8094step0 := by
      have heq : raw8094step0 = -raw8094 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8094).symm
    injectiveMoment H raw8094step0 = injectiveMoment H raw8094step1 := by
      have heq : raw8094step1 = (fun i j => raw8094step0 (permutation147 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8094step0 permutation147 permutation10
    _ = injectiveMoment H node2764 := by rfl

def raw8095 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, 0, 2], ![0, 0, 3, -3], ![0, 1, -1, 0], ![-1, 1, -1, 1], ![1, 0, -1, 0]]

def raw8095step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 2, 0, -2], ![0, 0, -3, 3], ![0, -1, 1, 0], ![1, -1, 1, -1], ![-1, 0, 1, 0]]

def raw8095step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, 0, 3, -3], ![0, 2, -2, 0], ![1, -1, -1, 1]]

theorem canonical8095 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8095 = injectiveMoment H node2764 := by
  calc
    injectiveMoment H raw8095 = injectiveMoment H raw8095step0 := by
      have heq : raw8095step0 = -raw8095 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8095).symm
    injectiveMoment H raw8095step0 = injectiveMoment H raw8095step1 := by
      have heq : raw8095step1 = (fun i j => raw8095step0 (permutation141 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8095step0 permutation141 permutation10
    _ = injectiveMoment H node2764 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
