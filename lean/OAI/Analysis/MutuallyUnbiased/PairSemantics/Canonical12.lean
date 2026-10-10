import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes1
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes2
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes3
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes5
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes8
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes9
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes10
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes21
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes22
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes29
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes32
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes33
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes38
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes41
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes43

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw384 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]

def raw384step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]

def raw384step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, 0, -2]]

theorem canonical384 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw384 = injectiveMoment H node2109 := by
  calc
    injectiveMoment H raw384 = injectiveMoment H raw384step0 := by
      have heq : raw384step0 = -raw384 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw384).symm
    injectiveMoment H raw384step0 = injectiveMoment H raw384step1 := by
      have heq : raw384step1 = (fun i j => raw384step0 (permutation202 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw384step0 permutation202 permutation6
    _ = injectiveMoment H node2109 := by rfl

def raw385 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]

def raw385step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, -1, 1], ![0, 3, -3], ![2, 0, -2]]

theorem canonical385 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw385 = injectiveMoment H node551 := by
  calc
    injectiveMoment H raw385 = injectiveMoment H raw385step0 := by
      have heq : raw385step0 = (fun i j => raw385 (permutation143 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw385 permutation143 permutation6
    _ = injectiveMoment H node551 := by rfl

def raw386 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]

def raw386step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2], ![-3, 3, 0]]

def raw386step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 3, -3], ![1, 0, -1], ![2, -1, -1]]

theorem canonical386 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw386 = injectiveMoment H node331 := by
  calc
    injectiveMoment H raw386 = injectiveMoment H raw386step0 := by
      have heq : raw386step0 = -raw386 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw386).symm
    injectiveMoment H raw386step0 = injectiveMoment H raw386step1 := by
      have heq : raw386step1 = (fun i j => raw386step0 (permutation37 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw386step0 permutation37 permutation8
    _ = injectiveMoment H node331 := by rfl

def raw387 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]

def raw387step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-1, 0, 1], ![-2, 2, 0], ![-2, 0, 2]]

def raw387step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![0, 1, -1], ![0, 2, -2], ![2, 0, -2]]

theorem canonical387 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw387 = injectiveMoment H node631 := by
  calc
    injectiveMoment H raw387 = injectiveMoment H raw387step0 := by
      have heq : raw387step0 = -raw387 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw387).symm
    injectiveMoment H raw387step0 = injectiveMoment H raw387step1 := by
      have heq : raw387step1 = (fun i j => raw387step0 (permutation58 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw387step0 permutation58 permutation6
    _ = injectiveMoment H node631 := by rfl

def raw388 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]

def raw388step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-1, 0, 1], ![-2, 1, 1], ![-2, 1, 1]]

def raw388step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![0, 1, -1], ![1, 1, -2], ![1, 1, -2]]

theorem canonical388 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw388 = injectiveMoment H node634 := by
  calc
    injectiveMoment H raw388 = injectiveMoment H raw388step0 := by
      have heq : raw388step0 = -raw388 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw388).symm
    injectiveMoment H raw388step0 = injectiveMoment H raw388step1 := by
      have heq : raw388step1 = (fun i j => raw388step0 (permutation57 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw388step0 permutation57 permutation6
    _ = injectiveMoment H node634 := by rfl

def raw389 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]

def raw389step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-1, -1, 2], ![-2, 2, 0], ![-2, 1, 1]]

def raw389step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]

theorem canonical389 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw389 = injectiveMoment H node329 := by
  calc
    injectiveMoment H raw389 = injectiveMoment H raw389step0 := by
      have heq : raw389step0 = -raw389 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw389).symm
    injectiveMoment H raw389step0 = injectiveMoment H raw389step1 := by
      have heq : raw389step1 = (fun i j => raw389step0 (permutation36 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw389step0 permutation36 permutation8
    _ = injectiveMoment H node329 := by rfl

def raw390 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, -2, 0], ![3, 0, -3]]

def raw390step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![0, 3, -3], ![2, 0, -2]]

theorem canonical390 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw390 = injectiveMoment H node192 := by
  calc
    injectiveMoment H raw390 = injectiveMoment H raw390step0 := by
      have heq : raw390step0 = (fun i j => raw390 (permutation25 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw390 permutation25 permutation6
    _ = injectiveMoment H node192 := by rfl

def raw391 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, -1, -1], ![3, -1, -2]]

def raw391step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-2, 1, 1], ![-3, 1, 2]]

def raw391step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![1, 1, -2], ![1, 2, -3]]

theorem canonical391 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw391 = injectiveMoment H node196 := by
  calc
    injectiveMoment H raw391 = injectiveMoment H raw391step0 := by
      have heq : raw391step0 = -raw391 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw391).symm
    injectiveMoment H raw391step0 = injectiveMoment H raw391step1 := by
      have heq : raw391step1 = (fun i j => raw391step0 (permutation15 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw391step0 permutation15 permutation6
    _ = injectiveMoment H node196 := by rfl

def raw392 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, 0, -2], ![3, -2, -1]]

def raw392step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 3, -3], ![2, 0, -2]]

theorem canonical392 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw392 = injectiveMoment H node163 := by
  calc
    injectiveMoment H raw392 = injectiveMoment H raw392step0 := by
      have heq : raw392step0 = (fun i j => raw392 (permutation31 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw392 permutation31 permutation6
    _ = injectiveMoment H node163 := by rfl

def raw393 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, 1, -3], ![3, -3, 0]]

def raw393step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-2, -1, 3], ![-3, 3, 0]]

def raw393step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 3, -3], ![3, -1, -2]]

theorem canonical393 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw393 = injectiveMoment H node91 := by
  calc
    injectiveMoment H raw393 = injectiveMoment H raw393step0 := by
      have heq : raw393step0 = -raw393 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw393).symm
    injectiveMoment H raw393step0 = injectiveMoment H raw393step1 := by
      have heq : raw393step1 = (fun i j => raw393step0 (permutation10 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw393step0 permutation10 permutation8
    _ = injectiveMoment H node91 := by rfl

def raw394 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]

def raw394step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![2, -3, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]

def raw394step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![2, 0, -2]]

theorem canonical394 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw394 = injectiveMoment H node1408 := by
  calc
    injectiveMoment H raw394 = injectiveMoment H raw394step0 := by
      have heq : raw394step0 = -raw394 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw394).symm
    injectiveMoment H raw394step0 = injectiveMoment H raw394step1 := by
      have heq : raw394step1 = (fun i j => raw394step0 (permutation171 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw394step0 permutation171 permutation8
    _ = injectiveMoment H node1408 := by rfl

def raw395 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]

def raw395step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -3, 1], ![-1, 1, 0], ![-1, 1, 0], ![-3, 1, 2]]

def raw395step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![2, 1, -3]]

theorem canonical395 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw395 = injectiveMoment H node342 := by
  calc
    injectiveMoment H raw395 = injectiveMoment H raw395step0 := by
      have heq : raw395step0 = -raw395 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw395).symm
    injectiveMoment H raw395step0 = injectiveMoment H raw395step1 := by
      have heq : raw395step1 = (fun i j => raw395step0 (permutation41 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw395step0 permutation41 permutation8
    _ = injectiveMoment H node342 := by rfl

def raw396 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]

def raw396step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![2, -3, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]

def raw396step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1]]

theorem canonical396 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw396 = injectiveMoment H node1412 := by
  calc
    injectiveMoment H raw396 = injectiveMoment H raw396step0 := by
      have heq : raw396step0 = -raw396 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw396).symm
    injectiveMoment H raw396step0 = injectiveMoment H raw396step1 := by
      have heq : raw396step1 = (fun i j => raw396step0 (permutation175 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw396step0 permutation175 permutation8
    _ = injectiveMoment H node1412 := by rfl

def raw397 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]

def raw397step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -3, 1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 2, 1]]

def raw397step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 2, -3]]

theorem canonical397 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw397 = injectiveMoment H node348 := by
  calc
    injectiveMoment H raw397 = injectiveMoment H raw397step0 := by
      have heq : raw397step0 = -raw397 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw397).symm
    injectiveMoment H raw397step0 = injectiveMoment H raw397step1 := by
      have heq : raw397step1 = (fun i j => raw397step0 (permutation39 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw397step0 permutation39 permutation8
    _ = injectiveMoment H node348 := by rfl

def raw398 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]

def raw398step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -3, 1], ![-1, 1, 0], ![-2, 2, 0], ![-2, 0, 2]]

def raw398step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -3, 2], ![2, 0, -2]]

theorem canonical398 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw398 = injectiveMoment H node344 := by
  calc
    injectiveMoment H raw398 = injectiveMoment H raw398step0 := by
      have heq : raw398step0 = -raw398 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw398).symm
    injectiveMoment H raw398step0 = injectiveMoment H raw398step1 := by
      have heq : raw398step1 = (fun i j => raw398step0 (permutation41 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw398step0 permutation41 permutation8
    _ = injectiveMoment H node344 := by rfl

def raw399 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]

def raw399step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 3, -3], ![3, -1, -2]]

theorem canonical399 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw399 = injectiveMoment H node333 := by
  calc
    injectiveMoment H raw399 = injectiveMoment H raw399step0 := by
      have heq : raw399step0 = (fun i j => raw399 (permutation143 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw399 permutation143 permutation6
    _ = injectiveMoment H node333 := by rfl

def raw400 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]

def raw400step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -3, 1], ![-1, 0, 1], ![-2, 2, 0], ![-2, 1, 1]]

def raw400step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -3, 2], ![1, 0, -1], ![1, 1, -2]]

theorem canonical400 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw400 = injectiveMoment H node350 := by
  calc
    injectiveMoment H raw400 = injectiveMoment H raw400step0 := by
      have heq : raw400step0 = -raw400 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw400).symm
    injectiveMoment H raw400step0 = injectiveMoment H raw400step1 := by
      have heq : raw400step1 = (fun i j => raw400step0 (permutation45 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw400step0 permutation45 permutation8
    _ = injectiveMoment H node350 := by rfl

def raw401 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![2, -2, 0], ![3, -1, -2]]

def raw401step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![2, -3, 1], ![-2, 2, 0], ![-3, 1, 2]]

def raw401step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -3, 2], ![2, 1, -3]]

theorem canonical401 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw401 = injectiveMoment H node96 := by
  calc
    injectiveMoment H raw401 = injectiveMoment H raw401step0 := by
      have heq : raw401step0 = -raw401 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw401).symm
    injectiveMoment H raw401step0 = injectiveMoment H raw401step1 := by
      have heq : raw401step1 = (fun i j => raw401step0 (permutation11 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw401step0 permutation11 permutation8
    _ = injectiveMoment H node96 := by rfl

def raw402 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![2, -1, -1], ![3, -2, -1]]

def raw402step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![2, -3, 1], ![-2, 1, 1], ![-3, 2, 1]]

def raw402step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -3, 2], ![1, 1, -2], ![1, 2, -3]]

theorem canonical402 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw402 = injectiveMoment H node100 := by
  calc
    injectiveMoment H raw402 = injectiveMoment H raw402step0 := by
      have heq : raw402step0 = -raw402 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw402).symm
    injectiveMoment H raw402step0 = injectiveMoment H raw402step1 := by
      have heq : raw402step1 = (fun i j => raw402step0 (permutation9 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw402step0 permutation9 permutation8
    _ = injectiveMoment H node100 := by rfl

def raw403 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]

def raw403step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0]]

theorem canonical403 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw403 = injectiveMoment H node2464 := by
  calc
    injectiveMoment H raw403 = injectiveMoment H raw403step0 := by
      have heq : raw403step0 = (fun i j => raw403 (permutation398 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw403 permutation398 permutation6
    _ = injectiveMoment H node2464 := by rfl

def raw404 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]

def raw404step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0]]

theorem canonical404 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw404 = injectiveMoment H node1887 := by
  calc
    injectiveMoment H raw404 = injectiveMoment H raw404step0 := by
      have heq : raw404step0 = (fun i j => raw404 (permutation398 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw404 permutation398 permutation6
    _ = injectiveMoment H node1887 := by rfl

def raw405 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]

def raw405step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 1, -1], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0]]

theorem canonical405 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw405 = injectiveMoment H node2122 := by
  calc
    injectiveMoment H raw405 = injectiveMoment H raw405step0 := by
      have heq : raw405step0 = (fun i j => raw405 (permutation298 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw405 permutation298 permutation6
    _ = injectiveMoment H node2122 := by rfl

def raw406 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]

def raw406step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 3, -3], ![1, -2, 1], ![1, -1, 0]]

theorem canonical406 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw406 = injectiveMoment H node575 := by
  calc
    injectiveMoment H raw406 = injectiveMoment H raw406step0 := by
      have heq : raw406step0 = (fun i j => raw406 (permutation134 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw406 permutation134 permutation6
    _ = injectiveMoment H node575 := by rfl

def raw407 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]

def raw407step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 3, -3], ![1, -3, 2], ![1, -1, 0]]

theorem canonical407 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw407 = injectiveMoment H node671 := by
  calc
    injectiveMoment H raw407 = injectiveMoment H raw407step0 := by
      have heq : raw407step0 = (fun i j => raw407 (permutation111 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw407 permutation111 permutation6
    _ = injectiveMoment H node671 := by rfl

def raw408 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]

def raw408step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 3, -3], ![2, -2, 0]]

theorem canonical408 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw408 = injectiveMoment H node557 := by
  calc
    injectiveMoment H raw408 = injectiveMoment H raw408step0 := by
      have heq : raw408step0 = (fun i j => raw408 (permutation147 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw408 permutation147 permutation6
    _ = injectiveMoment H node557 := by rfl

def raw409 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]

def raw409step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 1, -1], ![0, 3, -3], ![2, -2, 0]]

theorem canonical409 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw409 = injectiveMoment H node643 := by
  calc
    injectiveMoment H raw409 = injectiveMoment H raw409step0 := by
      have heq : raw409step0 = (fun i j => raw409 (permutation124 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw409 permutation124 permutation6
    _ = injectiveMoment H node643 := by rfl

def raw410 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]

def raw410step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, -3, 3], ![0, 3, -3], ![1, 0, -1], ![1, 0, -1]]

theorem canonical410 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw410 = injectiveMoment H node2787 := by
  calc
    injectiveMoment H raw410 = injectiveMoment H raw410step0 := by
      have heq : raw410step0 = (fun i j => raw410 (permutation252 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw410 permutation252 permutation6
    _ = injectiveMoment H node2787 := by rfl

def raw411 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]

def raw411step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 0, 1], ![0, -1, 1], ![0, 3, -3], ![1, 0, -1], ![1, 0, -1]]

theorem canonical411 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw411 = injectiveMoment H node2461 := by
  calc
    injectiveMoment H raw411 = injectiveMoment H raw411step0 := by
      have heq : raw411step0 = (fun i j => raw411 (permutation389 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw411 permutation389 permutation6
    _ = injectiveMoment H node2461 := by rfl

def raw412 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]

def raw412step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, -1, 1], ![0, 3, -3], ![1, 0, -1], ![1, 0, -1]]

theorem canonical412 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw412 = injectiveMoment H node1878 := by
  calc
    injectiveMoment H raw412 = injectiveMoment H raw412step0 := by
      have heq : raw412step0 = (fun i j => raw412 (permutation389 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw412 permutation389 permutation6
    _ = injectiveMoment H node1878 := by rfl

def raw413 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]

def raw413step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-3, 3, 0]]

def raw413step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 3, -3], ![1, 0, -1], ![2, -1, -1]]

theorem canonical413 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw413 = injectiveMoment H node1402 := by
  calc
    injectiveMoment H raw413 = injectiveMoment H raw413step0 := by
      have heq : raw413step0 = -raw413 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw413).symm
    injectiveMoment H raw413step0 = injectiveMoment H raw413step1 := by
      have heq : raw413step1 = (fun i j => raw413step0 (permutation155 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw413step0 permutation155 permutation8
    _ = injectiveMoment H node1402 := by rfl

def raw414 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]

def raw414step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, -1, 1], ![0, 3, -3], ![1, 0, -1], ![1, 0, -1]]

theorem canonical414 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw414 = injectiveMoment H node2116 := by
  calc
    injectiveMoment H raw414 = injectiveMoment H raw414step0 := by
      have heq : raw414step0 = (fun i j => raw414 (permutation303 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw414 permutation303 permutation6
    _ = injectiveMoment H node2116 := by rfl

def raw415 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]

def raw415step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![0, -1, 1], ![0, 3, -3], ![1, 0, -1], ![1, 0, -1]]

theorem canonical415 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw415 = injectiveMoment H node2649 := by
  calc
    injectiveMoment H raw415 = injectiveMoment H raw415step0 := by
      have heq : raw415step0 = (fun i j => raw415 (permutation303 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw415 permutation303 permutation6
    _ = injectiveMoment H node2649 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
