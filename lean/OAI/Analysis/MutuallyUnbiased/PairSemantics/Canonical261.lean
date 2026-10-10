import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes0
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes12
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes14
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes15
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes17
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes18
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes19
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes20
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes21
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes42
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes43
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes44
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes45
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes48
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes51

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw8352 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, -1, 2, 0], ![0, 2, 1, -3], ![1, 0, -3, 2]]

def raw8352step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 1, 0], ![0, 2, -3, 1], ![1, 0, 2, -3]]

theorem canonical8352 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8352 = injectiveMoment H node1001 := by
  calc
    injectiveMoment H raw8352 = injectiveMoment H raw8352step0 := by
      have heq : raw8352step0 = (fun i j => raw8352 (permutation15 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8352 permutation15 permutation10
    _ = injectiveMoment H node1001 := by rfl

def raw8353 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, 0, -1, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![-1, -1, 2, 0], ![2, 1, 1, -4]]

def raw8353step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, 0, -1], ![1, 0, 1, -2], ![0, 0, 1, -1], ![0, -1, 1, 0], ![1, 1, -2, 0], ![-2, -1, -1, 4]]

def raw8353step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, 1, -2], ![1, 1, -2, 0]]

theorem canonical8353 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8353 = injectiveMoment H node2915 := by
  calc
    injectiveMoment H raw8353 = injectiveMoment H raw8353step0 := by
      have heq : raw8353step0 = -raw8353 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8353).symm
    injectiveMoment H raw8353step0 = injectiveMoment H raw8353step1 := by
      have heq : raw8353step1 = (fun i j => raw8353step0 (permutation383 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8353step0 permutation383 permutation9
    _ = injectiveMoment H node2915 := by rfl

def raw8354 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, 0, -1, 2], ![0, 0, -1, 1], ![1, -1, 0, 0], ![-1, 2, -1, 0], ![1, 0, 3, -4]]

def raw8354step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, 0, -1], ![1, 0, 1, -2], ![0, 0, 1, -1], ![-1, 1, 0, 0], ![1, -2, 1, 0], ![-1, 0, -3, 4]]

def raw8354step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, -1, -3, 4], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, 0, 0, -1]]

theorem canonical8354 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8354 = injectiveMoment H node3298 := by
  calc
    injectiveMoment H raw8354 = injectiveMoment H raw8354step0 := by
      have heq : raw8354step0 = -raw8354 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8354).symm
    injectiveMoment H raw8354step0 = injectiveMoment H raw8354step1 := by
      have heq : raw8354step1 = (fun i j => raw8354step0 (permutation301 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8354step0 permutation301 permutation15
    _ = injectiveMoment H node3298 := by rfl

def raw8355 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, 0, -1, 2], ![0, 0, 3, -3], ![0, 2, -2, 0], ![1, -1, 0, 0]]

def raw8355step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 0, 1], ![0, 0, 3, -3], ![0, 2, -2, 0], ![1, -1, 0, 0]]

theorem canonical8355 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8355 = injectiveMoment H node2722 := by
  calc
    injectiveMoment H raw8355 = injectiveMoment H raw8355step0 := by
      have heq : raw8355step0 = (fun i j => raw8355 (permutation57 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8355 permutation57 permutation9
    _ = injectiveMoment H node2722 := by rfl

def raw8356 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, 0, -1, 2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![-1, -1, 1, 1], ![2, 0, 2, -4]]

def raw8356step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, 0, -1], ![1, 0, 1, -2], ![0, -1, 1, 0], ![0, -1, 1, 0], ![1, 1, -1, -1], ![-2, 0, -2, 4]]

def raw8356step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -1, 1, 0], ![0, -1, 1, 0], ![0, 1, 0, -1], ![1, 0, 1, -2], ![1, 1, -1, -1]]

theorem canonical8356 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8356 = injectiveMoment H node3106 := by
  calc
    injectiveMoment H raw8356 = injectiveMoment H raw8356step0 := by
      have heq : raw8356step0 = -raw8356 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8356).symm
    injectiveMoment H raw8356step0 = injectiveMoment H raw8356step1 := by
      have heq : raw8356step1 = (fun i j => raw8356step0 (permutation363 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8356step0 permutation363 permutation9
    _ = injectiveMoment H node3106 := by rfl

def raw8357 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, 0, -1, 2], ![0, 2, -2, 0], ![1, -1, 3, -3]]

def raw8357step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, 0, 2, -1], ![0, -1, -2, 3], ![1, 2, 0, -3]]

def raw8357step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, 0, -1], ![1, 0, -2, 1], ![0, 1, 2, -3], ![-1, -2, 0, 3]]

def raw8357step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 1, 0, -1], ![0, 1, 2, -3], ![1, 0, -2, 1]]

theorem canonical8357 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8357 = injectiveMoment H node819 := by
  calc
    injectiveMoment H raw8357 = injectiveMoment H raw8357step0 := by
      have heq : raw8357step0 = raw8357.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw8357).symm
    injectiveMoment H raw8357step0 = injectiveMoment H raw8357step1 := by
      have heq : raw8357step1 = -raw8357step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8357step0).symm
    injectiveMoment H raw8357step1 = injectiveMoment H raw8357step2 := by
      have heq : raw8357step2 = (fun i j => raw8357step1 (permutation28 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8357step1 permutation28 permutation9
    _ = injectiveMoment H node819 := by rfl

def raw8358 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, 0, -1, 2], ![0, 2, 2, -4], ![1, -1, -1, 1]]

def raw8358step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, 0, 2, -1], ![0, -1, 2, -1], ![1, 2, -4, 1]]

def raw8358step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, 0, -1], ![1, 0, -2, 1], ![0, 1, -2, 1], ![-1, -2, 4, -1]]

def raw8358step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, 0, 1, -2]]

theorem canonical8358 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8358 = injectiveMoment H node786 := by
  calc
    injectiveMoment H raw8358 = injectiveMoment H raw8358step0 := by
      have heq : raw8358step0 = raw8358.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw8358).symm
    injectiveMoment H raw8358step0 = injectiveMoment H raw8358step1 := by
      have heq : raw8358step1 = -raw8358step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8358step0).symm
    injectiveMoment H raw8358step1 = injectiveMoment H raw8358step2 := by
      have heq : raw8358step2 = (fun i j => raw8358step1 (permutation28 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8358step1 permutation28 permutation10
    _ = injectiveMoment H node786 := by rfl

def raw8359 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, 0, 0, 1], ![0, 2, 1, -3], ![1, -1, -1, 1]]

def raw8359step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, 0, 2, -1], ![0, 0, 1, -1], ![1, 1, -3, 1]]

def raw8359step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, 0, -1], ![1, 0, -2, 1], ![0, 0, -1, 1], ![-1, -1, 3, -1]]

def raw8359step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 0, 1, -2]]

theorem canonical8359 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8359 = injectiveMoment H node969 := by
  calc
    injectiveMoment H raw8359 = injectiveMoment H raw8359step0 := by
      have heq : raw8359step0 = raw8359.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw8359).symm
    injectiveMoment H raw8359step0 = injectiveMoment H raw8359step1 := by
      have heq : raw8359step1 = -raw8359step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8359step0).symm
    injectiveMoment H raw8359step1 = injectiveMoment H raw8359step2 := by
      have heq : raw8359step2 = (fun i j => raw8359step1 (permutation31 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8359step1 permutation31 permutation10
    _ = injectiveMoment H node969 := by rfl

def raw8360 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, 0, 1, 0], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -1, -2, 2]]

def raw8360step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -1, 0, 1], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -1, -2, 2]]

theorem canonical8360 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8360 = injectiveMoment H node2814 := by
  calc
    injectiveMoment H raw8360 = injectiveMoment H raw8360step0 := by
      have heq : raw8360step0 = (fun i j => raw8360 (permutation57 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8360 permutation57 permutation9
    _ = injectiveMoment H node2814 := by rfl

def raw8361 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, 0, 1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1]]

def raw8361step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0]]

theorem canonical8361 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8361 = injectiveMoment H node1280 := by
  calc
    injectiveMoment H raw8361 = injectiveMoment H raw8361step0 := by
      have heq : raw8361step0 = (fun i j => raw8361 (permutation15 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8361 permutation15 permutation10
    _ = injectiveMoment H node1280 := by rfl

def raw8362 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, 0, 1, 0], ![0, 2, -3, 1], ![1, -1, 2, -2]]

def raw8362step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, 0, 2, -1], ![0, 1, -3, 2], ![1, 0, 1, -2]]

def raw8362step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, 0, -1], ![1, 0, -2, 1], ![0, -1, 3, -2], ![-1, 0, -1, 2]]

def raw8362step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 2, -1], ![0, 1, 1, -2], ![1, 0, -1, 0]]

theorem canonical8362 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8362 = injectiveMoment H node1207 := by
  calc
    injectiveMoment H raw8362 = injectiveMoment H raw8362step0 := by
      have heq : raw8362step0 = raw8362.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw8362).symm
    injectiveMoment H raw8362step0 = injectiveMoment H raw8362step1 := by
      have heq : raw8362step1 = -raw8362step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8362step0).symm
    injectiveMoment H raw8362step1 = injectiveMoment H raw8362step2 := by
      have heq : raw8362step2 = (fun i j => raw8362step1 (permutation26 i) (permutation16 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8362step1 permutation26 permutation16
    _ = injectiveMoment H node1207 := by rfl

def raw8363 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, 0, 2, -1], ![0, 1, -2, 1], ![1, 0, 0, -1]]

def raw8363step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 1, 0], ![0, 1, 1, -2], ![1, 0, -1, 0]]

theorem canonical8363 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8363 = injectiveMoment H node1242 := by
  calc
    injectiveMoment H raw8363 = injectiveMoment H raw8363step0 := by
      have heq : raw8363step0 = (fun i j => raw8363 (permutation15 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8363 permutation15 permutation10
    _ = injectiveMoment H node1242 := by rfl

def raw8364 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, 0, 2, -1], ![0, 1, -1, 0], ![1, 0, -1, 0]]

def raw8364step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 0, 0, -1]]

theorem canonical8364 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8364 = injectiveMoment H node1048 := by
  calc
    injectiveMoment H raw8364 = injectiveMoment H raw8364step0 := by
      have heq : raw8364step0 = (fun i j => raw8364 (permutation17 i) (permutation13 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8364 permutation17 permutation13
    _ = injectiveMoment H node1048 := by rfl

def raw8365 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, 0, 2, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, -2, 2]]

def raw8365step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -1, 0, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, -2, 2]]

theorem canonical8365 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8365 = injectiveMoment H node2830 := by
  calc
    injectiveMoment H raw8365 = injectiveMoment H raw8365step0 := by
      have heq : raw8365step0 = (fun i j => raw8365 (permutation57 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8365 permutation57 permutation9
    _ = injectiveMoment H node2830 := by rfl

def raw8366 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, 0, 2, -1], ![0, 2, -3, 1], ![1, -1, 1, -1]]

def raw8366step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, -1, -1, 1]]

theorem canonical8366 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8366 = injectiveMoment H node1081 := by
  calc
    injectiveMoment H raw8366 = injectiveMoment H raw8366step0 := by
      have heq : raw8366step0 = (fun i j => raw8366 (permutation15 i) (permutation13 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8366 permutation15 permutation13
    _ = injectiveMoment H node1081 := by rfl

def raw8367 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, 0, 2, -1], ![0, 2, -1, -1], ![1, -1, -1, 1]]

def raw8367step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 2, -1], ![0, 1, -1, 0], ![1, 1, -1, -1]]

theorem canonical8367 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8367 = injectiveMoment H node1006 := by
  calc
    injectiveMoment H raw8367 = injectiveMoment H raw8367step0 := by
      have heq : raw8367step0 = (fun i j => raw8367 (permutation17 i) (permutation13 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8367 permutation17 permutation13
    _ = injectiveMoment H node1006 := by rfl

def raw8368 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, 0, 2, -1], ![0, 2, 0, -2], ![1, -1, -2, 2]]

def raw8368step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -1, 0, 1], ![0, 2, 0, -2], ![1, -1, -2, 2]]

theorem canonical8368 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8368 = injectiveMoment H node1311 := by
  calc
    injectiveMoment H raw8368 = injectiveMoment H raw8368step0 := by
      have heq : raw8368step0 = (fun i j => raw8368 (permutation15 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8368 permutation15 permutation9
    _ = injectiveMoment H node1311 := by rfl

def raw8369 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, 0, 2, -1], ![0, 2, 1, -3], ![1, -1, -3, 3]]

def raw8369step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -1, 0, 1], ![0, 2, 1, -3], ![1, -1, -3, 3]]

theorem canonical8369 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8369 = injectiveMoment H node1312 := by
  calc
    injectiveMoment H raw8369 = injectiveMoment H raw8369step0 := by
      have heq : raw8369step0 = (fun i j => raw8369 (permutation15 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8369 permutation15 permutation9
    _ = injectiveMoment H node1312 := by rfl

def raw8370 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, 0, 3, -2], ![0, 2, -3, 1], ![1, -1, 0, 0]]

def raw8370step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, 0, 2, -1], ![0, 3, -3, 0], ![1, -2, 1, 0]]

def raw8370step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 3, -3], ![0, 1, -2, 1], ![1, 0, -1, 0]]

theorem canonical8370 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8370 = injectiveMoment H node1063 := by
  calc
    injectiveMoment H raw8370 = injectiveMoment H raw8370step0 := by
      have heq : raw8370step0 = raw8370.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw8370).symm
    injectiveMoment H raw8370step0 = injectiveMoment H raw8370step1 := by
      have heq : raw8370step1 = (fun i j => raw8370step0 (permutation18 i) (permutation27 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8370step0 permutation18 permutation27
    _ = injectiveMoment H node1063 := by rfl

def raw8371 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, 0, 3, -2], ![0, 2, -2, 0], ![1, -1, -1, 1]]

def raw8371step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, 1, -1, -1]]

theorem canonical8371 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8371 = injectiveMoment H node805 := by
  calc
    injectiveMoment H raw8371 = injectiveMoment H raw8371step0 := by
      have heq : raw8371step0 = (fun i j => raw8371 (permutation17 i) (permutation13 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8371 permutation17 permutation13
    _ = injectiveMoment H node805 := by rfl

def raw8372 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, 0, 3, -2], ![0, 2, 0, -2], ![1, -1, -3, 3]]

def raw8372step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 3, -2], ![0, -1, 0, 1], ![0, 2, 0, -2], ![1, -1, -3, 3]]

theorem canonical8372 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8372 = injectiveMoment H node1320 := by
  calc
    injectiveMoment H raw8372 = injectiveMoment H raw8372step0 := by
      have heq : raw8372step0 = (fun i j => raw8372 (permutation15 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8372 permutation15 permutation9
    _ = injectiveMoment H node1320 := by rfl

def raw8373 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, 1, -3, 3], ![0, 1, 2, -3], ![1, -1, 1, -1]]

def raw8373step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, 1, 1, -1], ![0, -3, 2, 1], ![1, 3, -3, -1]]

def raw8373step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 1, 0, -1], ![0, 1, 2, -3], ![1, -1, -3, 3]]

theorem canonical8373 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8373 = injectiveMoment H node1128 := by
  calc
    injectiveMoment H raw8373 = injectiveMoment H raw8373step0 := by
      have heq : raw8373step0 = raw8373.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw8373).symm
    injectiveMoment H raw8373step0 = injectiveMoment H raw8373step1 := by
      have heq : raw8373step1 = (fun i j => raw8373step0 (permutation15 i) (permutation14 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8373step0 permutation15 permutation14
    _ = injectiveMoment H node1128 := by rfl

def raw8374 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, 1, -3, 3], ![0, 1, 3, -4], ![1, -1, 0, 0]]

def raw8374step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, 1, 1, -1], ![0, -3, 3, 0], ![1, 3, -4, 0]]

def raw8374step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -3, 3], ![0, 1, -1, 0], ![1, 0, 3, -4]]

theorem canonical8374 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8374 = injectiveMoment H node1102 := by
  calc
    injectiveMoment H raw8374 = injectiveMoment H raw8374step0 := by
      have heq : raw8374step0 = raw8374.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw8374).symm
    injectiveMoment H raw8374step0 = injectiveMoment H raw8374step1 := by
      have heq : raw8374step1 = (fun i j => raw8374step0 (permutation17 i) (permutation13 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8374step0 permutation17 permutation13
    _ = injectiveMoment H node1102 := by rfl

def raw8375 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, 1, -1, 1], ![0, 1, -2, 1], ![1, -1, 3, -3]]

def raw8375step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, 1, 1, -1], ![0, -1, -2, 3], ![1, 1, 1, -3]]

def raw8375step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, 0, -1], ![1, -1, -1, 1], ![0, 1, 2, -3], ![-1, -1, -1, 3]]

def raw8375step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 1, -1], ![0, 2, 1, -3], ![1, -1, -1, 1]]

theorem canonical8375 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8375 = injectiveMoment H node972 := by
  calc
    injectiveMoment H raw8375 = injectiveMoment H raw8375step0 := by
      have heq : raw8375step0 = raw8375.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw8375).symm
    injectiveMoment H raw8375step0 = injectiveMoment H raw8375step1 := by
      have heq : raw8375step1 = -raw8375step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8375step0).symm
    injectiveMoment H raw8375step1 = injectiveMoment H raw8375step2 := by
      have heq : raw8375step2 = (fun i j => raw8375step1 (permutation28 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8375step1 permutation28 permutation11
    _ = injectiveMoment H node972 := by rfl

def raw8376 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, 1, -1, 1], ![0, 1, 2, -3], ![1, -1, -1, 1]]

def raw8376step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, 1, 1, -1], ![0, -1, 2, -1], ![1, 1, -3, 1]]

def raw8376step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, 0, -1], ![1, -1, -1, 1], ![0, 1, -2, 1], ![-1, -1, 3, -1]]

def raw8376step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 1, 0], ![0, 1, 1, -2], ![1, 1, -1, -1]]

theorem canonical8376 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8376 = injectiveMoment H node936 := by
  calc
    injectiveMoment H raw8376 = injectiveMoment H raw8376step0 := by
      have heq : raw8376step0 = raw8376.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw8376).symm
    injectiveMoment H raw8376step0 = injectiveMoment H raw8376step1 := by
      have heq : raw8376step1 = -raw8376step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8376step0).symm
    injectiveMoment H raw8376step1 = injectiveMoment H raw8376step2 := by
      have heq : raw8376step2 = (fun i j => raw8376step1 (permutation28 i) (permutation13 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8376step1 permutation28 permutation13
    _ = injectiveMoment H node936 := by rfl

def raw8377 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, 1, 1, -1], ![0, 1, 1, -2], ![1, -1, -2, 2]]

def raw8377step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, 1, -1], ![0, -1, 0, 1], ![0, 1, 1, -2], ![1, -1, -2, 2]]

theorem canonical8377 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8377 = injectiveMoment H node1362 := by
  calc
    injectiveMoment H raw8377 = injectiveMoment H raw8377step0 := by
      have heq : raw8377step0 = (fun i j => raw8377 (permutation15 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8377 permutation15 permutation9
    _ = injectiveMoment H node1362 := by rfl

def raw8378 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, -1, -2, 3], ![0, 2, 2, -4]]

def raw8378step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 0, 0], ![-1, -1, 2], ![0, -2, 2], ![1, 3, -4]]

def raw8378step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 0, 0], ![1, 1, -2], ![0, 2, -2], ![-1, -3, 4]]

def raw8378step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 1, -2], ![0, 2, -2], ![-1, -3, 4]]

def raw8378step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 2, -2], ![1, 1, -2]]

theorem canonical8378 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8378 = injectiveMoment H node52 := by
  calc
    injectiveMoment H raw8378 = injectiveMoment H raw8378step0 := by
      have heq : raw8378step0 = raw8378.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw8378).symm
    injectiveMoment H raw8378step0 = injectiveMoment H raw8378step1 := by
      have heq : raw8378step1 = -raw8378step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8378step0).symm
    injectiveMoment H raw8378step1 = injectiveMoment H raw8378step2 := by
      have hz : ∀ j, raw8378step1 (permutation9 0) j = 0 := by decide +kernel
      have heq : raw8378step2 = (fun i j => raw8378step1 (permutation9 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8378step1 permutation9 hz
    injectiveMoment H raw8378step2 = injectiveMoment H raw8378step3 := by
      have heq : raw8378step3 = (fun i j => raw8378step2 (permutation8 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8378step2 permutation8 permutation3
    _ = injectiveMoment H node52 := by rfl

def raw8379 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, -1, -1, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![-2, 0, 2, 0], ![2, 1, 1, -4]]

def raw8379step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 1, 1, -2], ![0, 0, 1, -1], ![0, -1, 1, 0], ![2, 0, -2, 0], ![-2, -1, -1, 4]]

def raw8379step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 1, -2], ![2, 0, -2, 0]]

theorem canonical8379 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8379 = injectiveMoment H node2912 := by
  calc
    injectiveMoment H raw8379 = injectiveMoment H raw8379step0 := by
      have heq : raw8379step0 = -raw8379 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8379).symm
    injectiveMoment H raw8379step0 = injectiveMoment H raw8379step1 := by
      have heq : raw8379step1 = (fun i j => raw8379step0 (permutation383 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8379step0 permutation383 permutation9
    _ = injectiveMoment H node2912 := by rfl

def raw8380 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, -1, -1, 2], ![0, 0, -1, 1], ![1, 0, -1, 0], ![-2, 0, 2, 0], ![1, 2, 1, -4]]

def raw8380step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 1, 1, -2], ![0, 0, 1, -1], ![-1, 0, 1, 0], ![2, 0, -2, 0], ![-1, -2, -1, 4]]

def raw8380step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, 0, 0, -1], ![1, 0, 1, -2]]

theorem canonical8380 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8380 = injectiveMoment H node2916 := by
  calc
    injectiveMoment H raw8380 = injectiveMoment H raw8380step0 := by
      have heq : raw8380step0 = -raw8380 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8380).symm
    injectiveMoment H raw8380step0 = injectiveMoment H raw8380step1 := by
      have heq : raw8380step1 = (fun i j => raw8380step0 (permutation387 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8380step0 permutation387 permutation15
    _ = injectiveMoment H node2916 := by rfl

def raw8381 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, -1, -1, 2], ![0, 0, -1, 1], ![1, 0, -1, 0], ![-2, 1, 1, 0], ![1, 1, 2, -4]]

def raw8381step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, -1, -1, 2], ![0, -1, 0, 1], ![0, 0, -1, 1], ![1, 0, -1, 0], ![1, 1, 2, -4]]

theorem canonical8381 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8381 = injectiveMoment H node3299 := by
  calc
    injectiveMoment H raw8381 = injectiveMoment H raw8381step0 := by
      have heq : raw8381step0 = (fun i j => raw8381 (permutation277 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8381 permutation277 permutation9
    _ = injectiveMoment H node3299 := by rfl

def raw8382 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, -1, -1, 2], ![0, 0, -1, 1], ![1, 0, -1, 0], ![-2, 2, 0, 0], ![1, 0, 3, -4]]

def raw8382step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 1, 1, -2], ![0, 0, 1, -1], ![-1, 0, 1, 0], ![2, -2, 0, 0], ![-1, 0, -3, 4]]

def raw8382step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 2, 0, 0], ![0, -1, -3, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![1, 0, 0, -1], ![1, 0, 1, -2]]

theorem canonical8382 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8382 = injectiveMoment H node3323 := by
  calc
    injectiveMoment H raw8382 = injectiveMoment H raw8382step0 := by
      have heq : raw8382step0 = -raw8382 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8382).symm
    injectiveMoment H raw8382step0 = injectiveMoment H raw8382step1 := by
      have heq : raw8382step1 = (fun i j => raw8382step0 (permutation307 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8382step0 permutation307 permutation15
    _ = injectiveMoment H node3323 := by rfl

def raw8383 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, -1, -1, 2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![-2, 0, 1, 1], ![2, 0, 2, -4]]

def raw8383step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 1, 1, -2], ![0, -1, 1, 0], ![0, -1, 1, 0], ![2, 0, -1, -1], ![-2, 0, -2, 4]]

def raw8383step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -1, 1, 0], ![0, -1, 1, 0], ![0, 1, 0, -1], ![0, 1, 1, -2], ![2, 0, -1, -1]]

theorem canonical8383 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8383 = injectiveMoment H node3105 := by
  calc
    injectiveMoment H raw8383 = injectiveMoment H raw8383step0 := by
      have heq : raw8383step0 = -raw8383 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8383).symm
    injectiveMoment H raw8383step0 = injectiveMoment H raw8383step1 := by
      have heq : raw8383step1 = (fun i j => raw8383step0 (permutation363 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8383step0 permutation363 permutation9
    _ = injectiveMoment H node3105 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
