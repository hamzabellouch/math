import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes6
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes11
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes13
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes15
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes18
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes19
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes22
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes37

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw992 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 0, 2, -2], ![1, 0, 0, -1], ![1, 2, -1, -2]]

def raw992step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-2, 0, 0, 2], ![-1, 2, 0, -1], ![5, -2, -1, -2]]

def raw992step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -2, 5], ![0, 0, 2, -2], ![0, 2, -1, -1], ![1, 0, 1, -2]]

theorem canonical992 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw992 = injectiveMoment H node753 := by
  calc
    injectiveMoment H raw992 = injectiveMoment H raw992step0 := by
      have heq : raw992step0 = raw992.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw992).symm
    injectiveMoment H raw992step0 = injectiveMoment H raw992step1 := by
      have heq : raw992step1 = (fun i j => raw992step0 (permutation30 i) (permutation24 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw992step0 permutation30 permutation24
    _ = injectiveMoment H node753 := by rfl

def raw993 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 0, 2, -2], ![1, 1, -1, -1], ![1, 1, 0, -2]]

theorem canonical993 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw993 = injectiveMoment H node392 := by
  rfl

def raw994 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 0, 2, -2], ![1, 1, 0, -2], ![1, 1, -1, -1]]

def raw994step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 0, 2, -2], ![1, 1, -1, -1], ![1, 1, 0, -2]]

theorem canonical994 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw994 = injectiveMoment H node392 := by
  calc
    injectiveMoment H raw994 = injectiveMoment H raw994step0 := by
      have heq : raw994step0 = (fun i j => raw994 (permutation10 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw994 permutation10 permutation9
    _ = injectiveMoment H node392 := by rfl

def raw995 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 0, 2, -3]]

theorem canonical995 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw995 = injectiveMoment H node1450 := by
  rfl

def raw996 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, 1, -2], ![1, 0, 1, -2]]

theorem canonical996 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw996 = injectiveMoment H node1451 := by
  rfl

def raw997 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, 0, 2, -4]]

def raw997step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-2, 1, 1, 0], ![-1, -1, 0, 2], ![5, 0, -1, -4]]

def raw997step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![2, -1, -1, 0], ![1, 1, 0, -2], ![-5, 0, 1, 4]]

def raw997step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 1, -2, 1], ![1, 0, 4, -5]]

theorem canonical997 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw997 = injectiveMoment H node1030 := by
  calc
    injectiveMoment H raw997 = injectiveMoment H raw997step0 := by
      have heq : raw997step0 = raw997.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw997).symm
    injectiveMoment H raw997step0 = injectiveMoment H raw997step1 := by
      have heq : raw997step1 = -raw997step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw997step0).symm
    injectiveMoment H raw997step1 = injectiveMoment H raw997step2 := by
      have heq : raw997step2 = (fun i j => raw997step1 (permutation15 i) (permutation24 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw997step1 permutation15 permutation24
    _ = injectiveMoment H node1030 := by rfl

def raw998 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, 0, 0, -1], ![1, 0, 1, -2]]

theorem canonical998 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw998 = injectiveMoment H node1452 := by
  rfl

def raw999 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, 0, 1, -2], ![1, 0, 0, -1]]

def raw999step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, 0, 0, -1], ![1, 0, 1, -2]]

theorem canonical999 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw999 = injectiveMoment H node1452 := by
  calc
    injectiveMoment H raw999 = injectiveMoment H raw999step0 := by
      have heq : raw999step0 = (fun i j => raw999 (permutation34 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw999 permutation34 permutation9
    _ = injectiveMoment H node1452 := by rfl

def raw1000 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 1, -1, 0], ![0, 1, 1, -2], ![2, 0, 1, -3]]

def raw1000step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-2, 1, 1, 0], ![-1, -1, 1, 1], ![5, 0, -2, -3]]

def raw1000step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![2, -1, -1, 0], ![1, 1, -1, -1], ![-5, 0, 2, 3]]

def raw1000step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 2, 3, -5], ![1, -1, -1, 1]]

theorem canonical1000 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw1000 = injectiveMoment H node1038 := by
  calc
    injectiveMoment H raw1000 = injectiveMoment H raw1000step0 := by
      have heq : raw1000step0 = raw1000.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1000).symm
    injectiveMoment H raw1000step0 = injectiveMoment H raw1000step1 := by
      have heq : raw1000step1 = -raw1000step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw1000step0).symm
    injectiveMoment H raw1000step1 = injectiveMoment H raw1000step2 := by
      have heq : raw1000step2 = (fun i j => raw1000step1 (permutation16 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1000step1 permutation16 permutation18
    _ = injectiveMoment H node1038 := by rfl

def raw1001 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, 0, 0, -1], ![1, 0, 0, -1]]

theorem canonical1001 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1001 = injectiveMoment H node1453 := by
  rfl

def raw1002 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 1, -1, 0], ![0, 1, 2, -3], ![2, 0, 0, -2]]

def raw1002step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-2, 1, 1, 0], ![-1, -1, 2, 0], ![5, 0, -3, -2]]

def raw1002step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![2, -1, -1, 0], ![1, 1, -2, 0], ![-5, 0, 3, 2]]

def raw1002step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -2, 0, 2], ![0, 2, 3, -5], ![1, 0, -2, 1]]

theorem canonical1002 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw1002 = injectiveMoment H node1233 := by
  calc
    injectiveMoment H raw1002 = injectiveMoment H raw1002step0 := by
      have heq : raw1002step0 = raw1002.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1002).symm
    injectiveMoment H raw1002step0 = injectiveMoment H raw1002step1 := by
      have heq : raw1002step1 = -raw1002step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw1002step0).symm
    injectiveMoment H raw1002step1 = injectiveMoment H raw1002step2 := by
      have heq : raw1002step2 = (fun i j => raw1002step1 (permutation16 i) (permutation20 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1002step1 permutation16 permutation20
    _ = injectiveMoment H node1233 := by rfl

def raw1003 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 1, 2, -4]]

def raw1003step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-2, 1, 0, 1], ![-1, -1, 0, 2], ![5, 0, -1, -4]]

def raw1003step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -4, 5], ![0, -1, 2, -1], ![0, 1, 1, -2], ![1, 0, 1, -2]]

theorem canonical1003 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1003 = injectiveMoment H node1160 := by
  calc
    injectiveMoment H raw1003 = injectiveMoment H raw1003step0 := by
      have heq : raw1003step0 = raw1003.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1003).symm
    injectiveMoment H raw1003step0 = injectiveMoment H raw1003step1 := by
      have heq : raw1003step1 = (fun i j => raw1003step0 (permutation32 i) (permutation24 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1003step0 permutation32 permutation24
    _ = injectiveMoment H node1160 := by rfl

def raw1004 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 1, -1, 0], ![1, 0, 1, -2], ![1, 1, 1, -3]]

def raw1004step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-2, 1, 0, 1], ![-1, -1, 1, 1], ![5, 0, -2, -3]]

def raw1004step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![2, -1, 0, -1], ![1, 1, -1, -1], ![-5, 0, 2, 3]]

def raw1004step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, -1, 2], ![0, 2, 3, -5], ![1, -1, -1, 1]]

theorem canonical1004 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw1004 = injectiveMoment H node1240 := by
  calc
    injectiveMoment H raw1004 = injectiveMoment H raw1004step0 := by
      have heq : raw1004step0 = raw1004.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1004).symm
    injectiveMoment H raw1004step0 = injectiveMoment H raw1004step1 := by
      have heq : raw1004step1 = -raw1004step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw1004step0).symm
    injectiveMoment H raw1004step1 = injectiveMoment H raw1004step2 := by
      have heq : raw1004step2 = (fun i j => raw1004step1 (permutation16 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1004step1 permutation16 permutation18
    _ = injectiveMoment H node1240 := by rfl

def raw1005 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 1, -1, 0], ![1, 0, 2, -3], ![1, 1, 0, -2]]

def raw1005step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-2, 1, 0, 1], ![-1, -1, 2, 0], ![5, 0, -3, -2]]

def raw1005step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![2, -1, 0, -1], ![1, 1, -2, 0], ![-5, 0, 3, 2]]

def raw1005step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, -1, 2], ![0, 2, 3, -5], ![1, 0, -2, 1]]

theorem canonical1005 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw1005 = injectiveMoment H node999 := by
  calc
    injectiveMoment H raw1005 = injectiveMoment H raw1005step0 := by
      have heq : raw1005step0 = raw1005.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1005).symm
    injectiveMoment H raw1005step0 = injectiveMoment H raw1005step1 := by
      have heq : raw1005step1 = -raw1005step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw1005step0).symm
    injectiveMoment H raw1005step1 = injectiveMoment H raw1005step2 := by
      have heq : raw1005step2 = (fun i j => raw1005step1 (permutation16 i) (permutation20 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1005step1 permutation16 permutation20
    _ = injectiveMoment H node999 := by rfl

def raw1006 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 2, -3]]

def raw1006step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, 0, 0, -1], ![1, 0, 0, -1]]

theorem canonical1006 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1006 = injectiveMoment H node1453 := by
  calc
    injectiveMoment H raw1006 = injectiveMoment H raw1006step0 := by
      have heq : raw1006step0 = (fun i j => raw1006 (permutation49 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1006 permutation49 permutation15
    _ = injectiveMoment H node1453 := by rfl

def raw1007 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 0, 1, -2]]

def raw1007step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, -2, 5], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 1, 0, -2]]

theorem canonical1007 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1007 = injectiveMoment H node2385 := by
  calc
    injectiveMoment H raw1007 = injectiveMoment H raw1007step0 := by
      have heq : raw1007step0 = (fun i j => raw1007 (permutation33 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1007 permutation33 permutation21
    _ = injectiveMoment H node2385 := by rfl

def raw1008 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, 1, -3]]

def raw1008step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-2, 1, 1, 0], ![-1, 0, 0, 1], ![5, -1, -1, -3]]

def raw1008step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -3, 5], ![0, 0, 1, -1], ![0, 0, 2, -2], ![1, 1, 0, -2]]

theorem canonical1008 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1008 = injectiveMoment H node888 := by
  calc
    injectiveMoment H raw1008 = injectiveMoment H raw1008step0 := by
      have heq : raw1008step0 = raw1008.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1008).symm
    injectiveMoment H raw1008step0 = injectiveMoment H raw1008step1 := by
      have heq : raw1008step1 = (fun i j => raw1008step0 (permutation31 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1008step0 permutation31 permutation18
    _ = injectiveMoment H node888 := by rfl

def raw1009 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 1, 0, -1], ![0, 1, 1, -2], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def raw1009step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, -2, 5], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 1, 0, -2]]

theorem canonical1009 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1009 = injectiveMoment H node2385 := by
  calc
    injectiveMoment H raw1009 = injectiveMoment H raw1009step0 := by
      have heq : raw1009step0 = (fun i j => raw1009 (permutation49 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1009 permutation49 permutation23
    _ = injectiveMoment H node2385 := by rfl

def raw1010 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 1, 0, -1], ![0, 1, 1, -2], ![2, 0, 0, -2]]

def raw1010step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -2, 5], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, 0, 1, -2]]

theorem canonical1010 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1010 = injectiveMoment H node751 := by
  calc
    injectiveMoment H raw1010 = injectiveMoment H raw1010step0 := by
      have heq : raw1010step0 = (fun i j => raw1010 (permutation10 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1010 permutation10 permutation21
    _ = injectiveMoment H node751 := by rfl

def raw1011 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 1, 0, -1], ![0, 1, 2, -3], ![2, 0, -1, -1]]

def raw1011step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-2, 1, 1, 0], ![-1, 0, 2, -1], ![5, -1, -3, -1]]

def raw1011step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -3, 5], ![0, -1, 2, -1], ![0, 2, 0, -2], ![1, 0, 1, -2]]

theorem canonical1011 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1011 = injectiveMoment H node887 := by
  calc
    injectiveMoment H raw1011 = injectiveMoment H raw1011step0 := by
      have heq : raw1011step0 = raw1011.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1011).symm
    injectiveMoment H raw1011step0 = injectiveMoment H raw1011step1 := by
      have heq : raw1011step1 = (fun i j => raw1011step0 (permutation31 i) (permutation20 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1011step0 permutation31 permutation20
    _ = injectiveMoment H node887 := by rfl

def raw1012 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 1, 1, -3]]

def raw1012step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-2, 1, 0, 1], ![-1, 0, 0, 1], ![5, -1, -1, -3]]

def raw1012step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -3, 5], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, 0, 1, -2]]

theorem canonical1012 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1012 = injectiveMoment H node889 := by
  calc
    injectiveMoment H raw1012 = injectiveMoment H raw1012step0 := by
      have heq : raw1012step0 = raw1012.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1012).symm
    injectiveMoment H raw1012step0 = injectiveMoment H raw1012step1 := by
      have heq : raw1012step1 = (fun i j => raw1012step0 (permutation31 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1012step0 permutation31 permutation18
    _ = injectiveMoment H node889 := by rfl

def raw1013 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 1, 0, -1], ![1, 0, 1, -2], ![1, 1, 0, -2]]

def raw1013step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -2, 5], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, 1, 0, -2]]

theorem canonical1013 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1013 = injectiveMoment H node750 := by
  calc
    injectiveMoment H raw1013 = injectiveMoment H raw1013step0 := by
      have heq : raw1013step0 = (fun i j => raw1013 (permutation10 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1013 permutation10 permutation21
    _ = injectiveMoment H node750 := by rfl

def raw1014 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 1, 0, -1], ![1, 0, 2, -3], ![1, 1, -1, -1]]

def raw1014step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-2, 1, 0, 1], ![-1, 0, 2, -1], ![5, -1, -3, -1]]

def raw1014step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -3, 5], ![0, -1, 2, -1], ![0, 1, 1, -2], ![1, 1, 0, -2]]

theorem canonical1014 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1014 = injectiveMoment H node886 := by
  calc
    injectiveMoment H raw1014 = injectiveMoment H raw1014step0 := by
      have heq : raw1014step0 = raw1014.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1014).symm
    injectiveMoment H raw1014step0 = injectiveMoment H raw1014step1 := by
      have heq : raw1014step1 = (fun i j => raw1014step0 (permutation31 i) (permutation20 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1014step0 permutation31 permutation20
    _ = injectiveMoment H node886 := by rfl

def raw1015 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 1, 0, -1], ![1, 1, -1, -1], ![1, 0, 2, -3]]

def raw1015step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-2, 1, 1, 0], ![-1, 0, -1, 2], ![5, -1, -1, -3]]

def raw1015step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -3, 5], ![0, -1, 2, -1], ![0, 1, 1, -2], ![1, 1, 0, -2]]

theorem canonical1015 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1015 = injectiveMoment H node886 := by
  calc
    injectiveMoment H raw1015 = injectiveMoment H raw1015step0 := by
      have heq : raw1015step0 = raw1015.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1015).symm
    injectiveMoment H raw1015step0 = injectiveMoment H raw1015step1 := by
      have heq : raw1015step1 = (fun i j => raw1015step0 (permutation31 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1015step0 permutation31 permutation18
    _ = injectiveMoment H node886 := by rfl

def raw1016 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 1, 0, -1], ![1, 1, 0, -2], ![1, 0, 1, -2]]

def raw1016step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -2, 5], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, 1, 0, -2]]

theorem canonical1016 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1016 = injectiveMoment H node750 := by
  calc
    injectiveMoment H raw1016 = injectiveMoment H raw1016step0 := by
      have heq : raw1016step0 = (fun i j => raw1016 (permutation9 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1016 permutation9 permutation21
    _ = injectiveMoment H node750 := by rfl

def raw1017 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 1, 1, -2], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def raw1017step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, -2, 5], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 1, 0, -2]]

theorem canonical1017 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1017 = injectiveMoment H node2385 := by
  calc
    injectiveMoment H raw1017 = injectiveMoment H raw1017step0 := by
      have heq : raw1017step0 = (fun i j => raw1017 (permutation50 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1017 permutation50 permutation23
    _ = injectiveMoment H node2385 := by rfl

def raw1018 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 1, 1, -2], ![0, 1, 0, -1], ![2, 0, 0, -2]]

def raw1018step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -2, 5], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, 0, 1, -2]]

theorem canonical1018 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1018 = injectiveMoment H node751 := by
  calc
    injectiveMoment H raw1018 = injectiveMoment H raw1018step0 := by
      have heq : raw1018step0 = (fun i j => raw1018 (permutation12 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1018 permutation12 permutation21
    _ = injectiveMoment H node751 := by rfl

def raw1019 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 1, 1, -2], ![0, 1, 1, -2], ![2, 0, -1, -1]]

def raw1019step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-2, 1, 1, 0], ![-1, 1, 1, -1], ![5, -2, -2, -1]]

def raw1019step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 0, 2, -2], ![1, 1, -1, -1], ![1, 1, 0, -2]]

theorem canonical1019 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1019 = injectiveMoment H node392 := by
  calc
    injectiveMoment H raw1019 = injectiveMoment H raw1019step0 := by
      have heq : raw1019step0 = raw1019.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1019).symm
    injectiveMoment H raw1019step0 = injectiveMoment H raw1019step1 := by
      have heq : raw1019step1 = (fun i j => raw1019step0 (permutation28 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1019step0 permutation28 permutation18
    _ = injectiveMoment H node392 := by rfl

def raw1020 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 1, 1, -2], ![1, 0, 0, -1], ![1, 1, 0, -2]]

def raw1020step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -2, 5], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, 1, 0, -2]]

theorem canonical1020 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1020 = injectiveMoment H node750 := by
  calc
    injectiveMoment H raw1020 = injectiveMoment H raw1020step0 := by
      have heq : raw1020step0 = (fun i j => raw1020 (permutation12 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1020 permutation12 permutation23
    _ = injectiveMoment H node750 := by rfl

def raw1021 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 1, 1, -2], ![1, 1, -1, -1], ![1, 0, 1, -2]]

def raw1021step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 1, 1, -2], ![1, 0, 1, -2], ![1, 1, -1, -1]]

theorem canonical1021 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1021 = injectiveMoment H node393 := by
  calc
    injectiveMoment H raw1021 = injectiveMoment H raw1021step0 := by
      have heq : raw1021step0 = (fun i j => raw1021 (permutation10 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1021 permutation10 permutation9
    _ = injectiveMoment H node393 := by rfl

def raw1022 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 1, 2, -3], ![0, 1, 0, -1], ![2, 0, -1, -1]]

def raw1022step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-2, 1, 1, 0], ![-1, 2, 0, -1], ![5, -3, -1, -1]]

def raw1022step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -3, 5], ![0, -1, 2, -1], ![0, 2, 0, -2], ![1, 0, 1, -2]]

theorem canonical1022 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1022 = injectiveMoment H node887 := by
  calc
    injectiveMoment H raw1022 = injectiveMoment H raw1022step0 := by
      have heq : raw1022step0 = raw1022.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1022).symm
    injectiveMoment H raw1022step0 = injectiveMoment H raw1022step1 := by
      have heq : raw1022step1 = (fun i j => raw1022step0 (permutation31 i) (permutation26 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1022step0 permutation31 permutation26
    _ = injectiveMoment H node887 := by rfl

def raw1023 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 1, 2, -3], ![1, 0, 0, -1], ![1, 1, -1, -1]]

def raw1023step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-2, 1, 0, 1], ![-1, 2, 0, -1], ![5, -3, -1, -1]]

def raw1023step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -3, 5], ![0, -1, 2, -1], ![0, 1, 1, -2], ![1, 1, 0, -2]]

theorem canonical1023 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1023 = injectiveMoment H node886 := by
  calc
    injectiveMoment H raw1023 = injectiveMoment H raw1023step0 := by
      have heq : raw1023step0 = raw1023.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1023).symm
    injectiveMoment H raw1023step0 = injectiveMoment H raw1023step1 := by
      have heq : raw1023step1 = (fun i j => raw1023step0 (permutation32 i) (permutation26 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1023step0 permutation32 permutation26
    _ = injectiveMoment H node886 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
