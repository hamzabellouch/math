import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes6
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes7
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes9
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes10
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes11
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes12
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes15
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes18
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes19
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes21
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes25
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes36
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes40
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes42

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw4992 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, -1, -3, 4], ![0, 1, 2, -3], ![2, -1, 0, -1]]

def raw4992step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, -1, -1, 0], ![0, 1, 3, -4], ![0, -1, -2, 3], ![-2, 1, 0, 1]]

def raw4992step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, -2, 3], ![0, 1, 3, -4], ![2, -1, -1, 0]]

theorem canonical4992 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4992 = injectiveMoment H node688 := by
  calc
    injectiveMoment H raw4992 = injectiveMoment H raw4992step0 := by
      have heq : raw4992step0 = -raw4992 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4992).symm
    injectiveMoment H raw4992step0 = injectiveMoment H raw4992step1 := by
      have heq : raw4992step1 = (fun i j => raw4992step0 (permutation32 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4992step0 permutation32 permutation9
    _ = injectiveMoment H node688 := by rfl

def raw4993 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, -1, -3, 4], ![1, -1, 0, 0], ![1, 1, 2, -4]]

def raw4993step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, -1, -1, 1], ![1, -3, 0, 2], ![0, 4, 0, -4]]

def raw4993step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, 4, -4], ![0, 1, -3, 2], ![1, -2, 0, 1]]

theorem canonical4993 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4993 = injectiveMoment H node1353 := by
  calc
    injectiveMoment H raw4993 = injectiveMoment H raw4993step0 := by
      have heq : raw4993step0 = raw4993.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4993).symm
    injectiveMoment H raw4993step0 = injectiveMoment H raw4993step1 := by
      have heq : raw4993step1 = (fun i j => raw4993step0 (permutation20 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4993step0 permutation20 permutation21
    _ = injectiveMoment H node1353 := by rfl

def raw4994 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, -1, -3, 4], ![1, -1, 1, -1], ![1, 1, 1, -3]]

theorem canonical4994 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4994 = injectiveMoment H node712 := by
  rfl

def raw4995 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, -1, -3, 4], ![1, -1, 2, -2], ![1, 1, 0, -2]]

def raw4995step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, -1, -1, 1], ![1, -3, 2, 0], ![0, 4, -2, -2]]

def raw4995step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 1, 2, -3], ![1, -2, 1, 0], ![1, 1, -1, -1]]

theorem canonical4995 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4995 = injectiveMoment H node583 := by
  calc
    injectiveMoment H raw4995 = injectiveMoment H raw4995step0 := by
      have heq : raw4995step0 = raw4995.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4995).symm
    injectiveMoment H raw4995step0 = injectiveMoment H raw4995step1 := by
      have heq : raw4995step1 = (fun i j => raw4995step0 (permutation31 i) (permutation28 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4995step0 permutation31 permutation28
    _ = injectiveMoment H node583 := by rfl

def raw4996 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, -1, -3, 4], ![1, 0, 1, -2], ![1, 0, 1, -2]]

def raw4996step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, 1, 1, -2], ![0, 1, 1, -2], ![1, -2, 1, 0]]

theorem canonical4996 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4996 = injectiveMoment H node1186 := by
  calc
    injectiveMoment H raw4996 = injectiveMoment H raw4996step0 := by
      have heq : raw4996step0 = (fun i j => raw4996 (permutation18 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4996 permutation18 permutation15
    _ = injectiveMoment H node1186 := by rfl

def raw4997 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, -1, -3, 4], ![1, 0, 2, -3], ![1, 0, 0, -1]]

def raw4997step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, 1, 0, -1], ![0, 1, 2, -3], ![1, -2, 1, 0]]

theorem canonical4997 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4997 = injectiveMoment H node1185 := by
  calc
    injectiveMoment H raw4997 = injectiveMoment H raw4997step0 := by
      have heq : raw4997step0 = (fun i j => raw4997 (permutation20 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4997 permutation20 permutation15
    _ = injectiveMoment H node1185 := by rfl

def raw4998 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, -1, -3, 4], ![1, 1, 1, -3], ![1, -1, 1, -1]]

def raw4998step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, -1, -3, 4], ![1, -1, 1, -1], ![1, 1, 1, -3]]

theorem canonical4998 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4998 = injectiveMoment H node712 := by
  calc
    injectiveMoment H raw4998 = injectiveMoment H raw4998step0 := by
      have heq : raw4998step0 = (fun i j => raw4998 (permutation10 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4998 permutation10 permutation9
    _ = injectiveMoment H node712 := by rfl

def raw4999 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, -1, -2, 3], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, 1, 2, -4]]

theorem canonical4999 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4999 = injectiveMoment H node2313 := by
  rfl

def raw5000 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, -1, -2, 3], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 1, 0, -2]]

def raw5000step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 1, 1, -2], ![1, 0, 0, -1], ![1, 1, -2, 0]]

theorem canonical5000 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5000 = injectiveMoment H node1641 := by
  calc
    injectiveMoment H raw5000 = injectiveMoment H raw5000step0 := by
      have heq : raw5000step0 = (fun i j => raw5000 (permutation73 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5000 permutation73 permutation23
    _ = injectiveMoment H node1641 := by rfl

def raw5001 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, -1, -2, 3], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw5001step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![1, 1, -2, 0], ![1, 1, 0, -2]]

theorem canonical5001 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5001 = injectiveMoment H node1636 := by
  calc
    injectiveMoment H raw5001 = injectiveMoment H raw5001step0 := by
      have heq : raw5001step0 = (fun i j => raw5001 (permutation72 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5001 permutation72 permutation23
    _ = injectiveMoment H node1636 := by rfl

def raw5002 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, -1, -2, 3], ![1, -1, -1, 1], ![1, 1, 2, -4]]

def raw5002step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, -1, -1, 1], ![1, -2, -1, 2], ![0, 3, 1, -4]]

def raw5002step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 1, 3, -4], ![1, -1, -2, 2], ![1, -1, -1, 1]]

theorem canonical5002 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5002 = injectiveMoment H node693 := by
  calc
    injectiveMoment H raw5002 = injectiveMoment H raw5002step0 := by
      have heq : raw5002step0 = raw5002.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5002).symm
    injectiveMoment H raw5002step0 = injectiveMoment H raw5002step1 := by
      have heq : raw5002step1 = (fun i j => raw5002step0 (permutation14 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5002step0 permutation14 permutation11
    _ = injectiveMoment H node693 := by rfl

def raw5003 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, -1, -2, 3], ![1, -1, 0, 0], ![1, 1, 1, -3]]

def raw5003step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, -1, -1, 1], ![1, -2, 0, 1], ![0, 3, 0, -3]]

def raw5003step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, 3, -3], ![0, 1, -2, 1], ![1, -2, 0, 1]]

theorem canonical5003 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5003 = injectiveMoment H node1352 := by
  calc
    injectiveMoment H raw5003 = injectiveMoment H raw5003step0 := by
      have heq : raw5003step0 = raw5003.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5003).symm
    injectiveMoment H raw5003step0 = injectiveMoment H raw5003step1 := by
      have heq : raw5003step1 = (fun i j => raw5003step0 (permutation20 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5003step0 permutation20 permutation21
    _ = injectiveMoment H node1352 := by rfl

def raw5004 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, -1, -2, 3], ![1, -1, 1, -1], ![1, 1, 0, -2]]

def raw5004step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, 1, -2], ![1, -1, 1, -1], ![1, 1, -2, 0]]

theorem canonical5004 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5004 = injectiveMoment H node490 := by
  calc
    injectiveMoment H raw5004 = injectiveMoment H raw5004step0 := by
      have heq : raw5004step0 = (fun i j => raw5004 (permutation20 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5004 permutation20 permutation23
    _ = injectiveMoment H node490 := by rfl

def raw5005 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, -1, -1, 2], ![0, -1, -1, 2], ![1, 0, -1, 0], ![1, 1, 2, -4]]

theorem canonical5005 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5005 = injectiveMoment H node2314 := by
  rfl

def raw5006 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, -1, -1, 2], ![0, -1, -1, 2], ![2, 1, 1, -4]]

def raw5006step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, -1, -1, 1], ![1, -1, -1, 1], ![0, 2, 2, -4]]

def raw5006step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![-1, 1, 1, -1], ![-1, 1, 1, -1], ![0, -2, -2, 4]]

def raw5006step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 2, -2], ![1, 1, -1, -1], ![1, 1, -1, -1]]

theorem canonical5006 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw5006 = injectiveMoment H node398 := by
  calc
    injectiveMoment H raw5006 = injectiveMoment H raw5006step0 := by
      have heq : raw5006step0 = raw5006.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5006).symm
    injectiveMoment H raw5006step0 = injectiveMoment H raw5006step1 := by
      have heq : raw5006step1 = -raw5006step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw5006step0).symm
    injectiveMoment H raw5006step1 = injectiveMoment H raw5006step2 := by
      have heq : raw5006step2 = (fun i j => raw5006step1 (permutation27 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5006step1 permutation27 permutation17
    _ = injectiveMoment H node398 := by rfl

def raw5007 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, -1, -1, 2], ![0, 0, -2, 2], ![1, -1, 0, 0], ![1, 1, 2, -4]]

theorem canonical5007 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5007 = injectiveMoment H node2316 := by
  rfl

def raw5008 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, -1, -1, 2], ![0, 0, -2, 2], ![2, 0, 2, -4]]

def raw5008step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, -2, 2], ![0, 2, 2, -4], ![1, -2, 1, 0]]

theorem canonical5008 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5008 = injectiveMoment H node1257 := by
  calc
    injectiveMoment H raw5008 = injectiveMoment H raw5008step0 := by
      have heq : raw5008step0 = (fun i j => raw5008 (permutation18 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5008 permutation18 permutation15
    _ = injectiveMoment H node1257 := by rfl

def raw5009 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, -1, -1, 2], ![0, 0, -1, 1], ![1, -1, -1, 1], ![1, 1, 2, -4]]

theorem canonical5009 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5009 = injectiveMoment H node2317 := by
  rfl

def raw5010 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, -1, -1, 2], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, 1, 1, -3]]

def raw5010step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, -1, -1, 2], ![0, -1, 0, 1], ![1, 0, -1, 0], ![1, 1, 1, -3]]

theorem canonical5010 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5010 = injectiveMoment H node2315 := by
  calc
    injectiveMoment H raw5010 = injectiveMoment H raw5010step0 := by
      have heq : raw5010step0 = (fun i j => raw5010 (permutation33 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5010 permutation33 permutation11
    _ = injectiveMoment H node2315 := by rfl

def raw5011 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, -1, -1, 2], ![0, 0, -1, 1], ![1, 0, -1, 0], ![1, 0, 2, -3]]

def raw5011step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, -2, 1, 0]]

theorem canonical5011 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5011 = injectiveMoment H node2732 := by
  calc
    injectiveMoment H raw5011 = injectiveMoment H raw5011step0 := by
      have heq : raw5011step0 = (fun i j => raw5011 (permutation65 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5011 permutation65 permutation15
    _ = injectiveMoment H node2732 := by rfl

def raw5012 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, -1, -1, 2], ![1, -1, -2, 2], ![1, 1, 2, -4]]

def raw5012step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, -1, -1, 1], ![1, -1, -2, 2], ![0, 2, 2, -4]]

def raw5012step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, 1, 1, -1], ![-1, 1, 2, -2], ![0, -2, -2, 4]]

def raw5012step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 2, -1, -1], ![1, -1, 1, -1], ![1, -1, 2, -2]]

theorem canonical5012 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw5012 = injectiveMoment H node585 := by
  calc
    injectiveMoment H raw5012 = injectiveMoment H raw5012step0 := by
      have heq : raw5012step0 = raw5012.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5012).symm
    injectiveMoment H raw5012step0 = injectiveMoment H raw5012step1 := by
      have heq : raw5012step1 = -raw5012step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw5012step0).symm
    injectiveMoment H raw5012step1 = injectiveMoment H raw5012step2 := by
      have heq : raw5012step2 = (fun i j => raw5012step1 (permutation27 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5012step1 permutation27 permutation15
    _ = injectiveMoment H node585 := by rfl

def raw5013 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, -1, -1, 2], ![1, -1, -1, 1], ![1, 1, 1, -3]]

def raw5013step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, -1, -1, 1], ![1, -1, -1, 1], ![0, 2, 1, -3]]

def raw5013step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, 1, 1, -1], ![-1, 1, 1, -1], ![0, -2, -1, 3]]

def raw5013step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![1, 1, -1, -1], ![1, 1, -1, -1]]

theorem canonical5013 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw5013 = injectiveMoment H node477 := by
  calc
    injectiveMoment H raw5013 = injectiveMoment H raw5013step0 := by
      have heq : raw5013step0 = raw5013.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5013).symm
    injectiveMoment H raw5013step0 = injectiveMoment H raw5013step1 := by
      have heq : raw5013step1 = -raw5013step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw5013step0).symm
    injectiveMoment H raw5013step1 = injectiveMoment H raw5013step2 := by
      have heq : raw5013step2 = (fun i j => raw5013step1 (permutation27 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5013step1 permutation27 permutation17
    _ = injectiveMoment H node477 := by rfl

def raw5014 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, -1, -1, 2], ![1, 0, -1, 0], ![1, 0, 1, -2]]

def raw5014step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 1, 0], ![0, 1, 1, -2], ![1, 1, -2, 0]]

theorem canonical5014 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5014 = injectiveMoment H node1000 := by
  calc
    injectiveMoment H raw5014 = injectiveMoment H raw5014step0 := by
      have heq : raw5014step0 = (fun i j => raw5014 (permutation18 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5014 permutation18 permutation17
    _ = injectiveMoment H node1000 := by rfl

def raw5015 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, -1, 0, 1], ![0, -1, -1, 2], ![1, 0, -1, 0], ![1, 1, 1, -3]]

def raw5015step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, -1, -1, 2], ![0, -1, 0, 1], ![1, 0, -1, 0], ![1, 1, 1, -3]]

theorem canonical5015 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5015 = injectiveMoment H node2315 := by
  calc
    injectiveMoment H raw5015 = injectiveMoment H raw5015step0 := by
      have heq : raw5015step0 = (fun i j => raw5015 (permutation39 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5015 permutation39 permutation9
    _ = injectiveMoment H node2315 := by rfl

def raw5016 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, -1, 0, 1], ![0, 0, -1, 1], ![1, -1, -1, 1], ![1, 1, 1, -3]]

theorem canonical5016 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5016 = injectiveMoment H node2318 := by
  rfl

def raw5017 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, -1, 0, 1], ![0, 0, -1, 1], ![1, 0, -1, 0], ![1, 0, 1, -2]]

def raw5017step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, -1, -1, 0], ![0, 1, 0, -1], ![0, 0, 1, -1], ![-1, 0, 1, 0], ![-1, 0, -1, 2]]

def raw5017step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 2, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0]]

theorem canonical5017 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw5017 = injectiveMoment H node2588 := by
  calc
    injectiveMoment H raw5017 = injectiveMoment H raw5017step0 := by
      have heq : raw5017step0 = -raw5017 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw5017).symm
    injectiveMoment H raw5017step0 = injectiveMoment H raw5017step1 := by
      have heq : raw5017step1 = (fun i j => raw5017step0 (permutation54 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5017step0 permutation54 permutation18
    _ = injectiveMoment H node2588 := by rfl

def raw5018 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, -1, 1, 0], ![1, -1, -3, 3], ![1, 1, 1, -3]]

def raw5018step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, -1, -1, 1], ![1, 1, -3, 1], ![0, 0, 3, -3]]

def raw5018step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, 1, 1, -1], ![-1, -1, 3, -1], ![0, 0, -3, 3]]

def raw5018step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 3, -3], ![0, 2, -1, -1], ![1, -1, -1, 1]]

theorem canonical5018 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw5018 = injectiveMoment H node980 := by
  calc
    injectiveMoment H raw5018 = injectiveMoment H raw5018step0 := by
      have heq : raw5018step0 = raw5018.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5018).symm
    injectiveMoment H raw5018step0 = injectiveMoment H raw5018step1 := by
      have heq : raw5018step1 = -raw5018step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw5018step0).symm
    injectiveMoment H raw5018step1 = injectiveMoment H raw5018step2 := by
      have heq : raw5018step2 = (fun i j => raw5018step1 (permutation25 i) (permutation16 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5018step1 permutation25 permutation16
    _ = injectiveMoment H node980 := by rfl

def raw5019 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, -1, 2, -1], ![1, -1, -3, 3], ![1, 1, 0, -2]]

def raw5019step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, -1, -1, 1], ![1, 2, -3, 0], ![0, -1, 3, -2]]

def raw5019step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, 1, 1, -1], ![-1, -2, 3, 0], ![0, 1, -3, 2]]

def raw5019step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 2, -1, -1], ![1, -1, -1, 1], ![1, 0, 2, -3]]

theorem canonical5019 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw5019 = injectiveMoment H node495 := by
  calc
    injectiveMoment H raw5019 = injectiveMoment H raw5019step0 := by
      have heq : raw5019step0 = raw5019.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5019).symm
    injectiveMoment H raw5019step0 = injectiveMoment H raw5019step1 := by
      have heq : raw5019step1 = -raw5019step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw5019step0).symm
    injectiveMoment H raw5019step1 = injectiveMoment H raw5019step2 := by
      have heq : raw5019step2 = (fun i j => raw5019step1 (permutation21 i) (permutation16 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5019step1 permutation21 permutation16
    _ = injectiveMoment H node495 := by rfl

def raw5020 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, 0, -3, 3], ![0, 1, 0, -1], ![2, -2, 2, -2]]

def raw5020step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, 0, 1, -2], ![1, -3, 0, 2], ![0, 3, -1, -2]]

def raw5020step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![-1, 0, -1, 2], ![-1, 3, 0, -2], ![0, -3, 1, 2]]

def raw5020step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 3, -2], ![0, 2, 0, -2], ![1, 0, -3, 2]]

theorem canonical5020 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw5020 = injectiveMoment H node1017 := by
  calc
    injectiveMoment H raw5020 = injectiveMoment H raw5020step0 := by
      have heq : raw5020step0 = raw5020.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5020).symm
    injectiveMoment H raw5020step0 = injectiveMoment H raw5020step1 := by
      have heq : raw5020step1 = -raw5020step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw5020step0).symm
    injectiveMoment H raw5020step1 = injectiveMoment H raw5020step2 := by
      have heq : raw5020step2 = (fun i j => raw5020step1 (permutation17 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5020step1 permutation17 permutation21
    _ = injectiveMoment H node1017 := by rfl

def raw5021 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, 0, -2, 2], ![0, 1, -1, 0], ![2, -2, 2, -2]]

def raw5021step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, 0, 1, -2], ![1, -2, -1, 2], ![0, 2, 0, -2]]

def raw5021step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -2, 2], ![0, 2, 0, -2], ![1, 0, 1, -2]]

theorem canonical5021 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5021 = injectiveMoment H node831 := by
  calc
    injectiveMoment H raw5021 = injectiveMoment H raw5021step0 := by
      have heq : raw5021step0 = raw5021.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5021).symm
    injectiveMoment H raw5021step0 = injectiveMoment H raw5021step1 := by
      have heq : raw5021step1 = (fun i j => raw5021step0 (permutation22 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5021step0 permutation22 permutation23
    _ = injectiveMoment H node831 := by rfl

def raw5022 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, 0, -2, 2], ![1, -2, 2, -1], ![1, 1, -1, -1]]

def raw5022step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 0, -2, 1], ![1, -2, 2, -1], ![0, 2, -1, -1]]

def raw5022step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, -2, 1], ![0, 1, 1, -2], ![2, -1, 0, -1]]

theorem canonical5022 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5022 = injectiveMoment H node510 := by
  calc
    injectiveMoment H raw5022 = injectiveMoment H raw5022step0 := by
      have heq : raw5022step0 = raw5022.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5022).symm
    injectiveMoment H raw5022step0 = injectiveMoment H raw5022step1 := by
      have heq : raw5022step1 = (fun i j => raw5022step0 (permutation21 i) (permutation19 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5022step0 permutation21 permutation19
    _ = injectiveMoment H node510 := by rfl

def raw5023 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, 0, -1, 1], ![0, -1, -1, 2], ![1, -1, -1, 1], ![1, 1, 2, -4]]

def raw5023step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, -1, -1, 2], ![0, 0, -1, 1], ![1, -1, -1, 1], ![1, 1, 2, -4]]

theorem canonical5023 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5023 = injectiveMoment H node2317 := by
  calc
    injectiveMoment H raw5023 = injectiveMoment H raw5023step0 := by
      have heq : raw5023step0 = (fun i j => raw5023 (permutation39 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5023 permutation39 permutation9
    _ = injectiveMoment H node2317 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
