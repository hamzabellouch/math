import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes0
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes1
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes2
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes3
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes4
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes6
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes7
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes10
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes12
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes13
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes14
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes17
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes32
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes38
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes39

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw5984 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 4, -4], ![0, -2, 2], ![1, 0, -1]]

def raw5984step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -2, 2], ![0, 4, -4], ![1, 0, -1]]

theorem canonical5984 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5984 = injectiveMoment H node266 := by
  calc
    injectiveMoment H raw5984 = injectiveMoment H raw5984step0 := by
      have heq : raw5984step0 = (fun i j => raw5984 (permutation11 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5984 permutation11 permutation3
    _ = injectiveMoment H node266 := by rfl

def raw5985 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 4, -4], ![0, -1, 1], ![1, -1, 0]]

def raw5985step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -1, 1], ![0, 4, -4], ![1, -1, 0]]

theorem canonical5985 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5985 = injectiveMoment H node270 := by
  calc
    injectiveMoment H raw5985 = injectiveMoment H raw5985step0 := by
      have heq : raw5985step0 = (fun i j => raw5985 (permutation11 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5985 permutation11 permutation3
    _ = injectiveMoment H node270 := by rfl

def raw5986 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 4, -4], ![1, -2, 1]]

theorem canonical5986 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5986 = injectiveMoment H node59 := by
  rfl

def raw5987 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 4, -4], ![1, -1, 0], ![0, -1, 1]]

def raw5987step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -1, 1], ![0, 4, -4], ![1, -1, 0]]

theorem canonical5987 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5987 = injectiveMoment H node270 := by
  calc
    injectiveMoment H raw5987 = injectiveMoment H raw5987step0 := by
      have heq : raw5987step0 = (fun i j => raw5987 (permutation13 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5987 permutation13 permutation3
    _ = injectiveMoment H node270 := by rfl

def raw5988 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -2, 3], ![1, -2, 1], ![0, 4, -4]]

def raw5988step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 4, -4], ![1, -2, 1]]

theorem canonical5988 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5988 = injectiveMoment H node59 := by
  calc
    injectiveMoment H raw5988 = injectiveMoment H raw5988step0 := by
      have heq : raw5988step0 = (fun i j => raw5988 (permutation4 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5988 permutation4 permutation3
    _ = injectiveMoment H node59 := by rfl

def raw5989 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -2, 3], ![1, -1, 0], ![0, 3, -3]]

def raw5989step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 3, -3], ![1, -1, 0]]

theorem canonical5989 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5989 = injectiveMoment H node58 := by
  calc
    injectiveMoment H raw5989 = injectiveMoment H raw5989step0 := by
      have heq : raw5989step0 = (fun i j => raw5989 (permutation4 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5989 permutation4 permutation3
    _ = injectiveMoment H node58 := by rfl

def raw5990 : Matrix (Fin 2) (Fin 3) ℤ := ![![-1, -2, 3], ![1, 2, -3]]

def raw5990step0 : Matrix (Fin 3) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![3, -3]]

def raw5990step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]

theorem canonical5990 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5990 = injectiveMoment H node10 := by
  calc
    injectiveMoment H raw5990 = injectiveMoment H raw5990step0 := by
      have heq : raw5990step0 = raw5990.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5990).symm
    injectiveMoment H raw5990step0 = injectiveMoment H raw5990step1 := by
      have heq : raw5990step1 = (fun i j => raw5990step0 (permutation7 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5990step0 permutation7 permutation2
    _ = injectiveMoment H node10 := by rfl

def raw5991 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -2, 3, 0], ![-2, 2, 1, -1], ![3, 0, -4, 1]]

def raw5991step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-2, 2, 0], ![3, 1, -4], ![0, -1, 1]]

def raw5991step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-3, -1, 4], ![0, 1, -1]]

def raw5991step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 2, -3], ![2, -2, 0]]

theorem canonical5991 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw5991 = injectiveMoment H node83 := by
  calc
    injectiveMoment H raw5991 = injectiveMoment H raw5991step0 := by
      have heq : raw5991step0 = raw5991.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5991).symm
    injectiveMoment H raw5991step0 = injectiveMoment H raw5991step1 := by
      have heq : raw5991step1 = -raw5991step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw5991step0).symm
    injectiveMoment H raw5991step1 = injectiveMoment H raw5991step2 := by
      have heq : raw5991step2 = (fun i j => raw5991step1 (permutation25 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5991step1 permutation25 permutation3
    _ = injectiveMoment H node83 := by rfl

def raw5992 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -2, 3, 0], ![-1, 2, 1, -2], ![2, 0, -4, 2]]

def raw5992step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![3, 1, -4], ![0, -2, 2]]

def raw5992step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![2, -2, 0], ![-3, -1, 4], ![0, 2, -2]]

def raw5992step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]

theorem canonical5992 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw5992 = injectiveMoment H node85 := by
  calc
    injectiveMoment H raw5992 = injectiveMoment H raw5992step0 := by
      have heq : raw5992step0 = raw5992.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5992).symm
    injectiveMoment H raw5992step0 = injectiveMoment H raw5992step1 := by
      have heq : raw5992step1 = -raw5992step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw5992step0).symm
    injectiveMoment H raw5992step1 = injectiveMoment H raw5992step2 := by
      have heq : raw5992step2 = (fun i j => raw5992step1 (permutation25 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5992step1 permutation25 permutation3
    _ = injectiveMoment H node85 := by rfl

def raw5993 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -2, 3, 0], ![-1, 3, -1, -1], ![2, -1, -2, 1]]

def raw5993step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 3, -1], ![3, -1, -2], ![0, -1, 1]]

def raw5993step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![2, -3, 1], ![-3, 1, 2], ![0, 1, -1]]

def raw5993step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]

theorem canonical5993 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw5993 = injectiveMoment H node109 := by
  calc
    injectiveMoment H raw5993 = injectiveMoment H raw5993step0 := by
      have heq : raw5993step0 = raw5993.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5993).symm
    injectiveMoment H raw5993step0 = injectiveMoment H raw5993step1 := by
      have heq : raw5993step1 = -raw5993step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw5993step0).symm
    injectiveMoment H raw5993step1 = injectiveMoment H raw5993step2 := by
      have heq : raw5993step2 = (fun i j => raw5993step1 (permutation25 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5993step1 permutation25 permutation3
    _ = injectiveMoment H node109 := by rfl

def raw5994 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 3, 0], ![0, 1, -3, 2], ![0, 1, 0, -1], ![1, 0, 0, -1]]

def raw5994step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, 1, 1, 0], ![3, -3, 0, 0], ![0, 2, -1, -1]]

def raw5994step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 3, -3], ![0, 1, -2, 1], ![1, 0, -1, 0]]

theorem canonical5994 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5994 = injectiveMoment H node1063 := by
  calc
    injectiveMoment H raw5994 = injectiveMoment H raw5994step0 := by
      have heq : raw5994step0 = raw5994.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5994).symm
    injectiveMoment H raw5994step0 = injectiveMoment H raw5994step1 := by
      have heq : raw5994step1 = (fun i j => raw5994step0 (permutation32 i) (permutation31 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5994step0 permutation32 permutation31
    _ = injectiveMoment H node1063 := by rfl

def raw5995 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -2, 3, 0], ![0, 3, -1, -2], ![1, -1, -2, 2]]

def raw5995step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 3, -1], ![3, -1, -2], ![0, -2, 2]]

def raw5995step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![2, -3, 1], ![-3, 1, 2], ![0, 2, -2]]

def raw5995step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]

theorem canonical5995 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw5995 = injectiveMoment H node107 := by
  calc
    injectiveMoment H raw5995 = injectiveMoment H raw5995step0 := by
      have heq : raw5995step0 = raw5995.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5995).symm
    injectiveMoment H raw5995step0 = injectiveMoment H raw5995step1 := by
      have heq : raw5995step1 = -raw5995step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw5995step0).symm
    injectiveMoment H raw5995step1 = injectiveMoment H raw5995step2 := by
      have heq : raw5995step2 = (fun i j => raw5995step1 (permutation15 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5995step1 permutation15 permutation6
    _ = injectiveMoment H node107 := by rfl

def raw5996 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -2, 3, 0], ![1, -1, 1, -1], ![0, 3, -4, 1]]

def raw5996step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, -1, 3], ![3, 1, -4], ![0, -1, 1]]

def raw5996step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -1, 0], ![2, 1, -3], ![-3, -1, 4], ![0, 1, -1]]

def raw5996step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 1, 0], ![1, 0, -1], ![1, 2, -3]]

theorem canonical5996 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw5996 = injectiveMoment H node243 := by
  calc
    injectiveMoment H raw5996 = injectiveMoment H raw5996step0 := by
      have heq : raw5996step0 = raw5996.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5996).symm
    injectiveMoment H raw5996step0 = injectiveMoment H raw5996step1 := by
      have heq : raw5996step1 = -raw5996step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw5996step0).symm
    injectiveMoment H raw5996step1 = injectiveMoment H raw5996step2 := by
      have heq : raw5996step2 = (fun i j => raw5996step1 (permutation22 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5996step1 permutation22 permutation5
    _ = injectiveMoment H node243 := by rfl

def raw5997 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -2, 3, 0], ![2, -1, 1, -2], ![-1, 3, -4, 2]]

def raw5997step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 2, -1], ![-2, -1, 3], ![3, 1, -4], ![0, -2, 2]]

def raw5997step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -2, 1], ![2, 1, -3], ![-3, -1, 4], ![0, 2, -2]]

def raw5997step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -2, 1], ![2, 1, -3]]

theorem canonical5997 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw5997 = injectiveMoment H node84 := by
  calc
    injectiveMoment H raw5997 = injectiveMoment H raw5997step0 := by
      have heq : raw5997step0 = raw5997.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5997).symm
    injectiveMoment H raw5997step0 = injectiveMoment H raw5997step1 := by
      have heq : raw5997step1 = -raw5997step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw5997step0).symm
    injectiveMoment H raw5997step1 = injectiveMoment H raw5997step2 := by
      have heq : raw5997step2 = (fun i j => raw5997step1 (permutation25 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5997step1 permutation25 permutation3
    _ = injectiveMoment H node84 := by rfl

def raw5998 : Matrix (Fin 2) (Fin 4) ℤ := ![![-1, -2, 5, -2], ![1, 2, -5, 2]]

def raw5998step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![5, -5], ![-2, 2]]

def raw5998step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-5, 5], ![1, -1], ![2, -2], ![2, -2]]

theorem canonical5998 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5998 = injectiveMoment H node13 := by
  calc
    injectiveMoment H raw5998 = injectiveMoment H raw5998step0 := by
      have heq : raw5998step0 = raw5998.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5998).symm
    injectiveMoment H raw5998step0 = injectiveMoment H raw5998step1 := by
      have heq : raw5998step1 = (fun i j => raw5998step0 (permutation21 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5998step0 permutation21 permutation2
    _ = injectiveMoment H node13 := by rfl

def raw5999 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, -3, 5], ![0, 0, 2, -2], ![1, 1, 1, -3]]

def raw5999step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-3, 2, 1], ![5, -2, -3]]

def raw5999step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 1, -1], ![0, 1, -1], ![2, 1, -3]]

theorem canonical5999 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5999 = injectiveMoment H node119 := by
  calc
    injectiveMoment H raw5999 = injectiveMoment H raw5999step0 := by
      have heq : raw5999step0 = raw5999.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5999).symm
    injectiveMoment H raw5999step0 = injectiveMoment H raw5999step1 := by
      have heq : raw5999step1 = (fun i j => raw5999step0 (permutation27 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5999step0 permutation27 permutation6
    _ = injectiveMoment H node119 := by rfl

def raw6000 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, -3, 5], ![0, 0, 3, -3], ![1, 1, 0, -2]]

def raw6000step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-3, 3, 0], ![5, -3, -2]]

def raw6000step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 3, -3], ![1, 0, -1], ![1, 0, -1]]

theorem canonical6000 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6000 = injectiveMoment H node129 := by
  calc
    injectiveMoment H raw6000 = injectiveMoment H raw6000step0 := by
      have heq : raw6000step0 = raw6000.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6000).symm
    injectiveMoment H raw6000step0 = injectiveMoment H raw6000step1 := by
      have heq : raw6000step1 = (fun i j => raw6000step0 (permutation31 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6000step0 permutation31 permutation8
    _ = injectiveMoment H node129 := by rfl

def raw6001 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, -3, 5], ![0, 1, 1, -2], ![1, 0, 2, -3]]

def raw6001step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![-3, 1, 2], ![5, -2, -3]]

def raw6001step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 1, -1], ![1, 0, -1], ![1, 2, -3]]

theorem canonical6001 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6001 = injectiveMoment H node123 := by
  calc
    injectiveMoment H raw6001 = injectiveMoment H raw6001step0 := by
      have heq : raw6001step0 = raw6001.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6001).symm
    injectiveMoment H raw6001step0 = injectiveMoment H raw6001step1 := by
      have heq : raw6001step1 = (fun i j => raw6001step0 (permutation27 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6001step0 permutation27 permutation6
    _ = injectiveMoment H node123 := by rfl

def raw6002 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, -3, 5], ![0, 1, 2, -3], ![1, 0, 1, -2]]

def raw6002step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![-3, 2, 1], ![5, -3, -2]]

def raw6002step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 1, -1], ![1, 0, -1], ![1, 2, -3]]

theorem canonical6002 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6002 = injectiveMoment H node123 := by
  calc
    injectiveMoment H raw6002 = injectiveMoment H raw6002step0 := by
      have heq : raw6002step0 = raw6002.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6002).symm
    injectiveMoment H raw6002step0 = injectiveMoment H raw6002step1 := by
      have heq : raw6002step1 = (fun i j => raw6002step0 (permutation29 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6002step0 permutation29 permutation8
    _ = injectiveMoment H node123 := by rfl

def raw6003 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![-1, -1, 2, 0], ![0, 1, -1, 0], ![1, 0, 1, -2], ![1, 1, 0, -2]]

theorem canonical6003 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6003 = injectiveMoment H node2481 := by
  rfl

def raw6004 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![-1, -1, 2, 0], ![0, 1, 0, -1], ![1, 0, 1, -2], ![1, 1, -1, -1]]

theorem canonical6004 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6004 = injectiveMoment H node2482 := by
  rfl

def raw6005 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![-1, -1, 2, 0], ![1, 0, 1, -2], ![1, 2, -1, -2]]

def raw6005step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 1, 2, -4], ![1, 1, -2, 0], ![-1, 0, -1, 2], ![-1, -2, 1, 2]]

def raw6005step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, -1, 2], ![1, 1, -2, 0], ![1, 1, 2, -4]]

theorem canonical6005 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6005 = injectiveMoment H node501 := by
  calc
    injectiveMoment H raw6005 = injectiveMoment H raw6005step0 := by
      have heq : raw6005step0 = -raw6005 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6005).symm
    injectiveMoment H raw6005step0 = injectiveMoment H raw6005step1 := by
      have heq : raw6005step1 = (fun i j => raw6005step0 (permutation32 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6005step0 permutation32 permutation15
    _ = injectiveMoment H node501 := by rfl

def raw6006 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![-1, -1, 2, 0], ![1, 1, 0, -2], ![1, 1, 0, -2]]

def raw6006step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![-1, -1, 1, 1], ![-2, 2, 0, 0], ![4, 0, -2, -2]]

def raw6006step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 2, -2], ![1, 1, -1, -1], ![1, 1, -1, -1]]

theorem canonical6006 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6006 = injectiveMoment H node398 := by
  calc
    injectiveMoment H raw6006 = injectiveMoment H raw6006step0 := by
      have heq : raw6006step0 = raw6006.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6006).symm
    injectiveMoment H raw6006step0 = injectiveMoment H raw6006step1 := by
      have heq : raw6006step1 = (fun i j => raw6006step0 (permutation31 i) (permutation26 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6006step0 permutation31 permutation26
    _ = injectiveMoment H node398 := by rfl

def raw6007 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![-1, -1, 2, 0], ![1, 1, 1, -3], ![1, 1, -1, -1]]

def raw6007step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![-1, -1, 1, 1], ![-2, 2, 1, -1], ![4, 0, -3, -1]]

def raw6007step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 1, -1, -1], ![1, 1, -1, -1], ![2, -2, -1, 1], ![-4, 0, 3, 1]]

def raw6007step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 1, 3, -4], ![1, -1, -1, 1], ![1, -1, -1, 1]]

theorem canonical6007 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6007 = injectiveMoment H node687 := by
  calc
    injectiveMoment H raw6007 = injectiveMoment H raw6007step0 := by
      have heq : raw6007step0 = raw6007.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6007).symm
    injectiveMoment H raw6007step0 = injectiveMoment H raw6007step1 := by
      have heq : raw6007step1 = -raw6007step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6007step0).symm
    injectiveMoment H raw6007step1 = injectiveMoment H raw6007step2 := by
      have heq : raw6007step2 = (fun i j => raw6007step1 (permutation25 i) (permutation20 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6007step1 permutation25 permutation20
    _ = injectiveMoment H node687 := by rfl

def raw6008 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![-1, 0, 1, 0], ![1, 0, 1, -2], ![1, 1, 0, -2]]

def raw6008step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, 0, 1, -2]]

theorem canonical6008 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6008 = injectiveMoment H node786 := by
  calc
    injectiveMoment H raw6008 = injectiveMoment H raw6008step0 := by
      have heq : raw6008step0 = (fun i j => raw6008 (permutation9 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6008 permutation9 permutation17
    _ = injectiveMoment H node786 := by rfl

def raw6009 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![-1, 0, 2, -1], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, 1, -1, -1]]

theorem canonical6009 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6009 = injectiveMoment H node2484 := by
  rfl

def raw6010 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![-1, 0, 2, -1], ![0, 1, 1, -2], ![2, 0, -1, -1]]

def raw6010step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, -1, 2, -1], ![0, 2, -1, -1], ![1, 0, 1, -2]]

theorem canonical6010 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6010 = injectiveMoment H node896 := by
  calc
    injectiveMoment H raw6010 = injectiveMoment H raw6010step0 := by
      have heq : raw6010step0 = (fun i j => raw6010 (permutation10 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6010 permutation10 permutation15
    _ = injectiveMoment H node896 := by rfl

def raw6011 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![-1, 0, 2, -1], ![1, 0, 1, -2], ![1, 1, -1, -1]]

def raw6011step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, -1, 2, -1], ![0, 1, 1, -2], ![1, 1, -1, -1]]

theorem canonical6011 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6011 = injectiveMoment H node894 := by
  calc
    injectiveMoment H raw6011 = injectiveMoment H raw6011step0 := by
      have heq : raw6011step0 = (fun i j => raw6011 (permutation9 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6011 permutation9 permutation15
    _ = injectiveMoment H node894 := by rfl

def raw6012 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![-1, 0, 3, -2], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 1, -1, -1]]

theorem canonical6012 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6012 = injectiveMoment H node2485 := by
  rfl

def raw6013 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![-1, 0, 3, -2], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 0, -1]]

def raw6013step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, -1, 3, -2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, 0, -1]]

theorem canonical6013 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6013 = injectiveMoment H node2500 := by
  calc
    injectiveMoment H raw6013 = injectiveMoment H raw6013step0 := by
      have heq : raw6013step0 = (fun i j => raw6013 (permutation36 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6013 permutation36 permutation15
    _ = injectiveMoment H node2500 := by rfl

def raw6014 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![-1, 0, 3, -2], ![0, 2, -1, -1], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw6014step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 1, 2, -4], ![1, 0, -3, 2], ![0, -2, 1, 1], ![-1, 1, 0, 0], ![-1, 0, 0, 1]]

def raw6014step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 0, 1], ![0, 1, -3, 2], ![1, -1, 0, 0], ![1, 1, 2, -4]]

theorem canonical6014 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6014 = injectiveMoment H node2067 := by
  calc
    injectiveMoment H raw6014 = injectiveMoment H raw6014step0 := by
      have heq : raw6014step0 = -raw6014 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6014).symm
    injectiveMoment H raw6014step0 = injectiveMoment H raw6014step1 := by
      have heq : raw6014step1 = (fun i j => raw6014step0 (permutation101 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6014step0 permutation101 permutation15
    _ = injectiveMoment H node2067 := by rfl

def raw6015 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![-1, 0, 3, -2], ![1, -1, 0, 0], ![1, 2, -1, -2]]

def raw6015step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![-1, 0, -1, 2], ![-2, 3, 0, -1], ![4, -2, 0, -2]]

def raw6015step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 1, -1, -1], ![1, 0, 1, -2], ![2, -3, 0, 1], ![-4, 2, 0, 2]]

def raw6015step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 1, -3, 2], ![0, 2, 2, -4], ![1, -2, 0, 1]]

theorem canonical6015 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6015 = injectiveMoment H node1125 := by
  calc
    injectiveMoment H raw6015 = injectiveMoment H raw6015step0 := by
      have heq : raw6015step0 = raw6015.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6015).symm
    injectiveMoment H raw6015step0 = injectiveMoment H raw6015step1 := by
      have heq : raw6015step1 = -raw6015step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6015step0).symm
    injectiveMoment H raw6015step1 = injectiveMoment H raw6015step2 := by
      have heq : raw6015step2 = (fun i j => raw6015step1 (permutation12 i) (permutation26 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6015step1 permutation12 permutation26
    _ = injectiveMoment H node1125 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
