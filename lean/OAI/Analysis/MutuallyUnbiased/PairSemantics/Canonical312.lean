import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes0
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes2
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes3
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes4
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes6
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes8
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes10
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes11
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes17
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes38
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes48
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes52

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw9984 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, 2, -2], ![0, 2, 0, -2], ![0, -2, -2, 4]]

def raw9984step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![-2, -2, 4]]

def raw9984step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![2, 0, -2]]

theorem canonical9984 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9984 = injectiveMoment H node31 := by
  calc
    injectiveMoment H raw9984 = injectiveMoment H raw9984step0 := by
      have hz : ∀ i, raw9984 i (permutation9 0) = 0 := by decide +kernel
      have heq : raw9984step0 = (fun i j => raw9984 i (permutation9 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw9984 permutation9 hz
    injectiveMoment H raw9984step0 = injectiveMoment H raw9984step1 := by
      have heq : raw9984step1 = (fun i j => raw9984step0 (permutation7 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9984step0 permutation7 permutation3
    _ = injectiveMoment H node31 := by rfl

def raw9985 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, 2, -2], ![1, -3, 1, 1], ![-1, 3, -3, 1]]

def raw9985step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 1, -1], ![0, -3, 3], ![2, 1, -3], ![-2, 1, 1]]

def raw9985step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![0, 3, -3], ![-2, -1, 3], ![2, -1, -1]]

def raw9985step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 3, -3], ![2, -1, -1]]

theorem canonical9985 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9985 = injectiveMoment H node170 := by
  calc
    injectiveMoment H raw9985 = injectiveMoment H raw9985step0 := by
      have heq : raw9985step0 = raw9985.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw9985).symm
    injectiveMoment H raw9985step0 = injectiveMoment H raw9985step1 := by
      have heq : raw9985step1 = -raw9985step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9985step0).symm
    injectiveMoment H raw9985step1 = injectiveMoment H raw9985step2 := by
      have heq : raw9985step2 = (fun i j => raw9985step1 (permutation21 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9985step1 permutation21 permutation3
    _ = injectiveMoment H node170 := by rfl

def raw9986 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, 2, -2], ![1, -2, 0, 1], ![-1, 2, -2, 1]]

def raw9986step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 1, -1], ![0, -2, 2], ![2, 0, -2], ![-2, 1, 1]]

def raw9986step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![0, 2, -2], ![-2, 0, 2], ![2, -1, -1]]

def raw9986step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]

theorem canonical9986 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9986 = injectiveMoment H node203 := by
  calc
    injectiveMoment H raw9986 = injectiveMoment H raw9986step0 := by
      have heq : raw9986step0 = raw9986.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw9986).symm
    injectiveMoment H raw9986step0 = injectiveMoment H raw9986step1 := by
      have heq : raw9986step1 = -raw9986step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9986step0).symm
    injectiveMoment H raw9986step1 = injectiveMoment H raw9986step2 := by
      have heq : raw9986step2 = (fun i j => raw9986step1 (permutation21 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9986step1 permutation21 permutation3
    _ = injectiveMoment H node203 := by rfl

def raw9987 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, 2, -2], ![1, -2, 1, 0], ![-1, 2, -3, 2]]

def raw9987step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 1, -1], ![0, -2, 2], ![2, 1, -3], ![-2, 0, 2]]

def raw9987step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![0, 2, -2], ![-2, -1, 3], ![2, 0, -2]]

def raw9987step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 2, -2], ![2, 0, -2]]

theorem canonical9987 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9987 = injectiveMoment H node169 := by
  calc
    injectiveMoment H raw9987 = injectiveMoment H raw9987step0 := by
      have heq : raw9987step0 = raw9987.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw9987).symm
    injectiveMoment H raw9987step0 = injectiveMoment H raw9987step1 := by
      have heq : raw9987step1 = -raw9987step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9987step0).symm
    injectiveMoment H raw9987step1 = injectiveMoment H raw9987step2 := by
      have heq : raw9987step2 = (fun i j => raw9987step1 (permutation21 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9987step1 permutation21 permutation3
    _ = injectiveMoment H node169 := by rfl

def raw9988 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, 2, -2], ![2, -3, 0, 1], ![-2, 3, -2, 1]]

def raw9988step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![0, -3, 3], ![2, 0, -2], ![-2, 1, 1]]

def raw9988step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![0, 3, -3], ![-2, 0, 2], ![2, -1, -1]]

def raw9988step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 3, -3], ![2, -1, -1]]

theorem canonical9988 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9988 = injectiveMoment H node198 := by
  calc
    injectiveMoment H raw9988 = injectiveMoment H raw9988step0 := by
      have heq : raw9988step0 = raw9988.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw9988).symm
    injectiveMoment H raw9988step0 = injectiveMoment H raw9988step1 := by
      have heq : raw9988step1 = -raw9988step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9988step0).symm
    injectiveMoment H raw9988step1 = injectiveMoment H raw9988step2 := by
      have heq : raw9988step2 = (fun i j => raw9988step1 (permutation21 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9988step1 permutation21 permutation3
    _ = injectiveMoment H node198 := by rfl

def raw9989 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, 2, -2], ![2, -3, 1, 0], ![-2, 3, -3, 2]]

def raw9989step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![0, -3, 3], ![2, 1, -3], ![-2, 0, 2]]

def raw9989step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![0, 3, -3], ![-2, -1, 3], ![2, 0, -2]]

def raw9989step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 3, -3], ![2, 0, -2]]

theorem canonical9989 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9989 = injectiveMoment H node163 := by
  calc
    injectiveMoment H raw9989 = injectiveMoment H raw9989step0 := by
      have heq : raw9989step0 = raw9989.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw9989).symm
    injectiveMoment H raw9989step0 = injectiveMoment H raw9989step1 := by
      have heq : raw9989step1 = -raw9989step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9989step0).symm
    injectiveMoment H raw9989step1 = injectiveMoment H raw9989step2 := by
      have heq : raw9989step2 = (fun i j => raw9989step1 (permutation21 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9989step1 permutation21 permutation3
    _ = injectiveMoment H node163 := by rfl

def raw9990 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, 2, -2], ![2, -2, 0, 0], ![-2, 2, -2, 2]]

def raw9990step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![0, -2, 2], ![2, 0, -2], ![-2, 0, 2]]

def raw9990step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 2, -2], ![2, 0, -2]]

theorem canonical9990 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9990 = injectiveMoment H node197 := by
  calc
    injectiveMoment H raw9990 = injectiveMoment H raw9990step0 := by
      have heq : raw9990step0 = raw9990.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw9990).symm
    injectiveMoment H raw9990step0 = injectiveMoment H raw9990step1 := by
      have heq : raw9990step1 = (fun i j => raw9990step0 (permutation29 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9990step0 permutation29 permutation3
    _ = injectiveMoment H node197 := by rfl

def raw9991 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, 2, -2], ![2, -2, 1, -1], ![-2, 2, -3, 3]]

def raw9991step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![0, -2, 2], ![2, 1, -3], ![-2, -1, 3]]

def raw9991step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 2, -2], ![2, 1, -3]]

theorem canonical9991 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9991 = injectiveMoment H node162 := by
  calc
    injectiveMoment H raw9991 = injectiveMoment H raw9991step0 := by
      have heq : raw9991step0 = raw9991.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw9991).symm
    injectiveMoment H raw9991step0 = injectiveMoment H raw9991step1 := by
      have heq : raw9991step1 = (fun i j => raw9991step0 (permutation29 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9991step0 permutation29 permutation3
    _ = injectiveMoment H node162 := by rfl

def raw9992 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, 2, -2], ![3, -3, 0, 0], ![-3, 3, -2, 2]]

def raw9992step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![0, -3, 3], ![2, 0, -2], ![-2, 0, 2]]

def raw9992step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![0, 3, -3], ![2, 0, -2]]

theorem canonical9992 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9992 = injectiveMoment H node192 := by
  calc
    injectiveMoment H raw9992 = injectiveMoment H raw9992step0 := by
      have heq : raw9992step0 = raw9992.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw9992).symm
    injectiveMoment H raw9992step0 = injectiveMoment H raw9992step1 := by
      have heq : raw9992step1 = (fun i j => raw9992step0 (permutation29 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9992step0 permutation29 permutation3
    _ = injectiveMoment H node192 := by rfl

def raw9993 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, 2, -2], ![3, -2, 0, -1], ![-3, 2, -2, 3]]

def raw9993step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![0, -2, 2], ![2, 0, -2], ![-2, -1, 3]]

def raw9993step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 3, -3], ![2, 0, -2]]

theorem canonical9993 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9993 = injectiveMoment H node163 := by
  calc
    injectiveMoment H raw9993 = injectiveMoment H raw9993step0 := by
      have heq : raw9993step0 = raw9993.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw9993).symm
    injectiveMoment H raw9993step0 = injectiveMoment H raw9993step1 := by
      have heq : raw9993step1 = (fun i j => raw9993step0 (permutation29 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9993step0 permutation29 permutation3
    _ = injectiveMoment H node163 := by rfl

def raw9994 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 1, -3, 2], ![-1, 1, 1, -1], ![1, -2, 2, -1]]

def raw9994step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![1, 1, -2], ![-3, 1, 2], ![2, -1, -1]]

def raw9994step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 1, -1], ![-1, -1, 2], ![3, -1, -2], ![-2, 1, 1]]

def raw9994step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2]]

theorem canonical9994 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9994 = injectiveMoment H node261 := by
  calc
    injectiveMoment H raw9994 = injectiveMoment H raw9994step0 := by
      have heq : raw9994step0 = raw9994.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw9994).symm
    injectiveMoment H raw9994step0 = injectiveMoment H raw9994step1 := by
      have heq : raw9994step1 = -raw9994step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9994step0).symm
    injectiveMoment H raw9994step1 = injectiveMoment H raw9994step2 := by
      have heq : raw9994step2 = (fun i j => raw9994step1 (permutation23 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9994step1 permutation23 permutation6
    _ = injectiveMoment H node261 := by rfl

def raw9995 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 1, -3, 2], ![0, 1, 1, -2], ![0, -2, 2, 0]]

def raw9995step0 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, 3, -2], ![0, -1, -1, 2], ![0, 2, -2, 0]]

def raw9995step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, -1, 2], ![2, -2, 0]]

def raw9995step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![2, -1, -1]]

theorem canonical9995 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9995 = injectiveMoment H node36 := by
  calc
    injectiveMoment H raw9995 = injectiveMoment H raw9995step0 := by
      have heq : raw9995step0 = -raw9995 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9995).symm
    injectiveMoment H raw9995step0 = injectiveMoment H raw9995step1 := by
      have hz : ∀ i, raw9995step0 i (permutation9 0) = 0 := by decide +kernel
      have heq : raw9995step1 = (fun i j => raw9995step0 i (permutation9 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw9995step0 permutation9 hz
    injectiveMoment H raw9995step1 = injectiveMoment H raw9995step2 := by
      have heq : raw9995step2 = (fun i j => raw9995step1 (permutation4 i) (permutation7 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9995step1 permutation4 permutation7
    _ = injectiveMoment H node36 := by rfl

def raw9996 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, -2, 1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-2, 0, -1, 3], ![0, -1, 3, -2]]

def raw9996step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -1, 3, -2], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1]]

theorem canonical9996 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9996 = injectiveMoment H node3127 := by
  calc
    injectiveMoment H raw9996 = injectiveMoment H raw9996step0 := by
      have heq : raw9996step0 = (fun i j => raw9996 (permutation294 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9996 permutation294 permutation9
    _ = injectiveMoment H node3127 := by rfl

def raw9997 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, -2, 1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-1, -1, -1, 3], ![-1, 0, 3, -2]]

def raw9997step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 0, 3, -2], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1]]

theorem canonical9997 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9997 = injectiveMoment H node3361 := by
  calc
    injectiveMoment H raw9997 = injectiveMoment H raw9997step0 := by
      have heq : raw9997step0 = (fun i j => raw9997 (permutation294 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9997 permutation294 permutation9
    _ = injectiveMoment H node3361 := by rfl

def raw9998 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, -2, 1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-1, 0, -1, 2], ![-1, -1, 3, -1]]

def raw9998step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 0, 2, -1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, 0, -1, 0]]

theorem canonical9998 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9998 = injectiveMoment H node3360 := by
  calc
    injectiveMoment H raw9998 = injectiveMoment H raw9998step0 := by
      have heq : raw9998step0 = (fun i j => raw9998 (permutation398 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9998 permutation398 permutation10
    _ = injectiveMoment H node3360 := by rfl

def raw9999 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![-1, -2, 3]]

def raw9999step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

theorem canonical9999 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9999 = injectiveMoment H node2469 := by
  calc
    injectiveMoment H raw9999 = injectiveMoment H raw9999step0 := by
      have heq : raw9999step0 = (fun i j => raw9999 (permutation331 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9999 permutation331 permutation3
    _ = injectiveMoment H node2469 := by rfl

def raw10000 : Matrix (Fin 2) (Fin 3) ℤ := ![![0, 1, -1], ![0, -1, 1]]

def raw10000step0 : Matrix (Fin 2) (Fin 2) ℤ := ![![1, -1], ![-1, 1]]

def raw10000step1 : Matrix (Fin 2) (Fin 2) ℤ := ![![-1, 1], ![1, -1]]

theorem canonical10000 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw10000 = injectiveMoment H node5 := by
  calc
    injectiveMoment H raw10000 = injectiveMoment H raw10000step0 := by
      have hz : ∀ i, raw10000 i (permutation3 0) = 0 := by decide +kernel
      have heq : raw10000step0 = (fun i j => raw10000 i (permutation3 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw10000 permutation3 hz
    injectiveMoment H raw10000step0 = injectiveMoment H raw10000step1 := by
      have heq : raw10000step1 = (fun i j => raw10000step0 (permutation2 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw10000step0 permutation2 permutation1
    _ = injectiveMoment H node5 := by rfl

def raw10001 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![-2, -1, 3]]

def raw10001step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![-2, -1, 3]]

def raw10001step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

theorem canonical10001 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw10001 = injectiveMoment H node570 := by
  calc
    injectiveMoment H raw10001 = injectiveMoment H raw10001step0 := by
      have hz : ∀ j, raw10001 (permutation202 0) j = 0 := by decide +kernel
      have heq : raw10001step0 = (fun i j => raw10001 (permutation202 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw10001 permutation202 hz
    injectiveMoment H raw10001step0 = injectiveMoment H raw10001step1 := by
      have heq : raw10001step1 = (fun i j => raw10001step0 (permutation128 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw10001step0 permutation128 permutation3
    _ = injectiveMoment H node570 := by rfl

def raw10002 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![-2, -2, 4]]

def raw10002step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![-2, -2, 4]]

def raw10002step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

theorem canonical10002 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw10002 = injectiveMoment H node440 := by
  calc
    injectiveMoment H raw10002 = injectiveMoment H raw10002step0 := by
      have hz : ∀ j, raw10002 (permutation202 0) j = 0 := by decide +kernel
      have heq : raw10002step0 = (fun i j => raw10002 (permutation202 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw10002 permutation202 hz
    injectiveMoment H raw10002step0 = injectiveMoment H raw10002step1 := by
      have heq : raw10002step1 = (fun i j => raw10002step0 (permutation128 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw10002step0 permutation128 permutation3
    _ = injectiveMoment H node440 := by rfl

def raw10003 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![-3, 0, 3]]

def raw10003step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![-3, 0, 3]]

def raw10003step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0]]

theorem canonical10003 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw10003 = injectiveMoment H node1139 := by
  calc
    injectiveMoment H raw10003 = injectiveMoment H raw10003step0 := by
      have hz : ∀ j, raw10003 (permutation202 0) j = 0 := by decide +kernel
      have heq : raw10003step0 = (fun i j => raw10003 (permutation202 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw10003 permutation202 hz
    injectiveMoment H raw10003step0 = injectiveMoment H raw10003step1 := by
      have heq : raw10003step1 = (fun i j => raw10003step0 (permutation120 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw10003step0 permutation120 permutation6
    _ = injectiveMoment H node1139 := by rfl

def raw10004 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2], ![-3, -1, 4]]

def raw10004step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2], ![-3, -1, 4]]

def raw10004step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1]]

theorem canonical10004 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw10004 = injectiveMoment H node739 := by
  calc
    injectiveMoment H raw10004 = injectiveMoment H raw10004step0 := by
      have hz : ∀ j, raw10004 (permutation202 0) j = 0 := by decide +kernel
      have heq : raw10004step0 = (fun i j => raw10004 (permutation202 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw10004 permutation202 hz
    injectiveMoment H raw10004step0 = injectiveMoment H raw10004step1 := by
      have heq : raw10004step1 = (fun i j => raw10004step0 (permutation143 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw10004step0 permutation143 permutation5
    _ = injectiveMoment H node739 := by rfl

def raw10005 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![-2, -2, 4]]

def raw10005step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![-2, -2, 4]]

def raw10005step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]

theorem canonical10005 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw10005 = injectiveMoment H node441 := by
  calc
    injectiveMoment H raw10005 = injectiveMoment H raw10005step0 := by
      have hz : ∀ j, raw10005 (permutation202 0) j = 0 := by decide +kernel
      have heq : raw10005step0 = (fun i j => raw10005 (permutation202 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw10005 permutation202 hz
    injectiveMoment H raw10005step0 = injectiveMoment H raw10005step1 := by
      have heq : raw10005step1 = (fun i j => raw10005step0 (permutation128 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw10005step0 permutation128 permutation3
    _ = injectiveMoment H node441 := by rfl

def raw10006 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![-3, 0, 3]]

def raw10006step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![-3, 0, 3]]

def raw10006step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0]]

theorem canonical10006 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw10006 = injectiveMoment H node663 := by
  calc
    injectiveMoment H raw10006 = injectiveMoment H raw10006step0 := by
      have hz : ∀ j, raw10006 (permutation202 0) j = 0 := by decide +kernel
      have heq : raw10006step0 = (fun i j => raw10006 (permutation202 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw10006 permutation202 hz
    injectiveMoment H raw10006step0 = injectiveMoment H raw10006step1 := by
      have heq : raw10006step1 = (fun i j => raw10006step0 (permutation120 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw10006step0 permutation120 permutation6
    _ = injectiveMoment H node663 := by rfl

def raw10007 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![-3, -1, 4]]

def raw10007step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![-3, -1, 4]]

def raw10007step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]

theorem canonical10007 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw10007 = injectiveMoment H node737 := by
  calc
    injectiveMoment H raw10007 = injectiveMoment H raw10007step0 := by
      have hz : ∀ j, raw10007 (permutation202 0) j = 0 := by decide +kernel
      have heq : raw10007step0 = (fun i j => raw10007 (permutation202 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw10007 permutation202 hz
    injectiveMoment H raw10007step0 = injectiveMoment H raw10007step1 := by
      have heq : raw10007step1 = (fun i j => raw10007step0 (permutation135 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw10007step0 permutation135 permutation5
    _ = injectiveMoment H node737 := by rfl

def raw10008 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![-1, -2, 3]]

def raw10008step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

theorem canonical10008 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw10008 = injectiveMoment H node2469 := by
  calc
    injectiveMoment H raw10008 = injectiveMoment H raw10008step0 := by
      have heq : raw10008step0 = (fun i j => raw10008 (permutation355 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw10008 permutation355 permutation3
    _ = injectiveMoment H node2469 := by rfl

def raw10009 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![-2, -1, 3]]

def raw10009step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![-2, -1, 3]]

def raw10009step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

theorem canonical10009 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw10009 = injectiveMoment H node570 := by
  calc
    injectiveMoment H raw10009 = injectiveMoment H raw10009step0 := by
      have hz : ∀ j, raw10009 (permutation221 0) j = 0 := by decide +kernel
      have heq : raw10009step0 = (fun i j => raw10009 (permutation221 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw10009 permutation221 hz
    injectiveMoment H raw10009step0 = injectiveMoment H raw10009step1 := by
      have heq : raw10009step1 = (fun i j => raw10009step0 (permutation128 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw10009step0 permutation128 permutation3
    _ = injectiveMoment H node570 := by rfl

def raw10010 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![-2, -2, 4]]

def raw10010step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![-2, -2, 4]]

def raw10010step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

theorem canonical10010 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw10010 = injectiveMoment H node440 := by
  calc
    injectiveMoment H raw10010 = injectiveMoment H raw10010step0 := by
      have hz : ∀ j, raw10010 (permutation221 0) j = 0 := by decide +kernel
      have heq : raw10010step0 = (fun i j => raw10010 (permutation221 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw10010 permutation221 hz
    injectiveMoment H raw10010step0 = injectiveMoment H raw10010step1 := by
      have heq : raw10010step1 = (fun i j => raw10010step0 (permutation128 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw10010step0 permutation128 permutation3
    _ = injectiveMoment H node440 := by rfl

def raw10011 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1], ![-3, 0, 3]]

def raw10011step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![-3, 0, 3]]

def raw10011step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0]]

theorem canonical10011 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw10011 = injectiveMoment H node1139 := by
  calc
    injectiveMoment H raw10011 = injectiveMoment H raw10011step0 := by
      have hz : ∀ j, raw10011 (permutation221 0) j = 0 := by decide +kernel
      have heq : raw10011step0 = (fun i j => raw10011 (permutation221 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw10011 permutation221 hz
    injectiveMoment H raw10011step0 = injectiveMoment H raw10011step1 := by
      have heq : raw10011step1 = (fun i j => raw10011step0 (permutation120 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw10011step0 permutation120 permutation6
    _ = injectiveMoment H node1139 := by rfl

def raw10012 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![-3, -1, 4]]

def raw10012step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2], ![-3, -1, 4]]

def raw10012step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1]]

theorem canonical10012 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw10012 = injectiveMoment H node739 := by
  calc
    injectiveMoment H raw10012 = injectiveMoment H raw10012step0 := by
      have hz : ∀ j, raw10012 (permutation221 0) j = 0 := by decide +kernel
      have heq : raw10012step0 = (fun i j => raw10012 (permutation221 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw10012 permutation221 hz
    injectiveMoment H raw10012step0 = injectiveMoment H raw10012step1 := by
      have heq : raw10012step1 = (fun i j => raw10012step0 (permutation143 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw10012step0 permutation143 permutation5
    _ = injectiveMoment H node739 := by rfl

def raw10013 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![-2, -2, 4]]

def raw10013step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![-2, -2, 4]]

def raw10013step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]

theorem canonical10013 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw10013 = injectiveMoment H node441 := by
  calc
    injectiveMoment H raw10013 = injectiveMoment H raw10013step0 := by
      have hz : ∀ j, raw10013 (permutation221 0) j = 0 := by decide +kernel
      have heq : raw10013step0 = (fun i j => raw10013 (permutation221 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw10013 permutation221 hz
    injectiveMoment H raw10013step0 = injectiveMoment H raw10013step1 := by
      have heq : raw10013step1 = (fun i j => raw10013step0 (permutation128 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw10013step0 permutation128 permutation3
    _ = injectiveMoment H node441 := by rfl

def raw10014 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0], ![-3, 0, 3]]

def raw10014step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![-3, 0, 3]]

def raw10014step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0]]

theorem canonical10014 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw10014 = injectiveMoment H node663 := by
  calc
    injectiveMoment H raw10014 = injectiveMoment H raw10014step0 := by
      have hz : ∀ j, raw10014 (permutation221 0) j = 0 := by decide +kernel
      have heq : raw10014step0 = (fun i j => raw10014 (permutation221 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw10014 permutation221 hz
    injectiveMoment H raw10014step0 = injectiveMoment H raw10014step1 := by
      have heq : raw10014step1 = (fun i j => raw10014step0 (permutation120 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw10014step0 permutation120 permutation6
    _ = injectiveMoment H node663 := by rfl

def raw10015 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![-1, -2, 3]]

def raw10015step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1]]

theorem canonical10015 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw10015 = injectiveMoment H node2478 := by
  calc
    injectiveMoment H raw10015 = injectiveMoment H raw10015step0 := by
      have heq : raw10015step0 = (fun i j => raw10015 (permutation373 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw10015 permutation373 permutation3
    _ = injectiveMoment H node2478 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
