import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes1
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes2
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes3

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw9952 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, 2, -2], ![-4, 2, -1, 3], ![4, -2, -1, -1]]

def raw9952step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -4, 4], ![0, 2, -2], ![2, -1, -1], ![-2, 3, -1]]

def raw9952step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 4, -4], ![2, -1, -1]]

theorem canonical9952 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9952 = injectiveMoment H node164 := by
  calc
    injectiveMoment H raw9952 = injectiveMoment H raw9952step0 := by
      have heq : raw9952step0 = raw9952.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw9952).symm
    injectiveMoment H raw9952step0 = injectiveMoment H raw9952step1 := by
      have heq : raw9952step1 = (fun i j => raw9952step0 (permutation29 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9952step0 permutation29 permutation4
    _ = injectiveMoment H node164 := by rfl

def raw9953 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, 2, -2], ![-4, 2, 0, 2], ![4, -2, -2, 0]]

def raw9953step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -4, 4], ![0, 2, -2], ![2, 0, -2], ![-2, 2, 0]]

def raw9953step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 4, -4], ![2, -2, 0]]

theorem canonical9953 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9953 = injectiveMoment H node199 := by
  calc
    injectiveMoment H raw9953 = injectiveMoment H raw9953step0 := by
      have heq : raw9953step0 = raw9953.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw9953).symm
    injectiveMoment H raw9953step0 = injectiveMoment H raw9953step1 := by
      have heq : raw9953step1 = (fun i j => raw9953step0 (permutation29 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9953step0 permutation29 permutation4
    _ = injectiveMoment H node199 := by rfl

def raw9954 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, 2, -2], ![-4, 3, -1, 2], ![4, -3, -1, 0]]

def raw9954step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -4, 4], ![0, 3, -3], ![2, -1, -1], ![-2, 2, 0]]

def raw9954step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![0, 4, -4], ![2, -1, -1]]

theorem canonical9954 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9954 = injectiveMoment H node193 := by
  calc
    injectiveMoment H raw9954 = injectiveMoment H raw9954step0 := by
      have heq : raw9954step0 = raw9954.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw9954).symm
    injectiveMoment H raw9954step0 = injectiveMoment H raw9954step1 := by
      have heq : raw9954step1 = (fun i j => raw9954step0 (permutation29 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9954step0 permutation29 permutation4
    _ = injectiveMoment H node193 := by rfl

def raw9955 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, 2, -2], ![-4, 3, 0, 1], ![4, -3, -2, 1]]

def raw9955step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -4, 4], ![0, 3, -3], ![2, 0, -2], ![-2, 1, 1]]

def raw9955step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![0, -3, 3], ![-2, 0, 2], ![2, -1, -1]]

def raw9955step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![0, 4, -4], ![2, -1, -1]]

theorem canonical9955 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9955 = injectiveMoment H node193 := by
  calc
    injectiveMoment H raw9955 = injectiveMoment H raw9955step0 := by
      have heq : raw9955step0 = raw9955.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw9955).symm
    injectiveMoment H raw9955step0 = injectiveMoment H raw9955step1 := by
      have heq : raw9955step1 = -raw9955step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9955step0).symm
    injectiveMoment H raw9955step1 = injectiveMoment H raw9955step2 := by
      have heq : raw9955step2 = (fun i j => raw9955step1 (permutation23 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9955step1 permutation23 permutation3
    _ = injectiveMoment H node193 := by rfl

def raw9956 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, 2, -2], ![-3, 2, -1, 2], ![3, -2, -1, 0]]

def raw9956step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![0, 2, -2], ![2, -1, -1], ![-2, 2, 0]]

def raw9956step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 3, -3], ![2, -1, -1]]

theorem canonical9956 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9956 = injectiveMoment H node198 := by
  calc
    injectiveMoment H raw9956 = injectiveMoment H raw9956step0 := by
      have heq : raw9956step0 = raw9956.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw9956).symm
    injectiveMoment H raw9956step0 = injectiveMoment H raw9956step1 := by
      have heq : raw9956step1 = (fun i j => raw9956step0 (permutation29 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9956step0 permutation29 permutation4
    _ = injectiveMoment H node198 := by rfl

def raw9957 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, 2, -2], ![-3, 2, 0, 1], ![3, -2, -2, 1]]

def raw9957step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![0, 2, -2], ![2, 0, -2], ![-2, 1, 1]]

def raw9957step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![0, -2, 2], ![-2, 0, 2], ![2, -1, -1]]

def raw9957step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 3, -3], ![2, -1, -1]]

theorem canonical9957 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9957 = injectiveMoment H node198 := by
  calc
    injectiveMoment H raw9957 = injectiveMoment H raw9957step0 := by
      have heq : raw9957step0 = raw9957.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw9957).symm
    injectiveMoment H raw9957step0 = injectiveMoment H raw9957step1 := by
      have heq : raw9957step1 = -raw9957step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9957step0).symm
    injectiveMoment H raw9957step1 = injectiveMoment H raw9957step2 := by
      have heq : raw9957step2 = (fun i j => raw9957step1 (permutation23 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9957step1 permutation23 permutation3
    _ = injectiveMoment H node198 := by rfl

def raw9958 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, 2, -2], ![-3, 3, -1, 1], ![3, -3, -1, 1]]

def raw9958step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![0, 3, -3], ![2, -1, -1], ![-2, 1, 1]]

def raw9958step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -3, 3], ![0, 3, -3], ![2, -1, -1]]

theorem canonical9958 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9958 = injectiveMoment H node220 := by
  calc
    injectiveMoment H raw9958 = injectiveMoment H raw9958step0 := by
      have heq : raw9958step0 = raw9958.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw9958).symm
    injectiveMoment H raw9958step0 = injectiveMoment H raw9958step1 := by
      have heq : raw9958step1 = (fun i j => raw9958step0 (permutation27 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9958step0 permutation27 permutation3
    _ = injectiveMoment H node220 := by rfl

def raw9959 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, 2, -2], ![-3, 3, 0, 0], ![3, -3, -2, 2]]

def raw9959step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![0, 3, -3], ![2, 0, -2], ![-2, 0, 2]]

def raw9959step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![0, 3, -3], ![2, 0, -2]]

theorem canonical9959 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9959 = injectiveMoment H node192 := by
  calc
    injectiveMoment H raw9959 = injectiveMoment H raw9959step0 := by
      have heq : raw9959step0 = raw9959.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw9959).symm
    injectiveMoment H raw9959step0 = injectiveMoment H raw9959step1 := by
      have heq : raw9959step1 = (fun i j => raw9959step0 (permutation27 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9959step0 permutation27 permutation3
    _ = injectiveMoment H node192 := by rfl

def raw9960 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, 2, -2], ![-3, 4, -2, 1], ![3, -4, 0, 1]]

def raw9960step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![0, 4, -4], ![2, -2, 0], ![-2, 1, 1]]

def raw9960step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![0, -4, 4], ![-2, 2, 0], ![2, -1, -1]]

def raw9960step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![0, 4, -4], ![2, -1, -1]]

theorem canonical9960 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9960 = injectiveMoment H node193 := by
  calc
    injectiveMoment H raw9960 = injectiveMoment H raw9960step0 := by
      have heq : raw9960step0 = raw9960.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw9960).symm
    injectiveMoment H raw9960step0 = injectiveMoment H raw9960step1 := by
      have heq : raw9960step1 = -raw9960step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9960step0).symm
    injectiveMoment H raw9960step1 = injectiveMoment H raw9960step2 := by
      have heq : raw9960step2 = (fun i j => raw9960step1 (permutation21 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9960step1 permutation21 permutation4
    _ = injectiveMoment H node193 := by rfl

def raw9961 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, 2, -2], ![-2, -2, -1, 5], ![2, 2, -1, -3]]

def raw9961step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![0, -2, 2], ![2, -1, -1], ![-2, 5, -3]]

def raw9961step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 2, -2], ![0, 2, -2], ![2, -1, -1]]

theorem canonical9961 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9961 = injectiveMoment H node125 := by
  calc
    injectiveMoment H raw9961 = injectiveMoment H raw9961step0 := by
      have heq : raw9961step0 = raw9961.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw9961).symm
    injectiveMoment H raw9961step0 = injectiveMoment H raw9961step1 := by
      have heq : raw9961step1 = (fun i j => raw9961step0 (permutation27 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9961step0 permutation27 permutation4
    _ = injectiveMoment H node125 := by rfl

def raw9962 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, 2, -2], ![-2, -2, 0, 4], ![2, 2, -2, -2]]

def raw9962step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![0, -2, 2], ![2, 0, -2], ![-2, 4, -2]]

def raw9962step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![0, 2, -2], ![2, -2, 0]]

theorem canonical9962 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9962 = injectiveMoment H node151 := by
  calc
    injectiveMoment H raw9962 = injectiveMoment H raw9962step0 := by
      have heq : raw9962step0 = raw9962.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw9962).symm
    injectiveMoment H raw9962step0 = injectiveMoment H raw9962step1 := by
      have heq : raw9962step1 = (fun i j => raw9962step0 (permutation27 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9962step0 permutation27 permutation4
    _ = injectiveMoment H node151 := by rfl

def raw9963 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, 2, -2], ![-2, -2, 1, 3], ![2, 2, -3, -1]]

def raw9963step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![0, -2, 2], ![2, 1, -3], ![-2, 3, -1]]

def raw9963step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![0, 2, -2], ![2, -3, 1]]

theorem canonical9963 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9963 = injectiveMoment H node182 := by
  calc
    injectiveMoment H raw9963 = injectiveMoment H raw9963step0 := by
      have heq : raw9963step0 = raw9963.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw9963).symm
    injectiveMoment H raw9963step0 = injectiveMoment H raw9963step1 := by
      have heq : raw9963step1 = (fun i j => raw9963step0 (permutation27 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9963step0 permutation27 permutation4
    _ = injectiveMoment H node182 := by rfl

def raw9964 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, 2, -2], ![-2, -2, 2, 2], ![2, 2, -4, 0]]

def raw9964step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![0, -2, 2], ![2, 2, -4], ![-2, 2, 0]]

def raw9964step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![0, 2, -2], ![-2, -2, 4], ![2, -2, 0]]

def raw9964step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![0, 2, -2], ![2, -2, 0]]

theorem canonical9964 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9964 = injectiveMoment H node151 := by
  calc
    injectiveMoment H raw9964 = injectiveMoment H raw9964step0 := by
      have heq : raw9964step0 = raw9964.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw9964).symm
    injectiveMoment H raw9964step0 = injectiveMoment H raw9964step1 := by
      have heq : raw9964step1 = -raw9964step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9964step0).symm
    injectiveMoment H raw9964step1 = injectiveMoment H raw9964step2 := by
      have heq : raw9964step2 = (fun i j => raw9964step1 (permutation21 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9964step1 permutation21 permutation3
    _ = injectiveMoment H node151 := by rfl

def raw9965 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, 2, -2], ![-2, -2, 3, 1], ![2, 2, -5, 1]]

def raw9965step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![0, -2, 2], ![2, 3, -5], ![-2, 1, 1]]

def raw9965step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![0, 2, -2], ![-2, -3, 5], ![2, -1, -1]]

def raw9965step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 2, -2], ![0, 2, -2], ![2, -1, -1]]

theorem canonical9965 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9965 = injectiveMoment H node125 := by
  calc
    injectiveMoment H raw9965 = injectiveMoment H raw9965step0 := by
      have heq : raw9965step0 = raw9965.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw9965).symm
    injectiveMoment H raw9965step0 = injectiveMoment H raw9965step1 := by
      have heq : raw9965step1 = -raw9965step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9965step0).symm
    injectiveMoment H raw9965step1 = injectiveMoment H raw9965step2 := by
      have heq : raw9965step2 = (fun i j => raw9965step1 (permutation21 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9965step1 permutation21 permutation3
    _ = injectiveMoment H node125 := by rfl

def raw9966 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, 2, -2], ![-2, 2, -1, 1], ![2, -2, -1, 1]]

def raw9966step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![0, 2, -2], ![2, -1, -1], ![-2, 1, 1]]

def raw9966step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 2, -2], ![2, -1, -1]]

theorem canonical9966 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9966 = injectiveMoment H node224 := by
  calc
    injectiveMoment H raw9966 = injectiveMoment H raw9966step0 := by
      have heq : raw9966step0 = raw9966.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw9966).symm
    injectiveMoment H raw9966step0 = injectiveMoment H raw9966step1 := by
      have heq : raw9966step1 = (fun i j => raw9966step0 (permutation27 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9966step0 permutation27 permutation3
    _ = injectiveMoment H node224 := by rfl

def raw9967 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, 2, -2], ![-2, 2, 1, -1], ![2, -2, -3, 3]]

def raw9967step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![0, 2, -2], ![2, 1, -3], ![-2, -1, 3]]

def raw9967step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 2, -2], ![2, 1, -3]]

theorem canonical9967 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9967 = injectiveMoment H node162 := by
  calc
    injectiveMoment H raw9967 = injectiveMoment H raw9967step0 := by
      have heq : raw9967step0 = raw9967.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw9967).symm
    injectiveMoment H raw9967step0 = injectiveMoment H raw9967step1 := by
      have heq : raw9967step1 = (fun i j => raw9967step0 (permutation27 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9967step0 permutation27 permutation3
    _ = injectiveMoment H node162 := by rfl

def raw9968 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, 2, -2], ![-2, 3, -2, 1], ![2, -3, 0, 1]]

def raw9968step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![0, 3, -3], ![2, -2, 0], ![-2, 1, 1]]

def raw9968step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![0, -3, 3], ![-2, 2, 0], ![2, -1, -1]]

def raw9968step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 3, -3], ![2, -1, -1]]

theorem canonical9968 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9968 = injectiveMoment H node198 := by
  calc
    injectiveMoment H raw9968 = injectiveMoment H raw9968step0 := by
      have heq : raw9968step0 = raw9968.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw9968).symm
    injectiveMoment H raw9968step0 = injectiveMoment H raw9968step1 := by
      have heq : raw9968step1 = -raw9968step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9968step0).symm
    injectiveMoment H raw9968step1 = injectiveMoment H raw9968step2 := by
      have heq : raw9968step2 = (fun i j => raw9968step1 (permutation21 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9968step1 permutation21 permutation4
    _ = injectiveMoment H node198 := by rfl

def raw9969 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, 2, -2], ![-2, 3, -1, 0], ![2, -3, -1, 2]]

def raw9969step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![0, 3, -3], ![2, -1, -1], ![-2, 0, 2]]

def raw9969step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 3, -3], ![2, -1, -1]]

theorem canonical9969 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9969 = injectiveMoment H node198 := by
  calc
    injectiveMoment H raw9969 = injectiveMoment H raw9969step0 := by
      have heq : raw9969step0 = raw9969.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw9969).symm
    injectiveMoment H raw9969step0 = injectiveMoment H raw9969step1 := by
      have heq : raw9969step1 = (fun i j => raw9969step0 (permutation27 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9969step0 permutation27 permutation3
    _ = injectiveMoment H node198 := by rfl

def raw9970 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, 2, -2], ![-2, 3, 0, -1], ![2, -3, -2, 3]]

def raw9970step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![0, 3, -3], ![2, 0, -2], ![-2, -1, 3]]

def raw9970step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 3, -3], ![2, 0, -2]]

theorem canonical9970 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9970 = injectiveMoment H node163 := by
  calc
    injectiveMoment H raw9970 = injectiveMoment H raw9970step0 := by
      have heq : raw9970step0 = raw9970.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw9970).symm
    injectiveMoment H raw9970step0 = injectiveMoment H raw9970step1 := by
      have heq : raw9970step1 = (fun i j => raw9970step0 (permutation27 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9970step0 permutation27 permutation3
    _ = injectiveMoment H node163 := by rfl

def raw9971 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, 2, -2], ![-2, 4, -3, 1], ![2, -4, 1, 1]]

def raw9971step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![0, 4, -4], ![2, -3, 1], ![-2, 1, 1]]

def raw9971step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![0, -4, 4], ![-2, 3, -1], ![2, -1, -1]]

def raw9971step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 4, -4], ![2, -1, -1]]

theorem canonical9971 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9971 = injectiveMoment H node164 := by
  calc
    injectiveMoment H raw9971 = injectiveMoment H raw9971step0 := by
      have heq : raw9971step0 = raw9971.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw9971).symm
    injectiveMoment H raw9971step0 = injectiveMoment H raw9971step1 := by
      have heq : raw9971step1 = -raw9971step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9971step0).symm
    injectiveMoment H raw9971step1 = injectiveMoment H raw9971step2 := by
      have heq : raw9971step2 = (fun i j => raw9971step1 (permutation21 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9971step1 permutation21 permutation4
    _ = injectiveMoment H node164 := by rfl

def raw9972 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, 2, -2], ![-2, 4, -2, 0], ![2, -4, 0, 2]]

def raw9972step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![0, 4, -4], ![2, -2, 0], ![-2, 0, 2]]

def raw9972step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 4, -4], ![2, -2, 0]]

theorem canonical9972 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9972 = injectiveMoment H node199 := by
  calc
    injectiveMoment H raw9972 = injectiveMoment H raw9972step0 := by
      have heq : raw9972step0 = raw9972.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw9972).symm
    injectiveMoment H raw9972step0 = injectiveMoment H raw9972step1 := by
      have heq : raw9972step1 = (fun i j => raw9972step0 (permutation27 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9972step0 permutation27 permutation3
    _ = injectiveMoment H node199 := by rfl

def raw9973 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, 2, -2], ![-1, -2, -1, 4], ![1, 2, -1, -2]]

def raw9973step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![0, -2, 2], ![2, -1, -1], ![-2, 4, -2]]

def raw9973step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 2, -2], ![2, -1, -1]]

theorem canonical9973 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9973 = injectiveMoment H node146 := by
  calc
    injectiveMoment H raw9973 = injectiveMoment H raw9973step0 := by
      have heq : raw9973step0 = raw9973.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw9973).symm
    injectiveMoment H raw9973step0 = injectiveMoment H raw9973step1 := by
      have heq : raw9973step1 = (fun i j => raw9973step0 (permutation27 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9973step0 permutation27 permutation4
    _ = injectiveMoment H node146 := by rfl

def raw9974 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, 2, -2], ![-1, -2, 0, 3], ![1, 2, -2, -1]]

def raw9974step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![0, -2, 2], ![2, 0, -2], ![-2, 3, -1]]

def raw9974step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]

theorem canonical9974 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9974 = injectiveMoment H node177 := by
  calc
    injectiveMoment H raw9974 = injectiveMoment H raw9974step0 := by
      have heq : raw9974step0 = raw9974.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw9974).symm
    injectiveMoment H raw9974step0 = injectiveMoment H raw9974step1 := by
      have heq : raw9974step1 = (fun i j => raw9974step0 (permutation27 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9974step0 permutation27 permutation4
    _ = injectiveMoment H node177 := by rfl

def raw9975 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, 2, -2], ![-1, -2, 1, 2], ![1, 2, -3, 0]]

def raw9975step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![0, -2, 2], ![2, 1, -3], ![-2, 2, 0]]

def raw9975step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 1, -1], ![0, 2, -2], ![-2, -1, 3], ![2, -2, 0]]

def raw9975step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]

theorem canonical9975 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9975 = injectiveMoment H node177 := by
  calc
    injectiveMoment H raw9975 = injectiveMoment H raw9975step0 := by
      have heq : raw9975step0 = raw9975.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw9975).symm
    injectiveMoment H raw9975step0 = injectiveMoment H raw9975step1 := by
      have heq : raw9975step1 = -raw9975step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9975step0).symm
    injectiveMoment H raw9975step1 = injectiveMoment H raw9975step2 := by
      have heq : raw9975step2 = (fun i j => raw9975step1 (permutation21 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9975step1 permutation21 permutation3
    _ = injectiveMoment H node177 := by rfl

def raw9976 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, 2, -2], ![-1, -2, 2, 1], ![1, 2, -4, 1]]

def raw9976step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![0, -2, 2], ![2, 2, -4], ![-2, 1, 1]]

def raw9976step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 1, -1], ![0, 2, -2], ![-2, -2, 4], ![2, -1, -1]]

def raw9976step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 2, -2], ![2, -1, -1]]

theorem canonical9976 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9976 = injectiveMoment H node146 := by
  calc
    injectiveMoment H raw9976 = injectiveMoment H raw9976step0 := by
      have heq : raw9976step0 = raw9976.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw9976).symm
    injectiveMoment H raw9976step0 = injectiveMoment H raw9976step1 := by
      have heq : raw9976step1 = -raw9976step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9976step0).symm
    injectiveMoment H raw9976step1 = injectiveMoment H raw9976step2 := by
      have heq : raw9976step2 = (fun i j => raw9976step1 (permutation21 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9976step1 permutation21 permutation3
    _ = injectiveMoment H node146 := by rfl

def raw9977 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, 2, -2], ![-1, -2, 3, 0], ![1, 2, -5, 2]]

def raw9977step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![0, -2, 2], ![2, 3, -5], ![-2, 0, 2]]

def raw9977step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 1, -1], ![0, 2, -2], ![-2, -3, 5], ![2, 0, -2]]

def raw9977step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 1, -1], ![0, 2, -2], ![2, 0, -2]]

theorem canonical9977 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9977 = injectiveMoment H node120 := by
  calc
    injectiveMoment H raw9977 = injectiveMoment H raw9977step0 := by
      have heq : raw9977step0 = raw9977.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw9977).symm
    injectiveMoment H raw9977step0 = injectiveMoment H raw9977step1 := by
      have heq : raw9977step1 = -raw9977step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9977step0).symm
    injectiveMoment H raw9977step1 = injectiveMoment H raw9977step2 := by
      have heq : raw9977step2 = (fun i j => raw9977step1 (permutation21 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9977step1 permutation21 permutation3
    _ = injectiveMoment H node120 := by rfl

def raw9978 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, 2, -2], ![-1, 2, 0, -1], ![1, -2, -2, 3]]

def raw9978step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![0, 2, -2], ![2, 0, -2], ![-2, -1, 3]]

def raw9978step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 2, -2], ![2, 0, -2]]

theorem canonical9978 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9978 = injectiveMoment H node169 := by
  calc
    injectiveMoment H raw9978 = injectiveMoment H raw9978step0 := by
      have heq : raw9978step0 = raw9978.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw9978).symm
    injectiveMoment H raw9978step0 = injectiveMoment H raw9978step1 := by
      have heq : raw9978step1 = (fun i j => raw9978step0 (permutation27 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9978step0 permutation27 permutation3
    _ = injectiveMoment H node169 := by rfl

def raw9979 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, 2, -2], ![-1, 2, 1, -2], ![1, -2, -3, 4]]

def raw9979step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![0, 2, -2], ![2, 1, -3], ![-2, -2, 4]]

def raw9979step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, -1, 1], ![0, 2, -2], ![2, 1, -3]]

theorem canonical9979 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9979 = injectiveMoment H node140 := by
  calc
    injectiveMoment H raw9979 = injectiveMoment H raw9979step0 := by
      have heq : raw9979step0 = raw9979.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw9979).symm
    injectiveMoment H raw9979step0 = injectiveMoment H raw9979step1 := by
      have heq : raw9979step1 = (fun i j => raw9979step0 (permutation27 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9979step0 permutation27 permutation3
    _ = injectiveMoment H node140 := by rfl

def raw9980 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, 2, -2], ![-1, 3, -2, 0], ![1, -3, 0, 2]]

def raw9980step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![0, 3, -3], ![2, -2, 0], ![-2, 0, 2]]

def raw9980step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 3, -3], ![2, -2, 0]]

theorem canonical9980 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9980 = injectiveMoment H node204 := by
  calc
    injectiveMoment H raw9980 = injectiveMoment H raw9980step0 := by
      have heq : raw9980step0 = raw9980.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw9980).symm
    injectiveMoment H raw9980step0 = injectiveMoment H raw9980step1 := by
      have heq : raw9980step1 = (fun i j => raw9980step0 (permutation27 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9980step0 permutation27 permutation3
    _ = injectiveMoment H node204 := by rfl

def raw9981 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, 2, -2], ![-1, 3, -1, -1], ![1, -3, -1, 3]]

def raw9981step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![0, 3, -3], ![2, -1, -1], ![-2, -1, 3]]

def raw9981step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 3, -3], ![2, -1, -1]]

theorem canonical9981 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9981 = injectiveMoment H node170 := by
  calc
    injectiveMoment H raw9981 = injectiveMoment H raw9981step0 := by
      have heq : raw9981step0 = raw9981.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw9981).symm
    injectiveMoment H raw9981step0 = injectiveMoment H raw9981step1 := by
      have heq : raw9981step1 = (fun i j => raw9981step0 (permutation27 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9981step0 permutation27 permutation3
    _ = injectiveMoment H node170 := by rfl

def raw9982 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, 2, -2], ![-1, 3, 0, -2], ![1, -3, -2, 4]]

def raw9982step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![0, 3, -3], ![2, 0, -2], ![-2, -2, 4]]

def raw9982step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, -1, 1], ![0, 3, -3], ![2, 0, -2]]

theorem canonical9982 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9982 = injectiveMoment H node141 := by
  calc
    injectiveMoment H raw9982 = injectiveMoment H raw9982step0 := by
      have heq : raw9982step0 = raw9982.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw9982).symm
    injectiveMoment H raw9982step0 = injectiveMoment H raw9982step1 := by
      have heq : raw9982step1 = (fun i j => raw9982step0 (permutation27 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9982step0 permutation27 permutation3
    _ = injectiveMoment H node141 := by rfl

def raw9983 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, 2, -2], ![-1, 4, -3, 0], ![1, -4, 1, 2]]

def raw9983step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![0, 4, -4], ![2, -3, 1], ![-2, 0, 2]]

def raw9983step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 1, -1], ![0, -4, 4], ![-2, 3, -1], ![2, 0, -2]]

def raw9983step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 4, -4], ![2, -2, 0]]

theorem canonical9983 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9983 = injectiveMoment H node171 := by
  calc
    injectiveMoment H raw9983 = injectiveMoment H raw9983step0 := by
      have heq : raw9983step0 = raw9983.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw9983).symm
    injectiveMoment H raw9983step0 = injectiveMoment H raw9983step1 := by
      have heq : raw9983step1 = -raw9983step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9983step0).symm
    injectiveMoment H raw9983step1 = injectiveMoment H raw9983step2 := by
      have heq : raw9983step2 = (fun i j => raw9983step1 (permutation21 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9983step1 permutation21 permutation4
    _ = injectiveMoment H node171 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
