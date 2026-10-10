import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes1
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes2
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes3
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes12
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes14
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes15
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes31
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes39
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes40
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes41
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes43

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw6944 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![1, -1, -3, 3], ![0, 2, 1, -3]]

def raw6944step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![2, -3, 1], ![0, 3, -3]]

def raw6944step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -1, 0], ![1, 1, -2], ![-2, 3, -1], ![0, -3, 3]]

def raw6944step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 3, -3], ![1, -2, 1], ![1, 0, -1]]

theorem canonical6944 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6944 = injectiveMoment H node187 := by
  calc
    injectiveMoment H raw6944 = injectiveMoment H raw6944step0 := by
      have heq : raw6944step0 = raw6944.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6944).symm
    injectiveMoment H raw6944step0 = injectiveMoment H raw6944step1 := by
      have heq : raw6944step1 = -raw6944step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6944step0).symm
    injectiveMoment H raw6944step1 = injectiveMoment H raw6944step2 := by
      have heq : raw6944step2 = (fun i j => raw6944step1 (permutation26 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6944step1 permutation26 permutation4
    _ = injectiveMoment H node187 := by rfl

def raw6945 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![1, -1, -2, 2], ![0, 2, 0, -2]]

def raw6945step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![2, -2, 0], ![0, 2, -2]]

def raw6945step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]

theorem canonical6945 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6945 = injectiveMoment H node203 := by
  calc
    injectiveMoment H raw6945 = injectiveMoment H raw6945step0 := by
      have heq : raw6945step0 = raw6945.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6945).symm
    injectiveMoment H raw6945step0 = injectiveMoment H raw6945step1 := by
      have heq : raw6945step1 = (fun i j => raw6945step0 (permutation28 i) (permutation7 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6945step0 permutation28 permutation7
    _ = injectiveMoment H node203 := by rfl

def raw6946 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![1, -1, 2, -2], ![0, 2, -4, 2]]

def raw6946step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![2, 2, -4], ![0, -2, 2]]

def raw6946step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -1, 0], ![1, 1, -2], ![-2, -2, 4], ![0, 2, -2]]

def raw6946step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![1, -1, 0], ![1, 1, -2]]

theorem canonical6946 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6946 = injectiveMoment H node153 := by
  calc
    injectiveMoment H raw6946 = injectiveMoment H raw6946step0 := by
      have heq : raw6946step0 = raw6946.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6946).symm
    injectiveMoment H raw6946step0 = injectiveMoment H raw6946step1 := by
      have heq : raw6946step1 = -raw6946step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6946step0).symm
    injectiveMoment H raw6946step1 = injectiveMoment H raw6946step2 := by
      have heq : raw6946step2 = (fun i j => raw6946step1 (permutation25 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6946step1 permutation25 permutation3
    _ = injectiveMoment H node153 := by rfl

def raw6947 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![2, -3, 0, 1], ![-1, 4, -2, -1]]

def raw6947step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, -3, 4], ![2, 0, -2], ![0, 1, -1]]

def raw6947step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -2, 1], ![1, 3, -4], ![-2, 0, 2], ![0, -1, 1]]

def raw6947step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![1, -2, 1], ![1, 3, -4]]

theorem canonical6947 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6947 = injectiveMoment H node206 := by
  calc
    injectiveMoment H raw6947 = injectiveMoment H raw6947step0 := by
      have heq : raw6947step0 = raw6947.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6947).symm
    injectiveMoment H raw6947step0 = injectiveMoment H raw6947step1 := by
      have heq : raw6947step1 = -raw6947step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6947step0).symm
    injectiveMoment H raw6947step1 = injectiveMoment H raw6947step2 := by
      have heq : raw6947step2 = (fun i j => raw6947step1 (permutation25 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6947step1 permutation25 permutation3
    _ = injectiveMoment H node206 := by rfl

def raw6948 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![2, -2, 1, -1], ![-1, 3, -3, 1]]

def raw6948step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, -2, 3], ![2, 1, -3], ![0, -1, 1]]

def raw6948step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -2, 1], ![1, 2, -3], ![-2, -1, 3], ![0, 1, -1]]

def raw6948step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 2, -3]]

theorem canonical6948 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6948 = injectiveMoment H node180 := by
  calc
    injectiveMoment H raw6948 = injectiveMoment H raw6948step0 := by
      have heq : raw6948step0 = raw6948.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6948).symm
    injectiveMoment H raw6948step0 = injectiveMoment H raw6948step1 := by
      have heq : raw6948step1 = -raw6948step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6948step0).symm
    injectiveMoment H raw6948step1 = injectiveMoment H raw6948step2 := by
      have heq : raw6948step2 = (fun i j => raw6948step1 (permutation25 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6948step1 permutation25 permutation3
    _ = injectiveMoment H node180 := by rfl

def raw6949 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![2, -1, 0, -1], ![-1, 2, -2, 1]]

def raw6949step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, -1, 2], ![2, 0, -2], ![0, -1, 1]]

def raw6949step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -2, 1], ![1, 1, -2], ![-2, 0, 2], ![0, 1, -1]]

def raw6949step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]

theorem canonical6949 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6949 = injectiveMoment H node210 := by
  calc
    injectiveMoment H raw6949 = injectiveMoment H raw6949step0 := by
      have heq : raw6949step0 = raw6949.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6949).symm
    injectiveMoment H raw6949step0 = injectiveMoment H raw6949step1 := by
      have heq : raw6949step1 = -raw6949step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6949step0).symm
    injectiveMoment H raw6949step1 = injectiveMoment H raw6949step2 := by
      have heq : raw6949step2 = (fun i j => raw6949step1 (permutation25 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6949step1 permutation25 permutation3
    _ = injectiveMoment H node210 := by rfl

def raw6950 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![2, -1, 1, -2], ![-1, 2, -3, 2]]

def raw6950step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, -1, 2], ![2, 1, -3], ![0, -2, 2]]

def raw6950step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -2, 1], ![1, 1, -2], ![-2, -1, 3], ![0, 2, -2]]

def raw6950step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, -2, 1], ![1, 1, -2]]

theorem canonical6950 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6950 = injectiveMoment H node184 := by
  calc
    injectiveMoment H raw6950 = injectiveMoment H raw6950step0 := by
      have heq : raw6950step0 = raw6950.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6950).symm
    injectiveMoment H raw6950step0 = injectiveMoment H raw6950step1 := by
      have heq : raw6950step1 = -raw6950step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6950step0).symm
    injectiveMoment H raw6950step1 = injectiveMoment H raw6950step2 := by
      have heq : raw6950step2 = (fun i j => raw6950step1 (permutation25 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6950step1 permutation25 permutation3
    _ = injectiveMoment H node184 := by rfl

def raw6951 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![3, -2, 0, -1], ![-2, 3, -2, 1]]

def raw6951step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, -2, 3], ![2, 0, -2], ![0, -1, 1]]

def raw6951step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![1, 2, -3], ![-2, 0, 2], ![0, 1, -1]]

def raw6951step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -3, 2], ![1, 2, -3]]

theorem canonical6951 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6951 = injectiveMoment H node209 := by
  calc
    injectiveMoment H raw6951 = injectiveMoment H raw6951step0 := by
      have heq : raw6951step0 = raw6951.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6951).symm
    injectiveMoment H raw6951step0 = injectiveMoment H raw6951step1 := by
      have heq : raw6951step1 = -raw6951step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6951step0).symm
    injectiveMoment H raw6951step1 = injectiveMoment H raw6951step2 := by
      have heq : raw6951step2 = (fun i j => raw6951step1 (permutation25 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6951step1 permutation25 permutation3
    _ = injectiveMoment H node209 := by rfl

def raw6952 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![3, -1, 0, -2], ![-2, 2, -2, 2]]

def raw6952step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, -1, 2], ![2, 0, -2], ![0, -2, 2]]

def raw6952step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![1, 1, -2], ![-2, 0, 2], ![0, 2, -2]]

def raw6952step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![1, -3, 2], ![1, 1, -2]]

theorem canonical6952 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6952 = injectiveMoment H node212 := by
  calc
    injectiveMoment H raw6952 = injectiveMoment H raw6952step0 := by
      have heq : raw6952step0 = raw6952.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6952).symm
    injectiveMoment H raw6952step0 = injectiveMoment H raw6952step1 := by
      have heq : raw6952step1 = -raw6952step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6952step0).symm
    injectiveMoment H raw6952step1 = injectiveMoment H raw6952step2 := by
      have heq : raw6952step2 = (fun i j => raw6952step1 (permutation25 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6952step1 permutation25 permutation3
    _ = injectiveMoment H node212 := by rfl

def raw6953 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 3, -1], ![-1, 0, -3, 4], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 1, 0, -2]]

def raw6953step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 1, -3, 1], ![1, 0, 3, -4], ![0, -1, 0, 1], ![-1, 1, 0, 0], ![-1, -1, 0, 2]]

def raw6953step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![-1, 0, 0, 1], ![0, 1, 3, -4], ![1, -1, 0, 0], ![1, 1, -3, 1]]

theorem canonical6953 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6953 = injectiveMoment H node2563 := by
  calc
    injectiveMoment H raw6953 = injectiveMoment H raw6953step0 := by
      have heq : raw6953step0 = -raw6953 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6953).symm
    injectiveMoment H raw6953step0 = injectiveMoment H raw6953step1 := by
      have heq : raw6953step1 = (fun i j => raw6953step0 (permutation142 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6953step0 permutation142 permutation15
    _ = injectiveMoment H node2563 := by rfl

def raw6954 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 3, -1], ![-1, 0, -3, 4], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def raw6954step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 3, -1], ![0, -1, -3, 4], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, 0, -1]]

theorem canonical6954 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6954 = injectiveMoment H node2677 := by
  calc
    injectiveMoment H raw6954 = injectiveMoment H raw6954step0 := by
      have heq : raw6954step0 = (fun i j => raw6954 (permutation36 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6954 permutation36 permutation15
    _ = injectiveMoment H node2677 := by rfl

def raw6955 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 3, -1], ![-1, 0, -3, 4], ![0, 2, 0, -2], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw6955step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 1, -3, 1], ![1, 0, 3, -4], ![0, -2, 0, 2], ![-1, 1, 0, 0], ![-1, 0, 0, 1]]

def raw6955step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 0, 1], ![0, 1, 3, -4], ![1, -1, 0, 0], ![1, 1, -3, 1]]

theorem canonical6955 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6955 = injectiveMoment H node2010 := by
  calc
    injectiveMoment H raw6955 = injectiveMoment H raw6955step0 := by
      have heq : raw6955step0 = -raw6955 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6955).symm
    injectiveMoment H raw6955step0 = injectiveMoment H raw6955step1 := by
      have heq : raw6955step1 = (fun i j => raw6955step0 (permutation101 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6955step0 permutation101 permutation15
    _ = injectiveMoment H node2010 := by rfl

def raw6956 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 3, -1], ![-1, 0, -2, 3], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 1, 0, -2]]

def raw6956step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 1, -3, 1], ![1, 0, 2, -3], ![0, -1, 0, 1], ![-1, 1, 1, -1], ![-1, -1, 0, 2]]

def raw6956step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![-1, 0, 0, 1], ![0, 1, 2, -3], ![1, -1, 1, -1], ![1, 1, -3, 1]]

theorem canonical6956 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6956 = injectiveMoment H node2562 := by
  calc
    injectiveMoment H raw6956 = injectiveMoment H raw6956step0 := by
      have heq : raw6956step0 = -raw6956 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6956).symm
    injectiveMoment H raw6956step0 = injectiveMoment H raw6956step1 := by
      have heq : raw6956step1 = (fun i j => raw6956step0 (permutation142 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6956step0 permutation142 permutation15
    _ = injectiveMoment H node2562 := by rfl

def raw6957 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 3, -1], ![-1, 0, -2, 3], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 0, -1]]

def raw6957step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 3, -2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0]]

theorem canonical6957 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6957 = injectiveMoment H node2545 := by
  calc
    injectiveMoment H raw6957 = injectiveMoment H raw6957step0 := by
      have heq : raw6957step0 = (fun i j => raw6957 (permutation38 i) (permutation16 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6957 permutation38 permutation16
    _ = injectiveMoment H node2545 := by rfl

def raw6958 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 3, -1], ![-1, 0, -2, 3], ![0, 2, 0, -2], ![1, -1, -1, 1], ![1, 0, 0, -1]]

def raw6958step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 1, -3, 1], ![1, 0, 2, -3], ![0, -2, 0, 2], ![-1, 1, 1, -1], ![-1, 0, 0, 1]]

def raw6958step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 0, 1], ![0, 1, 2, -3], ![1, -1, 1, -1], ![1, 1, -3, 1]]

theorem canonical6958 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6958 = injectiveMoment H node2009 := by
  calc
    injectiveMoment H raw6958 = injectiveMoment H raw6958step0 := by
      have heq : raw6958step0 = -raw6958 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6958).symm
    injectiveMoment H raw6958step0 = injectiveMoment H raw6958step1 := by
      have heq : raw6958step1 = (fun i j => raw6958step0 (permutation101 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6958step0 permutation101 permutation15
    _ = injectiveMoment H node2009 := by rfl

def raw6959 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 3, -1], ![-1, 1, -3, 3], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw6959step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 1, 0, 0], ![0, 1, -1, 0], ![1, -1, 3, -3], ![1, 0, -1, 0]]

theorem canonical6959 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6959 = injectiveMoment H node2525 := by
  calc
    injectiveMoment H raw6959 = injectiveMoment H raw6959step0 := by
      have heq : raw6959step0 = (fun i j => raw6959 (permutation49 i) (permutation16 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6959 permutation49 permutation16
    _ = injectiveMoment H node2525 := by rfl

def raw6960 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 3, -1], ![-1, 1, -2, 2], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 0, 0, -1]]

def raw6960step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 1, 1, -1], ![0, 1, -1, 0], ![1, -1, 2, -2], ![1, 0, -1, 0]]

theorem canonical6960 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6960 = injectiveMoment H node2527 := by
  calc
    injectiveMoment H raw6960 = injectiveMoment H raw6960step0 := by
      have heq : raw6960step0 = (fun i j => raw6960 (permutation49 i) (permutation16 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6960 permutation49 permutation16
    _ = injectiveMoment H node2527 := by rfl

def raw6961 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 3, -1], ![-1, 3, -2, 0], ![2, -2, -1, 1]]

def raw6961step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 3, -2], ![3, -2, -1], ![-1, 0, 1]]

def raw6961step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![1, -3, 2], ![-3, 2, 1], ![1, 0, -1]]

def raw6961step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]

theorem canonical6961 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6961 = injectiveMoment H node109 := by
  calc
    injectiveMoment H raw6961 = injectiveMoment H raw6961step0 := by
      have heq : raw6961step0 = raw6961.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6961).symm
    injectiveMoment H raw6961step0 = injectiveMoment H raw6961step1 := by
      have heq : raw6961step1 = -raw6961step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6961step0).symm
    injectiveMoment H raw6961step1 = injectiveMoment H raw6961step2 := by
      have heq : raw6961step2 = (fun i j => raw6961step1 (permutation19 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6961step1 permutation19 permutation5
    _ = injectiveMoment H node109 := by rfl

def raw6962 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 3, -1], ![0, -1, -3, 4], ![0, 1, 0, -1], ![1, 1, 0, -2]]

def raw6962step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, -1, 1, 1], ![3, -3, 0, 0], ![-1, 4, -1, -2]]

def raw6962step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 3, -3], ![0, 1, -1, 0], ![1, 1, -1, -1]]

theorem canonical6962 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6962 = injectiveMoment H node779 := by
  calc
    injectiveMoment H raw6962 = injectiveMoment H raw6962step0 := by
      have heq : raw6962step0 = raw6962.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6962).symm
    injectiveMoment H raw6962step0 = injectiveMoment H raw6962step1 := by
      have heq : raw6962step1 = (fun i j => raw6962step0 (permutation31 i) (permutation25 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6962step0 permutation31 permutation25
    _ = injectiveMoment H node779 := by rfl

def raw6963 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 3, -1], ![0, -1, -3, 4], ![0, 2, 0, -2], ![1, 0, 0, -1]]

def raw6963step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, -1, 2, 0], ![3, -3, 0, 0], ![-1, 4, -2, -1]]

def raw6963step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 3, -3], ![0, 2, -1, -1], ![1, 0, -1, 0]]

theorem canonical6963 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6963 = injectiveMoment H node782 := by
  calc
    injectiveMoment H raw6963 = injectiveMoment H raw6963step0 := by
      have heq : raw6963step0 = raw6963.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6963).symm
    injectiveMoment H raw6963step0 = injectiveMoment H raw6963step1 := by
      have heq : raw6963step1 = (fun i j => raw6963step0 (permutation32 i) (permutation31 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6963step0 permutation32 permutation31
    _ = injectiveMoment H node782 := by rfl

def raw6964 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 3, -1], ![0, 0, -3, 3], ![0, 1, 0, -1], ![1, 0, 0, -1]]

def raw6964step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 3, -3], ![0, 1, -1, 0], ![1, 0, -1, 0]]

theorem canonical6964 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6964 = injectiveMoment H node978 := by
  calc
    injectiveMoment H raw6964 = injectiveMoment H raw6964step0 := by
      have heq : raw6964step0 = (fun i j => raw6964 (permutation9 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6964 permutation9 permutation10
    _ = injectiveMoment H node978 := by rfl

def raw6965 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 3, -1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 2, -1, -1], ![1, -1, 0, 0]]

def raw6965step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 2, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -1, 0]]

theorem canonical6965 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6965 = injectiveMoment H node2542 := by
  calc
    injectiveMoment H raw6965 = injectiveMoment H raw6965step0 := by
      have heq : raw6965step0 = (fun i j => raw6965 (permutation45 i) (permutation13 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6965 permutation45 permutation13
    _ = injectiveMoment H node2542 := by rfl

def raw6966 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 3, -1], ![0, 0, -1, 1], ![0, 2, -1, -1], ![1, -1, -1, 1]]

def raw6966step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 2, -1], ![0, 1, 0, -1], ![1, 1, -1, -1]]

theorem canonical6966 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6966 = injectiveMoment H node942 := by
  calc
    injectiveMoment H raw6966 = injectiveMoment H raw6966step0 := by
      have heq : raw6966step0 = (fun i j => raw6966 (permutation11 i) (permutation13 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6966 permutation11 permutation13
    _ = injectiveMoment H node942 := by rfl

def raw6967 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 3, -1], ![0, 2, -1, -1], ![1, -1, -2, 2]]

def raw6967step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 2, -1], ![3, -1, -2], ![-1, -1, 2]]

def raw6967step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![1, -2, 1], ![-3, 1, 2], ![1, 1, -2]]

def raw6967step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -2, 1], ![1, 2, -3]]

theorem canonical6967 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6967 = injectiveMoment H node229 := by
  calc
    injectiveMoment H raw6967 = injectiveMoment H raw6967step0 := by
      have heq : raw6967step0 = raw6967.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6967).symm
    injectiveMoment H raw6967step0 = injectiveMoment H raw6967step1 := by
      have heq : raw6967step1 = -raw6967step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6967step0).symm
    injectiveMoment H raw6967step1 = injectiveMoment H raw6967step2 := by
      have heq : raw6967step2 = (fun i j => raw6967step1 (permutation16 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6967step1 permutation16 permutation6
    _ = injectiveMoment H node229 := by rfl

def raw6968 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 3, -1], ![0, 2, 0, -2], ![1, -1, -3, 3]]

def raw6968step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 2, -1], ![3, 0, -3], ![-1, -2, 3]]

def raw6968step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 3, -3], ![2, -1, -1]]

theorem canonical6968 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6968 = injectiveMoment H node170 := by
  calc
    injectiveMoment H raw6968 = injectiveMoment H raw6968step0 := by
      have heq : raw6968step0 = raw6968.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6968).symm
    injectiveMoment H raw6968step0 = injectiveMoment H raw6968step1 := by
      have heq : raw6968step1 = (fun i j => raw6968step0 (permutation28 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6968step0 permutation28 permutation5
    _ = injectiveMoment H node170 := by rfl

def raw6969 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 3, -1], ![0, 3, -2, -1], ![1, -2, -1, 2]]

def raw6969step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 3, -2], ![3, -2, -1], ![-1, -1, 2]]

def raw6969step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![1, -3, 2], ![-3, 2, 1], ![1, 1, -2]]

def raw6969step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]

theorem canonical6969 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6969 = injectiveMoment H node109 := by
  calc
    injectiveMoment H raw6969 = injectiveMoment H raw6969step0 := by
      have heq : raw6969step0 = raw6969.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6969).symm
    injectiveMoment H raw6969step0 = injectiveMoment H raw6969step1 := by
      have heq : raw6969step1 = -raw6969step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6969step0).symm
    injectiveMoment H raw6969step1 = injectiveMoment H raw6969step2 := by
      have heq : raw6969step2 = (fun i j => raw6969step1 (permutation16 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6969step1 permutation16 permutation5
    _ = injectiveMoment H node109 := by rfl

def raw6970 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 3, -1], ![1, -2, 1, 0], ![0, 3, -4, 1]]

def raw6970step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -2, 3], ![3, 1, -4], ![-1, 0, 1]]

def raw6970step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 3, -4]]

theorem canonical6970 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6970 = injectiveMoment H node173 := by
  calc
    injectiveMoment H raw6970 = injectiveMoment H raw6970step0 := by
      have heq : raw6970step0 = raw6970.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6970).symm
    injectiveMoment H raw6970step0 = injectiveMoment H raw6970step1 := by
      have heq : raw6970step1 = (fun i j => raw6970step0 (permutation19 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6970step0 permutation19 permutation5
    _ = injectiveMoment H node173 := by rfl

def raw6971 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 3, -1], ![2, -2, 1, -1], ![-1, 3, -4, 2]]

def raw6971step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, -2, 3], ![3, 1, -4], ![-1, -1, 2]]

def raw6971step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -2, 1], ![1, 2, -3], ![-3, -1, 4], ![1, 1, -2]]

def raw6971step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -2, 1], ![1, 1, -2], ![1, 2, -3]]

theorem canonical6971 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6971 = injectiveMoment H node89 := by
  calc
    injectiveMoment H raw6971 = injectiveMoment H raw6971step0 := by
      have heq : raw6971step0 = raw6971.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6971).symm
    injectiveMoment H raw6971step0 = injectiveMoment H raw6971step1 := by
      have heq : raw6971step1 = -raw6971step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6971step0).symm
    injectiveMoment H raw6971step1 = injectiveMoment H raw6971step2 := by
      have heq : raw6971step2 = (fun i j => raw6971step1 (permutation22 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6971step1 permutation22 permutation3
    _ = injectiveMoment H node89 := by rfl

def raw6972 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![-1, -1, 2, 0], ![1, 0, 1, -2], ![1, 1, 0, -2]]

def raw6972step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 3, -4], ![1, 1, -2, 0], ![-1, 0, -1, 2], ![-1, -1, 0, 2]]

def raw6972step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, -1, 2], ![0, 1, 3, -4], ![1, 1, -2, 0]]

theorem canonical6972 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6972 = injectiveMoment H node996 := by
  calc
    injectiveMoment H raw6972 = injectiveMoment H raw6972step0 := by
      have heq : raw6972step0 = -raw6972 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6972).symm
    injectiveMoment H raw6972step0 = injectiveMoment H raw6972step1 := by
      have heq : raw6972step1 = (fun i j => raw6972step0 (permutation31 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6972step0 permutation31 permutation15
    _ = injectiveMoment H node996 := by rfl

def raw6973 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![-1, 0, 3, -2], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw6973step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 0, 3, -4], ![1, 0, -3, 2], ![0, -1, 0, 1], ![-1, 1, 0, 0], ![-1, 0, 0, 1]]

def raw6973step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, 1, -3, 2], ![0, 1, 3, -4], ![1, -1, 0, 0]]

theorem canonical6973 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6973 = injectiveMoment H node2766 := by
  calc
    injectiveMoment H raw6973 = injectiveMoment H raw6973step0 := by
      have heq : raw6973step0 = -raw6973 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6973).symm
    injectiveMoment H raw6973step0 = injectiveMoment H raw6973step1 := by
      have heq : raw6973step1 = (fun i j => raw6973step0 (permutation100 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6973step0 permutation100 permutation15
    _ = injectiveMoment H node2766 := by rfl

def raw6974 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![-1, 1, 1, -1], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, -1, 1, -1]]

theorem canonical6974 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6974 = injectiveMoment H node2678 := by
  rfl

def raw6975 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![-1, 1, 1, -1], ![0, 1, 1, -2], ![1, -1, 1, -1], ![1, -1, 0, 0]]

def raw6975step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![-1, 1, 1, -1], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, -1, 1, -1]]

theorem canonical6975 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6975 = injectiveMoment H node2678 := by
  calc
    injectiveMoment H raw6975 = injectiveMoment H raw6975step0 := by
      have heq : raw6975step0 = (fun i j => raw6975 (permutation34 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6975 permutation34 permutation9
    _ = injectiveMoment H node2678 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
