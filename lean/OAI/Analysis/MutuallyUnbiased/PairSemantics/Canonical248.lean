import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes1
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes2
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes3
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes4
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes12
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes14
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes15
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes19
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes20
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes21

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw7936 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 1, 1, -1], ![0, 0, 1, -1], ![1, -1, -2, 2]]

def raw7936step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![-1, -1, 2]]

def raw7936step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2]]

theorem canonical7936 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7936 = injectiveMoment H node283 := by
  calc
    injectiveMoment H raw7936 = injectiveMoment H raw7936step0 := by
      have heq : raw7936step0 = raw7936.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7936).symm
    injectiveMoment H raw7936step0 = injectiveMoment H raw7936step1 := by
      have heq : raw7936step1 = (fun i j => raw7936step0 (permutation27 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7936step0 permutation27 permutation5
    _ = injectiveMoment H node283 := by rfl

def raw7937 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 1, 1, -1], ![0, 0, 2, -2], ![1, -1, -3, 3]]

def raw7937step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![1, 0, -1], ![1, 2, -3], ![-1, -2, 3]]

def raw7937step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![2, 1, -3]]

theorem canonical7937 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7937 = injectiveMoment H node168 := by
  calc
    injectiveMoment H raw7937 = injectiveMoment H raw7937step0 := by
      have heq : raw7937step0 = raw7937.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7937).symm
    injectiveMoment H raw7937step0 = injectiveMoment H raw7937step1 := by
      have heq : raw7937step1 = (fun i j => raw7937step0 (permutation27 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7937step0 permutation27 permutation5
    _ = injectiveMoment H node168 := by rfl

def raw7938 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 1, 1, -1], ![0, 1, 1, -2], ![1, -2, -2, 3]]

def raw7938step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![1, 1, -2], ![1, 1, -2], ![-1, -2, 3]]

def raw7938step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![1, 1, -2], ![1, 1, -2]]

theorem canonical7938 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7938 = injectiveMoment H node175 := by
  calc
    injectiveMoment H raw7938 = injectiveMoment H raw7938step0 := by
      have heq : raw7938step0 = raw7938.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7938).symm
    injectiveMoment H raw7938step0 = injectiveMoment H raw7938step1 := by
      have heq : raw7938step1 = (fun i j => raw7938step0 (permutation27 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7938step0 permutation27 permutation5
    _ = injectiveMoment H node175 := by rfl

def raw7939 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 1, 1, -1], ![0, 1, 2, -3], ![1, -2, -3, 4]]

def raw7939step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![1, 1, -2], ![1, 2, -3], ![-1, -3, 4]]

def raw7939step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 0, 1], ![1, 1, -2], ![1, 2, -3]]

theorem canonical7939 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7939 = injectiveMoment H node241 := by
  calc
    injectiveMoment H raw7939 = injectiveMoment H raw7939step0 := by
      have heq : raw7939step0 = raw7939.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7939).symm
    injectiveMoment H raw7939step0 = injectiveMoment H raw7939step1 := by
      have heq : raw7939step1 = (fun i j => raw7939step0 (permutation27 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7939step0 permutation27 permutation3
    _ = injectiveMoment H node241 := by rfl

def raw7940 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 1, 1, -1], ![1, -4, 2, 1], ![0, 3, -3, 0]]

def raw7940step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![1, -4, 3], ![1, 2, -3], ![-1, 1, 0]]

def raw7940step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -1, 0], ![-1, 4, -3], ![-1, -2, 3], ![1, -1, 0]]

def raw7940step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 3, -2], ![1, 0, -1], ![1, 0, -1]]

theorem canonical7940 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7940 = injectiveMoment H node248 := by
  calc
    injectiveMoment H raw7940 = injectiveMoment H raw7940step0 := by
      have heq : raw7940step0 = raw7940.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7940).symm
    injectiveMoment H raw7940step0 = injectiveMoment H raw7940step1 := by
      have heq : raw7940step1 = -raw7940step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7940step0).symm
    injectiveMoment H raw7940step1 = injectiveMoment H raw7940step2 := by
      have heq : raw7940step2 = (fun i j => raw7940step1 (permutation17 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7940step1 permutation17 permutation4
    _ = injectiveMoment H node248 := by rfl

def raw7941 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 1, 1, -1], ![1, -3, 1, 1], ![0, 2, -2, 0]]

def raw7941step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![1, -3, 2], ![1, 1, -2], ![-1, 1, 0]]

def raw7941step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -1, 0], ![-1, 3, -2], ![-1, -1, 2], ![1, -1, 0]]

def raw7941step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]

theorem canonical7941 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7941 = injectiveMoment H node176 := by
  calc
    injectiveMoment H raw7941 = injectiveMoment H raw7941step0 := by
      have heq : raw7941step0 = raw7941.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7941).symm
    injectiveMoment H raw7941step0 = injectiveMoment H raw7941step1 := by
      have heq : raw7941step1 = -raw7941step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7941step0).symm
    injectiveMoment H raw7941step1 = injectiveMoment H raw7941step2 := by
      have heq : raw7941step2 = (fun i j => raw7941step1 (permutation16 i) (permutation7 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7941step1 permutation16 permutation7
    _ = injectiveMoment H node176 := by rfl

def raw7942 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 1, 1, -1], ![1, 1, 1, -3], ![0, -2, -2, 4]]

def raw7942step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![1, 1, -2], ![1, 1, -2], ![-1, -3, 4]]

def raw7942step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 1, 0], ![1, 1, -2], ![1, 1, -2]]

theorem canonical7942 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7942 = injectiveMoment H node244 := by
  calc
    injectiveMoment H raw7942 = injectiveMoment H raw7942step0 := by
      have heq : raw7942step0 = raw7942.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7942).symm
    injectiveMoment H raw7942step0 = injectiveMoment H raw7942step1 := by
      have heq : raw7942step1 = (fun i j => raw7942step0 (permutation27 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7942step0 permutation27 permutation3
    _ = injectiveMoment H node244 := by rfl

def raw7943 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 1, 2, -2], ![-1, -3, 2, 2], ![2, 2, -4, 0]]

def raw7943step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![1, -3, 2], ![2, 2, -4], ![-2, 2, 0]]

def raw7943step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 3, -2], ![-2, -2, 4], ![2, -2, 0]]

def raw7943step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 3, -2], ![1, 1, -2], ![2, -2, 0]]

theorem canonical7943 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7943 = injectiveMoment H node136 := by
  calc
    injectiveMoment H raw7943 = injectiveMoment H raw7943step0 := by
      have heq : raw7943step0 = raw7943.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7943).symm
    injectiveMoment H raw7943step0 = injectiveMoment H raw7943step1 := by
      have heq : raw7943step1 = -raw7943step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7943step0).symm
    injectiveMoment H raw7943step1 = injectiveMoment H raw7943step2 := by
      have heq : raw7943step2 = (fun i j => raw7943step1 (permutation23 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7943step1 permutation23 permutation3
    _ = injectiveMoment H node136 := by rfl

def raw7944 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 1, 2, -2], ![-1, 3, -3, 1], ![2, -4, 1, 1]]

def raw7944step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![1, 3, -4], ![2, -3, 1], ![-2, 1, 1]]

def raw7944step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![-1, -3, 4], ![-2, 3, -1], ![2, -1, -1]]

def raw7944step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 4, -3], ![1, -2, 1], ![2, -1, -1]]

theorem canonical7944 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7944 = injectiveMoment H node161 := by
  calc
    injectiveMoment H raw7944 = injectiveMoment H raw7944step0 := by
      have heq : raw7944step0 = raw7944.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7944).symm
    injectiveMoment H raw7944step0 = injectiveMoment H raw7944step1 := by
      have heq : raw7944step1 = -raw7944step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7944step0).symm
    injectiveMoment H raw7944step1 = injectiveMoment H raw7944step2 := by
      have heq : raw7944step2 = (fun i j => raw7944step1 (permutation23 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7944step1 permutation23 permutation4
    _ = injectiveMoment H node161 := by rfl

def raw7945 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 1, 2, -2], ![-1, 3, -2, 0], ![2, -4, 0, 2]]

def raw7945step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![1, 3, -4], ![2, -2, 0], ![-2, 0, 2]]

def raw7945step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![-1, -3, 4], ![-2, 2, 0], ![2, 0, -2]]

def raw7945step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]

theorem canonical7945 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7945 = injectiveMoment H node85 := by
  calc
    injectiveMoment H raw7945 = injectiveMoment H raw7945step0 := by
      have heq : raw7945step0 = raw7945.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7945).symm
    injectiveMoment H raw7945step0 = injectiveMoment H raw7945step1 := by
      have heq : raw7945step1 = -raw7945step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7945step0).symm
    injectiveMoment H raw7945step1 = injectiveMoment H raw7945step2 := by
      have heq : raw7945step2 = (fun i j => raw7945step1 (permutation19 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7945step1 permutation19 permutation5
    _ = injectiveMoment H node85 := by rfl

def raw7946 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 1, 2, -2], ![0, -3, 2, 1], ![1, 2, -4, 1]]

def raw7946step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![1, -3, 2], ![2, 2, -4], ![-2, 1, 1]]

def raw7946step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![2, 2, -4]]

theorem canonical7946 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7946 = injectiveMoment H node106 := by
  calc
    injectiveMoment H raw7946 = injectiveMoment H raw7946step0 := by
      have heq : raw7946step0 = raw7946.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7946).symm
    injectiveMoment H raw7946step0 = injectiveMoment H raw7946step1 := by
      have heq : raw7946step1 = (fun i j => raw7946step0 (permutation16 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7946step0 permutation16 permutation5
    _ = injectiveMoment H node106 := by rfl

def raw7947 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, 2, -2], ![0, -2, 0, 2], ![0, 1, 0, -1], ![1, 0, -2, 1]]

def raw7947step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, -1, -2, 2], ![0, 2, 0, -2], ![0, -1, 0, 1], ![-1, 0, 2, -1]]

def raw7947step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -1, 0, 1], ![0, 2, 0, -2], ![1, -1, -2, 2]]

theorem canonical7947 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7947 = injectiveMoment H node1311 := by
  calc
    injectiveMoment H raw7947 = injectiveMoment H raw7947step0 := by
      have heq : raw7947step0 = -raw7947 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7947).symm
    injectiveMoment H raw7947step0 = injectiveMoment H raw7947step1 := by
      have heq : raw7947step1 = (fun i j => raw7947step0 (permutation32 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7947step0 permutation32 permutation9
    _ = injectiveMoment H node1311 := by rfl

def raw7948 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 1, 2, -2], ![0, -2, 2, 0], ![1, 1, -4, 2]]

def raw7948step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![1, -2, 1], ![2, 2, -4], ![-2, 0, 2]]

def raw7948step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![-1, 2, -1], ![-2, -2, 4], ![2, 0, -2]]

def raw7948step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 2, -2], ![2, -1, -1]]

theorem canonical7948 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7948 = injectiveMoment H node146 := by
  calc
    injectiveMoment H raw7948 = injectiveMoment H raw7948step0 := by
      have heq : raw7948step0 = raw7948.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7948).symm
    injectiveMoment H raw7948step0 = injectiveMoment H raw7948step1 := by
      have heq : raw7948step1 = -raw7948step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7948step0).symm
    injectiveMoment H raw7948step1 = injectiveMoment H raw7948step2 := by
      have heq : raw7948step2 = (fun i j => raw7948step1 (permutation22 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7948step1 permutation22 permutation5
    _ = injectiveMoment H node146 := by rfl

def raw7949 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, 2, -2], ![0, -1, -1, 2], ![0, 1, 0, -1], ![1, -1, -1, 1]]

def raw7949step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, -1, -2, 2], ![0, 1, 1, -2], ![0, -1, 0, 1], ![-1, 1, 1, -1]]

def raw7949step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, 1, -1], ![0, -1, 0, 1], ![0, 1, 1, -2], ![1, -1, -2, 2]]

theorem canonical7949 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7949 = injectiveMoment H node1362 := by
  calc
    injectiveMoment H raw7949 = injectiveMoment H raw7949step0 := by
      have heq : raw7949step0 = -raw7949 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7949).symm
    injectiveMoment H raw7949step0 = injectiveMoment H raw7949step1 := by
      have heq : raw7949step1 = (fun i j => raw7949step0 (permutation32 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7949step0 permutation32 permutation9
    _ = injectiveMoment H node1362 := by rfl

def raw7950 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 1, 2, -2], ![0, 1, 0, -1], ![1, -2, -2, 3]]

def raw7950step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![1, 1, -2], ![2, 0, -2], ![-2, -1, 3]]

def raw7950step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2]]

theorem canonical7950 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7950 = injectiveMoment H node268 := by
  calc
    injectiveMoment H raw7950 = injectiveMoment H raw7950step0 := by
      have heq : raw7950step0 = raw7950.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7950).symm
    injectiveMoment H raw7950step0 = injectiveMoment H raw7950step1 := by
      have heq : raw7950step1 = (fun i j => raw7950step0 (permutation28 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7950step0 permutation28 permutation5
    _ = injectiveMoment H node268 := by rfl

def raw7951 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 1, 2, -2], ![0, 1, 1, -2], ![1, -2, -3, 4]]

def raw7951step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![1, 1, -2], ![2, 1, -3], ![-2, -2, 4]]

def raw7951step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, -1, 1], ![1, 1, -2], ![1, 2, -3]]

theorem canonical7951 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7951 = injectiveMoment H node144 := by
  calc
    injectiveMoment H raw7951 = injectiveMoment H raw7951step0 := by
      have heq : raw7951step0 = raw7951.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7951).symm
    injectiveMoment H raw7951step0 = injectiveMoment H raw7951step1 := by
      have heq : raw7951step1 = (fun i j => raw7951step0 (permutation27 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7951step0 permutation27 permutation5
    _ = injectiveMoment H node144 := by rfl

def raw7952 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 1, 2, -2], ![0, 3, -3, 0], ![1, -4, 1, 2]]

def raw7952step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![1, 3, -4], ![2, -3, 1], ![-2, 0, 2]]

def raw7952step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![-1, -3, 4], ![-2, 3, -1], ![2, 0, -2]]

def raw7952step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![3, -2, -1]]

theorem canonical7952 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7952 = injectiveMoment H node81 := by
  calc
    injectiveMoment H raw7952 = injectiveMoment H raw7952step0 := by
      have heq : raw7952step0 = raw7952.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7952).symm
    injectiveMoment H raw7952step0 = injectiveMoment H raw7952step1 := by
      have heq : raw7952step1 = -raw7952step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7952step0).symm
    injectiveMoment H raw7952step1 = injectiveMoment H raw7952step2 := by
      have heq : raw7952step2 = (fun i j => raw7952step1 (permutation16 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7952step1 permutation16 permutation5
    _ = injectiveMoment H node81 := by rfl

def raw7953 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 1, 2, -2], ![0, 3, -2, -1], ![1, -4, 0, 3]]

def raw7953step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![1, 3, -4], ![2, -2, 0], ![-2, -1, 3]]

def raw7953step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![-1, -3, 4], ![-2, 2, 0], ![2, 1, -3]]

def raw7953step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 2, -3], ![2, -2, 0]]

theorem canonical7953 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7953 = injectiveMoment H node83 := by
  calc
    injectiveMoment H raw7953 = injectiveMoment H raw7953step0 := by
      have heq : raw7953step0 = raw7953.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7953).symm
    injectiveMoment H raw7953step0 = injectiveMoment H raw7953step1 := by
      have heq : raw7953step1 = -raw7953step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7953step0).symm
    injectiveMoment H raw7953step1 = injectiveMoment H raw7953step2 := by
      have heq : raw7953step2 = (fun i j => raw7953step1 (permutation16 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7953step1 permutation16 permutation5
    _ = injectiveMoment H node83 := by rfl

def raw7954 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 1, 2, -2], ![1, -3, 2, 0], ![0, 2, -4, 2]]

def raw7954step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![1, -3, 2], ![2, 2, -4], ![-2, 0, 2]]

def raw7954step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![2, 2, -4]]

theorem canonical7954 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7954 = injectiveMoment H node102 := by
  calc
    injectiveMoment H raw7954 = injectiveMoment H raw7954step0 := by
      have heq : raw7954step0 = raw7954.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7954).symm
    injectiveMoment H raw7954step0 = injectiveMoment H raw7954step1 := by
      have heq : raw7954step1 = (fun i j => raw7954step0 (permutation19 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7954step0 permutation19 permutation5
    _ = injectiveMoment H node102 := by rfl

def raw7955 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 1, 2, -2], ![1, -2, 2, -1], ![0, 1, -4, 3]]

def raw7955step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![1, -2, 1], ![2, 2, -4], ![-2, -1, 3]]

def raw7955step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -1, 0], ![-1, 2, -1], ![-2, -2, 4], ![2, 1, -3]]

def raw7955step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 2, -3], ![2, -1, -1]]

theorem canonical7955 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7955 = injectiveMoment H node132 := by
  calc
    injectiveMoment H raw7955 = injectiveMoment H raw7955step0 := by
      have heq : raw7955step0 = raw7955.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7955).symm
    injectiveMoment H raw7955step0 = injectiveMoment H raw7955step1 := by
      have heq : raw7955step1 = -raw7955step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7955step0).symm
    injectiveMoment H raw7955step1 = injectiveMoment H raw7955step2 := by
      have heq : raw7955step2 = (fun i j => raw7955step1 (permutation22 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7955step1 permutation22 permutation5
    _ = injectiveMoment H node132 := by rfl

def raw7956 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 2, -3, 2], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -2, 1, 0]]

def raw7956step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![2, 0, 0, -2], ![-3, 1, 1, 1], ![2, -1, -1, 0]]

def raw7956step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 0, -1], ![-2, 0, 0, 2], ![3, -1, -1, -1], ![-2, 1, 1, 0]]

def raw7956step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, -1, 1], ![0, 0, 2, -2], ![1, 1, 0, -2]]

theorem canonical7956 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7956 = injectiveMoment H node959 := by
  calc
    injectiveMoment H raw7956 = injectiveMoment H raw7956step0 := by
      have heq : raw7956step0 = raw7956.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7956).symm
    injectiveMoment H raw7956step0 = injectiveMoment H raw7956step1 := by
      have heq : raw7956step1 = -raw7956step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7956step0).symm
    injectiveMoment H raw7956step1 = injectiveMoment H raw7956step2 := by
      have heq : raw7956step2 = (fun i j => raw7956step1 (permutation21 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7956step1 permutation21 permutation18
    _ = injectiveMoment H node959 := by rfl

def raw7957 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 2, -3, 2], ![0, 0, 1, -1], ![0, 0, 2, -2], ![1, -2, 0, 1]]

def raw7957step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![2, 0, 0, -2], ![-3, 1, 2, 0], ![2, -1, -2, 1]]

def raw7957step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 0, -1], ![-2, 0, 0, 2], ![3, -1, -2, 0], ![-2, 1, 2, -1]]

def raw7957step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, -1, 1], ![0, 0, 2, -2], ![1, 2, -1, -2]]

theorem canonical7957 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7957 = injectiveMoment H node796 := by
  calc
    injectiveMoment H raw7957 = injectiveMoment H raw7957step0 := by
      have heq : raw7957step0 = raw7957.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7957).symm
    injectiveMoment H raw7957step0 = injectiveMoment H raw7957step1 := by
      have heq : raw7957step1 = -raw7957step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7957step0).symm
    injectiveMoment H raw7957step1 = injectiveMoment H raw7957step2 := by
      have heq : raw7957step2 = (fun i j => raw7957step1 (permutation21 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7957step1 permutation21 permutation18
    _ = injectiveMoment H node796 := by rfl

def raw7958 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 2, -3, 2], ![0, 0, 2, -2], ![0, 0, 1, -1], ![1, -2, 0, 1]]

def raw7958step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![2, 0, 0, -2], ![-3, 2, 1, 0], ![2, -2, -1, 1]]

def raw7958step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 0, -1], ![-2, 0, 0, 2], ![3, -2, -1, 0], ![-2, 2, 1, -1]]

def raw7958step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, -1, 1], ![0, 0, 2, -2], ![1, 2, -1, -2]]

theorem canonical7958 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7958 = injectiveMoment H node796 := by
  calc
    injectiveMoment H raw7958 = injectiveMoment H raw7958step0 := by
      have heq : raw7958step0 = raw7958.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7958).symm
    injectiveMoment H raw7958step0 = injectiveMoment H raw7958step1 := by
      have heq : raw7958step1 = -raw7958step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7958step0).symm
    injectiveMoment H raw7958step1 = injectiveMoment H raw7958step2 := by
      have heq : raw7958step2 = (fun i j => raw7958step1 (permutation21 i) (permutation24 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7958step1 permutation21 permutation24
    _ = injectiveMoment H node796 := by rfl

def raw7959 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 2, -2, 1], ![0, -1, -1, 2], ![0, -1, 2, -1], ![1, 0, 1, -2]]

def raw7959step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, -2, 2, -1], ![0, 1, 1, -2], ![0, 1, -2, 1], ![-1, 0, -1, 2]]

def raw7959step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 1, -2, 1], ![0, 1, 1, -2], ![1, -2, 2, -1]]

theorem canonical7959 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7959 = injectiveMoment H node1276 := by
  calc
    injectiveMoment H raw7959 = injectiveMoment H raw7959step0 := by
      have heq : raw7959step0 = -raw7959 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7959).symm
    injectiveMoment H raw7959step0 = injectiveMoment H raw7959step1 := by
      have heq : raw7959step1 = (fun i j => raw7959step0 (permutation32 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7959step0 permutation32 permutation9
    _ = injectiveMoment H node1276 := by rfl

def raw7960 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 2, -2, 1], ![0, -1, -1, 2], ![0, -1, 3, -2], ![1, 0, 0, -1]]

def raw7960step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, -2, 2, -1], ![0, 1, 1, -2], ![0, 1, -3, 2], ![-1, 0, 0, 1]]

def raw7960step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 1, -3, 2], ![0, 1, 1, -2], ![1, -2, 2, -1]]

theorem canonical7960 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7960 = injectiveMoment H node1286 := by
  calc
    injectiveMoment H raw7960 = injectiveMoment H raw7960step0 := by
      have heq : raw7960step0 = -raw7960 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7960).symm
    injectiveMoment H raw7960step0 = injectiveMoment H raw7960step1 := by
      have heq : raw7960step1 = (fun i j => raw7960step0 (permutation32 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7960step0 permutation32 permutation9
    _ = injectiveMoment H node1286 := by rfl

def raw7961 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 2, -2, 1], ![0, -1, 3, -2], ![1, -1, -1, 1]]

def raw7961step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![2, -1, -1], ![-2, 3, -1], ![1, -2, 1]]

def raw7961step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2]]

theorem canonical7961 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7961 = injectiveMoment H node261 := by
  calc
    injectiveMoment H raw7961 = injectiveMoment H raw7961step0 := by
      have heq : raw7961step0 = raw7961.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7961).symm
    injectiveMoment H raw7961step0 = injectiveMoment H raw7961step1 := by
      have heq : raw7961step1 = (fun i j => raw7961step0 (permutation23 i) (permutation7 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7961step0 permutation23 permutation7
    _ = injectiveMoment H node261 := by rfl

def raw7962 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 2, -2, 1], ![0, 0, -1, 1], ![0, 0, 3, -3], ![1, -2, 0, 1]]

def raw7962step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![2, 0, 0, -2], ![-2, -1, 3, 0], ![1, 1, -3, 1]]

def raw7962step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 0, -1], ![-2, 0, 0, 2], ![2, 1, -3, 0], ![-1, -1, 3, -1]]

def raw7962step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 1, 0], ![0, 2, -2, 0], ![1, 0, 2, -3]]

theorem canonical7962 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7962 = injectiveMoment H node938 := by
  calc
    injectiveMoment H raw7962 = injectiveMoment H raw7962step0 := by
      have heq : raw7962step0 = raw7962.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7962).symm
    injectiveMoment H raw7962step0 = injectiveMoment H raw7962step1 := by
      have heq : raw7962step1 = -raw7962step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7962step0).symm
    injectiveMoment H raw7962step1 = injectiveMoment H raw7962step2 := by
      have heq : raw7962step2 = (fun i j => raw7962step1 (permutation27 i) (permutation19 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7962step1 permutation27 permutation19
    _ = injectiveMoment H node938 := by rfl

def raw7963 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 2, -2, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -2, 0, 1]]

def raw7963step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![2, 0, 0, -2], ![-2, 1, 1, 0], ![1, -1, -1, 1]]

def raw7963step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 0, -1], ![-2, 0, 0, 2], ![2, -1, -1, 0], ![-1, 1, 1, -1]]

def raw7963step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 0, 2, -2], ![1, 1, -1, -1]]

theorem canonical7963 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7963 = injectiveMoment H node1040 := by
  calc
    injectiveMoment H raw7963 = injectiveMoment H raw7963step0 := by
      have heq : raw7963step0 = raw7963.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7963).symm
    injectiveMoment H raw7963step0 = injectiveMoment H raw7963step1 := by
      have heq : raw7963step1 = -raw7963step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7963step0).symm
    injectiveMoment H raw7963step1 = injectiveMoment H raw7963step2 := by
      have heq : raw7963step2 = (fun i j => raw7963step1 (permutation21 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7963step1 permutation21 permutation18
    _ = injectiveMoment H node1040 := by rfl

def raw7964 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 2, -2, 1], ![0, 0, 3, -3], ![1, -2, -1, 2]]

def raw7964step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![2, 0, -2], ![-2, 3, -1], ![1, -3, 2]]

def raw7964step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![3, -2, -1]]

theorem canonical7964 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7964 = injectiveMoment H node105 := by
  calc
    injectiveMoment H raw7964 = injectiveMoment H raw7964step0 := by
      have heq : raw7964step0 = raw7964.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7964).symm
    injectiveMoment H raw7964step0 = injectiveMoment H raw7964step1 := by
      have heq : raw7964step1 = (fun i j => raw7964step0 (permutation27 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7964step0 permutation27 permutation5
    _ = injectiveMoment H node105 := by rfl

def raw7965 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 2, -1, 0], ![0, 0, -2, 2], ![0, 0, 3, -3], ![1, -2, 0, 1]]

theorem canonical7965 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7965 = injectiveMoment H node1374 := by
  rfl

def raw7966 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 2, -1, 0], ![0, 0, -1, 1], ![0, 0, 2, -2], ![1, -2, 0, 1]]

def raw7966step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 1, 0], ![0, 2, -2, 0], ![1, 0, 1, -2]]

theorem canonical7966 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7966 = injectiveMoment H node1002 := by
  calc
    injectiveMoment H raw7966 = injectiveMoment H raw7966step0 := by
      have heq : raw7966step0 = (fun i j => raw7966 (permutation9 i) (permutation12 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7966 permutation9 permutation12
    _ = injectiveMoment H node1002 := by rfl

def raw7967 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 2, -1, 0], ![0, 0, -1, 1], ![0, 0, 3, -3], ![1, -2, -1, 2]]

def raw7967step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![2, 0, 0, -2], ![-1, -1, 3, -1], ![0, 1, -3, 2]]

def raw7967step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 1, 0], ![0, 2, -2, 0], ![1, 0, 2, -3]]

theorem canonical7967 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7967 = injectiveMoment H node938 := by
  calc
    injectiveMoment H raw7967 = injectiveMoment H raw7967step0 := by
      have heq : raw7967step0 = raw7967.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7967).symm
    injectiveMoment H raw7967step0 = injectiveMoment H raw7967step1 := by
      have heq : raw7967step1 = (fun i j => raw7967step0 (permutation21 i) (permutation16 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7967step0 permutation21 permutation16
    _ = injectiveMoment H node938 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
