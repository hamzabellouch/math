import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes7
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes9
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes12
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes15
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes17
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes20
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes25
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes30
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes40
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes42
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes43
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes44

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw3136 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 2, -2], ![0, 1, -2, 1], ![2, -1, 1, -2]]

def raw3136step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 1, -3], ![0, 0, -2, 2], ![0, -1, 2, -1], ![-2, 1, -1, 2]]

def raw3136step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, 0, -2, 2], ![0, 2, 1, -3], ![1, -2, -1, 2]]

theorem canonical3136 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3136 = injectiveMoment H node1315 := by
  calc
    injectiveMoment H raw3136 = injectiveMoment H raw3136step0 := by
      have heq : raw3136step0 = -raw3136 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3136).symm
    injectiveMoment H raw3136step0 = injectiveMoment H raw3136step1 := by
      have heq : raw3136step1 = (fun i j => raw3136step0 (permutation23 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3136step0 permutation23 permutation15
    _ = injectiveMoment H node1315 := by rfl

def raw3137 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, -2, 1, -1]]

theorem canonical3137 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3137 = injectiveMoment H node1960 := by
  rfl

def raw3138 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, -2, 0, 0]]

def raw3138step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 2, 0, -2], ![2, 0, -2, 0]]

theorem canonical3138 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3138 = injectiveMoment H node1633 := by
  calc
    injectiveMoment H raw3138 = injectiveMoment H raw3138step0 := by
      have heq : raw3138step0 = (fun i j => raw3138 (permutation41 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3138 permutation41 permutation11
    _ = injectiveMoment H node1633 := by rfl

def raw3139 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, -2, 1, 0], ![1, 1, -1, -1]]

theorem canonical3139 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3139 = injectiveMoment H node1961 := by
  rfl

def raw3140 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw3140step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -1, -2, 3], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -1, 0, 0]]

theorem canonical3140 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3140 = injectiveMoment H node2810 := by
  calc
    injectiveMoment H raw3140 = injectiveMoment H raw3140step0 := by
      have heq : raw3140step0 = (fun i j => raw3140 (permutation108 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3140 permutation108 permutation17
    _ = injectiveMoment H node2810 := by rfl

def raw3141 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 2, -2], ![0, 1, -1, 0], ![2, -1, 0, -1]]

def raw3141step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 1, -3], ![0, 0, -2, 2], ![0, -1, 1, 0], ![-2, 1, 0, 1]]

def raw3141step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, 0, -2, 2], ![0, 2, 1, -3], ![1, -2, 0, 1]]

theorem canonical3141 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3141 = injectiveMoment H node1301 := by
  calc
    injectiveMoment H raw3141 = injectiveMoment H raw3141step0 := by
      have heq : raw3141step0 = -raw3141 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3141).symm
    injectiveMoment H raw3141step0 = injectiveMoment H raw3141step1 := by
      have heq : raw3141step1 = (fun i j => raw3141step0 (permutation23 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3141step0 permutation23 permutation15
    _ = injectiveMoment H node1301 := by rfl

def raw3142 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 2, -2], ![0, 1, 0, -1], ![0, 1, -1, 0], ![2, -2, 0, 0]]

def raw3142step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 2, 0, -2], ![2, 0, -2, 0]]

theorem canonical3142 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3142 = injectiveMoment H node1633 := by
  calc
    injectiveMoment H raw3142 = injectiveMoment H raw3142step0 := by
      have heq : raw3142step0 = (fun i j => raw3142 (permutation47 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3142 permutation47 permutation11
    _ = injectiveMoment H node1633 := by rfl

def raw3143 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, -2, 1, 0], ![1, 1, -2, 0]]

theorem canonical3143 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3143 = injectiveMoment H node1962 := by
  rfl

def raw3144 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 0, 0, -1]]

def raw3144step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, -2, 3], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, 0, 0, -1]]

theorem canonical3144 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3144 = injectiveMoment H node2619 := by
  calc
    injectiveMoment H raw3144 = injectiveMoment H raw3144step0 := by
      have heq : raw3144step0 = (fun i j => raw3144 (permutation108 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3144 permutation108 permutation17
    _ = injectiveMoment H node2619 := by rfl

def raw3145 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def raw3145step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 1, -3], ![0, 0, -2, 2], ![0, -1, 0, 1], ![-1, 1, 0, 0], ![-1, 0, 1, 0]]

def raw3145step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 0, 2], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, 0, -1, 0]]

theorem canonical3145 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3145 = injectiveMoment H node2740 := by
  calc
    injectiveMoment H raw3145 = injectiveMoment H raw3145step0 := by
      have heq : raw3145step0 = -raw3145 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3145).symm
    injectiveMoment H raw3145step0 = injectiveMoment H raw3145step1 := by
      have heq : raw3145step1 = (fun i j => raw3145step0 (permutation90 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3145step0 permutation90 permutation17
    _ = injectiveMoment H node2740 := by rfl

def raw3146 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 2, -2], ![0, 1, 0, -1], ![2, -1, -1, 0]]

def raw3146step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, 1, -1], ![-1, 2, 0, -1], ![3, -2, -1, 0]]

def raw3146step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 2, -2], ![0, 2, -1, -1], ![1, 0, -1, 0]]

theorem canonical3146 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3146 = injectiveMoment H node807 := by
  calc
    injectiveMoment H raw3146 = injectiveMoment H raw3146step0 := by
      have heq : raw3146step0 = raw3146.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3146).symm
    injectiveMoment H raw3146step0 = injectiveMoment H raw3146step1 := by
      have heq : raw3146step1 = (fun i j => raw3146step0 (permutation28 i) (permutation24 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3146step0 permutation28 permutation24
    _ = injectiveMoment H node807 := by rfl

def raw3147 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 2, -2], ![0, 2, -2, 0], ![1, -2, 1, 0], ![1, 0, 0, -1]]

theorem canonical3147 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3147 = injectiveMoment H node1963 := by
  rfl

def raw3148 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 2, -2], ![0, 2, -2, 0], ![1, -1, 0, 0], ![1, -1, 1, -1]]

theorem canonical3148 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3148 = injectiveMoment H node1964 := by
  rfl

def raw3149 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 2, -2], ![0, 2, -2, 0], ![1, -1, 1, -1], ![1, -1, 0, 0]]

def raw3149step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 2, -2], ![0, 2, -2, 0], ![1, -1, 0, 0], ![1, -1, 1, -1]]

theorem canonical3149 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3149 = injectiveMoment H node1964 := by
  calc
    injectiveMoment H raw3149 = injectiveMoment H raw3149step0 := by
      have heq : raw3149step0 = (fun i j => raw3149 (permutation34 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3149 permutation34 permutation9
    _ = injectiveMoment H node1964 := by rfl

def raw3150 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 2, -2], ![0, 2, -2, 0], ![2, -2, 1, -1]]

theorem canonical3150 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3150 = injectiveMoment H node591 := by
  rfl

def raw3151 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 2, -2], ![0, 2, -1, -1], ![1, -2, 1, 0], ![1, 0, -1, 0]]

theorem canonical3151 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3151 = injectiveMoment H node1965 := by
  rfl

def raw3152 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 2, -2], ![0, 2, -1, -1], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def raw3152step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![0, 2, 0, -2], ![1, 0, -1, 0], ![1, 0, -1, 0]]

theorem canonical3152 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3152 = injectiveMoment H node1657 := by
  calc
    injectiveMoment H raw3152 = injectiveMoment H raw3152step0 := by
      have heq : raw3152step0 = (fun i j => raw3152 (permutation39 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3152 permutation39 permutation11
    _ = injectiveMoment H node1657 := by rfl

def raw3153 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 2, -2], ![0, 2, -1, -1], ![2, -2, 0, 0]]

def raw3153step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![0, 2, 0, -2], ![2, 0, -2, 0]]

theorem canonical3153 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3153 = injectiveMoment H node474 := by
  calc
    injectiveMoment H raw3153 = injectiveMoment H raw3153step0 := by
      have heq : raw3153step0 = (fun i j => raw3153 (permutation11 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3153 permutation11 permutation11
    _ = injectiveMoment H node474 := by rfl

def raw3154 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 2, -2], ![1, -2, 1, 0], ![1, 2, -2, -1]]

def raw3154step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, -2, 2], ![-1, 2, 1, -2], ![3, -2, 0, -1]]

def raw3154step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 0, 2, -2], ![1, -2, -1, 2], ![-3, 2, 0, 1]]

def raw3154step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 2, -1], ![0, 2, 0, -2], ![2, 0, -3, 1]]

theorem canonical3154 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3154 = injectiveMoment H node504 := by
  calc
    injectiveMoment H raw3154 = injectiveMoment H raw3154step0 := by
      have heq : raw3154step0 = raw3154.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3154).symm
    injectiveMoment H raw3154step0 = injectiveMoment H raw3154step1 := by
      have heq : raw3154step1 = -raw3154step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3154step0).symm
    injectiveMoment H raw3154step1 = injectiveMoment H raw3154step2 := by
      have heq : raw3154step2 = (fun i j => raw3154step1 (permutation21 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3154step1 permutation21 permutation17
    _ = injectiveMoment H node504 := by rfl

def raw3155 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 2, -2], ![1, -1, -1, 1], ![1, 1, 0, -2]]

def raw3155step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 1, -3], ![0, 0, -2, 2], ![-1, 1, 1, -1], ![-1, -1, 0, 2]]

def raw3155step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 2, 1, -3], ![1, -1, 1, -1]]

theorem canonical3155 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3155 = injectiveMoment H node1036 := by
  calc
    injectiveMoment H raw3155 = injectiveMoment H raw3155step0 := by
      have heq : raw3155step0 = -raw3155 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3155).symm
    injectiveMoment H raw3155step0 = injectiveMoment H raw3155step1 := by
      have heq : raw3155step1 = (fun i j => raw3155step0 (permutation29 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3155step0 permutation29 permutation15
    _ = injectiveMoment H node1036 := by rfl

def raw3156 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 2, -2], ![1, -1, 0, 0], ![1, 1, -1, -1]]

def raw3156step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, -1, 1], ![-1, 2, 0, -1], ![3, -2, 0, -1]]

def raw3156step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 0, 1, -1], ![1, -2, 0, 1], ![-3, 2, 0, 1]]

def raw3156step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, -2, 1], ![0, 1, 2, -3], ![1, -1, 0, 0]]

theorem canonical3156 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3156 = injectiveMoment H node1079 := by
  calc
    injectiveMoment H raw3156 = injectiveMoment H raw3156step0 := by
      have heq : raw3156step0 = raw3156.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3156).symm
    injectiveMoment H raw3156step0 = injectiveMoment H raw3156step1 := by
      have heq : raw3156step1 = -raw3156step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3156step0).symm
    injectiveMoment H raw3156step1 = injectiveMoment H raw3156step2 := by
      have heq : raw3156step2 = (fun i j => raw3156step1 (permutation12 i) (permutation26 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3156step1 permutation12 permutation26
    _ = injectiveMoment H node1079 := by rfl

def raw3157 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 2, -2], ![1, -1, 1, -1], ![1, 1, -2, 0]]

def raw3157step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 1, -3], ![0, 0, -2, 2], ![-1, 1, -1, 1], ![-1, -1, 2, 0]]

def raw3157step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 2, -3, 1], ![1, -1, 1, -1]]

theorem canonical3157 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3157 = injectiveMoment H node1056 := by
  calc
    injectiveMoment H raw3157 = injectiveMoment H raw3157step0 := by
      have heq : raw3157step0 = -raw3157 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3157).symm
    injectiveMoment H raw3157step0 = injectiveMoment H raw3157step1 := by
      have heq : raw3157step1 = (fun i j => raw3157step0 (permutation29 i) (permutation16 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3157step0 permutation29 permutation16
    _ = injectiveMoment H node1056 := by rfl

def raw3158 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 2, -2], ![1, 1, -2, 0], ![1, -1, 1, -1]]

def raw3158step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 1, -3], ![0, 0, -2, 2], ![-1, -1, 2, 0], ![-1, 1, -1, 1]]

def raw3158step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 2, -3, 1], ![1, -1, 1, -1]]

theorem canonical3158 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3158 = injectiveMoment H node1056 := by
  calc
    injectiveMoment H raw3158 = injectiveMoment H raw3158step0 := by
      have heq : raw3158step0 = -raw3158 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3158).symm
    injectiveMoment H raw3158step0 = injectiveMoment H raw3158step1 := by
      have heq : raw3158step1 = (fun i j => raw3158step0 (permutation23 i) (permutation16 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3158step0 permutation23 permutation16
    _ = injectiveMoment H node1056 := by rfl

def raw3159 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 2, -2], ![1, 2, -2, -1], ![1, -2, 1, 0]]

def raw3159step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, 2, -2], ![-1, 2, -2, 1], ![3, -2, -1, 0]]

def raw3159step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 0, -2, 2], ![1, -2, 2, -1], ![-3, 2, 1, 0]]

def raw3159step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 2, -1], ![0, 2, 0, -2], ![2, 0, -3, 1]]

theorem canonical3159 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3159 = injectiveMoment H node504 := by
  calc
    injectiveMoment H raw3159 = injectiveMoment H raw3159step0 := by
      have heq : raw3159step0 = raw3159.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3159).symm
    injectiveMoment H raw3159step0 = injectiveMoment H raw3159step1 := by
      have heq : raw3159step1 = -raw3159step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3159step0).symm
    injectiveMoment H raw3159step1 = injectiveMoment H raw3159step2 := by
      have heq : raw3159step2 = (fun i j => raw3159step1 (permutation21 i) (permutation19 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3159step1 permutation21 permutation19
    _ = injectiveMoment H node504 := by rfl

def raw3160 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 3, -3], ![0, 1, -2, 1], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw3160step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 1, -3], ![0, 0, -3, 3], ![0, -1, 2, -1], ![-1, 1, 0, 0], ![-1, 0, 0, 1]]

def raw3160step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -1, 0, 1], ![0, 0, -3, 3], ![0, 2, 1, -3], ![1, -1, 0, 0]]

theorem canonical3160 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3160 = injectiveMoment H node2827 := by
  calc
    injectiveMoment H raw3160 = injectiveMoment H raw3160step0 := by
      have heq : raw3160step0 = -raw3160 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3160).symm
    injectiveMoment H raw3160step0 = injectiveMoment H raw3160step1 := by
      have heq : raw3160step1 = (fun i j => raw3160step0 (permutation100 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3160step0 permutation100 permutation15
    _ = injectiveMoment H node2827 := by rfl

def raw3161 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 3, -3], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, -2, 0, 0]]

theorem canonical3161 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3161 = injectiveMoment H node1966 := by
  rfl

def raw3162 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 3, -3], ![0, 1, -1, 0], ![2, -1, -1, 0]]

def raw3162step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, 1, -1], ![-1, 3, -1, -1], ![3, -3, 0, 0]]

def raw3162step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 3, -3], ![0, 2, -2, 0], ![1, -1, 0, 0]]

theorem canonical3162 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3162 = injectiveMoment H node979 := by
  calc
    injectiveMoment H raw3162 = injectiveMoment H raw3162step0 := by
      have heq : raw3162step0 = raw3162.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3162).symm
    injectiveMoment H raw3162step0 = injectiveMoment H raw3162step1 := by
      have heq : raw3162step1 = (fun i j => raw3162step0 (permutation25 i) (permutation25 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3162step0 permutation25 permutation25
    _ = injectiveMoment H node979 := by rfl

def raw3163 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 3, -3], ![0, 2, -2, 0], ![1, -1, 0, 0], ![1, -1, 0, 0]]

theorem canonical3163 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3163 = injectiveMoment H node1967 := by
  rfl

def raw3164 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 3, -3], ![0, 2, -2, 0], ![2, -2, 0, 0]]

theorem canonical3164 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3164 = injectiveMoment H node592 := by
  rfl

def raw3165 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 3, -3], ![1, -1, -1, 1], ![1, 1, -1, -1]]

def raw3165step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 1, -3], ![0, 0, -3, 3], ![-1, 1, 1, -1], ![-1, -1, 1, 1]]

def raw3165step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -3, 3], ![0, 2, 1, -3], ![1, -1, 1, -1]]

theorem canonical3165 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3165 = injectiveMoment H node1105 := by
  calc
    injectiveMoment H raw3165 = injectiveMoment H raw3165step0 := by
      have heq : raw3165step0 = -raw3165 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3165).symm
    injectiveMoment H raw3165step0 = injectiveMoment H raw3165step1 := by
      have heq : raw3165step1 = (fun i j => raw3165step0 (permutation29 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3165step0 permutation29 permutation15
    _ = injectiveMoment H node1105 := by rfl

def raw3166 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 3, -3], ![1, -1, 0, 0], ![1, 1, -2, 0]]

def raw3166step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 1, -3], ![0, 0, -3, 3], ![-1, 1, 0, 0], ![-1, -1, 2, 0]]

def raw3166step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 3, -3], ![0, 2, -3, 1], ![1, -1, 0, 0]]

theorem canonical3166 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3166 = injectiveMoment H node1065 := by
  calc
    injectiveMoment H raw3166 = injectiveMoment H raw3166step0 := by
      have heq : raw3166step0 = -raw3166 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3166).symm
    injectiveMoment H raw3166step0 = injectiveMoment H raw3166step1 := by
      have heq : raw3166step1 = (fun i j => raw3166step0 (permutation29 i) (permutation16 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3166step0 permutation29 permutation16
    _ = injectiveMoment H node1065 := by rfl

def raw3167 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 3, -3], ![1, 1, -2, 0], ![1, -1, 0, 0]]

def raw3167step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 1, -3], ![0, 0, -3, 3], ![-1, -1, 2, 0], ![-1, 1, 0, 0]]

def raw3167step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 3, -3], ![0, 2, -3, 1], ![1, -1, 0, 0]]

theorem canonical3167 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3167 = injectiveMoment H node1065 := by
  calc
    injectiveMoment H raw3167 = injectiveMoment H raw3167step0 := by
      have heq : raw3167step0 = -raw3167 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3167).symm
    injectiveMoment H raw3167step0 = injectiveMoment H raw3167step1 := by
      have heq : raw3167step1 = (fun i j => raw3167step0 (permutation23 i) (permutation16 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3167step0 permutation23 permutation16
    _ = injectiveMoment H node1065 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
