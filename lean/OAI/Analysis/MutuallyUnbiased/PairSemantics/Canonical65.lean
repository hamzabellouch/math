import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes7
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes11
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes12
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes14
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes15
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes17
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes18
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes19

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw2080 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, 1, -2], ![1, -1, -1, 1], ![1, 1, 0, -2]]

def raw2080step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 1, 0, -3], ![0, -1, -1, 2], ![-1, 1, 1, -1], ![-1, -1, 0, 2]]

def raw2080step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, -1, 2], ![0, 1, 2, -3], ![1, 1, -1, -1]]

theorem canonical2080 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2080 = injectiveMoment H node995 := by
  calc
    injectiveMoment H raw2080 = injectiveMoment H raw2080step0 := by
      have heq : raw2080step0 = -raw2080 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2080).symm
    injectiveMoment H raw2080step0 = injectiveMoment H raw2080step1 := by
      have heq : raw2080step1 = (fun i j => raw2080step0 (permutation19 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2080step0 permutation19 permutation23
    _ = injectiveMoment H node995 := by rfl

def raw2081 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, 1, -1, -1]]

def raw2081step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 1, 0, -3], ![0, -1, -1, 2], ![-1, 1, 0, 0], ![-1, -1, 1, 1]]

def raw2081step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, -1, -1, 1]]

theorem canonical2081 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2081 = injectiveMoment H node1081 := by
  calc
    injectiveMoment H raw2081 = injectiveMoment H raw2081step0 := by
      have heq : raw2081step0 = -raw2081 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2081).symm
    injectiveMoment H raw2081step0 = injectiveMoment H raw2081step1 := by
      have heq : raw2081step1 = (fun i j => raw2081step0 (permutation17 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2081step0 permutation17 permutation23
    _ = injectiveMoment H node1081 := by rfl

def raw2082 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, 1, -2], ![1, -1, 1, -1], ![1, 1, -2, 0]]

theorem canonical2082 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2082 = injectiveMoment H node490 := by
  rfl

def raw2083 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, 1, -2], ![1, 0, -1, 0], ![1, 0, 0, -1]]

def raw2083step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 1, 0, -3], ![0, -1, -1, 2], ![-1, 0, 1, 0], ![-1, 0, 0, 1]]

def raw2083step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, 0, 2, -3]]

theorem canonical2083 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2083 = injectiveMoment H node1043 := by
  calc
    injectiveMoment H raw2083 = injectiveMoment H raw2083step0 := by
      have heq : raw2083step0 = -raw2083 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2083).symm
    injectiveMoment H raw2083step0 = injectiveMoment H raw2083step1 := by
      have heq : raw2083step1 = (fun i j => raw2083step0 (permutation20 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2083step0 permutation20 permutation17
    _ = injectiveMoment H node1043 := by rfl

def raw2084 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, 1, -2], ![1, 0, 0, -1], ![1, 0, -1, 0]]

def raw2084step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 1, 0, -3], ![0, -1, -1, 2], ![-1, 0, 0, 1], ![-1, 0, 1, 0]]

def raw2084step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, 0, 2, -3]]

theorem canonical2084 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2084 = injectiveMoment H node1043 := by
  calc
    injectiveMoment H raw2084 = injectiveMoment H raw2084step0 := by
      have heq : raw2084step0 = -raw2084 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2084).symm
    injectiveMoment H raw2084step0 = injectiveMoment H raw2084step1 := by
      have heq : raw2084step1 = (fun i j => raw2084step0 (permutation18 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2084step0 permutation18 permutation17
    _ = injectiveMoment H node1043 := by rfl

def raw2085 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, 2, -3], ![0, 1, -2, 1], ![2, -1, 0, -1]]

def raw2085step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -2, 1], ![0, 1, 2, -3], ![2, -1, 0, -1]]

theorem canonical2085 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2085 = injectiveMoment H node485 := by
  calc
    injectiveMoment H raw2085 = injectiveMoment H raw2085step0 := by
      have heq : raw2085step0 = (fun i j => raw2085 (permutation11 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2085 permutation11 permutation9
    _ = injectiveMoment H node485 := by rfl

def raw2086 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, 2, -3], ![0, 1, 0, -1], ![2, -1, -2, 1]]

def raw2086step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-1, 1, 1, -1], ![0, 2, 0, -2], ![3, -3, -1, 1]]

def raw2086step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -3, 1, 3], ![0, 0, 2, -2], ![0, 2, -2, 0], ![1, 1, -1, -1]]

theorem canonical2086 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2086 = injectiveMoment H node726 := by
  calc
    injectiveMoment H raw2086 = injectiveMoment H raw2086step0 := by
      have heq : raw2086step0 = raw2086.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2086).symm
    injectiveMoment H raw2086step0 = injectiveMoment H raw2086step1 := by
      have heq : raw2086step1 = (fun i j => raw2086step0 (permutation28 i) (permutation24 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2086step0 permutation28 permutation24
    _ = injectiveMoment H node726 := by rfl

def raw2087 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, 2, -3], ![1, -1, -1, 1], ![1, 1, -1, -1]]

theorem canonical2087 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2087 = injectiveMoment H node491 := by
  rfl

def raw2088 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, 2, -3], ![1, -1, 0, 0], ![1, 1, -2, 0]]

def raw2088step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 1, -1, 1], ![0, 2, 0, -2], ![3, -3, 0, 0]]

def raw2088step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![1, -1, 1, -1], ![0, -2, 0, 2], ![-3, 3, 0, 0]]

def raw2088step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 3, -3], ![0, 2, -2, 0], ![1, -1, -1, 1]]

theorem canonical2088 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2088 = injectiveMoment H node1066 := by
  calc
    injectiveMoment H raw2088 = injectiveMoment H raw2088step0 := by
      have heq : raw2088step0 = raw2088.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2088).symm
    injectiveMoment H raw2088step0 = injectiveMoment H raw2088step1 := by
      have heq : raw2088step1 = -raw2088step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2088step0).symm
    injectiveMoment H raw2088step1 = injectiveMoment H raw2088step2 := by
      have heq : raw2088step2 = (fun i j => raw2088step1 (permutation14 i) (permutation26 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2088step1 permutation14 permutation26
    _ = injectiveMoment H node1066 := by rfl

def raw2089 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, 2, -3], ![1, -1, 1, -1], ![1, 1, -3, 1]]

theorem canonical2089 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2089 = injectiveMoment H node492 := by
  rfl

def raw2090 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, 2, -3], ![1, 0, -1, 0], ![1, 0, -1, 0]]

def raw2090step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 1, 0, 0], ![0, 2, -1, -1], ![3, -3, 0, 0]]

def raw2090step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 0, 3, -3], ![1, 1, -2, 0]]

theorem canonical2090 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2090 = injectiveMoment H node1041 := by
  calc
    injectiveMoment H raw2090 = injectiveMoment H raw2090step0 := by
      have heq : raw2090step0 = raw2090.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2090).symm
    injectiveMoment H raw2090step0 = injectiveMoment H raw2090step1 := by
      have heq : raw2090step1 = (fun i j => raw2090step0 (permutation24 i) (permutation25 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2090step0 permutation24 permutation25
    _ = injectiveMoment H node1041 := by rfl

def raw2091 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, 2, -3], ![1, 0, 0, -1], ![1, 0, -2, 1]]

def raw2091step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 1, 0, -3], ![0, -1, -2, 3], ![-1, 0, 0, 1], ![-1, 0, 2, -1]]

def raw2091step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, -1, 1], ![0, 2, -1, -1], ![1, 0, 2, -3]]

theorem canonical2091 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2091 = injectiveMoment H node799 := by
  calc
    injectiveMoment H raw2091 = injectiveMoment H raw2091step0 := by
      have heq : raw2091step0 = -raw2091 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2091).symm
    injectiveMoment H raw2091step0 = injectiveMoment H raw2091step1 := by
      have heq : raw2091step1 = (fun i j => raw2091step0 (permutation18 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2091step0 permutation18 permutation17
    _ = injectiveMoment H node799 := by rfl

def raw2092 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, 3, -4], ![1, -1, -1, 1], ![1, 1, -2, 0]]

theorem canonical2092 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2092 = injectiveMoment H node493 := by
  rfl

def raw2093 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, 3, -4], ![1, -1, 0, 0], ![1, 1, -3, 1]]

def raw2093step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 1, -1, 1], ![0, 3, 0, -3], ![3, -4, 0, 1]]

def raw2093step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -3, 3], ![0, 3, 1, -4], ![1, -2, 1, 0]]

theorem canonical2093 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2093 = injectiveMoment H node1106 := by
  calc
    injectiveMoment H raw2093 = injectiveMoment H raw2093step0 := by
      have heq : raw2093step0 = raw2093.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2093).symm
    injectiveMoment H raw2093step0 = injectiveMoment H raw2093step1 := by
      have heq : raw2093step1 = (fun i j => raw2093step0 (permutation18 i) (permutation22 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2093step0 permutation18 permutation22
    _ = injectiveMoment H node1106 := by rfl

def raw2094 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, 3, -4], ![1, 0, -2, 1], ![1, 0, -1, 0]]

def raw2094step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 1, 0, 0], ![0, 3, -2, -1], ![3, -4, 1, 0]]

def raw2094step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, -1, 1], ![0, 1, 3, -4], ![1, 1, -2, 0]]

theorem canonical2094 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2094 = injectiveMoment H node798 := by
  calc
    injectiveMoment H raw2094 = injectiveMoment H raw2094step0 := by
      have heq : raw2094step0 = raw2094.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2094).symm
    injectiveMoment H raw2094step0 = injectiveMoment H raw2094step1 := by
      have heq : raw2094step1 = (fun i j => raw2094step0 (permutation24 i) (permutation31 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2094step0 permutation24 permutation31
    _ = injectiveMoment H node798 := by rfl

def raw2095 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, 3, -4], ![1, 0, -1, 0], ![1, 0, -2, 1]]

def raw2095step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 1, 0, 0], ![0, 3, -1, -2], ![3, -4, 0, 1]]

def raw2095step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, -1, 1], ![0, 1, 3, -4], ![1, 1, -2, 0]]

theorem canonical2095 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2095 = injectiveMoment H node798 := by
  calc
    injectiveMoment H raw2095 = injectiveMoment H raw2095step0 := by
      have heq : raw2095step0 = raw2095.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2095).symm
    injectiveMoment H raw2095step0 = injectiveMoment H raw2095step1 := by
      have heq : raw2095step1 = (fun i j => raw2095step0 (permutation24 i) (permutation25 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2095step0 permutation24 permutation25
    _ = injectiveMoment H node798 := by rfl

def raw2096 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 2, -3, 1], ![1, -1, 0, 0], ![1, 0, 3, -4]]

def raw2096step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 2, -1, 0], ![0, -3, 0, 3], ![3, 1, 0, -4]]

def raw2096step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![0, 0, -3, 3], ![0, 3, 1, -4], ![1, -2, 0, 1]]

theorem canonical2096 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2096 = injectiveMoment H node1158 := by
  calc
    injectiveMoment H raw2096 = injectiveMoment H raw2096step0 := by
      have heq : raw2096step0 = raw2096.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2096).symm
    injectiveMoment H raw2096step0 = injectiveMoment H raw2096step1 := by
      have heq : raw2096step1 = (fun i j => raw2096step0 (permutation18 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2096step0 permutation18 permutation21
    _ = injectiveMoment H node1158 := by rfl

def raw2097 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 2, -3, 1], ![1, -1, 1, -1], ![1, 0, 2, -3]]

theorem canonical2097 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2097 = injectiveMoment H node494 := by
  rfl

def raw2098 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 2, -2, 0], ![1, -1, -1, 1], ![1, 0, 3, -4]]

def raw2098step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 2, -1, 0], ![0, -2, -1, 3], ![3, 0, 1, -4]]

def raw2098step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -2, 1], ![0, 1, 3, -4], ![2, -1, -1, 0]]

theorem canonical2098 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2098 = injectiveMoment H node486 := by
  calc
    injectiveMoment H raw2098 = injectiveMoment H raw2098step0 := by
      have heq : raw2098step0 = raw2098.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2098).symm
    injectiveMoment H raw2098step0 = injectiveMoment H raw2098step1 := by
      have heq : raw2098step1 = (fun i j => raw2098step0 (permutation22 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2098step0 permutation22 permutation17
    _ = injectiveMoment H node486 := by rfl

def raw2099 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 2, -2, 0], ![1, -1, 0, 0], ![1, 0, 2, -3]]

def raw2099step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 2, -1, 0], ![0, -2, 0, 2], ![3, 0, 0, -3]]

def raw2099step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![1, -2, 1, 0], ![0, 2, 0, -2], ![-3, 0, 0, 3]]

def raw2099step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, 3, -3], ![0, 2, -2, 0], ![1, -2, 0, 1]]

theorem canonical2099 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2099 = injectiveMoment H node1269 := by
  calc
    injectiveMoment H raw2099 = injectiveMoment H raw2099step0 := by
      have heq : raw2099step0 = raw2099.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2099).symm
    injectiveMoment H raw2099step0 = injectiveMoment H raw2099step1 := by
      have heq : raw2099step1 = -raw2099step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2099step0).symm
    injectiveMoment H raw2099step1 = injectiveMoment H raw2099step2 := by
      have heq : raw2099step2 = (fun i j => raw2099step1 (permutation14 i) (permutation24 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2099step1 permutation14 permutation24
    _ = injectiveMoment H node1269 := by rfl

def raw2100 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 2, -2, 0], ![1, -1, 1, -1], ![1, 0, 1, -2]]

def raw2100step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 2, -1, 0], ![0, -2, 1, 1], ![3, 0, -1, -2]]

def raw2100step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![1, 1, -2, 0], ![1, 1, 0, -2]]

theorem canonical2100 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2100 = injectiveMoment H node476 := by
  calc
    injectiveMoment H raw2100 = injectiveMoment H raw2100step0 := by
      have heq : raw2100step0 = raw2100.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2100).symm
    injectiveMoment H raw2100step0 = injectiveMoment H raw2100step1 := by
      have heq : raw2100step1 = (fun i j => raw2100step0 (permutation30 i) (permutation32 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2100step0 permutation30 permutation32
    _ = injectiveMoment H node476 := by rfl

def raw2101 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 2, -2, 0], ![1, -1, 2, -2], ![1, 0, 0, -1]]

def raw2101step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 2, -1, 0], ![0, -2, 2, 0], ![3, 0, -2, -1]]

def raw2101step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -2, 2, 0], ![0, 2, -1, -1], ![1, 0, 1, -2]]

theorem canonical2101 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2101 = injectiveMoment H node1190 := by
  calc
    injectiveMoment H raw2101 = injectiveMoment H raw2101step0 := by
      have heq : raw2101step0 = raw2101.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2101).symm
    injectiveMoment H raw2101step0 = injectiveMoment H raw2101step1 := by
      have heq : raw2101step1 = (fun i j => raw2101step0 (permutation32 i) (permutation30 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2101step0 permutation32 permutation30
    _ = injectiveMoment H node1190 := by rfl

def raw2102 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 2, -2, 0], ![1, -1, 3, -3], ![1, 0, -1, 0]]

def raw2102step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 2, -1, 0], ![0, -2, 3, -1], ![3, 0, -3, 0]]

def raw2102step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 3, -3], ![0, 2, -1, -1], ![1, 0, -2, 1]]

theorem canonical2102 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2102 = injectiveMoment H node812 := by
  calc
    injectiveMoment H raw2102 = injectiveMoment H raw2102step0 := by
      have heq : raw2102step0 = raw2102.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2102).symm
    injectiveMoment H raw2102step0 = injectiveMoment H raw2102step1 := by
      have heq : raw2102step1 = (fun i j => raw2102step0 (permutation26 i) (permutation29 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2102step0 permutation26 permutation29
    _ = injectiveMoment H node812 := by rfl

def raw2103 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 2, -2, 0], ![1, 0, 0, -1], ![1, -1, 2, -2]]

def raw2103step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 2, 0, -1], ![0, -2, 0, 2], ![3, 0, -1, -2]]

def raw2103step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -2, 2, 0], ![0, 2, -1, -1], ![1, 0, 1, -2]]

theorem canonical2103 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2103 = injectiveMoment H node1190 := by
  calc
    injectiveMoment H raw2103 = injectiveMoment H raw2103step0 := by
      have heq : raw2103step0 = raw2103.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2103).symm
    injectiveMoment H raw2103step0 = injectiveMoment H raw2103step1 := by
      have heq : raw2103step1 = (fun i j => raw2103step0 (permutation32 i) (permutation24 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2103step0 permutation32 permutation24
    _ = injectiveMoment H node1190 := by rfl

def raw2104 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 2, -1, -1], ![1, -1, -1, 1], ![1, 0, 2, -3]]

theorem canonical2104 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2104 = injectiveMoment H node495 := by
  rfl

def raw2105 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 2, -1, -1], ![1, -1, 0, 0], ![1, 0, 1, -2]]

def raw2105step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 1, 0, -3], ![0, -2, 1, 1], ![-1, 1, 0, 0], ![-1, 0, -1, 2]]

def raw2105step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 1, 0], ![0, 2, 1, -3], ![1, 0, -2, 1]]

theorem canonical2105 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2105 = injectiveMoment H node1003 := by
  calc
    injectiveMoment H raw2105 = injectiveMoment H raw2105step0 := by
      have heq : raw2105step0 = -raw2105 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2105).symm
    injectiveMoment H raw2105step0 = injectiveMoment H raw2105step1 := by
      have heq : raw2105step1 = (fun i j => raw2105step0 (permutation31 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2105step0 permutation31 permutation21
    _ = injectiveMoment H node1003 := by rfl

def raw2106 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 2, -1, -1], ![1, -1, 1, -1], ![1, 0, 0, -1]]

def raw2106step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 2, -1, 0], ![0, -1, 1, 0], ![3, -1, -1, -1]]

def raw2106step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 1, 0], ![0, 2, -1, -1], ![1, 0, 1, -2]]

theorem canonical2106 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2106 = injectiveMoment H node939 := by
  calc
    injectiveMoment H raw2106 = injectiveMoment H raw2106step0 := by
      have heq : raw2106step0 = raw2106.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2106).symm
    injectiveMoment H raw2106step0 = injectiveMoment H raw2106step1 := by
      have heq : raw2106step1 = (fun i j => raw2106step0 (permutation32 i) (permutation30 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2106step0 permutation32 permutation30
    _ = injectiveMoment H node939 := by rfl

def raw2107 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 2, -1, -1], ![1, -1, 2, -2], ![1, 0, -1, 0]]

def raw2107step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 2, -1, 0], ![0, -1, 2, -1], ![3, -1, -2, 0]]

def raw2107step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 3, -2], ![0, 2, -1, -1], ![1, 0, -2, 1]]

theorem canonical2107 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2107 = injectiveMoment H node1016 := by
  calc
    injectiveMoment H raw2107 = injectiveMoment H raw2107step0 := by
      have heq : raw2107step0 = raw2107.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2107).symm
    injectiveMoment H raw2107step0 = injectiveMoment H raw2107step1 := by
      have heq : raw2107step1 = (fun i j => raw2107step0 (permutation26 i) (permutation29 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2107step0 permutation26 permutation29
    _ = injectiveMoment H node1016 := by rfl

def raw2108 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 2, -1, -1], ![1, 0, -1, 0], ![1, -1, 2, -2]]

def raw2108step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 2, 0, -1], ![0, -1, -1, 2], ![3, -1, 0, -2]]

def raw2108step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 3, -2], ![0, 2, -1, -1], ![1, 0, -2, 1]]

theorem canonical2108 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2108 = injectiveMoment H node1016 := by
  calc
    injectiveMoment H raw2108 = injectiveMoment H raw2108step0 := by
      have heq : raw2108step0 = raw2108.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2108).symm
    injectiveMoment H raw2108step0 = injectiveMoment H raw2108step1 := by
      have heq : raw2108step1 = (fun i j => raw2108step0 (permutation26 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2108step0 permutation26 permutation23
    _ = injectiveMoment H node1016 := by rfl

def raw2109 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 2, 0, -2], ![1, -1, -1, 1], ![1, 0, 1, -2]]

def raw2109step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 1, 0, -3], ![0, -2, 0, 2], ![-1, 1, 1, -1], ![-1, 0, -1, 2]]

def raw2109step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 2, 1, -3], ![1, -1, 1, -1]]

theorem canonical2109 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2109 = injectiveMoment H node1036 := by
  calc
    injectiveMoment H raw2109 = injectiveMoment H raw2109step0 := by
      have heq : raw2109step0 = -raw2109 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2109).symm
    injectiveMoment H raw2109step0 = injectiveMoment H raw2109step1 := by
      have heq : raw2109step1 = (fun i j => raw2109step0 (permutation29 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2109step0 permutation29 permutation21
    _ = injectiveMoment H node1036 := by rfl

def raw2110 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 2, 0, -2], ![1, -1, 1, -1], ![1, 0, -1, 0]]

def raw2110step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 2, -1, 0], ![0, 0, 1, -1], ![3, -2, -1, 0]]

def raw2110step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![1, -2, 1, 0], ![0, 0, -1, 1], ![-3, 2, 1, 0]]

def raw2110step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, -2, 1], ![0, 1, 2, -3], ![1, -1, 0, 0]]

theorem canonical2110 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2110 = injectiveMoment H node1079 := by
  calc
    injectiveMoment H raw2110 = injectiveMoment H raw2110step0 := by
      have heq : raw2110step0 = raw2110.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2110).symm
    injectiveMoment H raw2110step0 = injectiveMoment H raw2110step1 := by
      have heq : raw2110step1 = -raw2110step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2110step0).symm
    injectiveMoment H raw2110step1 = injectiveMoment H raw2110step2 := by
      have heq : raw2110step2 = (fun i j => raw2110step1 (permutation10 i) (permutation32 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2110step1 permutation10 permutation32
    _ = injectiveMoment H node1079 := by rfl

def raw2111 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 2, 0, -2], ![1, -1, 2, -2], ![1, 0, -2, 1]]

theorem canonical2111 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2111 = injectiveMoment H node496 := by
  rfl

end MUB6.Certificate.PairSemantics

end OAI
