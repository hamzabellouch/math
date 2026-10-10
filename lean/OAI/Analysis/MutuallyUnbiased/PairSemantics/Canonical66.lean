import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes1
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes2
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes4
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes7
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes12
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes14
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes15
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes18
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes34
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes42
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes44

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw2112 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 2, 1, -3], ![1, -1, -1, 1], ![1, 0, 0, -1]]

def raw2112step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 1, 0, -3], ![0, -2, -1, 3], ![-1, 1, 1, -1], ![-1, 0, 0, 1]]

def raw2112step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, -1, 1], ![0, 1, 2, -3], ![1, 1, -1, -1]]

theorem canonical2112 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2112 = injectiveMoment H node797 := by
  calc
    injectiveMoment H raw2112 = injectiveMoment H raw2112step0 := by
      have heq : raw2112step0 = -raw2112 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2112).symm
    injectiveMoment H raw2112step0 = injectiveMoment H raw2112step1 := by
      have heq : raw2112step1 = (fun i j => raw2112step0 (permutation19 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2112step0 permutation19 permutation23
    _ = injectiveMoment H node797 := by rfl

def raw2113 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 2, 1, -3], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def raw2113step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 2, -1, 0], ![0, 1, 0, -1], ![3, -3, 0, 0]]

def raw2113step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![1, -2, 1, 0], ![0, -1, 0, 1], ![-3, 3, 0, 0]]

def raw2113step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 3, -3], ![0, 1, -2, 1], ![1, 0, -1, 0]]

theorem canonical2113 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2113 = injectiveMoment H node1063 := by
  calc
    injectiveMoment H raw2113 = injectiveMoment H raw2113step0 := by
      have heq : raw2113step0 = raw2113.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2113).symm
    injectiveMoment H raw2113step0 = injectiveMoment H raw2113step1 := by
      have heq : raw2113step1 = -raw2113step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2113step0).symm
    injectiveMoment H raw2113step1 = injectiveMoment H raw2113step2 := by
      have heq : raw2113step2 = (fun i j => raw2113step1 (permutation13 i) (permutation32 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2113step1 permutation13 permutation32
    _ = injectiveMoment H node1063 := by rfl

def raw2114 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 2, 1, -3], ![1, -1, 1, -1], ![1, 0, -2, 1]]

def raw2114step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 1, 0, -3], ![0, -2, -1, 3], ![-1, 1, -1, 1], ![-1, 0, 2, -1]]

def raw2114step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 2, -1, -1], ![1, -1, -1, 1], ![1, 0, 2, -3]]

theorem canonical2114 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2114 = injectiveMoment H node495 := by
  calc
    injectiveMoment H raw2114 = injectiveMoment H raw2114step0 := by
      have heq : raw2114step0 = -raw2114 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2114).symm
    injectiveMoment H raw2114step0 = injectiveMoment H raw2114step1 := by
      have heq : raw2114step1 = (fun i j => raw2114step0 (permutation20 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2114step0 permutation20 permutation17
    _ = injectiveMoment H node495 := by rfl

def raw2115 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 2, 1, -3], ![1, 0, -1, 0], ![1, -1, 0, 0]]

def raw2115step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 2, 0, -1], ![0, 1, -1, 0], ![3, -3, 0, 0]]

def raw2115step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![1, -2, 0, 1], ![0, -1, 1, 0], ![-3, 3, 0, 0]]

def raw2115step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 3, -3], ![0, 1, -2, 1], ![1, 0, -1, 0]]

theorem canonical2115 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2115 = injectiveMoment H node1063 := by
  calc
    injectiveMoment H raw2115 = injectiveMoment H raw2115step0 := by
      have heq : raw2115step0 = raw2115.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2115).symm
    injectiveMoment H raw2115step0 = injectiveMoment H raw2115step1 := by
      have heq : raw2115step1 = -raw2115step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2115step0).symm
    injectiveMoment H raw2115step1 = injectiveMoment H raw2115step2 := by
      have heq : raw2115step2 = (fun i j => raw2115step1 (permutation13 i) (permutation26 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2115step1 permutation13 permutation26
    _ = injectiveMoment H node1063 := by rfl

def raw2116 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 2, 2, -4], ![1, -1, -1, 1], ![1, 0, -1, 0]]

def raw2116step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 2, -1, 0], ![0, 2, -1, -1], ![3, -4, 1, 0]]

def raw2116step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, -1, 2], ![0, 1, 3, -4], ![1, 1, -2, 0]]

theorem canonical2116 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2116 = injectiveMoment H node996 := by
  calc
    injectiveMoment H raw2116 = injectiveMoment H raw2116step0 := by
      have heq : raw2116step0 = raw2116.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2116).symm
    injectiveMoment H raw2116step0 = injectiveMoment H raw2116step1 := by
      have heq : raw2116step1 = (fun i j => raw2116step0 (permutation24 i) (permutation31 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2116step0 permutation24 permutation31
    _ = injectiveMoment H node996 := by rfl

def raw2117 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 2, 2, -4], ![1, -1, 0, 0], ![1, 0, -2, 1]]

def raw2117step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 2, -1, 0], ![0, 2, 0, -2], ![3, -4, 0, 1]]

def raw2117step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![1, -2, 1, 0], ![0, -2, 0, 2], ![-3, 4, 0, -1]]

def raw2117step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![0, -1, -3, 4], ![0, 2, 0, -2], ![1, 0, 1, -2]]

theorem canonical2117 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2117 = injectiveMoment H node1155 := by
  calc
    injectiveMoment H raw2117 = injectiveMoment H raw2117step0 := by
      have heq : raw2117step0 = raw2117.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2117).symm
    injectiveMoment H raw2117step0 = injectiveMoment H raw2117step1 := by
      have heq : raw2117step1 = -raw2117step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2117step0).symm
    injectiveMoment H raw2117step1 = injectiveMoment H raw2117step2 := by
      have heq : raw2117step2 = (fun i j => raw2117step1 (permutation14 i) (permutation25 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2117step1 permutation14 permutation25
    _ = injectiveMoment H node1155 := by rfl

def raw2118 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![1, -1, -2, 2], ![0, 0, 2, -2], ![1, 2, 0, -3]]

def raw2118step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 1, 0, -3], ![-1, 1, 2, -2], ![0, 0, -2, 2], ![-1, -2, 0, 3]]

def raw2118step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, -2, 2], ![1, -1, 2, -2], ![1, 2, 0, -3]]

theorem canonical2118 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2118 = injectiveMoment H node479 := by
  calc
    injectiveMoment H raw2118 = injectiveMoment H raw2118step0 := by
      have heq : raw2118step0 = -raw2118 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2118).symm
    injectiveMoment H raw2118step0 = injectiveMoment H raw2118step1 := by
      have heq : raw2118step1 = (fun i j => raw2118step0 (permutation32 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2118step0 permutation32 permutation15
    _ = injectiveMoment H node479 := by rfl

def raw2119 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![1, -1, -1, 1], ![0, 1, 2, -3], ![1, 1, -1, -1]]

def raw2119step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, 2, -3], ![1, -1, -1, 1], ![1, 1, -1, -1]]

theorem canonical2119 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2119 = injectiveMoment H node491 := by
  calc
    injectiveMoment H raw2119 = injectiveMoment H raw2119step0 := by
      have heq : raw2119step0 = (fun i j => raw2119 (permutation11 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2119 permutation11 permutation9
    _ = injectiveMoment H node491 := by rfl

def raw2120 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![1, -1, 1, -1], ![0, 2, -1, -1], ![1, 0, 0, -1]]

def raw2120step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![-1, -1, 2, 0], ![0, 1, -1, 0], ![3, -1, -1, -1]]

def raw2120step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 1, 0], ![0, 2, -1, -1], ![1, 0, 1, -2]]

theorem canonical2120 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2120 = injectiveMoment H node939 := by
  calc
    injectiveMoment H raw2120 = injectiveMoment H raw2120step0 := by
      have heq : raw2120step0 = raw2120.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2120).symm
    injectiveMoment H raw2120step0 = injectiveMoment H raw2120step1 := by
      have heq : raw2120step1 = (fun i j => raw2120step0 (permutation32 i) (permutation32 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2120step0 permutation32 permutation32
    _ = injectiveMoment H node939 := by rfl

def raw2121 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![1, -1, 1, -1], ![0, 2, 0, -2], ![1, 0, -1, 0]]

def raw2121step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![-1, -1, 2, 0], ![0, 1, 0, -1], ![3, -1, -2, 0]]

def raw2121step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, -1, 0, -1], ![1, 1, -2, 0], ![0, -1, 0, 1], ![-3, 1, 2, 0]]

def raw2121step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, -2, 1], ![0, 1, 2, -3], ![1, -1, 0, 0]]

theorem canonical2121 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2121 = injectiveMoment H node1079 := by
  calc
    injectiveMoment H raw2121 = injectiveMoment H raw2121step0 := by
      have heq : raw2121step0 = raw2121.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2121).symm
    injectiveMoment H raw2121step0 = injectiveMoment H raw2121step1 := by
      have heq : raw2121step1 = -raw2121step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2121step0).symm
    injectiveMoment H raw2121step1 = injectiveMoment H raw2121step2 := by
      have heq : raw2121step2 = (fun i j => raw2121step1 (permutation10 i) (permutation30 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2121step1 permutation10 permutation30
    _ = injectiveMoment H node1079 := by rfl

def raw2122 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![1, -1, 2, -2], ![0, 1, -2, 1], ![1, 1, 0, -2]]

def raw2122step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -2, 1], ![1, -1, 2, -2], ![1, 1, 0, -2]]

theorem canonical2122 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2122 = injectiveMoment H node488 := by
  calc
    injectiveMoment H raw2122 = injectiveMoment H raw2122step0 := by
      have heq : raw2122step0 = (fun i j => raw2122 (permutation11 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2122 permutation11 permutation9
    _ = injectiveMoment H node488 := by rfl

def raw2123 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![1, -1, 2, -2], ![0, 2, -2, 0], ![1, 0, 0, -1]]

def raw2123step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![-1, -1, 2, 0], ![0, 2, -2, 0], ![3, -2, 0, -1]]

def raw2123step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -2, 2, 0], ![0, 2, -1, -1], ![1, 0, 1, -2]]

theorem canonical2123 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2123 = injectiveMoment H node1190 := by
  calc
    injectiveMoment H raw2123 = injectiveMoment H raw2123step0 := by
      have heq : raw2123step0 = raw2123.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2123).symm
    injectiveMoment H raw2123step0 = injectiveMoment H raw2123step1 := by
      have heq : raw2123step1 = (fun i j => raw2123step0 (permutation32 i) (permutation32 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2123step0 permutation32 permutation32
    _ = injectiveMoment H node1190 := by rfl

def raw2124 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![1, -1, 2, -2], ![0, 2, -1, -1], ![1, 0, -1, 0]]

def raw2124step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![-1, -1, 2, 0], ![0, 2, -1, -1], ![3, -2, -1, 0]]

def raw2124step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 3, -2], ![0, 2, -1, -1], ![1, 0, -2, 1]]

theorem canonical2124 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2124 = injectiveMoment H node1016 := by
  calc
    injectiveMoment H raw2124 = injectiveMoment H raw2124step0 := by
      have heq : raw2124step0 = raw2124.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2124).symm
    injectiveMoment H raw2124step0 = injectiveMoment H raw2124step1 := by
      have heq : raw2124step1 = (fun i j => raw2124step0 (permutation26 i) (permutation31 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2124step0 permutation26 permutation31
    _ = injectiveMoment H node1016 := by rfl

def raw2125 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![1, -1, 2, -2], ![0, 2, 0, -2], ![1, 0, -2, 1]]

def raw2125step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 2, 0, -2], ![1, -1, 2, -2], ![1, 0, -2, 1]]

theorem canonical2125 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2125 = injectiveMoment H node496 := by
  calc
    injectiveMoment H raw2125 = injectiveMoment H raw2125step0 := by
      have heq : raw2125step0 = (fun i j => raw2125 (permutation11 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2125 permutation11 permutation9
    _ = injectiveMoment H node496 := by rfl

def raw2126 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![1, 0, -2, 1], ![0, 1, 3, -4], ![1, 0, -1, 0]]

def raw2126step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![-1, 0, 1, 0], ![0, -2, 3, -1], ![3, 1, -4, 0]]

def raw2126step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, -1, 1], ![0, 1, 3, -4], ![1, 1, -2, 0]]

theorem canonical2126 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2126 = injectiveMoment H node798 := by
  calc
    injectiveMoment H raw2126 = injectiveMoment H raw2126step0 := by
      have heq : raw2126step0 = raw2126.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2126).symm
    injectiveMoment H raw2126step0 = injectiveMoment H raw2126step1 := by
      have heq : raw2126step1 = (fun i j => raw2126step0 (permutation24 i) (permutation29 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2126step0 permutation24 permutation29
    _ = injectiveMoment H node798 := by rfl

def raw2127 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![1, 0, -2, 1], ![0, 2, 0, -2], ![1, -1, 2, -2]]

def raw2127step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 2, 0, -2], ![1, -1, 2, -2], ![1, 0, -2, 1]]

theorem canonical2127 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2127 = injectiveMoment H node496 := by
  calc
    injectiveMoment H raw2127 = injectiveMoment H raw2127step0 := by
      have heq : raw2127step0 = (fun i j => raw2127 (permutation12 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2127 permutation12 permutation9
    _ = injectiveMoment H node496 := by rfl

def raw2128 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![1, 0, -2, 1], ![0, 2, 1, -3], ![1, -1, 1, -1]]

def raw2128step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 1, 0, -3], ![-1, 0, 2, -1], ![0, -2, -1, 3], ![-1, 1, -1, 1]]

def raw2128step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 2, -1, -1], ![1, -1, -1, 1], ![1, 0, 2, -3]]

theorem canonical2128 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2128 = injectiveMoment H node495 := by
  calc
    injectiveMoment H raw2128 = injectiveMoment H raw2128step0 := by
      have heq : raw2128step0 = -raw2128 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2128).symm
    injectiveMoment H raw2128step0 = injectiveMoment H raw2128step1 := by
      have heq : raw2128step1 = (fun i j => raw2128step0 (permutation24 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2128step0 permutation24 permutation17
    _ = injectiveMoment H node495 := by rfl

def raw2129 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![1, 0, 1, -2], ![0, 2, 0, -2], ![1, -1, -1, 1]]

def raw2129step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 1, 0, -3], ![-1, 0, -1, 2], ![0, -2, 0, 2], ![-1, 1, 1, -1]]

def raw2129step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 2, 1, -3], ![1, -1, 1, -1]]

theorem canonical2129 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2129 = injectiveMoment H node1036 := by
  calc
    injectiveMoment H raw2129 = injectiveMoment H raw2129step0 := by
      have heq : raw2129step0 = -raw2129 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2129).symm
    injectiveMoment H raw2129step0 = injectiveMoment H raw2129step1 := by
      have heq : raw2129step1 = (fun i j => raw2129step0 (permutation17 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2129step0 permutation17 permutation21
    _ = injectiveMoment H node1036 := by rfl

def raw2130 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![1, 0, 2, -3], ![0, 2, -1, -1], ![1, -1, -1, 1]]

def raw2130step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 2, -1, -1], ![1, -1, -1, 1], ![1, 0, 2, -3]]

theorem canonical2130 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2130 = injectiveMoment H node495 := by
  calc
    injectiveMoment H raw2130 = injectiveMoment H raw2130step0 := by
      have heq : raw2130step0 = (fun i j => raw2130 (permutation12 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2130 permutation12 permutation9
    _ = injectiveMoment H node495 := by rfl

def raw2131 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![1, 1, -3, 1], ![0, 1, 2, -3], ![1, -1, 1, -1]]

def raw2131step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, 2, -3], ![1, -1, 1, -1], ![1, 1, -3, 1]]

theorem canonical2131 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2131 = injectiveMoment H node492 := by
  calc
    injectiveMoment H raw2131 = injectiveMoment H raw2131step0 := by
      have heq : raw2131step0 = (fun i j => raw2131 (permutation12 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2131 permutation12 permutation9
    _ = injectiveMoment H node492 := by rfl

def raw2132 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![1, 1, -2, 0], ![0, 1, 1, -2], ![1, -1, 1, -1]]

def raw2132step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, 1, -2], ![1, -1, 1, -1], ![1, 1, -2, 0]]

theorem canonical2132 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2132 = injectiveMoment H node490 := by
  calc
    injectiveMoment H raw2132 = injectiveMoment H raw2132step0 := by
      have heq : raw2132step0 = (fun i j => raw2132 (permutation12 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2132 permutation12 permutation9
    _ = injectiveMoment H node490 := by rfl

def raw2133 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![-3, 2, 1, 0], ![5, -1, -2, -2]]

def raw2133step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -3, 5], ![-1, 2, -1], ![1, 1, -2], ![2, 0, -2]]

def raw2133step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]

theorem canonical2133 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2133 = injectiveMoment H node74 := by
  calc
    injectiveMoment H raw2133 = injectiveMoment H raw2133step0 := by
      have heq : raw2133step0 = raw2133.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2133).symm
    injectiveMoment H raw2133step0 = injectiveMoment H raw2133step1 := by
      have heq : raw2133step1 = (fun i j => raw2133step0 (permutation14 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2133step0 permutation14 permutation5
    _ = injectiveMoment H node74 := by rfl

def raw2134 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![-2, 2, 1, -1], ![4, -1, -2, -1]]

def raw2134step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![1, 1, -2], ![2, -1, -1]]

theorem canonical2134 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2134 = injectiveMoment H node134 := by
  calc
    injectiveMoment H raw2134 = injectiveMoment H raw2134step0 := by
      have heq : raw2134step0 = raw2134.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2134).symm
    _ = injectiveMoment H node134 := by rfl

def raw2135 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![-2, 3, 1, -2], ![4, -2, -2, 0]]

def raw2135step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 3, -2], ![1, 1, -2], ![2, -2, 0]]

theorem canonical2135 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2135 = injectiveMoment H node136 := by
  calc
    injectiveMoment H raw2135 = injectiveMoment H raw2135step0 := by
      have heq : raw2135step0 = raw2135.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2135).symm
    _ = injectiveMoment H node136 := by rfl

def raw2136 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![-1, -1, 1, 1], ![0, 1, -1, 0], ![1, 1, -1, -1], ![2, 0, 0, -2]]

def raw2136step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 1, -2, 2], ![-1, 1, -1, 1], ![0, 0, 2, -2], ![1, -1, 0, 0], ![1, -1, 1, -1]]

theorem canonical2136 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2136 = injectiveMoment H node2839 := by
  calc
    injectiveMoment H raw2136 = injectiveMoment H raw2136step0 := by
      have heq : raw2136step0 = (fun i j => raw2136 (permutation37 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2136 permutation37 permutation17
    _ = injectiveMoment H node2839 := by rfl

def raw2137 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![-1, -1, 1, 1], ![0, 1, -1, 0], ![1, 1, 0, -2], ![2, 0, -1, -1]]

def raw2137step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![-1, 1, 0, 0], ![0, 1, -2, 1], ![1, -1, 1, -1], ![1, -1, 2, -2]]

theorem canonical2137 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2137 = injectiveMoment H node2712 := by
  calc
    injectiveMoment H raw2137 = injectiveMoment H raw2137step0 := by
      have heq : raw2137step0 = (fun i j => raw2137 (permutation144 i) (permutation24 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2137 permutation144 permutation24
    _ = injectiveMoment H node2712 := by rfl

def raw2138 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![-1, -1, 1, 1], ![0, 1, 0, -1], ![1, 1, -1, -1], ![2, 0, -1, -1]]

def raw2138step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![-1, 1, -1, 1], ![0, 1, -1, 0], ![1, -1, 1, -1], ![1, -1, 2, -2]]

theorem canonical2138 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2138 = injectiveMoment H node2711 := by
  calc
    injectiveMoment H raw2138 = injectiveMoment H raw2138step0 := by
      have heq : raw2138step0 = (fun i j => raw2138 (permutation150 i) (permutation24 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2138 permutation150 permutation24
    _ = injectiveMoment H node2711 := by rfl

def raw2139 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![-1, -1, 1, 1], ![1, 0, -1, 0], ![1, 1, -1, -1], ![1, 1, 0, -2]]

def raw2139step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 1, -1, -2], ![1, 1, -1, -1], ![-1, 0, 1, 0], ![-1, -1, 1, 1], ![-1, -1, 0, 2]]

def raw2139step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![-1, 1, -1, 1], ![0, 1, -1, 0], ![1, -1, 1, -1], ![1, -1, 2, -2]]

theorem canonical2139 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2139 = injectiveMoment H node2711 := by
  calc
    injectiveMoment H raw2139 = injectiveMoment H raw2139step0 := by
      have heq : raw2139step0 = -raw2139 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2139).symm
    injectiveMoment H raw2139step0 = injectiveMoment H raw2139step1 := by
      have heq : raw2139step1 = (fun i j => raw2139step0 (permutation150 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2139step0 permutation150 permutation17
    _ = injectiveMoment H node2711 := by rfl

def raw2140 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![-1, -1, 1, 1], ![1, 0, 0, -1], ![1, 1, -1, -1], ![1, 1, -1, -1]]

def raw2140step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 1, -2, 2], ![-1, 1, -1, 1], ![0, 0, 1, -1], ![1, -1, 1, -1], ![1, -1, 1, -1]]

theorem canonical2140 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2140 = injectiveMoment H node2838 := by
  calc
    injectiveMoment H raw2140 = injectiveMoment H raw2140step0 := by
      have heq : raw2140step0 = (fun i j => raw2140 (permutation33 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2140 permutation33 permutation17
    _ = injectiveMoment H node2838 := by rfl

def raw2141 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![-1, -1, 1, 1], ![3, 2, -2, -3]]

def raw2141step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![1, 1, -2], ![2, 1, -3]]

def raw2141step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, -1, 2], ![1, 1, -2], ![1, 2, -3]]

theorem canonical2141 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2141 = injectiveMoment H node258 := by
  calc
    injectiveMoment H raw2141 = injectiveMoment H raw2141step0 := by
      have heq : raw2141step0 = raw2141.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2141).symm
    injectiveMoment H raw2141step0 = injectiveMoment H raw2141step1 := by
      have heq : raw2141step1 = (fun i j => raw2141step0 (permutation9 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2141step0 permutation9 permutation5
    _ = injectiveMoment H node258 := by rfl

def raw2142 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![-1, -1, 2, 0], ![0, 1, -1, 0], ![1, 1, -1, -1], ![2, 0, -1, -1]]

def raw2142step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 1, -1, -2], ![1, 1, -2, 0], ![0, -1, 1, 0], ![-1, -1, 1, 1], ![-2, 0, 1, 1]]

def raw2142step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -1, 1, 0], ![0, 1, -2, 1], ![1, -1, 1, -1], ![1, 0, 1, -2]]

theorem canonical2142 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2142 = injectiveMoment H node2204 := by
  calc
    injectiveMoment H raw2142 = injectiveMoment H raw2142step0 := by
      have heq : raw2142step0 = -raw2142 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2142).symm
    injectiveMoment H raw2142step0 = injectiveMoment H raw2142step1 := by
      have heq : raw2142step1 = (fun i j => raw2142step0 (permutation39 i) (permutation30 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2142step0 permutation39 permutation30
    _ = injectiveMoment H node2204 := by rfl

def raw2143 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![-1, -1, 2, 0], ![1, 0, -1, 0], ![1, 1, -1, -1], ![1, 1, -1, -1]]

def raw2143step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 1, -1, -2], ![1, 1, -2, 0], ![-1, 0, 1, 0], ![-1, -1, 1, 1], ![-1, -1, 1, 1]]

def raw2143step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 1, -1], ![0, 1, -2, 1], ![1, -1, 1, -1], ![1, -1, 1, -1]]

theorem canonical2143 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2143 = injectiveMoment H node2238 := by
  calc
    injectiveMoment H raw2143 = injectiveMoment H raw2143step0 := by
      have heq : raw2143step0 = -raw2143 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2143).symm
    injectiveMoment H raw2143step0 = injectiveMoment H raw2143step1 := by
      have heq : raw2143step1 = (fun i j => raw2143step0 (permutation39 i) (permutation30 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2143step0 permutation39 permutation30
    _ = injectiveMoment H node2238 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
