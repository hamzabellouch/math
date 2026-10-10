import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes3
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes5
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes8
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes9
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes10
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes13
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes17
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes32
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes33
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes41

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw3872 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]

def raw3872step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 1, -2]]

theorem canonical3872 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3872 = injectiveMoment H node2130 := by
  calc
    injectiveMoment H raw3872 = injectiveMoment H raw3872step0 := by
      have heq : raw3872step0 = (fun i j => raw3872 (permutation390 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3872 permutation390 permutation6
    _ = injectiveMoment H node2130 := by rfl

def raw3873 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]

def raw3873step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, 1, -2]]

theorem canonical3873 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3873 = injectiveMoment H node647 := by
  calc
    injectiveMoment H raw3873 = injectiveMoment H raw3873step0 := by
      have heq : raw3873step0 = (fun i j => raw3873 (permutation123 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3873 permutation123 permutation6
    _ = injectiveMoment H node647 := by rfl

def raw3874 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]

def raw3874step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, 1, -2]]

theorem canonical3874 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3874 = injectiveMoment H node1131 := by
  calc
    injectiveMoment H raw3874 = injectiveMoment H raw3874step0 := by
      have heq : raw3874step0 = (fun i j => raw3874 (permutation123 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3874 permutation123 permutation6
    _ = injectiveMoment H node1131 := by rfl

def raw3875 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]

def raw3875step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-2, 2, 0]]

def raw3875step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]

theorem canonical3875 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3875 = injectiveMoment H node2091 := by
  calc
    injectiveMoment H raw3875 = injectiveMoment H raw3875step0 := by
      have heq : raw3875step0 = -raw3875 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3875).symm
    injectiveMoment H raw3875step0 = injectiveMoment H raw3875step1 := by
      have heq : raw3875step1 = (fun i j => raw3875step0 (permutation161 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3875step0 permutation161 permutation8
    _ = injectiveMoment H node2091 := by rfl

def raw3876 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]

def raw3876step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]

theorem canonical3876 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3876 = injectiveMoment H node622 := by
  calc
    injectiveMoment H raw3876 = injectiveMoment H raw3876step0 := by
      have heq : raw3876step0 = (fun i j => raw3876 (permutation122 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3876 permutation122 permutation6
    _ = injectiveMoment H node622 := by rfl

def raw3877 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]

def raw3877step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]

def raw3877step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]

theorem canonical3877 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3877 = injectiveMoment H node2668 := by
  calc
    injectiveMoment H raw3877 = injectiveMoment H raw3877step0 := by
      have heq : raw3877step0 = -raw3877 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3877).symm
    injectiveMoment H raw3877step0 = injectiveMoment H raw3877step1 := by
      have heq : raw3877step1 = (fun i j => raw3877step0 (permutation217 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3877step0 permutation217 permutation6
    _ = injectiveMoment H node2668 := by rfl

def raw3878 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]

def raw3878step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![1, 1, -2]]

theorem canonical3878 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3878 = injectiveMoment H node1136 := by
  calc
    injectiveMoment H raw3878 = injectiveMoment H raw3878step0 := by
      have heq : raw3878step0 = (fun i j => raw3878 (permutation140 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3878 permutation140 permutation6
    _ = injectiveMoment H node1136 := by rfl

def raw3879 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]

def raw3879step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![1, 1, -2]]

theorem canonical3879 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3879 = injectiveMoment H node660 := by
  calc
    injectiveMoment H raw3879 = injectiveMoment H raw3879step0 := by
      have heq : raw3879step0 = (fun i j => raw3879 (permutation140 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3879 permutation140 permutation6
    _ = injectiveMoment H node660 := by rfl

def raw3880 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]

def raw3880step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![2, 0, -2]]

theorem canonical3880 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3880 = injectiveMoment H node2112 := by
  calc
    injectiveMoment H raw3880 = injectiveMoment H raw3880step0 := by
      have heq : raw3880step0 = (fun i j => raw3880 (permutation307 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3880 permutation307 permutation6
    _ = injectiveMoment H node2112 := by rfl

def raw3881 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]

def raw3881step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]

theorem canonical3881 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3881 = injectiveMoment H node2095 := by
  calc
    injectiveMoment H raw3881 = injectiveMoment H raw3881step0 := by
      have heq : raw3881step0 = (fun i j => raw3881 (permutation287 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3881 permutation287 permutation6
    _ = injectiveMoment H node2095 := by rfl

def raw3882 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]

def raw3882step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]

def raw3882step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]

theorem canonical3882 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3882 = injectiveMoment H node2121 := by
  calc
    injectiveMoment H raw3882 = injectiveMoment H raw3882step0 := by
      have heq : raw3882step0 = -raw3882 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3882).symm
    injectiveMoment H raw3882step0 = injectiveMoment H raw3882step1 := by
      have heq : raw3882step1 = (fun i j => raw3882step0 (permutation206 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3882step0 permutation206 permutation6
    _ = injectiveMoment H node2121 := by rfl

def raw3883 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]

def raw3883step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]

def raw3883step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

theorem canonical3883 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3883 = injectiveMoment H node2119 := by
  calc
    injectiveMoment H raw3883 = injectiveMoment H raw3883step0 := by
      have heq : raw3883step0 = -raw3883 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3883).symm
    injectiveMoment H raw3883step0 = injectiveMoment H raw3883step1 := by
      have heq : raw3883step1 = (fun i j => raw3883step0 (permutation204 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3883step0 permutation204 permutation6
    _ = injectiveMoment H node2119 := by rfl

def raw3884 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]

def raw3884step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![0, 1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]

def raw3884step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]

theorem canonical3884 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3884 = injectiveMoment H node2096 := by
  calc
    injectiveMoment H raw3884 = injectiveMoment H raw3884step0 := by
      have heq : raw3884step0 = -raw3884 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3884).symm
    injectiveMoment H raw3884step0 = injectiveMoment H raw3884step1 := by
      have heq : raw3884step1 = (fun i j => raw3884step0 (permutation168 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3884step0 permutation168 permutation8
    _ = injectiveMoment H node2096 := by rfl

def raw3885 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]

def raw3885step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]

def raw3885step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]

theorem canonical3885 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3885 = injectiveMoment H node2101 := by
  calc
    injectiveMoment H raw3885 = injectiveMoment H raw3885step0 := by
      have heq : raw3885step0 = -raw3885 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3885).symm
    injectiveMoment H raw3885step0 = injectiveMoment H raw3885step1 := by
      have heq : raw3885step1 = (fun i j => raw3885step0 (permutation218 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3885step0 permutation218 permutation6
    _ = injectiveMoment H node2101 := by rfl

def raw3886 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]

def raw3886step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]

def raw3886step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]

theorem canonical3886 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3886 = injectiveMoment H node2118 := by
  calc
    injectiveMoment H raw3886 = injectiveMoment H raw3886step0 := by
      have heq : raw3886step0 = -raw3886 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3886).symm
    injectiveMoment H raw3886step0 = injectiveMoment H raw3886step1 := by
      have heq : raw3886step1 = (fun i j => raw3886step0 (permutation205 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3886step0 permutation205 permutation6
    _ = injectiveMoment H node2118 := by rfl

def raw3887 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]

def raw3887step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]

def raw3887step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![2, -1, -1]]

theorem canonical3887 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3887 = injectiveMoment H node642 := by
  calc
    injectiveMoment H raw3887 = injectiveMoment H raw3887step0 := by
      have heq : raw3887step0 = -raw3887 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3887).symm
    injectiveMoment H raw3887step0 = injectiveMoment H raw3887step1 := by
      have heq : raw3887step1 = (fun i j => raw3887step0 (permutation60 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3887step0 permutation60 permutation6
    _ = injectiveMoment H node642 := by rfl

def raw3888 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]

def raw3888step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-1, 2, -1], ![-1, -1, 2], ![-2, 1, 1]]

def raw3888step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]

theorem canonical3888 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3888 = injectiveMoment H node625 := by
  calc
    injectiveMoment H raw3888 = injectiveMoment H raw3888step0 := by
      have heq : raw3888step0 = -raw3888 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3888).symm
    injectiveMoment H raw3888step0 = injectiveMoment H raw3888step1 := by
      have heq : raw3888step1 = (fun i j => raw3888step0 (permutation69 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3888step0 permutation69 permutation6
    _ = injectiveMoment H node625 := by rfl

def raw3889 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]

def raw3889step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]

def raw3889step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]

theorem canonical3889 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3889 = injectiveMoment H node2120 := by
  calc
    injectiveMoment H raw3889 = injectiveMoment H raw3889step0 := by
      have heq : raw3889step0 = -raw3889 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3889).symm
    injectiveMoment H raw3889step0 = injectiveMoment H raw3889step1 := by
      have heq : raw3889step1 = (fun i j => raw3889step0 (permutation206 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3889step0 permutation206 permutation6
    _ = injectiveMoment H node2120 := by rfl

def raw3890 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]

def raw3890step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]

def raw3890step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![2, 0, -2]]

theorem canonical3890 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3890 = injectiveMoment H node641 := by
  calc
    injectiveMoment H raw3890 = injectiveMoment H raw3890step0 := by
      have heq : raw3890step0 = -raw3890 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3890).symm
    injectiveMoment H raw3890step0 = injectiveMoment H raw3890step1 := by
      have heq : raw3890step1 = (fun i j => raw3890step0 (permutation33 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3890step0 permutation33 permutation8
    _ = injectiveMoment H node641 := by rfl

def raw3891 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]

def raw3891step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]

def raw3891step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]

theorem canonical3891 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3891 = injectiveMoment H node646 := by
  calc
    injectiveMoment H raw3891 = injectiveMoment H raw3891step0 := by
      have heq : raw3891step0 = -raw3891 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3891).symm
    injectiveMoment H raw3891step0 = injectiveMoment H raw3891step1 := by
      have heq : raw3891step1 = (fun i j => raw3891step0 (permutation59 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3891step0 permutation59 permutation6
    _ = injectiveMoment H node646 := by rfl

def raw3892 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![2, -2, 0], ![2, 0, -2]]

def raw3892step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 2, -2], ![2, 0, -2]]

theorem canonical3892 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3892 = injectiveMoment H node197 := by
  calc
    injectiveMoment H raw3892 = injectiveMoment H raw3892step0 := by
      have heq : raw3892step0 = (fun i j => raw3892 (permutation25 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3892 permutation25 permutation6
    _ = injectiveMoment H node197 := by rfl

def raw3893 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![2, -1, -1], ![2, -1, -1]]

def raw3893step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-2, 1, 1], ![-2, 1, 1]]

def raw3893step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![1, 1, -2], ![1, 1, -2]]

theorem canonical3893 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3893 = injectiveMoment H node202 := by
  calc
    injectiveMoment H raw3893 = injectiveMoment H raw3893step0 := by
      have heq : raw3893step0 = -raw3893 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3893).symm
    injectiveMoment H raw3893step0 = injectiveMoment H raw3893step1 := by
      have heq : raw3893step1 = (fun i j => raw3893step0 (permutation15 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3893step0 permutation15 permutation6
    _ = injectiveMoment H node202 := by rfl

def raw3894 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -2, 3], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]

def raw3894step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]

theorem canonical3894 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3894 = injectiveMoment H node534 := by
  calc
    injectiveMoment H raw3894 = injectiveMoment H raw3894step0 := by
      have heq : raw3894step0 = (fun i j => raw3894 (permutation75 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3894 permutation75 permutation5
    _ = injectiveMoment H node534 := by rfl

def raw3895 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]

def raw3895step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -1, 1], ![-1, 1, 0], ![-2, -1, 3]]

def raw3895step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, 1, -2]]

theorem canonical3895 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3895 = injectiveMoment H node863 := by
  calc
    injectiveMoment H raw3895 = injectiveMoment H raw3895step0 := by
      have heq : raw3895step0 = -raw3895 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3895).symm
    injectiveMoment H raw3895step0 = injectiveMoment H raw3895step1 := by
      have heq : raw3895step1 = (fun i j => raw3895step0 (permutation140 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3895step0 permutation140 permutation5
    _ = injectiveMoment H node863 := by rfl

def raw3896 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]

def raw3896step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]

def raw3896step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![1, 1, -2]]

theorem canonical3896 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3896 = injectiveMoment H node1136 := by
  calc
    injectiveMoment H raw3896 = injectiveMoment H raw3896step0 := by
      have heq : raw3896step0 = -raw3896 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3896).symm
    injectiveMoment H raw3896step0 = injectiveMoment H raw3896step1 := by
      have heq : raw3896step1 = (fun i j => raw3896step0 (permutation117 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3896step0 permutation117 permutation5
    _ = injectiveMoment H node1136 := by rfl

def raw3897 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -2, 1], ![2, 1, -3]]

def raw3897step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -2, 2], ![-1, 2, -1], ![-2, -1, 3]]

def raw3897step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]

theorem canonical3897 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3897 = injectiveMoment H node534 := by
  calc
    injectiveMoment H raw3897 = injectiveMoment H raw3897step0 := by
      have heq : raw3897step0 = -raw3897 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3897).symm
    injectiveMoment H raw3897step0 = injectiveMoment H raw3897step1 := by
      have heq : raw3897step1 = (fun i j => raw3897step0 (permutation150 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3897step0 permutation150 permutation3
    _ = injectiveMoment H node534 := by rfl

def raw3898 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]

def raw3898step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]

def raw3898step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, 1, -2]]

theorem canonical3898 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3898 = injectiveMoment H node647 := by
  calc
    injectiveMoment H raw3898 = injectiveMoment H raw3898step0 := by
      have heq : raw3898step0 = -raw3898 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3898).symm
    injectiveMoment H raw3898step0 = injectiveMoment H raw3898step1 := by
      have heq : raw3898step1 = (fun i j => raw3898step0 (permutation99 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3898step0 permutation99 permutation5
    _ = injectiveMoment H node647 := by rfl

def raw3899 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]

def raw3899step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]

def raw3899step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![1, 1, -2]]

theorem canonical3899 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3899 = injectiveMoment H node660 := by
  calc
    injectiveMoment H raw3899 = injectiveMoment H raw3899step0 := by
      have heq : raw3899step0 = -raw3899 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3899).symm
    injectiveMoment H raw3899step0 = injectiveMoment H raw3899step1 := by
      have heq : raw3899step1 = (fun i j => raw3899step0 (permutation93 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3899step0 permutation93 permutation5
    _ = injectiveMoment H node660 := by rfl

def raw3900 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]

theorem canonical3900 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3900 = injectiveMoment H node622 := by
  rfl

def raw3901 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![2, -2, 0], ![1, 1, -2]]

def raw3901step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]

theorem canonical3901 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3901 = injectiveMoment H node622 := by
  calc
    injectiveMoment H raw3901 = injectiveMoment H raw3901step0 := by
      have heq : raw3901step0 = (fun i j => raw3901 (permutation34 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3901 permutation34 permutation3
    _ = injectiveMoment H node622 := by rfl

def raw3902 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 3, -3], ![1, -2, 1], ![2, 0, -2]]

def raw3902step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -3, 3], ![-1, 2, -1], ![-2, 0, 2]]

def raw3902step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]

theorem canonical3902 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3902 = injectiveMoment H node329 := by
  calc
    injectiveMoment H raw3902 = injectiveMoment H raw3902step0 := by
      have heq : raw3902step0 = -raw3902 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3902).symm
    injectiveMoment H raw3902step0 = injectiveMoment H raw3902step1 := by
      have heq : raw3902step1 = (fun i j => raw3902step0 (permutation98 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3902step0 permutation98 permutation5
    _ = injectiveMoment H node329 := by rfl

def raw3903 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 3, -3], ![1, 0, -1], ![2, -2, 0]]

def raw3903step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -3, 3], ![-1, 0, 1], ![-2, 2, 0]]

def raw3903step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]

theorem canonical3903 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3903 = injectiveMoment H node338 := by
  calc
    injectiveMoment H raw3903 = injectiveMoment H raw3903step0 := by
      have heq : raw3903step0 = -raw3903 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3903).symm
    injectiveMoment H raw3903step0 = injectiveMoment H raw3903step1 := by
      have heq : raw3903step1 = (fun i j => raw3903step0 (permutation92 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3903step0 permutation92 permutation5
    _ = injectiveMoment H node338 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
