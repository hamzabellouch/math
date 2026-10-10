import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes0
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes3
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes4
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes10
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes11
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes12
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes13
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes17
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes18
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes20
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes22
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes37
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes38

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw7872 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, 3, -3], ![1, -1, -2, 2]]

def raw7872step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![1, 0, -1], ![-1, 3, -2], ![1, -3, 2]]

def raw7872step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 2, -3]]

theorem canonical7872 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7872 = injectiveMoment H node259 := by
  calc
    injectiveMoment H raw7872 = injectiveMoment H raw7872step0 := by
      have heq : raw7872step0 = raw7872.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7872).symm
    injectiveMoment H raw7872step0 = injectiveMoment H raw7872step1 := by
      have heq : raw7872step1 = (fun i j => raw7872step0 (permutation21 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7872step0 permutation21 permutation4
    _ = injectiveMoment H node259 := by rfl

def raw7873 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![1, -2, -2, 3], ![0, 1, 3, -4]]

def raw7873step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![1, -2, 1], ![-1, -2, 3], ![1, 3, -4]]

def raw7873step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -1, 0], ![-1, 2, -1], ![1, 2, -3], ![-1, -3, 4]]

def raw7873step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 2, -1], ![1, -1, 0], ![1, 2, -3]]

theorem canonical7873 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7873 = injectiveMoment H node245 := by
  calc
    injectiveMoment H raw7873 = injectiveMoment H raw7873step0 := by
      have heq : raw7873step0 = raw7873.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7873).symm
    injectiveMoment H raw7873step0 = injectiveMoment H raw7873step1 := by
      have heq : raw7873step1 = -raw7873step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7873step0).symm
    injectiveMoment H raw7873step1 = injectiveMoment H raw7873step2 := by
      have heq : raw7873step2 = (fun i j => raw7873step1 (permutation29 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7873step1 permutation29 permutation3
    _ = injectiveMoment H node245 := by rfl

def raw7874 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![1, -1, -2, 2], ![0, 0, 3, -3]]

def raw7874step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![1, -1, 0], ![-1, -2, 3], ![1, 2, -3]]

def raw7874step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 2, -3]]

theorem canonical7874 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7874 = injectiveMoment H node259 := by
  calc
    injectiveMoment H raw7874 = injectiveMoment H raw7874step0 := by
      have heq : raw7874step0 = raw7874.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7874).symm
    injectiveMoment H raw7874step0 = injectiveMoment H raw7874step1 := by
      have heq : raw7874step1 = (fun i j => raw7874step0 (permutation21 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7874step0 permutation21 permutation3
    _ = injectiveMoment H node259 := by rfl

def raw7875 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -3, 4], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1]]

def raw7875step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 1, 0], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1]]

theorem canonical7875 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7875 = injectiveMoment H node740 := by
  calc
    injectiveMoment H raw7875 = injectiveMoment H raw7875step0 := by
      have heq : raw7875step0 = (fun i j => raw7875 (permutation57 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7875 permutation57 permutation3
    _ = injectiveMoment H node740 := by rfl

def raw7876 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -2, 3], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]

def raw7876step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]

theorem canonical7876 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7876 = injectiveMoment H node869 := by
  calc
    injectiveMoment H raw7876 = injectiveMoment H raw7876step0 := by
      have heq : raw7876step0 = (fun i j => raw7876 (permutation57 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7876 permutation57 permutation3
    _ = injectiveMoment H node869 := by rfl

def raw7877 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![2, 3, -5]]

def raw7877step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -1, 0], ![1, 1, -2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![-2, -3, 5]]

def raw7877step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

theorem canonical7877 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7877 = injectiveMoment H node1437 := by
  calc
    injectiveMoment H raw7877 = injectiveMoment H raw7877step0 := by
      have heq : raw7877step0 = -raw7877 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7877).symm
    injectiveMoment H raw7877step0 = injectiveMoment H raw7877step1 := by
      have heq : raw7877step1 = (fun i j => raw7877step0 (permutation366 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7877step0 permutation366 permutation3
    _ = injectiveMoment H node1437 := by rfl

def raw7878 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

def raw7878step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -1, 0], ![1, 1, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1]]

def raw7878step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

theorem canonical7878 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7878 = injectiveMoment H node711 := by
  calc
    injectiveMoment H raw7878 = injectiveMoment H raw7878step0 := by
      have heq : raw7878step0 = -raw7878 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7878).symm
    injectiveMoment H raw7878step0 = injectiveMoment H raw7878step1 := by
      have heq : raw7878step1 = (fun i j => raw7878step0 (permutation69 i) (permutation7 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7878step0 permutation69 permutation7
    _ = injectiveMoment H node711 := by rfl

def raw7879 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![0, -3, 3], ![-1, 3, -2], ![1, -1, 0], ![1, 0, -1]]

def raw7879step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 0, 1], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1]]

theorem canonical7879 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7879 = injectiveMoment H node864 := by
  calc
    injectiveMoment H raw7879 = injectiveMoment H raw7879step0 := by
      have heq : raw7879step0 = (fun i j => raw7879 (permutation81 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7879 permutation81 permutation4
    _ = injectiveMoment H node864 := by rfl

def raw7880 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![0, -3, 3], ![0, 2, -2], ![1, 0, -1]]

def raw7880step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -2, 2], ![0, 3, -3], ![1, -1, 0]]

theorem canonical7880 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7880 = injectiveMoment H node292 := by
  calc
    injectiveMoment H raw7880 = injectiveMoment H raw7880step0 := by
      have heq : raw7880step0 = (fun i j => raw7880 (permutation11 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7880 permutation11 permutation4
    _ = injectiveMoment H node292 := by rfl

def raw7881 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![0, -3, 3], ![0, 3, -3], ![0, -1, 1], ![1, 0, -1]]

def raw7881step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -3, 3], ![0, 1, -1], ![0, 3, -3], ![1, -1, 0]]

theorem canonical7881 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7881 = injectiveMoment H node1289 := by
  calc
    injectiveMoment H raw7881 = injectiveMoment H raw7881step0 := by
      have heq : raw7881step0 = (fun i j => raw7881 (permutation41 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7881 permutation41 permutation4
    _ = injectiveMoment H node1289 := by rfl

def raw7882 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![0, -3, 3], ![0, 3, -3], ![1, -1, 0], ![0, 0, 0]]

def raw7882step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![0, -3, 3], ![0, 3, -3], ![1, -1, 0]]

def raw7882step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -3, 3], ![0, 3, -3], ![1, 0, -1]]

theorem canonical7882 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7882 = injectiveMoment H node289 := by
  calc
    injectiveMoment H raw7882 = injectiveMoment H raw7882step0 := by
      have hz : ∀ j, raw7882 (permutation128 0) j = 0 := by decide +kernel
      have heq : raw7882step0 = (fun i j => raw7882 (permutation128 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7882 permutation128 hz
    injectiveMoment H raw7882step0 = injectiveMoment H raw7882step1 := by
      have heq : raw7882step1 = (fun i j => raw7882step0 (permutation11 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7882step0 permutation11 permutation4
    _ = injectiveMoment H node289 := by rfl

def raw7883 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, 1, 0], ![0, -3, 3], ![1, 2, -3]]

def raw7883step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, -1, 0], ![0, 3, -3], ![-1, -2, 3]]

def raw7883step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 3, -3], ![1, -1, 0]]

theorem canonical7883 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7883 = injectiveMoment H node58 := by
  calc
    injectiveMoment H raw7883 = injectiveMoment H raw7883step0 := by
      have heq : raw7883step0 = -raw7883 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7883).symm
    injectiveMoment H raw7883step0 = injectiveMoment H raw7883step1 := by
      have heq : raw7883step1 = (fun i j => raw7883step0 (permutation8 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7883step0 permutation8 permutation3
    _ = injectiveMoment H node58 := by rfl

def raw7884 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![0, -2, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1]]

def raw7884step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -1, 0], ![0, 2, -2], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1]]

def raw7884step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

theorem canonical7884 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7884 = injectiveMoment H node659 := by
  calc
    injectiveMoment H raw7884 = injectiveMoment H raw7884step0 := by
      have heq : raw7884step0 = -raw7884 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7884).symm
    injectiveMoment H raw7884step0 = injectiveMoment H raw7884step1 := by
      have heq : raw7884step1 = (fun i j => raw7884step0 (permutation69 i) (permutation7 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7884step0 permutation69 permutation7
    _ = injectiveMoment H node659 := by rfl

def raw7885 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![0, -2, 2], ![0, 2, -2], ![0, -1, 1], ![1, 0, -1]]

def raw7885step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0]]

theorem canonical7885 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7885 = injectiveMoment H node1292 := by
  calc
    injectiveMoment H raw7885 = injectiveMoment H raw7885step0 := by
      have heq : raw7885step0 = (fun i j => raw7885 (permutation41 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7885 permutation41 permutation4
    _ = injectiveMoment H node1292 := by rfl

def raw7886 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![0, 0, 0]]

def raw7886step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0]]

def raw7886step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1]]

theorem canonical7886 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7886 = injectiveMoment H node291 := by
  calc
    injectiveMoment H raw7886 = injectiveMoment H raw7886step0 := by
      have hz : ∀ j, raw7886 (permutation128 0) j = 0 := by decide +kernel
      have heq : raw7886step0 = (fun i j => raw7886 (permutation128 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7886 permutation128 hz
    injectiveMoment H raw7886step0 = injectiveMoment H raw7886step1 := by
      have heq : raw7886step1 = (fun i j => raw7886step0 (permutation11 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7886step0 permutation11 permutation4
    _ = injectiveMoment H node291 := by rfl

def raw7887 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![0, -1, 1], ![-1, -1, 2], ![0, -1, 1], ![0, -1, 1], ![2, 3, -5]]

def raw7887step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -1, 0], ![0, 1, -1], ![1, 1, -2], ![0, 1, -1], ![0, 1, -1], ![-2, -3, 5]]

def raw7887step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

theorem canonical7887 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7887 = injectiveMoment H node1437 := by
  calc
    injectiveMoment H raw7887 = injectiveMoment H raw7887step0 := by
      have heq : raw7887step0 = -raw7887 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7887).symm
    injectiveMoment H raw7887step0 = injectiveMoment H raw7887step1 := by
      have heq : raw7887step1 = (fun i j => raw7887step0 (permutation347 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7887step0 permutation347 permutation3
    _ = injectiveMoment H node1437 := by rfl

def raw7888 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![0, -1, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1]]

def raw7888step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0]]

theorem canonical7888 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7888 = injectiveMoment H node1294 := by
  calc
    injectiveMoment H raw7888 = injectiveMoment H raw7888step0 := by
      have heq : raw7888step0 = (fun i j => raw7888 (permutation146 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7888 permutation146 permutation8
    _ = injectiveMoment H node1294 := by rfl

def raw7889 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2], ![0, -1, 1], ![2, 3, -5]]

def raw7889step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![0, 1, -1], ![-2, -3, 5]]

def raw7889step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

theorem canonical7889 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7889 = injectiveMoment H node1437 := by
  calc
    injectiveMoment H raw7889 = injectiveMoment H raw7889step0 := by
      have heq : raw7889step0 = -raw7889 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7889).symm
    injectiveMoment H raw7889step0 = injectiveMoment H raw7889step1 := by
      have heq : raw7889step1 = (fun i j => raw7889step0 (permutation341 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7889step0 permutation341 permutation3
    _ = injectiveMoment H node1437 := by rfl

def raw7890 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2], ![2, 3, -5]]

def raw7890step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![-2, -3, 5]]

def raw7890step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

theorem canonical7890 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7890 = injectiveMoment H node1437 := by
  calc
    injectiveMoment H raw7890 = injectiveMoment H raw7890step0 := by
      have heq : raw7890step0 = -raw7890 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7890).symm
    injectiveMoment H raw7890step0 = injectiveMoment H raw7890step1 := by
      have heq : raw7890step1 = (fun i j => raw7890step0 (permutation339 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7890step0 permutation339 permutation3
    _ = injectiveMoment H node1437 := by rfl

def raw7891 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 3, -4]]

def raw7891step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![-1, -3, 4]]

def raw7891step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0]]

theorem canonical7891 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7891 = injectiveMoment H node2384 := by
  calc
    injectiveMoment H raw7891 = injectiveMoment H raw7891step0 := by
      have heq : raw7891step0 = -raw7891 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7891).symm
    injectiveMoment H raw7891step0 = injectiveMoment H raw7891step1 := by
      have heq : raw7891step1 = (fun i j => raw7891step0 (permutation340 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7891step0 permutation340 permutation3
    _ = injectiveMoment H node2384 := by rfl

def raw7892 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1]]

def raw7892step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0]]

theorem canonical7892 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7892 = injectiveMoment H node1294 := by
  calc
    injectiveMoment H raw7892 = injectiveMoment H raw7892step0 := by
      have heq : raw7892step0 = (fun i j => raw7892 (permutation39 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7892 permutation39 permutation4
    _ = injectiveMoment H node1294 := by rfl

def raw7893 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0]]

def raw7893step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0]]

def raw7893step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1]]

theorem canonical7893 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7893 = injectiveMoment H node293 := by
  calc
    injectiveMoment H raw7893 = injectiveMoment H raw7893step0 := by
      have hz : ∀ j, raw7893 (permutation128 0) j = 0 := by decide +kernel
      have heq : raw7893step0 = (fun i j => raw7893 (permutation128 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7893 permutation128 hz
    injectiveMoment H raw7893step0 = injectiveMoment H raw7893step1 := by
      have heq : raw7893step1 = (fun i j => raw7893step0 (permutation11 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7893step0 permutation11 permutation4
    _ = injectiveMoment H node293 := by rfl

def raw7894 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![-1, -2, 3]]

def raw7894step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

theorem canonical7894 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7894 = injectiveMoment H node2469 := by
  calc
    injectiveMoment H raw7894 = injectiveMoment H raw7894step0 := by
      have heq : raw7894step0 = (fun i j => raw7894 (permutation308 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7894 permutation308 permutation3
    _ = injectiveMoment H node2469 := by rfl

def raw7895 : Matrix (Fin 2) (Fin 3) ℤ := ![![-1, 1, 0], ![1, -1, 0]]

def raw7895step0 : Matrix (Fin 2) (Fin 2) ℤ := ![![-1, 1], ![1, -1]]

theorem canonical7895 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7895 = injectiveMoment H node5 := by
  calc
    injectiveMoment H raw7895 = injectiveMoment H raw7895step0 := by
      have hz : ∀ i, raw7895 i (permutation7 0) = 0 := by decide +kernel
      have heq : raw7895step0 = (fun i j => raw7895 i (permutation7 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw7895 permutation7 hz
    _ = injectiveMoment H node5 := by rfl

def raw7896 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, 0, 0], ![0, -1, -3, 4], ![0, 0, 2, -2], ![1, 0, 1, -2]]

def raw7896step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, 0, 2, -2], ![0, 1, 1, -2], ![1, -1, 0, 0]]

theorem canonical7896 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7896 = injectiveMoment H node1178 := by
  calc
    injectiveMoment H raw7896 = injectiveMoment H raw7896step0 := by
      have heq : raw7896step0 = (fun i j => raw7896 (permutation18 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7896 permutation18 permutation15
    _ = injectiveMoment H node1178 := by rfl

def raw7897 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, 0, 0], ![0, -1, -1, 2], ![0, -1, -1, 2], ![1, 1, 2, -4]]

def raw7897step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, -1, 0, 0], ![0, 1, 1, -2], ![0, 1, 1, -2], ![-1, -1, -2, 4]]

def raw7897step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 1, 1, -2], ![0, 1, 1, -2], ![1, 0, -1, 0]]

theorem canonical7897 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7897 = injectiveMoment H node787 := by
  calc
    injectiveMoment H raw7897 = injectiveMoment H raw7897step0 := by
      have heq : raw7897step0 = -raw7897 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7897).symm
    injectiveMoment H raw7897step0 = injectiveMoment H raw7897step1 := by
      have heq : raw7897step1 = (fun i j => raw7897step0 (permutation30 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7897step0 permutation30 permutation11
    _ = injectiveMoment H node787 := by rfl

def raw7898 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, 0, 0], ![0, -1, 3, -2], ![0, 1, -2, 1], ![1, -1, -1, 1]]

def raw7898step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, -1, 0, 0], ![0, 1, -3, 2], ![0, -1, 2, -1], ![-1, 1, 1, -1]]

def raw7898step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, -1, 2], ![0, 2, 1, -3], ![1, 0, -1, 0]]

theorem canonical7898 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7898 = injectiveMoment H node1099 := by
  calc
    injectiveMoment H raw7898 = injectiveMoment H raw7898step0 := by
      have heq : raw7898step0 = -raw7898 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7898).symm
    injectiveMoment H raw7898step0 = injectiveMoment H raw7898step1 := by
      have heq : raw7898step1 = (fun i j => raw7898step0 (permutation32 i) (permutation13 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7898step0 permutation32 permutation13
    _ = injectiveMoment H node1099 := by rfl

def raw7899 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, 0, 0], ![0, 0, -1, 1], ![0, 1, 2, -3], ![1, -2, -1, 2]]

def raw7899step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![1, 0, 1, -2], ![0, -1, 2, -1], ![0, 1, -3, 2]]

def raw7899step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 0, -1], ![-1, 0, -1, 2], ![0, 1, -2, 1], ![0, -1, 3, -2]]

def raw7899step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 2, -1], ![0, 1, -1, 0], ![1, 0, 1, -2]]

theorem canonical7899 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7899 = injectiveMoment H node1206 := by
  calc
    injectiveMoment H raw7899 = injectiveMoment H raw7899step0 := by
      have heq : raw7899step0 = raw7899.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7899).symm
    injectiveMoment H raw7899step0 = injectiveMoment H raw7899step1 := by
      have heq : raw7899step1 = -raw7899step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7899step0).symm
    injectiveMoment H raw7899step1 = injectiveMoment H raw7899step2 := by
      have heq : raw7899step2 = (fun i j => raw7899step1 (permutation29 i) (permutation16 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7899step1 permutation29 permutation16
    _ = injectiveMoment H node1206 := by rfl

def raw7900 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, 0, 0], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, -2, -2, 3]]

def raw7900step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![1, 0, 1, -2], ![0, 1, 1, -2], ![0, -1, -2, 3]]

def raw7900step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 0, 1], ![0, 1, 1, -2], ![1, 0, 1, -2]]

theorem canonical7900 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7900 = injectiveMoment H node1198 := by
  calc
    injectiveMoment H raw7900 = injectiveMoment H raw7900step0 := by
      have heq : raw7900step0 = raw7900.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7900).symm
    injectiveMoment H raw7900step0 = injectiveMoment H raw7900step1 := by
      have heq : raw7900step1 = (fun i j => raw7900step0 (permutation27 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7900step0 permutation27 permutation15
    _ = injectiveMoment H node1198 := by rfl

def raw7901 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 1, 0, 0], ![0, 1, 2, -3], ![1, -2, -2, 3]]

def raw7901step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![1, 1, -2], ![0, 2, -2], ![0, -3, 3]]

def raw7901step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![-1, -1, 2], ![0, -2, 2], ![0, 3, -3]]

def raw7901step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -2, 2], ![0, 3, -3], ![1, 0, -1]]

theorem canonical7901 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7901 = injectiveMoment H node280 := by
  calc
    injectiveMoment H raw7901 = injectiveMoment H raw7901step0 := by
      have heq : raw7901step0 = raw7901.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7901).symm
    injectiveMoment H raw7901step0 = injectiveMoment H raw7901step1 := by
      have heq : raw7901step1 = -raw7901step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7901step0).symm
    injectiveMoment H raw7901step1 = injectiveMoment H raw7901step2 := by
      have heq : raw7901step2 = (fun i j => raw7901step1 (permutation18 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7901step1 permutation18 permutation3
    _ = injectiveMoment H node280 := by rfl

def raw7902 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 1, 1, -1], ![-3, 1, 1, 1], ![4, -2, -2, 0]]

def raw7902step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![1, 1, -2], ![1, 1, -2], ![-1, 1, 0]]

def raw7902step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 1, 0], ![1, 1, -2], ![1, 1, -2]]

theorem canonical7902 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7902 = injectiveMoment H node244 := by
  calc
    injectiveMoment H raw7902 = injectiveMoment H raw7902step0 := by
      have heq : raw7902step0 = raw7902.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7902).symm
    injectiveMoment H raw7902step0 = injectiveMoment H raw7902step1 := by
      have heq : raw7902step1 = (fun i j => raw7902step0 (permutation13 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7902step0 permutation13 permutation3
    _ = injectiveMoment H node244 := by rfl

def raw7903 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 1, 1, -1], ![-3, 1, 2, 0], ![4, -2, -3, 1]]

def raw7903step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![1, 1, -2], ![1, 2, -3], ![-1, 0, 1]]

def raw7903step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 0, 1], ![1, 1, -2], ![1, 2, -3]]

theorem canonical7903 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7903 = injectiveMoment H node241 := by
  calc
    injectiveMoment H raw7903 = injectiveMoment H raw7903step0 := by
      have heq : raw7903step0 = raw7903.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7903).symm
    injectiveMoment H raw7903step0 = injectiveMoment H raw7903step1 := by
      have heq : raw7903step1 = (fun i j => raw7903step0 (permutation13 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7903step0 permutation13 permutation3
    _ = injectiveMoment H node241 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
