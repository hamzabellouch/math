import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes2
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes3
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes4
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes8
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes13
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes17
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes20

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw5856 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, -1, 2], ![0, 2, -2], ![1, 0, -1], ![1, 1, -2]]

theorem canonical5856 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5856 = injectiveMoment H node858 := by
  rfl

def raw5857 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, -1, 2], ![0, 2, -2], ![2, 1, -3]]

def raw5857step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, 1, -2], ![0, -2, 2], ![-2, -1, 3]]

def raw5857step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![1, 1, -2], ![1, 2, -3]]

theorem canonical5857 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw5857 = injectiveMoment H node167 := by
  calc
    injectiveMoment H raw5857 = injectiveMoment H raw5857step0 := by
      have heq : raw5857step0 = -raw5857 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw5857).symm
    injectiveMoment H raw5857step0 = injectiveMoment H raw5857step1 := by
      have heq : raw5857step1 = (fun i j => raw5857step0 (permutation32 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5857step0 permutation32 permutation3
    _ = injectiveMoment H node167 := by rfl

def raw5858 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, -1, 2], ![0, 3, -3], ![1, -1, 0], ![1, 1, -2]]

theorem canonical5858 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5858 = injectiveMoment H node859 := by
  rfl

def raw5859 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, -1, 2], ![0, 3, -3], ![1, 0, -1], ![1, 0, -1]]

theorem canonical5859 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5859 = injectiveMoment H node860 := by
  rfl

def raw5860 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, -1, 2], ![0, 3, -3], ![2, 0, -2]]

def raw5860step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, 1, -2], ![0, -3, 3], ![-2, 0, 2]]

def raw5860step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![1, 1, -2], ![1, 2, -3]]

theorem canonical5860 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw5860 = injectiveMoment H node196 := by
  calc
    injectiveMoment H raw5860 = injectiveMoment H raw5860step0 := by
      have heq : raw5860step0 = -raw5860 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw5860).symm
    injectiveMoment H raw5860step0 = injectiveMoment H raw5860step1 := by
      have heq : raw5860step1 = (fun i j => raw5860step0 (permutation32 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5860step0 permutation32 permutation3
    _ = injectiveMoment H node196 := by rfl

def raw5861 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, -1, 2], ![0, 4, -4], ![1, -1, 0], ![1, 0, -1]]

theorem canonical5861 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5861 = injectiveMoment H node861 := by
  rfl

def raw5862 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, -1, 2], ![0, 4, -4], ![2, -1, -1]]

def raw5862step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, 1, -2], ![0, -4, 4], ![-2, 1, 1]]

def raw5862step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -4, 4], ![1, 1, -2], ![1, 2, -3]]

theorem canonical5862 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw5862 = injectiveMoment H node219 := by
  calc
    injectiveMoment H raw5862 = injectiveMoment H raw5862step0 := by
      have heq : raw5862step0 = -raw5862 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw5862).symm
    injectiveMoment H raw5862step0 = injectiveMoment H raw5862step1 := by
      have heq : raw5862step1 = (fun i j => raw5862step0 (permutation32 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5862step0 permutation32 permutation3
    _ = injectiveMoment H node219 := by rfl

def raw5863 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, -1, 2], ![1, 0, -1], ![1, 3, -4]]

def raw5863step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, 1, -2], ![-1, 0, 1], ![-1, -3, 4]]

def raw5863step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 0, 1], ![1, 1, -2], ![1, 2, -3]]

theorem canonical5863 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw5863 = injectiveMoment H node241 := by
  calc
    injectiveMoment H raw5863 = injectiveMoment H raw5863step0 := by
      have heq : raw5863step0 = -raw5863 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw5863).symm
    injectiveMoment H raw5863step0 = injectiveMoment H raw5863step1 := by
      have heq : raw5863step1 = (fun i j => raw5863step0 (permutation32 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5863step0 permutation32 permutation3
    _ = injectiveMoment H node241 := by rfl

def raw5864 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, -1, 2], ![1, 1, -2], ![1, 2, -3]]

theorem canonical5864 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5864 = injectiveMoment H node258 := by
  rfl

def raw5865 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, -1, 2], ![1, 2, -3], ![1, 1, -2]]

def raw5865step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, -1, 2], ![1, 1, -2], ![1, 2, -3]]

theorem canonical5865 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5865 = injectiveMoment H node258 := by
  calc
    injectiveMoment H raw5865 = injectiveMoment H raw5865step0 := by
      have heq : raw5865step0 = (fun i j => raw5865 (permutation10 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5865 permutation10 permutation3
    _ = injectiveMoment H node258 := by rfl

def raw5866 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, -1, 2], ![1, 3, -4], ![1, 0, -1]]

def raw5866step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, 1, -2], ![-1, -3, 4], ![-1, 0, 1]]

def raw5866step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 0, 1], ![1, 1, -2], ![1, 2, -3]]

theorem canonical5866 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw5866 = injectiveMoment H node241 := by
  calc
    injectiveMoment H raw5866 = injectiveMoment H raw5866step0 := by
      have heq : raw5866step0 = -raw5866 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw5866).symm
    injectiveMoment H raw5866step0 = injectiveMoment H raw5866step1 := by
      have heq : raw5866step1 = (fun i j => raw5866step0 (permutation26 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5866step0 permutation26 permutation3
    _ = injectiveMoment H node241 := by rfl

def raw5867 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 2, -3]]

theorem canonical5867 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5867 = injectiveMoment H node862 := by
  rfl

def raw5868 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]

def raw5868step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]

theorem canonical5868 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5868 = injectiveMoment H node560 := by
  calc
    injectiveMoment H raw5868 = injectiveMoment H raw5868step0 := by
      have heq : raw5868step0 = (fun i j => raw5868 (permutation35 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5868 permutation35 permutation5
    _ = injectiveMoment H node560 := by rfl

def raw5869 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1]]

def raw5869step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, 0, -2]]

theorem canonical5869 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5869 = injectiveMoment H node555 := by
  calc
    injectiveMoment H raw5869 = injectiveMoment H raw5869step0 := by
      have heq : raw5869step0 = (fun i j => raw5869 (permutation36 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5869 permutation36 permutation5
    _ = injectiveMoment H node555 := by rfl

def raw5870 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 0, 1], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1]]

theorem canonical5870 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5870 = injectiveMoment H node864 := by
  rfl

def raw5871 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 0, 1], ![1, 0, -1], ![1, 2, -3]]

def raw5871step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![2, 1, -3]]

theorem canonical5871 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5871 = injectiveMoment H node168 := by
  calc
    injectiveMoment H raw5871 = injectiveMoment H raw5871step0 := by
      have heq : raw5871step0 = (fun i j => raw5871 (permutation9 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5871 permutation9 permutation5
    _ = injectiveMoment H node168 := by rfl

def raw5872 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 0, 1], ![1, 1, -2], ![1, 1, -2]]

def raw5872step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![1, 1, -2], ![1, 1, -2]]

theorem canonical5872 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5872 = injectiveMoment H node175 := by
  calc
    injectiveMoment H raw5872 = injectiveMoment H raw5872step0 := by
      have heq : raw5872step0 = (fun i j => raw5872 (permutation9 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5872 permutation9 permutation5
    _ = injectiveMoment H node175 := by rfl

def raw5873 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

theorem canonical5873 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5873 = injectiveMoment H node868 := by
  rfl

def raw5874 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]

def raw5874step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

theorem canonical5874 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5874 = injectiveMoment H node570 := by
  calc
    injectiveMoment H raw5874 = injectiveMoment H raw5874step0 := by
      have heq : raw5874step0 = (fun i j => raw5874 (permutation49 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5874 permutation49 permutation5
    _ = injectiveMoment H node570 := by rfl

def raw5875 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]

theorem canonical5875 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5875 = injectiveMoment H node869 := by
  rfl

def raw5876 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 1, 0], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0]]

def raw5876step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, -3, 3], ![-1, 1, 0], ![-1, 1, 0]]

def raw5876step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 3, -3], ![1, -3, 2], ![1, 0, -1]]

theorem canonical5876 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw5876 = injectiveMoment H node1287 := by
  calc
    injectiveMoment H raw5876 = injectiveMoment H raw5876step0 := by
      have heq : raw5876step0 = -raw5876 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw5876).symm
    injectiveMoment H raw5876step0 = injectiveMoment H raw5876step1 := by
      have heq : raw5876step1 = (fun i j => raw5876step0 (permutation126 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5876step0 permutation126 permutation4
    _ = injectiveMoment H node1287 := by rfl

def raw5877 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 2, -3]]

theorem canonical5877 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5877 = injectiveMoment H node259 := by
  rfl

def raw5878 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2]]

def raw5878step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

theorem canonical5878 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5878 = injectiveMoment H node181 := by
  calc
    injectiveMoment H raw5878 = injectiveMoment H raw5878step0 := by
      have heq : raw5878step0 = (fun i j => raw5878 (permutation11 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5878 permutation11 permutation5
    _ = injectiveMoment H node181 := by rfl

def raw5879 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2]]

def raw5879step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2]]

theorem canonical5879 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5879 = injectiveMoment H node261 := by
  calc
    injectiveMoment H raw5879 = injectiveMoment H raw5879step0 := by
      have hz : ∀ j, raw5879 (permutation80 0) j = 0 := by decide +kernel
      have heq : raw5879step0 = (fun i j => raw5879 (permutation80 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5879 permutation80 hz
    _ = injectiveMoment H node261 := by rfl

def raw5880 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1]]

def raw5880step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1]]

def raw5880step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]

theorem canonical5880 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5880 = injectiveMoment H node176 := by
  calc
    injectiveMoment H raw5880 = injectiveMoment H raw5880step0 := by
      have hz : ∀ j, raw5880 (permutation80 0) j = 0 := by decide +kernel
      have heq : raw5880step0 = (fun i j => raw5880 (permutation80 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5880 permutation80 hz
    injectiveMoment H raw5880step0 = injectiveMoment H raw5880step1 := by
      have heq : raw5880step1 = (fun i j => raw5880step0 (permutation12 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5880step0 permutation12 permutation5
    _ = injectiveMoment H node176 := by rfl

def raw5881 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]

theorem canonical5881 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5881 = injectiveMoment H node871 := by
  rfl

def raw5882 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

theorem canonical5882 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5882 = injectiveMoment H node872 := by
  rfl

def raw5883 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]

def raw5883step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

theorem canonical5883 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5883 = injectiveMoment H node872 := by
  calc
    injectiveMoment H raw5883 = injectiveMoment H raw5883step0 := by
      have heq : raw5883step0 = (fun i j => raw5883 (permutation34 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5883 permutation34 permutation3
    _ = injectiveMoment H node872 := by rfl

def raw5884 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 2, -1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1]]

theorem canonical5884 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5884 = injectiveMoment H node873 := by
  rfl

def raw5885 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 2, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]

def raw5885step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 3, -2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1]]

theorem canonical5885 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5885 = injectiveMoment H node1143 := by
  calc
    injectiveMoment H raw5885 = injectiveMoment H raw5885step0 := by
      have heq : raw5885step0 = (fun i j => raw5885 (permutation57 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5885 permutation57 permutation4
    _ = injectiveMoment H node1143 := by rfl

def raw5886 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 2, -1], ![0, 2, -2], ![2, -2, 0]]

def raw5886step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -2, 1], ![0, -2, 2], ![-2, 2, 0]]

def raw5886step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![1, -3, 2], ![1, 1, -2]]

theorem canonical5886 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw5886 = injectiveMoment H node212 := by
  calc
    injectiveMoment H raw5886 = injectiveMoment H raw5886step0 := by
      have heq : raw5886step0 = -raw5886 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw5886).symm
    injectiveMoment H raw5886step0 = injectiveMoment H raw5886step1 := by
      have heq : raw5886step1 = (fun i j => raw5886step0 (permutation31 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5886step0 permutation31 permutation4
    _ = injectiveMoment H node212 := by rfl

def raw5887 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 2, -3]]

theorem canonical5887 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5887 = injectiveMoment H node260 := by
  rfl

end MUB6.Certificate.PairSemantics

end OAI
