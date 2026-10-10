import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes6
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes7
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes9
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes22
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes23
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes29
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes40
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes42
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes43

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw2880 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -2, 2, 0], ![0, 2, -1, -1], ![1, 0, 0, -1], ![1, 0, 1, -2]]

theorem canonical2880 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2880 = injectiveMoment H node1898 := by
  rfl

def raw2881 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -2, 2, 0], ![0, 2, -1, -1], ![2, 0, 1, -3]]

theorem canonical2881 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2881 = injectiveMoment H node576 := by
  rfl

def raw2882 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -2, 2, 0], ![0, 2, 0, -2], ![1, 0, -1, 0], ![1, 0, 1, -2]]

theorem canonical2882 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2882 = injectiveMoment H node1899 := by
  rfl

def raw2883 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -2, 2, 0], ![0, 2, 0, -2], ![2, 0, 0, -2]]

def raw2883step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 2, -2], ![0, 2, -2, 0], ![2, 0, 0, -2]]

theorem canonical2883 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2883 = injectiveMoment H node395 := by
  calc
    injectiveMoment H raw2883 = injectiveMoment H raw2883step0 := by
      have heq : raw2883step0 = (fun i j => raw2883 (permutation11 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2883 permutation11 permutation11
    _ = injectiveMoment H node395 := by rfl

def raw2884 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -2, 2, 0], ![0, 2, 1, -3], ![2, 0, -1, -1]]

theorem canonical2884 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2884 = injectiveMoment H node577 := by
  rfl

def raw2885 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -2, 2, 0], ![1, 0, 1, -2], ![1, 2, -1, -2]]

def raw2885step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 2, -4], ![0, 2, -2, 0], ![-1, 0, -1, 2], ![-1, -2, 1, 2]]

def raw2885step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, -1, 2], ![0, 2, 2, -4], ![2, 0, -2, 0]]

theorem canonical2885 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2885 = injectiveMoment H node499 := by
  calc
    injectiveMoment H raw2885 = injectiveMoment H raw2885step0 := by
      have heq : raw2885step0 = -raw2885 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2885).symm
    injectiveMoment H raw2885step0 = injectiveMoment H raw2885step1 := by
      have heq : raw2885step1 = (fun i j => raw2885step0 (permutation31 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2885step0 permutation31 permutation15
    _ = injectiveMoment H node499 := by rfl

def raw2886 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -2, 2, 0], ![1, 1, -1, -1], ![1, 1, 1, -3]]

theorem canonical2886 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2886 = injectiveMoment H node578 := by
  rfl

def raw2887 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -2, 2, 0], ![1, 1, 0, -2], ![1, 1, 0, -2]]

def raw2887step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -2, 1, 1], ![-2, 2, 0, 0], ![4, 0, -2, -2]]

def raw2887step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 2, -2], ![1, 1, -2, 0], ![1, 1, 0, -2]]

theorem canonical2887 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2887 = injectiveMoment H node397 := by
  calc
    injectiveMoment H raw2887 = injectiveMoment H raw2887step0 := by
      have heq : raw2887step0 = raw2887.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2887).symm
    injectiveMoment H raw2887step0 = injectiveMoment H raw2887step1 := by
      have heq : raw2887step1 = (fun i j => raw2887step0 (permutation32 i) (permutation26 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2887step0 permutation32 permutation26
    _ = injectiveMoment H node397 := by rfl

def raw2888 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -2, 2, 0], ![1, 1, 1, -3], ![1, 1, -1, -1]]

def raw2888step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -2, 2, 0], ![1, 1, -1, -1], ![1, 1, 1, -3]]

theorem canonical2888 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2888 = injectiveMoment H node578 := by
  calc
    injectiveMoment H raw2888 = injectiveMoment H raw2888step0 := by
      have heq : raw2888step0 = (fun i j => raw2888 (permutation10 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2888 permutation10 permutation9
    _ = injectiveMoment H node578 := by rfl

def raw2889 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -2, 2, 0], ![1, 2, -1, -2], ![1, 0, 1, -2]]

def raw2889step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 2, -4], ![0, 2, -2, 0], ![-1, -2, 1, 2], ![-1, 0, -1, 2]]

def raw2889step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, -1, 2], ![0, 2, 2, -4], ![2, 0, -2, 0]]

theorem canonical2889 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2889 = injectiveMoment H node499 := by
  calc
    injectiveMoment H raw2889 = injectiveMoment H raw2889step0 := by
      have heq : raw2889step0 = -raw2889 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2889).symm
    injectiveMoment H raw2889step0 = injectiveMoment H raw2889step1 := by
      have heq : raw2889step1 = (fun i j => raw2889step0 (permutation25 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2889step0 permutation25 permutation15
    _ = injectiveMoment H node499 := by rfl

def raw2890 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -2, 3, -1], ![0, 2, -1, -1], ![2, 0, 0, -2]]

def raw2890step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 2, 0], ![-2, 3, -1, 0], ![4, -1, -1, -2]]

def raw2890step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 3, -2], ![0, 2, -2, 0], ![2, 0, 0, -2]]

theorem canonical2890 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2890 = injectiveMoment H node455 := by
  calc
    injectiveMoment H raw2890 = injectiveMoment H raw2890step0 := by
      have heq : raw2890step0 = raw2890.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2890).symm
    injectiveMoment H raw2890step0 = injectiveMoment H raw2890step1 := by
      have heq : raw2890step1 = (fun i j => raw2890step0 (permutation32 i) (permutation32 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2890step0 permutation32 permutation32
    _ = injectiveMoment H node455 := by rfl

def raw2891 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -2, 3, -1], ![0, 2, 0, -2], ![2, 0, -1, -1]]

def raw2891step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 2, 0], ![-2, 3, 0, -1], ![4, -1, -2, -1]]

def raw2891step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 3, -2], ![0, 2, 0, -2], ![2, 0, -2, 0]]

theorem canonical2891 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2891 = injectiveMoment H node457 := by
  calc
    injectiveMoment H raw2891 = injectiveMoment H raw2891step0 := by
      have heq : raw2891step0 = raw2891.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2891).symm
    injectiveMoment H raw2891step0 = injectiveMoment H raw2891step1 := by
      have heq : raw2891step1 = (fun i j => raw2891step0 (permutation31 i) (permutation26 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2891step0 permutation31 permutation26
    _ = injectiveMoment H node457 := by rfl

def raw2892 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -2, 3, -1], ![1, 1, -1, -1], ![1, 1, 0, -2]]

def raw2892step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -2, 1, 1], ![-2, 3, -1, 0], ![4, -1, -1, -2]]

def raw2892step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 3, -2], ![1, 1, -2, 0], ![1, 1, 0, -2]]

theorem canonical2892 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2892 = injectiveMoment H node458 := by
  calc
    injectiveMoment H raw2892 = injectiveMoment H raw2892step0 := by
      have heq : raw2892step0 = raw2892.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2892).symm
    injectiveMoment H raw2892step0 = injectiveMoment H raw2892step1 := by
      have heq : raw2892step1 = (fun i j => raw2892step0 (permutation32 i) (permutation32 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2892step0 permutation32 permutation32
    _ = injectiveMoment H node458 := by rfl

def raw2893 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -1, 1, 0], ![0, -1, 2, -1], ![0, 2, -1, -1], ![2, 0, 0, -2]]

theorem canonical2893 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2893 = injectiveMoment H node1900 := by
  rfl

def raw2894 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -1, 1, 0], ![0, -1, 2, -1], ![0, 2, 0, -2], ![2, 0, -1, -1]]

theorem canonical2894 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2894 = injectiveMoment H node1901 := by
  rfl

def raw2895 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -1, 1, 0], ![0, -1, 2, -1], ![1, 1, -1, -1], ![1, 1, 0, -2]]

theorem canonical2895 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2895 = injectiveMoment H node1902 := by
  rfl

def raw2896 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -1, 1, 0], ![0, 0, 0, 0], ![0, 1, 1, -2], ![2, 0, 0, -2]]

def raw2896step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 2, -4], ![0, 1, -1, 0], ![0, 0, 0, 0], ![0, -1, -1, 2], ![-2, 0, 0, 2]]

def raw2896step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 2, -4], ![0, 1, -1, 0], ![0, -1, -1, 2], ![-2, 0, 0, 2]]

def raw2896step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 2, 2, -4], ![1, -1, 0, 0]]

theorem canonical2896 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2896 = injectiveMoment H node1037 := by
  calc
    injectiveMoment H raw2896 = injectiveMoment H raw2896step0 := by
      have heq : raw2896step0 = -raw2896 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2896).symm
    injectiveMoment H raw2896step0 = injectiveMoment H raw2896step1 := by
      have hz : ∀ j, raw2896step0 (permutation80 0) j = 0 := by decide +kernel
      have heq : raw2896step1 = (fun i j => raw2896step0 (permutation80 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw2896step0 permutation80 hz
    injectiveMoment H raw2896step1 = injectiveMoment H raw2896step2 := by
      have heq : raw2896step2 = (fun i j => raw2896step1 (permutation25 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2896step1 permutation25 permutation17
    _ = injectiveMoment H node1037 := by rfl

def raw2897 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, 0, 0, -2]]

def raw2897step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 2, -4], ![0, 1, -1, 0], ![0, 0, -1, 1], ![0, -1, 0, 1], ![-2, 0, 0, 2]]

def raw2897step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 0, 2], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, 0, -1, 0]]

theorem canonical2897 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2897 = injectiveMoment H node2739 := by
  calc
    injectiveMoment H raw2897 = injectiveMoment H raw2897step0 := by
      have heq : raw2897step0 = -raw2897 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2897).symm
    injectiveMoment H raw2897step0 = injectiveMoment H raw2897step1 := by
      have heq : raw2897step1 = (fun i j => raw2897step0 (permutation126 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2897step0 permutation126 permutation15
    _ = injectiveMoment H node2739 := by rfl

def raw2898 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, 1, -2], ![2, 0, -1, -1]]

def raw2898step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 2, -4], ![0, 1, -1, 0], ![0, 0, -1, 1], ![0, -1, -1, 2], ![-2, 0, 1, 1]]

def raw2898step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -2, 1, 1], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, 0, -1, 0]]

theorem canonical2898 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2898 = injectiveMoment H node2716 := by
  calc
    injectiveMoment H raw2898 = injectiveMoment H raw2898step0 := by
      have heq : raw2898step0 = -raw2898 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2898).symm
    injectiveMoment H raw2898step0 = injectiveMoment H raw2898step1 := by
      have heq : raw2898step1 = (fun i j => raw2898step0 (permutation126 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2898step0 permutation126 permutation15
    _ = injectiveMoment H node2716 := by rfl

def raw2899 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 2, -1, -1], ![2, -1, 1, -2]]

theorem canonical2899 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2899 = injectiveMoment H node1903 := by
  rfl

def raw2900 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 2, 0, -2], ![2, -1, 0, -1]]

def raw2900step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, 0, -1, -1]]

theorem canonical2900 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2900 = injectiveMoment H node1476 := by
  calc
    injectiveMoment H raw2900 = injectiveMoment H raw2900step0 := by
      have heq : raw2900step0 = (fun i j => raw2900 (permutation45 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2900 permutation45 permutation11
    _ = injectiveMoment H node1476 := by rfl

def raw2901 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![1, 0, 0, -1], ![1, 1, 0, -2]]

def raw2901step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 2, -4], ![0, 1, -1, 0], ![0, 0, -1, 1], ![-1, 0, 0, 1], ![-1, -1, 0, 2]]

def raw2901step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, 0, -1, 0]]

theorem canonical2901 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2901 = injectiveMoment H node2578 := by
  calc
    injectiveMoment H raw2901 = injectiveMoment H raw2901step0 := by
      have heq : raw2901step0 = -raw2901 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2901).symm
    injectiveMoment H raw2901step0 = injectiveMoment H raw2901step1 := by
      have heq : raw2901step1 = (fun i j => raw2901step0 (permutation149 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2901step0 permutation149 permutation15
    _ = injectiveMoment H node2578 := by rfl

def raw2902 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![1, 0, 1, -2], ![1, 1, -1, -1]]

def raw2902step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 2, -4], ![0, 1, -1, 0], ![0, 0, -1, 1], ![-1, 0, -1, 2], ![-1, -1, 1, 1]]

def raw2902step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, -1, 2], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, 0, -1, 0]]

theorem canonical2902 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2902 = injectiveMoment H node2622 := by
  calc
    injectiveMoment H raw2902 = injectiveMoment H raw2902step0 := by
      have heq : raw2902step0 = -raw2902 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2902).symm
    injectiveMoment H raw2902step0 = injectiveMoment H raw2902step1 := by
      have heq : raw2902step1 = (fun i j => raw2902step0 (permutation149 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2902step0 permutation149 permutation15
    _ = injectiveMoment H node2622 := by rfl

def raw2903 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![1, 1, -1, -1], ![1, 0, 1, -2]]

def raw2903step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 2, -4], ![0, 1, -1, 0], ![0, 0, -1, 1], ![-1, -1, 1, 1], ![-1, 0, -1, 2]]

def raw2903step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, -1, 2], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, 0, -1, 0]]

theorem canonical2903 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2903 = injectiveMoment H node2622 := by
  calc
    injectiveMoment H raw2903 = injectiveMoment H raw2903step0 := by
      have heq : raw2903step0 = -raw2903 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2903).symm
    injectiveMoment H raw2903step0 = injectiveMoment H raw2903step1 := by
      have heq : raw2903step1 = (fun i j => raw2903step0 (permutation126 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2903step0 permutation126 permutation15
    _ = injectiveMoment H node2622 := by rfl

def raw2904 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -1, 1, 0], ![0, 1, -1, 0], ![0, 0, 2, -2], ![2, 0, 0, -2]]

def raw2904step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -2, -2, 4], ![0, 0, 2, -2], ![0, 2, 0, -2], ![1, 0, -1, 0]]

theorem canonical2904 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2904 = injectiveMoment H node2802 := by
  calc
    injectiveMoment H raw2904 = injectiveMoment H raw2904step0 := by
      have heq : raw2904step0 = (fun i j => raw2904 (permutation60 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2904 permutation60 permutation15
    _ = injectiveMoment H node2802 := by rfl

def raw2905 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -1, 1, 0], ![0, 1, -1, 0], ![0, 1, 1, -2], ![2, -1, 1, -2]]

theorem canonical2905 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2905 = injectiveMoment H node1904 := by
  rfl

def raw2906 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -1, 1, 0], ![0, 1, 0, -1], ![0, 0, 2, -2], ![2, 0, -1, -1]]

def raw2906step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 2, -4], ![0, 1, -1, 0], ![0, -1, 0, 1], ![0, 0, -2, 2], ![-2, 0, 1, 1]]

def raw2906step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 1, 1], ![0, 0, -2, 2], ![0, 2, 2, -4], ![1, 0, -1, 0]]

theorem canonical2906 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2906 = injectiveMoment H node2741 := by
  calc
    injectiveMoment H raw2906 = injectiveMoment H raw2906step0 := by
      have heq : raw2906step0 = -raw2906 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2906).symm
    injectiveMoment H raw2906step0 = injectiveMoment H raw2906step1 := by
      have heq : raw2906step1 = (fun i j => raw2906step0 (permutation102 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2906step0 permutation102 permutation15
    _ = injectiveMoment H node2741 := by rfl

def raw2907 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -1, 1, 0], ![0, 1, 0, -1], ![0, 1, 1, -2], ![2, -1, 0, -1]]

def raw2907step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![2, 0, -1, -1]]

theorem canonical2907 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2907 = injectiveMoment H node1468 := by
  calc
    injectiveMoment H raw2907 = injectiveMoment H raw2907step0 := by
      have heq : raw2907step0 = (fun i j => raw2907 (permutation39 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2907 permutation39 permutation11
    _ = injectiveMoment H node1468 := by rfl

def raw2908 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -1, 1, 0], ![0, 1, 0, -1], ![1, -1, 2, -2], ![1, 1, -1, -1]]

theorem canonical2908 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2908 = injectiveMoment H node1905 := by
  rfl

def raw2909 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -1, 1, 0], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 0, 1, -2]]

def raw2909step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 2, -4], ![0, 1, -1, 0], ![0, -1, 0, 1], ![-1, 0, 0, 1], ![-1, 0, -1, 2]]

def raw2909step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, -1, 2], ![0, -1, 0, 1], ![0, 2, 2, -4], ![1, 0, -1, 0]]

theorem canonical2909 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2909 = injectiveMoment H node2747 := by
  calc
    injectiveMoment H raw2909 = injectiveMoment H raw2909step0 := by
      have heq : raw2909step0 = -raw2909 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2909).symm
    injectiveMoment H raw2909step0 = injectiveMoment H raw2909step1 := by
      have heq : raw2909step1 = (fun i j => raw2909step0 (permutation102 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2909step0 permutation102 permutation15
    _ = injectiveMoment H node2747 := by rfl

def raw2910 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -1, 1, 0], ![0, 1, 0, -1], ![1, 0, 1, -2], ![1, 0, 0, -1]]

def raw2910step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 2, -4], ![0, 1, -1, 0], ![0, -1, 0, 1], ![-1, 0, -1, 2], ![-1, 0, 0, 1]]

def raw2910step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, -1, 2], ![0, -1, 0, 1], ![0, 2, 2, -4], ![1, 0, -1, 0]]

theorem canonical2910 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2910 = injectiveMoment H node2747 := by
  calc
    injectiveMoment H raw2910 = injectiveMoment H raw2910step0 := by
      have heq : raw2910step0 = -raw2910 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2910).symm
    injectiveMoment H raw2910step0 = injectiveMoment H raw2910step1 := by
      have heq : raw2910step1 = (fun i j => raw2910step0 (permutation96 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2910step0 permutation96 permutation15
    _ = injectiveMoment H node2747 := by rfl

def raw2911 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -1, 1, 0], ![0, 1, 1, -2], ![1, 0, -1, 0], ![1, 0, 1, -2]]

def raw2911step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 2, -4], ![0, 1, -1, 0], ![0, -1, -1, 2], ![-1, 0, 1, 0], ![-1, 0, -1, 2]]

def raw2911step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, -1, 2], ![0, -1, 1, 0], ![0, 2, 2, -4], ![1, 0, -1, 0]]

theorem canonical2911 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2911 = injectiveMoment H node2720 := by
  calc
    injectiveMoment H raw2911 = injectiveMoment H raw2911step0 := by
      have heq : raw2911step0 = -raw2911 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2911).symm
    injectiveMoment H raw2911step0 = injectiveMoment H raw2911step1 := by
      have heq : raw2911step1 = (fun i j => raw2911step0 (permutation102 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2911step0 permutation102 permutation15
    _ = injectiveMoment H node2720 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
