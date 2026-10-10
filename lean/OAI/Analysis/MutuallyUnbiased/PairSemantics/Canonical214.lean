import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes0
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes4
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes17
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes18
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes29
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes38
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes41

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw6848 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0]]

def raw6848step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0]]

theorem canonical6848 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6848 = injectiveMoment H node287 := by
  calc
    injectiveMoment H raw6848 = injectiveMoment H raw6848step0 := by
      have hz : ∀ j, raw6848 (permutation128 0) j = 0 := by decide +kernel
      have heq : raw6848step0 = (fun i j => raw6848 (permutation128 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw6848 permutation128 hz
    _ = injectiveMoment H node287 := by rfl

def raw6849 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![-1, -1, 2]]

def raw6849step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]

theorem canonical6849 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6849 = injectiveMoment H node2651 := by
  calc
    injectiveMoment H raw6849 = injectiveMoment H raw6849step0 := by
      have heq : raw6849step0 = (fun i j => raw6849 (permutation197 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6849 permutation197 permutation3
    _ = injectiveMoment H node2651 := by rfl

def raw6850 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![0, -2, 2], ![1, 0, -1]]

def raw6850step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1]]

theorem canonical6850 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6850 = injectiveMoment H node1147 := by
  calc
    injectiveMoment H raw6850 = injectiveMoment H raw6850step0 := by
      have heq : raw6850step0 = (fun i j => raw6850 (permutation45 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6850 permutation45 permutation3
    _ = injectiveMoment H node1147 := by rfl

def raw6851 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![0, -1, 1], ![1, -1, 0]]

def raw6851step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0]]

theorem canonical6851 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6851 = injectiveMoment H node1152 := by
  calc
    injectiveMoment H raw6851 = injectiveMoment H raw6851step0 := by
      have heq : raw6851step0 = (fun i j => raw6851 (permutation45 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6851 permutation45 permutation3
    _ = injectiveMoment H node1152 := by rfl

def raw6852 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1]]

theorem canonical6852 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6852 = injectiveMoment H node288 := by
  rfl

def raw6853 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![0, 0, 0]]

def raw6853step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1]]

theorem canonical6853 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6853 = injectiveMoment H node288 := by
  calc
    injectiveMoment H raw6853 = injectiveMoment H raw6853step0 := by
      have hz : ∀ j, raw6853 (permutation128 0) j = 0 := by decide +kernel
      have heq : raw6853step0 = (fun i j => raw6853 (permutation128 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw6853 permutation128 hz
    _ = injectiveMoment H node288 := by rfl

def raw6854 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![0, -1, 1]]

def raw6854step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0]]

theorem canonical6854 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6854 = injectiveMoment H node1152 := by
  calc
    injectiveMoment H raw6854 = injectiveMoment H raw6854step0 := by
      have heq : raw6854step0 = (fun i j => raw6854 (permutation51 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6854 permutation51 permutation3
    _ = injectiveMoment H node1152 := by rfl

def raw6855 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 1, -1], ![1, -2, 1], ![0, 2, -2]]

def raw6855step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1]]

theorem canonical6855 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6855 = injectiveMoment H node288 := by
  calc
    injectiveMoment H raw6855 = injectiveMoment H raw6855step0 := by
      have heq : raw6855step0 = (fun i j => raw6855 (permutation10 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6855 permutation10 permutation3
    _ = injectiveMoment H node288 := by rfl

def raw6856 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![0, 1, -1]]

def raw6856step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0]]

theorem canonical6856 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6856 = injectiveMoment H node287 := by
  calc
    injectiveMoment H raw6856 = injectiveMoment H raw6856step0 := by
      have heq : raw6856step0 = (fun i j => raw6856 (permutation10 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6856 permutation10 permutation3
    _ = injectiveMoment H node287 := by rfl

def raw6857 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![-1, -2, 3], ![0, 3, -3]]

def raw6857step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, -1, 2], ![0, 1, -1], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1]]

theorem canonical6857 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6857 = injectiveMoment H node2457 := by
  calc
    injectiveMoment H raw6857 = injectiveMoment H raw6857step0 := by
      have heq : raw6857step0 = (fun i j => raw6857 (permutation262 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6857 permutation262 permutation3
    _ = injectiveMoment H node2457 := by rfl

def raw6858 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 1, -1], ![1, 0, -1]]

theorem canonical6858 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6858 = injectiveMoment H node61 := by
  rfl

def raw6859 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![-2, 3, -1], ![1, -3, 2]]

def raw6859step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]

theorem canonical6859 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6859 = injectiveMoment H node1867 := by
  calc
    injectiveMoment H raw6859 = injectiveMoment H raw6859step0 := by
      have heq : raw6859step0 = (fun i j => raw6859 (permutation258 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6859 permutation258 permutation4
    _ = injectiveMoment H node1867 := by rfl

def raw6860 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![-1, 3, -2], ![0, -3, 3]]

def raw6860step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 3, -2], ![0, -3, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]

theorem canonical6860 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6860 = injectiveMoment H node2670 := by
  calc
    injectiveMoment H raw6860 = injectiveMoment H raw6860step0 := by
      have heq : raw6860step0 = (fun i j => raw6860 (permutation195 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6860 permutation195 permutation3
    _ = injectiveMoment H node2670 := by rfl

def raw6861 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 2, -2], ![0, -2, 2], ![1, 1, -2]]

def raw6861step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 1, -2]]

theorem canonical6861 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6861 = injectiveMoment H node279 := by
  calc
    injectiveMoment H raw6861 = injectiveMoment H raw6861step0 := by
      have heq : raw6861step0 = (fun i j => raw6861 (permutation11 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6861 permutation11 permutation3
    _ = injectiveMoment H node279 := by rfl

def raw6862 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 2, -2], ![0, -1, 1], ![1, 0, -1]]

def raw6862step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1]]

theorem canonical6862 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6862 = injectiveMoment H node284 := by
  calc
    injectiveMoment H raw6862 = injectiveMoment H raw6862step0 := by
      have heq : raw6862step0 = (fun i j => raw6862 (permutation11 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6862 permutation11 permutation3
    _ = injectiveMoment H node284 := by rfl

def raw6863 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 2, -2], ![0, 1, -1], ![1, -2, 1]]

def raw6863step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1]]

theorem canonical6863 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6863 = injectiveMoment H node288 := by
  calc
    injectiveMoment H raw6863 = injectiveMoment H raw6863step0 := by
      have heq : raw6863step0 = (fun i j => raw6863 (permutation11 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6863 permutation11 permutation3
    _ = injectiveMoment H node288 := by rfl

def raw6864 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 2, -2], ![1, -2, 1], ![0, 1, -1]]

def raw6864step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1]]

theorem canonical6864 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6864 = injectiveMoment H node288 := by
  calc
    injectiveMoment H raw6864 = injectiveMoment H raw6864step0 := by
      have heq : raw6864step0 = (fun i j => raw6864 (permutation13 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6864 permutation13 permutation3
    _ = injectiveMoment H node288 := by rfl

def raw6865 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 2, -2], ![1, -1, 0]]

theorem canonical6865 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6865 = injectiveMoment H node62 := by
  rfl

def raw6866 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 3, -3], ![0, -3, 3], ![1, 1, -2]]

def raw6866step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -3, 3], ![0, 3, -3], ![1, 1, -2]]

theorem canonical6866 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6866 = injectiveMoment H node277 := by
  calc
    injectiveMoment H raw6866 = injectiveMoment H raw6866step0 := by
      have heq : raw6866step0 = (fun i j => raw6866 (permutation11 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6866 permutation11 permutation3
    _ = injectiveMoment H node277 := by rfl

def raw6867 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 3, -3], ![0, -2, 2], ![1, 0, -1]]

def raw6867step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -2, 2], ![0, 3, -3], ![1, 0, -1]]

theorem canonical6867 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6867 = injectiveMoment H node280 := by
  calc
    injectiveMoment H raw6867 = injectiveMoment H raw6867step0 := by
      have heq : raw6867step0 = (fun i j => raw6867 (permutation11 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6867 permutation11 permutation3
    _ = injectiveMoment H node280 := by rfl

def raw6868 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 3, -3], ![0, -1, 1], ![1, -1, 0]]

def raw6868step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0]]

theorem canonical6868 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6868 = injectiveMoment H node285 := by
  calc
    injectiveMoment H raw6868 = injectiveMoment H raw6868step0 := by
      have heq : raw6868step0 = (fun i j => raw6868 (permutation11 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6868 permutation11 permutation3
    _ = injectiveMoment H node285 := by rfl

def raw6869 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 3, -3], ![1, -3, 2], ![0, 1, -1]]

def raw6869step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![0, -3, 3], ![-1, 3, -2], ![0, -1, 1]]

def raw6869step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 1, -1], ![0, 3, -3], ![1, -2, 1]]

theorem canonical6869 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6869 = injectiveMoment H node273 := by
  calc
    injectiveMoment H raw6869 = injectiveMoment H raw6869step0 := by
      have heq : raw6869step0 = -raw6869 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6869).symm
    injectiveMoment H raw6869step0 = injectiveMoment H raw6869step1 := by
      have heq : raw6869step1 = (fun i j => raw6869step0 (permutation26 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6869step0 permutation26 permutation4
    _ = injectiveMoment H node273 := by rfl

def raw6870 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 3, -3], ![1, -2, 1]]

theorem canonical6870 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6870 = injectiveMoment H node63 := by
  rfl

def raw6871 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 3, -3], ![1, -2, 1], ![0, 0, 0]]

def raw6871step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 3, -3], ![1, -2, 1]]

theorem canonical6871 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6871 = injectiveMoment H node63 := by
  calc
    injectiveMoment H raw6871 = injectiveMoment H raw6871step0 := by
      have hz : ∀ j, raw6871 (permutation27 0) j = 0 := by decide +kernel
      have heq : raw6871step0 = (fun i j => raw6871 (permutation27 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw6871 permutation27 hz
    _ = injectiveMoment H node63 := by rfl

def raw6872 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 3, -3], ![1, -1, 0], ![0, -1, 1]]

def raw6872step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0]]

theorem canonical6872 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6872 = injectiveMoment H node285 := by
  calc
    injectiveMoment H raw6872 = injectiveMoment H raw6872step0 := by
      have heq : raw6872step0 = (fun i j => raw6872 (permutation13 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6872 permutation13 permutation3
    _ = injectiveMoment H node285 := by rfl

def raw6873 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 4, -4], ![0, -3, 3], ![1, 0, -1]]

def raw6873step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -3, 3], ![0, 4, -4], ![1, 0, -1]]

theorem canonical6873 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6873 = injectiveMoment H node278 := by
  calc
    injectiveMoment H raw6873 = injectiveMoment H raw6873step0 := by
      have heq : raw6873step0 = (fun i j => raw6873 (permutation11 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6873 permutation11 permutation3
    _ = injectiveMoment H node278 := by rfl

def raw6874 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 4, -4], ![0, -2, 2], ![1, -1, 0]]

def raw6874step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -2, 2], ![0, 4, -4], ![1, -1, 0]]

theorem canonical6874 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6874 = injectiveMoment H node281 := by
  calc
    injectiveMoment H raw6874 = injectiveMoment H raw6874step0 := by
      have heq : raw6874step0 = (fun i j => raw6874 (permutation11 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6874 permutation11 permutation3
    _ = injectiveMoment H node281 := by rfl

def raw6875 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 4, -4], ![1, -3, 2]]

def raw6875step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 1, -2], ![0, -4, 4], ![-1, 3, -2]]

def raw6875step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 4, -4], ![1, -2, 1]]

theorem canonical6875 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6875 = injectiveMoment H node59 := by
  calc
    injectiveMoment H raw6875 = injectiveMoment H raw6875step0 := by
      have heq : raw6875step0 = -raw6875 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6875).symm
    injectiveMoment H raw6875step0 = injectiveMoment H raw6875step1 := by
      have heq : raw6875step1 = (fun i j => raw6875step0 (permutation8 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6875step0 permutation8 permutation4
    _ = injectiveMoment H node59 := by rfl

def raw6876 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 4, -4], ![1, -2, 1], ![0, -1, 1]]

def raw6876step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 4, -4], ![1, -2, 1]]

theorem canonical6876 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6876 = injectiveMoment H node286 := by
  calc
    injectiveMoment H raw6876 = injectiveMoment H raw6876step0 := by
      have heq : raw6876step0 = (fun i j => raw6876 (permutation13 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6876 permutation13 permutation3
    _ = injectiveMoment H node286 := by rfl

def raw6877 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -1, 2], ![1, -3, 2], ![0, 4, -4]]

def raw6877step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 3, -2], ![0, -4, 4]]

def raw6877step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 4, -4], ![1, -2, 1]]

theorem canonical6877 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6877 = injectiveMoment H node59 := by
  calc
    injectiveMoment H raw6877 = injectiveMoment H raw6877step0 := by
      have heq : raw6877step0 = -raw6877 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6877).symm
    injectiveMoment H raw6877step0 = injectiveMoment H raw6877step1 := by
      have heq : raw6877step1 = (fun i j => raw6877step0 (permutation6 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6877step0 permutation6 permutation4
    _ = injectiveMoment H node59 := by rfl

def raw6878 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![1, -2, 1], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2]]

def raw6878step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]

theorem canonical6878 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6878 = injectiveMoment H node1141 := by
  calc
    injectiveMoment H raw6878 = injectiveMoment H raw6878step0 := by
      have heq : raw6878step0 = (fun i j => raw6878 (permutation41 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6878 permutation41 permutation3
    _ = injectiveMoment H node1141 := by rfl

def raw6879 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![1, -2, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1]]

def raw6879step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1]]

theorem canonical6879 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6879 = injectiveMoment H node1153 := by
  calc
    injectiveMoment H raw6879 = injectiveMoment H raw6879step0 := by
      have heq : raw6879step0 = (fun i j => raw6879 (permutation42 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6879 permutation42 permutation3
    _ = injectiveMoment H node1153 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
