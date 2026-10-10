import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes38
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes44
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes45
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes46
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes47
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes48
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes49
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes50
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes51
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes52
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes53

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw9856 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-1, -1, -2, 4], ![-1, 2, 1, -2]]

def raw9856step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![-1, 1, 0, 0], ![-1, 0, 1, 0], ![1, 1, 2, -4], ![1, -2, -1, 2]]

def raw9856step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, 1, 2, -4]]

theorem canonical9856 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9856 = injectiveMoment H node3245 := by
  calc
    injectiveMoment H raw9856 = injectiveMoment H raw9856step0 := by
      have heq : raw9856step0 = -raw9856 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9856).symm
    injectiveMoment H raw9856step0 = injectiveMoment H raw9856step1 := by
      have heq : raw9856step1 = (fun i j => raw9856step0 (permutation373 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9856step0 permutation373 permutation15
    _ = injectiveMoment H node3245 := by rfl

def raw9857 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-1, -1, -1, 3], ![-1, 2, 0, -1]]

def raw9857step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![-1, 1, 0, 0], ![-1, 0, 1, 0], ![1, 1, 1, -3], ![1, -2, 0, 1]]

def raw9857step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 0, 1], ![0, -1, 0, 1], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 1, 1, -3]]

theorem canonical9857 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9857 = injectiveMoment H node3197 := by
  calc
    injectiveMoment H raw9857 = injectiveMoment H raw9857step0 := by
      have heq : raw9857step0 = -raw9857 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9857).symm
    injectiveMoment H raw9857step0 = injectiveMoment H raw9857step1 := by
      have heq : raw9857step1 = (fun i j => raw9857step0 (permutation310 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9857step0 permutation310 permutation17
    _ = injectiveMoment H node3197 := by rfl

def raw9858 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-1, 2, 0, -1], ![-1, -1, -1, 3]]

def raw9858step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![-1, 1, 0, 0], ![-1, 0, 1, 0], ![1, -2, 0, 1], ![1, 1, 1, -3]]

def raw9858step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 0, 1], ![0, -1, 0, 1], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 1, 1, -3]]

theorem canonical9858 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9858 = injectiveMoment H node3197 := by
  calc
    injectiveMoment H raw9858 = injectiveMoment H raw9858step0 := by
      have heq : raw9858step0 = -raw9858 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9858).symm
    injectiveMoment H raw9858step0 = injectiveMoment H raw9858step1 := by
      have heq : raw9858step1 = (fun i j => raw9858step0 (permutation260 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9858step0 permutation260 permutation17
    _ = injectiveMoment H node3197 := by rfl

def raw9859 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![0, 2, -1, -1], ![-2, -1, 0, 3]]

def raw9859step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, -1, 0, 0], ![1, 0, -1, 0]]

theorem canonical9859 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9859 = injectiveMoment H node3004 := by
  calc
    injectiveMoment H raw9859 = injectiveMoment H raw9859step0 := by
      have heq : raw9859step0 = (fun i j => raw9859 (permutation312 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9859 permutation312 permutation9
    _ = injectiveMoment H node3004 := by rfl

def raw9860 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![0, 2, 0, -2], ![-2, -1, -1, 4]]

def raw9860step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -1, 0, 0], ![1, 0, -1, 0]]

theorem canonical9860 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9860 = injectiveMoment H node2935 := by
  calc
    injectiveMoment H raw9860 = injectiveMoment H raw9860step0 := by
      have heq : raw9860step0 = (fun i j => raw9860 (permutation312 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9860 permutation312 permutation9
    _ = injectiveMoment H node2935 := by rfl

def raw9861 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-1, 2, -1, 0], ![-1, -1, -1, 3]]

def raw9861step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![-1, 1, 0, 0], ![-1, 0, 0, 1], ![1, -2, 1, 0], ![1, 1, 1, -3]]

def raw9861step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, -1, 0, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![1, 0, -1, 0], ![1, 1, 1, -3]]

theorem canonical9861 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9861 = injectiveMoment H node3301 := by
  calc
    injectiveMoment H raw9861 = injectiveMoment H raw9861step0 := by
      have heq : raw9861step0 = -raw9861 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9861).symm
    injectiveMoment H raw9861step0 = injectiveMoment H raw9861step1 := by
      have heq : raw9861step1 = (fun i j => raw9861step0 (permutation260 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9861step0 permutation260 permutation17
    _ = injectiveMoment H node3301 := by rfl

def raw9862 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-1, 2, 0, -1], ![-1, -1, -2, 4]]

def raw9862step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, 0, 0, -1], ![1, 0, 0, -1]]

theorem canonical9862 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9862 = injectiveMoment H node2918 := by
  calc
    injectiveMoment H raw9862 = injectiveMoment H raw9862step0 := by
      have heq : raw9862step0 = (fun i j => raw9862 (permutation366 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9862 permutation366 permutation23
    _ = injectiveMoment H node2918 := by rfl

def raw9863 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![0, 2, -2, 0], ![-2, -1, 0, 3]]

def raw9863step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, -1, 0, 0], ![1, 0, 0, -1]]

theorem canonical9863 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9863 = injectiveMoment H node3002 := by
  calc
    injectiveMoment H raw9863 = injectiveMoment H raw9863step0 := by
      have heq : raw9863step0 = (fun i j => raw9863 (permutation312 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9863 permutation312 permutation9
    _ = injectiveMoment H node3002 := by rfl

def raw9864 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![0, 2, -1, -1], ![-2, -1, -1, 4]]

def raw9864step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 2, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 0, -1]]

theorem canonical9864 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9864 = injectiveMoment H node2922 := by
  calc
    injectiveMoment H raw9864 = injectiveMoment H raw9864step0 := by
      have heq : raw9864step0 = (fun i j => raw9864 (permutation395 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9864 permutation395 permutation11
    _ = injectiveMoment H node2922 := by rfl

def raw9865 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![0, 2, 0, -2], ![-2, -1, -2, 5]]

def raw9865step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 0, 0, -1]]

theorem canonical9865 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9865 = injectiveMoment H node2868 := by
  calc
    injectiveMoment H raw9865 = injectiveMoment H raw9865step0 := by
      have heq : raw9865step0 = (fun i j => raw9865 (permutation404 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9865 permutation404 permutation21
    _ = injectiveMoment H node2868 := by rfl

def raw9866 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, -2, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![-2, -1, 0, 3], ![1, 0, 2, -3]]

def raw9866step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 1, -2, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 2, -3]]

theorem canonical9866 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9866 = injectiveMoment H node3007 := by
  calc
    injectiveMoment H raw9866 = injectiveMoment H raw9866step0 := by
      have heq : raw9866step0 = (fun i j => raw9866 (permutation258 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9866 permutation258 permutation9
    _ = injectiveMoment H node3007 := by rfl

def raw9867 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![-2, 0, -1, 3], ![1, -1, 2, -2]]

def raw9867step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 1, -1], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, -1, 2, -2]]

theorem canonical9867 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9867 = injectiveMoment H node3139 := by
  calc
    injectiveMoment H raw9867 = injectiveMoment H raw9867step0 := by
      have heq : raw9867step0 = (fun i j => raw9867 (permutation258 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9867 permutation258 permutation9
    _ = injectiveMoment H node3139 := by rfl

def raw9868 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-2, 0, 1, 1]]

def raw9868step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, -1, 0, 0]]

theorem canonical9868 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9868 = injectiveMoment H node3217 := by
  calc
    injectiveMoment H raw9868 = injectiveMoment H raw9868step0 := by
      have heq : raw9868step0 = (fun i j => raw9868 (permutation314 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9868 permutation314 permutation10
    _ = injectiveMoment H node3217 := by rfl

def raw9869 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-2, -1, 1, 2]]

def raw9869step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1]]

theorem canonical9869 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9869 = injectiveMoment H node3079 := by
  calc
    injectiveMoment H raw9869 = injectiveMoment H raw9869step0 := by
      have heq : raw9869step0 = (fun i j => raw9869 (permutation308 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9869 permutation308 permutation9
    _ = injectiveMoment H node3079 := by rfl

def raw9870 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, -2, 1], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-2, 0, -1, 3], ![0, 1, 2, -3]]

def raw9870step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 1, -1], ![0, 1, -2, 1], ![0, 1, 2, -3], ![1, -1, 0, 0], ![1, -1, 0, 0]]

theorem canonical9870 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9870 = injectiveMoment H node3140 := by
  calc
    injectiveMoment H raw9870 = injectiveMoment H raw9870step0 := by
      have heq : raw9870step0 = (fun i j => raw9870 (permutation262 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9870 permutation262 permutation9
    _ = injectiveMoment H node3140 := by rfl

def raw9871 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, -2, 1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-2, -1, 0, 3], ![0, 1, 2, -3]]

def raw9871step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 1, -2, 1], ![0, 1, 2, -3], ![1, -1, 0, 0], ![1, 0, -1, 0]]

theorem canonical9871 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9871 = injectiveMoment H node3009 := by
  calc
    injectiveMoment H raw9871 = injectiveMoment H raw9871step0 := by
      have heq : raw9871step0 = (fun i j => raw9871 (permutation262 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9871 permutation262 permutation9
    _ = injectiveMoment H node3009 := by rfl

def raw9872 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, -2, 1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-1, -1, -1, 3], ![-1, 1, 2, -2]]

def raw9872step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 1, 0, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 2, -2], ![1, 0, -2, 1]]

theorem canonical9872 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9872 = injectiveMoment H node3369 := by
  calc
    injectiveMoment H raw9872 = injectiveMoment H raw9872step0 := by
      have heq : raw9872step0 = (fun i j => raw9872 (permutation285 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9872 permutation285 permutation15
    _ = injectiveMoment H node3369 := by rfl

def raw9873 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 0, 0, 0], ![1, 0, -1, 0], ![1, 0, 0, -1], ![-2, -1, 1, 2]]

def raw9873step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 0, 0, -1], ![-2, -1, 1, 2]]

def raw9873step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0]]

theorem canonical9873 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9873 = injectiveMoment H node2449 := by
  calc
    injectiveMoment H raw9873 = injectiveMoment H raw9873step0 := by
      have hz : ∀ j, raw9873 (permutation221 0) j = 0 := by decide +kernel
      have heq : raw9873step0 = (fun i j => raw9873 (permutation221 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9873 permutation221 hz
    injectiveMoment H raw9873step0 = injectiveMoment H raw9873step1 := by
      have heq : raw9873step1 = (fun i j => raw9873step0 (permutation131 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9873step0 permutation131 permutation15
    _ = injectiveMoment H node2449 := by rfl

def raw9874 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -2, 1], ![1, -1, 0, 0], ![-2, -1, 0, 3], ![1, 0, 2, -3]]

def raw9874step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 1, -2, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 2, -3]]

theorem canonical9874 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9874 = injectiveMoment H node3007 := by
  calc
    injectiveMoment H raw9874 = injectiveMoment H raw9874step0 := by
      have heq : raw9874step0 = (fun i j => raw9874 (permutation264 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9874 permutation264 permutation9
    _ = injectiveMoment H node3007 := by rfl

def raw9875 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, -1, 1], ![-2, -1, 0, 3], ![1, 0, 2, -3]]

def raw9875step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, 0, 2, -3]]

theorem canonical9875 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9875 = injectiveMoment H node3010 := by
  calc
    injectiveMoment H raw9875 = injectiveMoment H raw9875step0 := by
      have heq : raw9875step0 = (fun i j => raw9875 (permutation258 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9875 permutation258 permutation9
    _ = injectiveMoment H node3010 := by rfl

def raw9876 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 0, 0], ![-2, -1, -1, 4], ![1, 0, 2, -3]]

def raw9876step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 2, -3]]

theorem canonical9876 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9876 = injectiveMoment H node2936 := by
  calc
    injectiveMoment H raw9876 = injectiveMoment H raw9876step0 := by
      have heq : raw9876step0 = (fun i j => raw9876 (permutation258 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9876 permutation258 permutation9
    _ = injectiveMoment H node2936 := by rfl

def raw9877 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 0, 0], ![-2, -1, 0, 3], ![1, 0, 1, -2]]

def raw9877step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 1, -2]]

theorem canonical9877 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9877 = injectiveMoment H node3011 := by
  calc
    injectiveMoment H raw9877 = injectiveMoment H raw9877step0 := by
      have heq : raw9877step0 = (fun i j => raw9877 (permutation258 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9877 permutation258 permutation9
    _ = injectiveMoment H node3011 := by rfl

def raw9878 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 0, 0], ![-2, 0, -1, 3], ![1, -1, 2, -2]]

def raw9878step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, -1, 2, -2]]

theorem canonical9878 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9878 = injectiveMoment H node3143 := by
  calc
    injectiveMoment H raw9878 = injectiveMoment H raw9878step0 := by
      have heq : raw9878step0 = (fun i j => raw9878 (permutation258 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9878 permutation258 permutation9
    _ = injectiveMoment H node3143 := by rfl

def raw9879 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-2, 0, 1, 1]]

def raw9879step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, -1, 1, 0], ![0, -1, 1, 0], ![-1, 1, 0, 0], ![-1, 1, 0, 0], ![2, 0, -1, -1]]

def raw9879step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 0, 0]]

theorem canonical9879 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9879 = injectiveMoment H node3397 := by
  calc
    injectiveMoment H raw9879 = injectiveMoment H raw9879step0 := by
      have heq : raw9879step0 = -raw9879 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9879).symm
    injectiveMoment H raw9879step0 = injectiveMoment H raw9879step1 := by
      have heq : raw9879step1 = (fun i j => raw9879step0 (permutation392 i) (permutation32 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9879step0 permutation392 permutation32
    _ = injectiveMoment H node3397 := by rfl

def raw9880 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-2, -1, 1, 2]]

def raw9880step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 0, -1]]

theorem canonical9880 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9880 = injectiveMoment H node3081 := by
  calc
    injectiveMoment H raw9880 = injectiveMoment H raw9880step0 := by
      have heq : raw9880step0 = (fun i j => raw9880 (permutation308 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9880 permutation308 permutation9
    _ = injectiveMoment H node3081 := by rfl

def raw9881 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, -1, 1], ![-2, 0, -1, 3], ![1, -1, 2, -2]]

def raw9881step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, -1, 2, -2]]

theorem canonical9881 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9881 = injectiveMoment H node3145 := by
  calc
    injectiveMoment H raw9881 = injectiveMoment H raw9881step0 := by
      have heq : raw9881step0 = (fun i j => raw9881 (permutation258 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9881 permutation258 permutation9
    _ = injectiveMoment H node3145 := by rfl

def raw9882 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, -1, 0, 0], ![-2, 0, 1, 1]]

def raw9882step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, -1, 1, -1]]

theorem canonical9882 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9882 = injectiveMoment H node3216 := by
  calc
    injectiveMoment H raw9882 = injectiveMoment H raw9882step0 := by
      have heq : raw9882step0 = (fun i j => raw9882 (permutation315 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9882 permutation315 permutation10
    _ = injectiveMoment H node3216 := by rfl

def raw9883 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 0, 0, -1], ![-2, -1, 1, 2]]

def raw9883step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 0, 0, -1]]

theorem canonical9883 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9883 = injectiveMoment H node3082 := by
  calc
    injectiveMoment H raw9883 = injectiveMoment H raw9883step0 := by
      have heq : raw9883step0 = (fun i j => raw9883 (permutation308 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9883 permutation308 permutation9
    _ = injectiveMoment H node3082 := by rfl

def raw9884 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 0, 0], ![-2, 0, -2, 4], ![1, -1, 2, -2]]

def raw9884step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, -1, 2, -2]]

theorem canonical9884 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9884 = injectiveMoment H node3122 := by
  calc
    injectiveMoment H raw9884 = injectiveMoment H raw9884step0 := by
      have heq : raw9884step0 = (fun i j => raw9884 (permutation258 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9884 permutation258 permutation9
    _ = injectiveMoment H node3122 := by rfl

def raw9885 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 0, 0], ![-2, 0, -1, 3], ![1, -1, 1, -1]]

def raw9885step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 1, -1, -1]]

theorem canonical9885 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9885 = injectiveMoment H node2967 := by
  calc
    injectiveMoment H raw9885 = injectiveMoment H raw9885step0 := by
      have heq : raw9885step0 = (fun i j => raw9885 (permutation280 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9885 permutation280 permutation11
    _ = injectiveMoment H node2967 := by rfl

def raw9886 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, -1, -1, 1], ![-2, 0, 1, 1]]

def raw9886step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, -1, 1, -1]]

theorem canonical9886 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9886 = injectiveMoment H node3216 := by
  calc
    injectiveMoment H raw9886 = injectiveMoment H raw9886step0 := by
      have heq : raw9886step0 = (fun i j => raw9886 (permutation314 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9886 permutation314 permutation10
    _ = injectiveMoment H node3216 := by rfl

def raw9887 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-2, 0, 0, 2]]

def raw9887step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 2, 0], ![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -1, 0]]

theorem canonical9887 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9887 = injectiveMoment H node3437 := by
  calc
    injectiveMoment H raw9887 = injectiveMoment H raw9887step0 := by
      have heq : raw9887step0 = (fun i j => raw9887 (permutation219 i) (permutation22 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9887 permutation219 permutation22
    _ = injectiveMoment H node3437 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
