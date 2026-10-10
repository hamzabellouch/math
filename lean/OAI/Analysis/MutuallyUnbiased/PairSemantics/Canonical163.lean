import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes0
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes6
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes9
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes10
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes11
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes12
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes14
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes15
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes18
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes19
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes23
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes31
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes36

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw5216 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![2, -2], ![0, 0], ![0, 0], ![0, 0]]

def raw5216step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![2, -2], ![0, 0], ![0, 0]]

def raw5216step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![2, -2], ![0, 0]]

def raw5216step2 : Matrix (Fin 2) (Fin 2) ℤ := ![![-2, 2], ![2, -2]]

theorem canonical5216 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5216 = injectiveMoment H node4 := by
  calc
    injectiveMoment H raw5216 = injectiveMoment H raw5216step0 := by
      have hz : ∀ j, raw5216 (permutation128 0) j = 0 := by decide +kernel
      have heq : raw5216step0 = (fun i j => raw5216 (permutation128 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5216 permutation128 hz
    injectiveMoment H raw5216step0 = injectiveMoment H raw5216step1 := by
      have hz : ∀ j, raw5216step0 (permutation27 0) j = 0 := by decide +kernel
      have heq : raw5216step1 = (fun i j => raw5216step0 (permutation27 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5216step0 permutation27 hz
    injectiveMoment H raw5216step1 = injectiveMoment H raw5216step2 := by
      have hz : ∀ j, raw5216step1 (permutation7 0) j = 0 := by decide +kernel
      have heq : raw5216step2 = (fun i j => raw5216step1 (permutation7 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5216step1 permutation7 hz
    _ = injectiveMoment H node4 := by rfl

def raw5217 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![2, -2], ![1, -1], ![0, 0], ![-1, 1]]

def raw5217step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![2, -2], ![1, -1], ![-1, 1]]

def raw5217step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

theorem canonical5217 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5217 = injectiveMoment H node46 := by
  calc
    injectiveMoment H raw5217 = injectiveMoment H raw5217step0 := by
      have hz : ∀ j, raw5217 (permutation104 0) j = 0 := by decide +kernel
      have heq : raw5217step0 = (fun i j => raw5217 (permutation104 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5217 permutation104 hz
    injectiveMoment H raw5217step0 = injectiveMoment H raw5217step1 := by
      have heq : raw5217step1 = (fun i j => raw5217step0 (permutation14 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5217step0 permutation14 permutation1
    _ = injectiveMoment H node46 := by rfl

def raw5218 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![3, -3], ![-1, 1]]

def raw5218step0 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]

theorem canonical5218 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5218 = injectiveMoment H node10 := by
  calc
    injectiveMoment H raw5218 = injectiveMoment H raw5218step0 := by
      have heq : raw5218step0 = (fun i j => raw5218 (permutation6 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5218 permutation6 permutation2
    _ = injectiveMoment H node10 := by rfl

def raw5219 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, -3, 3], ![0, -1, 2, -1], ![1, -1, 0, 0], ![1, 0, 1, -2]]

def raw5219step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![2, -1, -1, 0], ![-3, 2, 0, 1], ![3, -1, 0, -2]]

def raw5219step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, -2, 3], ![0, 2, 1, -3], ![1, 0, 1, -2]]

theorem canonical5219 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5219 = injectiveMoment H node993 := by
  calc
    injectiveMoment H raw5219 = injectiveMoment H raw5219step0 := by
      have heq : raw5219step0 = raw5219.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5219).symm
    injectiveMoment H raw5219step0 = injectiveMoment H raw5219step1 := by
      have heq : raw5219step1 = (fun i j => raw5219step0 (permutation20 i) (permutation24 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5219step0 permutation20 permutation24
    _ = injectiveMoment H node993 := by rfl

def raw5220 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, -3, 3], ![0, -1, 2, -1], ![1, -1, 1, -1], ![1, 0, 0, -1]]

def raw5220step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![2, -1, -1, 0], ![-3, 2, 1, 0], ![3, -1, -1, -1]]

def raw5220step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, -1, 2], ![0, 1, 2, -3], ![1, 1, 0, -2]]

theorem canonical5220 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5220 = injectiveMoment H node931 := by
  calc
    injectiveMoment H raw5220 = injectiveMoment H raw5220step0 := by
      have heq : raw5220step0 = raw5220.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5220).symm
    injectiveMoment H raw5220step0 = injectiveMoment H raw5220step1 := by
      have heq : raw5220step1 = (fun i j => raw5220step0 (permutation30 i) (permutation32 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5220step0 permutation30 permutation32
    _ = injectiveMoment H node931 := by rfl

def raw5221 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, -3, 3], ![0, -1, 3, -2], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw5221step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![2, -1, -1, 0], ![-3, 3, 0, 0], ![3, -2, 0, -1]]

def raw5221step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-2, 1, 1, 0], ![3, -3, 0, 0], ![-3, 2, 0, 1]]

def raw5221step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -3, 3], ![0, 1, 1, -2], ![1, 0, 2, -3]]

theorem canonical5221 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw5221 = injectiveMoment H node1024 := by
  calc
    injectiveMoment H raw5221 = injectiveMoment H raw5221step0 := by
      have heq : raw5221step0 = raw5221.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5221).symm
    injectiveMoment H raw5221step0 = injectiveMoment H raw5221step1 := by
      have heq : raw5221step1 = -raw5221step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw5221step0).symm
    injectiveMoment H raw5221step1 = injectiveMoment H raw5221step2 := by
      have heq : raw5221step2 = (fun i j => raw5221step1 (permutation11 i) (permutation32 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5221step1 permutation11 permutation32
    _ = injectiveMoment H node1024 := by rfl

def raw5222 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, -3, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, -1, 1, -1]]

theorem canonical5222 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5222 = injectiveMoment H node2329 := by
  rfl

def raw5223 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, -3, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![2, -2, 1, -1]]

def raw5223step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![2, 0, 0, -2], ![-3, 1, 1, 1], ![3, -1, -1, -1]]

def raw5223step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, -2, 2], ![0, 0, 2, -2], ![1, 1, 1, -3]]

theorem canonical5223 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5223 = injectiveMoment H node955 := by
  calc
    injectiveMoment H raw5223 = injectiveMoment H raw5223step0 := by
      have heq : raw5223step0 = raw5223.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5223).symm
    injectiveMoment H raw5223step0 = injectiveMoment H raw5223step1 := by
      have heq : raw5223step1 = (fun i j => raw5223step0 (permutation29 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5223step0 permutation29 permutation18
    _ = injectiveMoment H node955 := by rfl

def raw5224 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, -3, 3], ![0, 0, 1, -1], ![0, 0, 2, -2], ![1, -1, 0, 0], ![1, -1, 0, 0]]

theorem canonical5224 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5224 = injectiveMoment H node2330 := by
  rfl

def raw5225 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, -3, 3], ![0, 0, 1, -1], ![0, 0, 2, -2], ![2, -2, 0, 0]]

def raw5225step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![2, 0, 0, -2], ![-3, 1, 2, 0], ![3, -1, -2, 0]]

def raw5225step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, -2, 2], ![0, 0, 2, -2], ![1, 2, 0, -3]]

theorem canonical5225 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5225 = injectiveMoment H node789 := by
  calc
    injectiveMoment H raw5225 = injectiveMoment H raw5225step0 := by
      have heq : raw5225step0 = raw5225.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5225).symm
    injectiveMoment H raw5225step0 = injectiveMoment H raw5225step1 := by
      have heq : raw5225step1 = (fun i j => raw5225step0 (permutation29 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5225step0 permutation29 permutation18
    _ = injectiveMoment H node789 := by rfl

def raw5226 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, -3, 3], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, -1, 2, -2]]

def raw5226step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![2, 0, -1, -1], ![-3, 1, 0, 2], ![3, -1, 0, -2]]

def raw5226step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, -1, 2], ![0, 1, 1, -2], ![1, 0, 2, -3]]

theorem canonical5226 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5226 = injectiveMoment H node1195 := by
  calc
    injectiveMoment H raw5226 = injectiveMoment H raw5226step0 := by
      have heq : raw5226step0 = raw5226.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5226).symm
    injectiveMoment H raw5226step0 = injectiveMoment H raw5226step1 := by
      have heq : raw5226step1 = (fun i j => raw5226step0 (permutation29 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5226step0 permutation29 permutation18
    _ = injectiveMoment H node1195 := by rfl

def raw5227 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, -3, 3], ![0, 0, 1, -1], ![1, -1, 1, -1], ![1, -1, 1, -1]]

def raw5227step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![2, 0, -1, -1], ![-3, 1, 1, 1], ![3, -1, -1, -1]]

def raw5227step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, -1, 2], ![0, 1, 1, -2], ![1, 1, 1, -3]]

theorem canonical5227 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5227 = injectiveMoment H node930 := by
  calc
    injectiveMoment H raw5227 = injectiveMoment H raw5227step0 := by
      have heq : raw5227step0 = raw5227.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5227).symm
    injectiveMoment H raw5227step0 = injectiveMoment H raw5227step1 := by
      have heq : raw5227step1 = (fun i j => raw5227step0 (permutation29 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5227step0 permutation29 permutation18
    _ = injectiveMoment H node930 := by rfl

def raw5228 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, -3, 3], ![0, 0, 2, -2], ![1, -2, 0, 1], ![1, 0, 1, -2]]

def raw5228step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![2, 0, -2, 0], ![-3, 2, 0, 1], ![3, -2, 1, -2]]

def raw5228step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, -2, 2], ![0, 1, 1, -2], ![2, 1, 0, -3]]

theorem canonical5228 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5228 = injectiveMoment H node405 := by
  calc
    injectiveMoment H raw5228 = injectiveMoment H raw5228step0 := by
      have heq : raw5228step0 = raw5228.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5228).symm
    injectiveMoment H raw5228step0 = injectiveMoment H raw5228step1 := by
      have heq : raw5228step1 = (fun i j => raw5228step0 (permutation29 i) (permutation20 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5228step0 permutation29 permutation20
    _ = injectiveMoment H node405 := by rfl

def raw5229 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, -3, 3], ![0, 0, 2, -2], ![1, -2, 1, 0], ![1, 0, 0, -1]]

def raw5229step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![2, 0, -2, 0], ![-3, 2, 1, 0], ![3, -2, 0, -1]]

def raw5229step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, -2, 2], ![0, 2, 1, -3], ![1, 0, 1, -2]]

theorem canonical5229 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5229 = injectiveMoment H node794 := by
  calc
    injectiveMoment H raw5229 = injectiveMoment H raw5229step0 := by
      have heq : raw5229step0 = raw5229.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5229).symm
    injectiveMoment H raw5229step0 = injectiveMoment H raw5229step1 := by
      have heq : raw5229step1 = (fun i j => raw5229step0 (permutation30 i) (permutation30 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5229step0 permutation30 permutation30
    _ = injectiveMoment H node794 := by rfl

def raw5230 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, -3, 3], ![0, 0, 2, -2], ![1, -1, 0, 0], ![1, -1, 1, -1]]

def raw5230step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![2, 0, -1, -1], ![-3, 2, 0, 1], ![3, -2, 0, -1]]

def raw5230step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, -2, 3], ![0, 1, 2, -3], ![1, 1, 0, -2]]

theorem canonical5230 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5230 = injectiveMoment H node991 := by
  calc
    injectiveMoment H raw5230 = injectiveMoment H raw5230step0 := by
      have heq : raw5230step0 = raw5230.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5230).symm
    injectiveMoment H raw5230step0 = injectiveMoment H raw5230step1 := by
      have heq : raw5230step1 = (fun i j => raw5230step0 (permutation20 i) (permutation26 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5230step0 permutation20 permutation26
    _ = injectiveMoment H node991 := by rfl

def raw5231 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, -3, 3], ![0, 0, 2, -2], ![1, -1, 1, -1], ![1, -1, 0, 0]]

def raw5231step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![2, 0, -1, -1], ![-3, 2, 1, 0], ![3, -2, -1, 0]]

def raw5231step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, -2, 3], ![0, 1, 2, -3], ![1, 1, 0, -2]]

theorem canonical5231 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5231 = injectiveMoment H node991 := by
  calc
    injectiveMoment H raw5231 = injectiveMoment H raw5231step0 := by
      have heq : raw5231step0 = raw5231.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5231).symm
    injectiveMoment H raw5231step0 = injectiveMoment H raw5231step1 := by
      have heq : raw5231step1 = (fun i j => raw5231step0 (permutation20 i) (permutation32 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5231step0 permutation20 permutation32
    _ = injectiveMoment H node991 := by rfl

def raw5232 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, -3, 3], ![0, 0, 3, -3], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def raw5232step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![2, 0, -1, -1], ![-3, 3, 0, 0], ![3, -3, 0, 0]]

def raw5232step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -3, 3], ![0, 0, 3, -3], ![1, 1, 0, -2]]

theorem canonical5232 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5232 = injectiveMoment H node1021 := by
  calc
    injectiveMoment H raw5232 = injectiveMoment H raw5232step0 := by
      have heq : raw5232step0 = raw5232.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5232).symm
    injectiveMoment H raw5232step0 = injectiveMoment H raw5232step1 := by
      have heq : raw5232step1 = (fun i j => raw5232step0 (permutation20 i) (permutation26 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5232step0 permutation20 permutation26
    _ = injectiveMoment H node1021 := by rfl

def raw5233 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, -2, 2], ![0, -2, 2, 0], ![0, 0, -1, 1], ![1, 0, 0, -1], ![1, 0, 1, -2]]

def raw5233step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, 1, -1], ![0, 1, -2, 1], ![0, 1, -1, 0], ![2, -2, 2, -2]]

theorem canonical5233 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5233 = injectiveMoment H node2035 := by
  calc
    injectiveMoment H raw5233 = injectiveMoment H raw5233step0 := by
      have heq : raw5233step0 = (fun i j => raw5233 (permutation67 i) (permutation16 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5233 permutation67 permutation16
    _ = injectiveMoment H node2035 := by rfl

def raw5234 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, -2, 2], ![0, -1, -1, 2], ![0, -1, 2, -1], ![1, 0, 0, -1], ![1, 0, 1, -2]]

theorem canonical5234 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5234 = injectiveMoment H node2331 := by
  rfl

def raw5235 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, -2, 2], ![0, -1, -1, 2], ![0, -1, 2, -1], ![1, 0, 1, -2], ![1, 0, 0, -1]]

def raw5235step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, -2, 2], ![0, -1, -1, 2], ![0, -1, 2, -1], ![1, 0, 0, -1], ![1, 0, 1, -2]]

theorem canonical5235 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5235 = injectiveMoment H node2331 := by
  calc
    injectiveMoment H raw5235 = injectiveMoment H raw5235step0 := by
      have heq : raw5235step0 = (fun i j => raw5235 (permutation34 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5235 permutation34 permutation9
    _ = injectiveMoment H node2331 := by rfl

def raw5236 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, -2, 2], ![0, -1, -1, 2], ![0, -1, 2, -1], ![2, 0, 1, -3]]

def raw5236step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, -2, 2, -2], ![0, 1, 1, -2], ![0, 1, -2, 1], ![-2, 0, -1, 3]]

def raw5236step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -2, 1], ![0, 1, 1, -2], ![2, -2, 2, -2]]

theorem canonical5236 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw5236 = injectiveMoment H node593 := by
  calc
    injectiveMoment H raw5236 = injectiveMoment H raw5236step0 := by
      have heq : raw5236step0 = -raw5236 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw5236).symm
    injectiveMoment H raw5236step0 = injectiveMoment H raw5236step1 := by
      have heq : raw5236step1 = (fun i j => raw5236step0 (permutation32 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5236step0 permutation32 permutation9
    _ = injectiveMoment H node593 := by rfl

def raw5237 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, -2, 2], ![0, -1, -1, 2], ![0, -1, 3, -2], ![1, 0, 0, -1], ![1, 0, 0, -1]]

theorem canonical5237 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5237 = injectiveMoment H node2332 := by
  rfl

def raw5238 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, -2, 2], ![0, -1, -1, 2], ![0, -1, 3, -2], ![2, 0, 0, -2]]

def raw5238step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, -2, 2, -2], ![0, 1, 1, -2], ![0, 1, -3, 2], ![-2, 0, 0, 2]]

def raw5238step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -3, 2], ![0, 1, 1, -2], ![2, -2, 2, -2]]

theorem canonical5238 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw5238 = injectiveMoment H node610 := by
  calc
    injectiveMoment H raw5238 = injectiveMoment H raw5238step0 := by
      have heq : raw5238step0 = -raw5238 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw5238).symm
    injectiveMoment H raw5238step0 = injectiveMoment H raw5238step1 := by
      have heq : raw5238step1 = (fun i j => raw5238step0 (permutation32 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5238step0 permutation32 permutation9
    _ = injectiveMoment H node610 := by rfl

def raw5239 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, -2, 2], ![0, -1, -1, 2], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, 2, -3]]

theorem canonical5239 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5239 = injectiveMoment H node2333 := by
  rfl

def raw5240 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, -2, 2], ![0, -1, -1, 2], ![0, 0, 1, -1], ![1, -1, 1, -1], ![1, 0, 1, -2]]

theorem canonical5240 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5240 = injectiveMoment H node2334 := by
  rfl

def raw5241 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, -2, 2], ![0, -1, -1, 2], ![0, 0, 2, -2], ![1, -1, 0, 0], ![1, 0, 1, -2]]

theorem canonical5241 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5241 = injectiveMoment H node2335 := by
  rfl

def raw5242 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, -2, 2], ![0, -1, -1, 2], ![0, 0, 2, -2], ![2, -1, 1, -2]]

def raw5242step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, -2, 2, -2], ![0, 1, 1, -2], ![0, 0, -2, 2], ![-2, 1, -1, 2]]

def raw5242step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -2, 2], ![0, 1, 1, -2], ![2, -2, 2, -2]]

theorem canonical5242 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw5242 = injectiveMoment H node681 := by
  calc
    injectiveMoment H raw5242 = injectiveMoment H raw5242step0 := by
      have heq : raw5242step0 = -raw5242 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw5242).symm
    injectiveMoment H raw5242step0 = injectiveMoment H raw5242step1 := by
      have heq : raw5242step1 = (fun i j => raw5242step0 (permutation32 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5242step0 permutation32 permutation9
    _ = injectiveMoment H node681 := by rfl

def raw5243 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, -2, 2], ![0, -1, -1, 2], ![1, -1, 0, 0], ![1, 0, 3, -4]]

def raw5243step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![2, -1, -1, 0], ![-2, -1, 0, 3], ![2, 2, 0, -4]]

def raw5243step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 3, -2], ![0, 2, -4, 2], ![1, 0, 1, -2]]

theorem canonical5243 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5243 = injectiveMoment H node1014 := by
  calc
    injectiveMoment H raw5243 = injectiveMoment H raw5243step0 := by
      have heq : raw5243step0 = raw5243.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5243).symm
    injectiveMoment H raw5243step0 = injectiveMoment H raw5243step1 := by
      have heq : raw5243step1 = (fun i j => raw5243step0 (permutation18 i) (permutation24 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5243step0 permutation18 permutation24
    _ = injectiveMoment H node1014 := by rfl

def raw5244 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, -2, 2], ![0, -1, -1, 2], ![1, -1, 1, -1], ![1, 0, 2, -3]]

def raw5244step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![2, -1, -1, 0], ![-2, -1, 1, 2], ![2, 2, -1, -3]]

def raw5244step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-2, 1, 1, 0], ![2, 1, -1, -2], ![-2, -2, 1, 3]]

def raw5244step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 3, -2], ![0, -1, -1, 2], ![1, -1, -2, 2], ![1, 1, 0, -2]]

theorem canonical5244 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw5244 = injectiveMoment H node714 := by
  calc
    injectiveMoment H raw5244 = injectiveMoment H raw5244step0 := by
      have heq : raw5244step0 = raw5244.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5244).symm
    injectiveMoment H raw5244step0 = injectiveMoment H raw5244step1 := by
      have heq : raw5244step1 = -raw5244step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw5244step0).symm
    injectiveMoment H raw5244step1 = injectiveMoment H raw5244step2 := by
      have heq : raw5244step2 = (fun i j => raw5244step1 (permutation28 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5244step1 permutation28 permutation18
    _ = injectiveMoment H node714 := by rfl

def raw5245 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, -2, 2], ![0, -1, -1, 2], ![1, -1, 2, -2], ![1, 0, 1, -2]]

theorem canonical5245 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5245 = injectiveMoment H node718 := by
  rfl

def raw5246 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 2, -2, 2], ![0, -1, -1, 2], ![1, -1, 3, -3], ![1, 0, 0, -1]]

def raw5246step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![2, -1, -1, 0], ![-2, -1, 3, 0], ![2, 2, -3, -1]]

def raw5246step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-2, 1, 1, 0], ![2, 1, -3, 0], ![-2, -2, 3, 1]]

def raw5246step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 1, -3, 2], ![0, 1, 1, -2], ![1, -2, 3, -2]]

theorem canonical5246 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw5246 = injectiveMoment H node1274 := by
  calc
    injectiveMoment H raw5246 = injectiveMoment H raw5246step0 := by
      have heq : raw5246step0 = raw5246.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5246).symm
    injectiveMoment H raw5246step0 = injectiveMoment H raw5246step1 := by
      have heq : raw5246step1 = -raw5246step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw5246step0).symm
    injectiveMoment H raw5246step1 = injectiveMoment H raw5246step2 := by
      have heq : raw5246step2 = (fun i j => raw5246step1 (permutation11 i) (permutation30 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5246step1 permutation11 permutation30
    _ = injectiveMoment H node1274 := by rfl

def raw5247 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, -2, 2], ![0, -1, 0, 1], ![0, -1, 2, -1], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def raw5247step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, -1, -1]]

theorem canonical5247 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5247 = injectiveMoment H node1521 := by
  calc
    injectiveMoment H raw5247 = injectiveMoment H raw5247step0 := by
      have heq : raw5247step0 = (fun i j => raw5247 (permutation36 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5247 permutation36 permutation21
    _ = injectiveMoment H node1521 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
