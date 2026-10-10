import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes7
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes10
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes12
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes15
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes17
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes19
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes21
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes23
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes33

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw4288 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -3, 4], ![0, 1, 3, -4], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def raw4288step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 1, -1, -1], ![-3, 3, 0, 0], ![4, -4, 0, 0]]

def raw4288step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, -1, 1, 1], ![3, -3, 0, 0], ![-4, 4, 0, 0]]

def raw4288step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -3, 3], ![0, 0, 4, -4], ![1, 1, -1, -1]]

theorem canonical4288 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4288 = injectiveMoment H node1022 := by
  calc
    injectiveMoment H raw4288 = injectiveMoment H raw4288step0 := by
      have heq : raw4288step0 = raw4288.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4288).symm
    injectiveMoment H raw4288step0 = injectiveMoment H raw4288step1 := by
      have heq : raw4288step1 = -raw4288step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4288step0).symm
    injectiveMoment H raw4288step1 = injectiveMoment H raw4288step2 := by
      have heq : raw4288step2 = (fun i j => raw4288step1 (permutation12 i) (permutation26 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4288step1 permutation12 permutation26
    _ = injectiveMoment H node1022 := by rfl

def raw4289 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -3, 4], ![1, -2, 2, -1], ![0, 1, 1, -2], ![1, 0, 0, -1]]

def raw4289step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![1, -2, 1, 0], ![-3, 2, 1, 0], ![4, -1, -2, -1]]

def raw4289step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 1, -2, 1], ![0, 1, 2, -3], ![1, 0, 1, -2]]

theorem canonical4289 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4289 = injectiveMoment H node785 := by
  calc
    injectiveMoment H raw4289 = injectiveMoment H raw4289step0 := by
      have heq : raw4289step0 = raw4289.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4289).symm
    injectiveMoment H raw4289step0 = injectiveMoment H raw4289step1 := by
      have heq : raw4289step1 = (fun i j => raw4289step0 (permutation30 i) (permutation32 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4289step0 permutation30 permutation32
    _ = injectiveMoment H node785 := by rfl

def raw4290 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -3, 4], ![1, -1, 2, -2], ![0, 1, 1, -2], ![1, -1, 0, 0]]

def raw4290step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![1, -1, 1, -1], ![-3, 2, 1, 0], ![4, -2, -2, 0]]

def raw4290step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, -1, 0, -1], ![-1, 1, -1, 1], ![3, -2, -1, 0], ![-4, 2, 2, 0]]

def raw4290step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, -2, 3], ![0, 2, 2, -4], ![1, -1, 1, -1]]

theorem canonical4290 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4290 = injectiveMoment H node1236 := by
  calc
    injectiveMoment H raw4290 = injectiveMoment H raw4290step0 := by
      have heq : raw4290step0 = raw4290.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4290).symm
    injectiveMoment H raw4290step0 = injectiveMoment H raw4290step1 := by
      have heq : raw4290step1 = -raw4290step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4290step0).symm
    injectiveMoment H raw4290step1 = injectiveMoment H raw4290step2 := by
      have heq : raw4290step2 = (fun i j => raw4290step1 (permutation12 i) (permutation32 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4290step1 permutation12 permutation32
    _ = injectiveMoment H node1236 := by rfl

def raw4291 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, -2, 1, 1], ![1, 0, -1, 0], ![1, 1, 2, -4]]

def raw4291step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, -2, 0, 1], ![-2, 1, -1, 2], ![3, 1, 0, -4]]

def raw4291step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, 2, 0, -1], ![2, -1, 1, -2], ![-3, -1, 0, 4]]

def raw4291step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 4, -3], ![0, 2, -1, -1], ![1, -1, -2, 2]]

theorem canonical4291 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4291 = injectiveMoment H node1251 := by
  calc
    injectiveMoment H raw4291 = injectiveMoment H raw4291step0 := by
      have heq : raw4291step0 = raw4291.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4291).symm
    injectiveMoment H raw4291step0 = injectiveMoment H raw4291step1 := by
      have heq : raw4291step1 = -raw4291step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4291step0).symm
    injectiveMoment H raw4291step1 = injectiveMoment H raw4291step2 := by
      have heq : raw4291step2 = (fun i j => raw4291step1 (permutation13 i) (permutation24 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4291step1 permutation13 permutation24
    _ = injectiveMoment H node1251 := by rfl

def raw4292 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, -2, 2, 0], ![0, 1, 1, -2], ![2, 0, -1, -1]]

def raw4292step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, -2, 1, 0], ![-2, 2, 1, -1], ![3, 0, -2, -1]]

def raw4292step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 2, 0, -2], ![1, -1, 2, -2], ![1, 0, -2, 1]]

theorem canonical4292 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4292 = injectiveMoment H node496 := by
  calc
    injectiveMoment H raw4292 = injectiveMoment H raw4292step0 := by
      have heq : raw4292step0 = raw4292.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4292).symm
    injectiveMoment H raw4292step0 = injectiveMoment H raw4292step1 := by
      have heq : raw4292step1 = (fun i j => raw4292step0 (permutation28 i) (permutation26 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4292step0 permutation28 permutation26
    _ = injectiveMoment H node496 := by rfl

def raw4293 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, -2, 2, 0], ![1, 0, 1, -2], ![1, 1, -1, -1]]

def raw4293step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, -2, 0, 1], ![-2, 2, 1, -1], ![3, 0, -2, -1]]

def raw4293step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -2, 1], ![1, -1, 2, -2], ![1, 1, 0, -2]]

theorem canonical4293 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4293 = injectiveMoment H node488 := by
  calc
    injectiveMoment H raw4293 = injectiveMoment H raw4293step0 := by
      have heq : raw4293step0 = raw4293.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4293).symm
    injectiveMoment H raw4293step0 = injectiveMoment H raw4293step1 := by
      have heq : raw4293step1 = (fun i j => raw4293step0 (permutation30 i) (permutation26 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4293step0 permutation30 permutation26
    _ = injectiveMoment H node488 := by rfl

def raw4294 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, -1, 0, 1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 1, 1, -3]]

def raw4294step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 1, 1, -3]]

theorem canonical4294 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4294 = injectiveMoment H node1498 := by
  calc
    injectiveMoment H raw4294 = injectiveMoment H raw4294step0 := by
      have heq : raw4294step0 = (fun i j => raw4294 (permutation35 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4294 permutation35 permutation21
    _ = injectiveMoment H node1498 := by rfl

def raw4295 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, -1, 0, 1], ![0, 0, 1, -1], ![1, -1, 1, -1], ![1, 1, 0, -2]]

def raw4295step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, 0, 1, -2], ![1, 1, -1, -1]]

theorem canonical4295 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4295 = injectiveMoment H node1500 := by
  calc
    injectiveMoment H raw4295 = injectiveMoment H raw4295step0 := by
      have heq : raw4295step0 = (fun i j => raw4295 (permutation34 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4295 permutation34 permutation11
    _ = injectiveMoment H node1500 := by rfl

def raw4296 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, -1, 0, 1], ![0, 0, 2, -2], ![1, -1, 0, 0], ![1, 1, 0, -2]]

def raw4296step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![2, 0, 0, -2]]

theorem canonical4296 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4296 = injectiveMoment H node1496 := by
  calc
    injectiveMoment H raw4296 = injectiveMoment H raw4296step0 := by
      have heq : raw4296step0 = (fun i j => raw4296 (permutation36 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4296 permutation36 permutation21
    _ = injectiveMoment H node1496 := by rfl

def raw4297 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 1, 0, -2]]

def raw4297step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 1, -2]]

theorem canonical4297 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4297 = injectiveMoment H node1513 := by
  calc
    injectiveMoment H raw4297 = injectiveMoment H raw4297step0 := by
      have heq : raw4297step0 = (fun i j => raw4297 (permutation33 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4297 permutation33 permutation11
    _ = injectiveMoment H node1513 := by rfl

def raw4298 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![1, -1, 1, -1], ![1, 1, -1, -1]]

theorem canonical4298 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4298 = injectiveMoment H node2161 := by
  rfl

def raw4299 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, -1, 1, 0], ![0, 0, 2, -2], ![1, -1, 0, 0], ![1, 1, -1, -1]]

theorem canonical4299 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4299 = injectiveMoment H node2162 := by
  rfl

def raw4300 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, -1, 1, 0], ![1, -1, 0, 0], ![1, 1, 1, -3]]

def raw4300step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, -1, -1, 1], ![-2, 1, 0, 1], ![3, 0, 0, -3]]

def raw4300step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -3, 3], ![0, 1, 1, -2], ![1, 0, 1, -2]]

theorem canonical4300 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4300 = injectiveMoment H node1104 := by
  calc
    injectiveMoment H raw4300 = injectiveMoment H raw4300step0 := by
      have heq : raw4300step0 = raw4300.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4300).symm
    injectiveMoment H raw4300step0 = injectiveMoment H raw4300step1 := by
      have heq : raw4300step1 = (fun i j => raw4300step0 (permutation19 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4300step0 permutation19 permutation18
    _ = injectiveMoment H node1104 := by rfl

def raw4301 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, -1, 1, 0], ![1, -1, 1, -1], ![1, 1, 0, -2]]

def raw4301step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, -1, -1, 1], ![-2, 1, 1, 0], ![3, 0, -1, -2]]

def raw4301step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, 1, 1, -1], ![2, -1, -1, 0], ![-3, 0, 1, 2]]

def raw4301step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, -1, 2], ![0, 1, 2, -3], ![1, 1, -1, -1]]

theorem canonical4301 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4301 = injectiveMoment H node995 := by
  calc
    injectiveMoment H raw4301 = injectiveMoment H raw4301step0 := by
      have heq : raw4301step0 = raw4301.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4301).symm
    injectiveMoment H raw4301step0 = injectiveMoment H raw4301step1 := by
      have heq : raw4301step1 = -raw4301step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4301step0).symm
    injectiveMoment H raw4301step1 = injectiveMoment H raw4301step2 := by
      have heq : raw4301step2 = (fun i j => raw4301step1 (permutation22 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4301step1 permutation22 permutation18
    _ = injectiveMoment H node995 := by rfl

def raw4302 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, -1, 2, -1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, 1, 1, -3]]

theorem canonical4302 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4302 = injectiveMoment H node2163 := by
  rfl

def raw4303 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, -1, 2, -1], ![0, 0, 0, 0], ![1, -1, 0, 0], ![1, 1, 0, -2]]

def raw4303step0 : Matrix (Fin 4) (Fin 5) ℤ := ![![-2, 0, 0, 1, 1], ![1, -1, 0, -1, 1], ![-2, 2, 0, 0, 0], ![3, -1, 0, 0, -2]]

def raw4303step1 : Matrix (Fin 4) (Fin 5) ℤ := ![![2, 0, 0, -1, -1], ![-1, 1, 0, 1, -1], ![2, -2, 0, 0, 0], ![-3, 1, 0, 0, 2]]

def raw4303step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, 1, 1, -1], ![2, -2, 0, 0], ![-3, 1, 0, 2]]

def raw4303step3 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 2, 1, -3], ![1, -1, 1, -1]]

theorem canonical4303 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4303 = injectiveMoment H node1036 := by
  calc
    injectiveMoment H raw4303 = injectiveMoment H raw4303step0 := by
      have heq : raw4303step0 = raw4303.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4303).symm
    injectiveMoment H raw4303step0 = injectiveMoment H raw4303step1 := by
      have heq : raw4303step1 = -raw4303step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4303step0).symm
    injectiveMoment H raw4303step1 = injectiveMoment H raw4303step2 := by
      have hz : ∀ i, raw4303step1 i (permutation80 0) = 0 := by decide +kernel
      have heq : raw4303step2 = (fun i j => raw4303step1 i (permutation80 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw4303step1 permutation80 hz
    injectiveMoment H raw4303step2 = injectiveMoment H raw4303step3 := by
      have heq : raw4303step3 = (fun i j => raw4303step2 (permutation12 i) (permutation26 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4303step2 permutation12 permutation26
    _ = injectiveMoment H node1036 := by rfl

def raw4304 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, -1, 2, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![2, -1, 0, -1]]

theorem canonical4304 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4304 = injectiveMoment H node2165 := by
  rfl

def raw4305 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, -1, 2, -1], ![0, 0, 1, -1], ![1, -1, -1, 1], ![1, 1, 0, -2]]

theorem canonical4305 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4305 = injectiveMoment H node2166 := by
  rfl

def raw4306 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, -1, 2, -1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 1, -1, -1]]

theorem canonical4306 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4306 = injectiveMoment H node2167 := by
  rfl

def raw4307 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, -1, 2, -1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 1, -2]]

theorem canonical4307 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4307 = injectiveMoment H node2168 := by
  rfl

def raw4308 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, -1, 2, -1], ![0, 1, -1, 0], ![1, -1, 1, -1], ![1, 0, 0, -1]]

theorem canonical4308 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4308 = injectiveMoment H node2169 := by
  rfl

def raw4309 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, -1, 2, -1], ![0, 1, -1, 0], ![2, -1, 1, -2]]

def raw4309step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, -1, 1, -1], ![-2, 2, -1, 1], ![3, -1, 0, -2]]

def raw4309step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![-1, 1, -1, 1], ![2, -2, 1, -1], ![-3, 1, 0, 2]]

def raw4309step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, 1, -1], ![0, 0, -2, 2], ![0, 1, 2, -3], ![1, -2, -1, 2]]

theorem canonical4309 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4309 = injectiveMoment H node1366 := by
  calc
    injectiveMoment H raw4309 = injectiveMoment H raw4309step0 := by
      have heq : raw4309step0 = raw4309.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4309).symm
    injectiveMoment H raw4309step0 = injectiveMoment H raw4309step1 := by
      have heq : raw4309step1 = -raw4309step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4309step0).symm
    injectiveMoment H raw4309step1 = injectiveMoment H raw4309step2 := by
      have heq : raw4309step2 = (fun i j => raw4309step1 (permutation16 i) (permutation24 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4309step1 permutation16 permutation24
    _ = injectiveMoment H node1366 := by rfl

def raw4310 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, -1, 2, -1], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 0, 1, -2]]

theorem canonical4310 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4310 = injectiveMoment H node2170 := by
  rfl

def raw4311 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, -1, 2, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw4311step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, 0, -1, -1]]

theorem canonical4311 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4311 = injectiveMoment H node1504 := by
  calc
    injectiveMoment H raw4311 = injectiveMoment H raw4311step0 := by
      have heq : raw4311step0 = (fun i j => raw4311 (permutation42 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4311 permutation42 permutation21
    _ = injectiveMoment H node1504 := by rfl

def raw4312 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, -1, 2, -1], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 0, -1, 0]]

theorem canonical4312 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4312 = injectiveMoment H node2171 := by
  rfl

def raw4313 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, -1, 2, -1], ![0, 1, 0, -1], ![2, -1, 0, -1]]

def raw4313step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, -1, 1, -1], ![-2, 2, 0, 0], ![3, -1, -1, -1]]

def raw4313step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 2, -2], ![0, 2, 0, -2], ![1, -1, -1, 1]]

theorem canonical4313 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4313 = injectiveMoment H node976 := by
  calc
    injectiveMoment H raw4313 = injectiveMoment H raw4313step0 := by
      have heq : raw4313step0 = raw4313.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4313).symm
    injectiveMoment H raw4313step0 = injectiveMoment H raw4313step1 := by
      have heq : raw4313step1 = (fun i j => raw4313step0 (permutation28 i) (permutation24 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4313step0 permutation28 permutation24
    _ = injectiveMoment H node976 := by rfl

def raw4314 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, -1, 2, -1], ![0, 1, 1, -2], ![1, -1, -1, 1], ![1, 0, 0, -1]]

theorem canonical4314 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4314 = injectiveMoment H node2172 := by
  rfl

def raw4315 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, -1, 2, -1], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, 0, -1, 0]]

theorem canonical4315 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4315 = injectiveMoment H node2173 := by
  rfl

def raw4316 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, -1, 2, -1], ![0, 1, 1, -2], ![2, -1, -1, 0]]

def raw4316step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, -1, 1, -1], ![-2, 2, 1, -1], ![3, -1, -2, 0]]

def raw4316step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 2, -2], ![1, -1, -1, 1], ![1, 2, -1, -2]]

theorem canonical4316 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4316 = injectiveMoment H node483 := by
  calc
    injectiveMoment H raw4316 = injectiveMoment H raw4316step0 := by
      have heq : raw4316step0 = raw4316.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4316).symm
    injectiveMoment H raw4316step0 = injectiveMoment H raw4316step1 := by
      have heq : raw4316step1 = (fun i j => raw4316step0 (permutation27 i) (permutation24 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4316step0 permutation27 permutation24
    _ = injectiveMoment H node483 := by rfl

def raw4317 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, -1, 2, -1], ![1, -1, -1, 1], ![1, 1, 1, -3]]

theorem canonical4317 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4317 = injectiveMoment H node673 := by
  rfl

def raw4318 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, -1, 2, -1], ![1, -1, 0, 0], ![1, 1, 0, -2]]

def raw4318step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, -1, -1, 1], ![-2, 2, 0, 0], ![3, -1, 0, -2]]

def raw4318step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, 1, 1, -1], ![2, -2, 0, 0], ![-3, 1, 0, 2]]

def raw4318step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 2, 1, -3], ![1, -1, 1, -1]]

theorem canonical4318 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4318 = injectiveMoment H node1036 := by
  calc
    injectiveMoment H raw4318 = injectiveMoment H raw4318step0 := by
      have heq : raw4318step0 = raw4318.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4318).symm
    injectiveMoment H raw4318step0 = injectiveMoment H raw4318step1 := by
      have heq : raw4318step1 = -raw4318step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4318step0).symm
    injectiveMoment H raw4318step1 = injectiveMoment H raw4318step2 := by
      have heq : raw4318step2 = (fun i j => raw4318step1 (permutation12 i) (permutation26 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4318step1 permutation12 permutation26
    _ = injectiveMoment H node1036 := by rfl

def raw4319 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, -1, 2, -1], ![1, -1, 1, -1], ![1, 1, -1, -1]]

def raw4319step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, -1, -1, 1], ![-2, 2, 1, -1], ![3, -1, -1, -1]]

def raw4319step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, 1, 1, -1], ![2, -2, -1, 1], ![-3, 1, 1, 1]]

def raw4319step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, -1, 2], ![1, 1, -1, -1], ![1, 1, 1, -3]]

theorem canonical4319 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4319 = injectiveMoment H node502 := by
  calc
    injectiveMoment H raw4319 = injectiveMoment H raw4319step0 := by
      have heq : raw4319step0 = raw4319.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4319).symm
    injectiveMoment H raw4319step0 = injectiveMoment H raw4319step1 := by
      have heq : raw4319step1 = -raw4319step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4319step0).symm
    injectiveMoment H raw4319step1 = injectiveMoment H raw4319step2 := by
      have heq : raw4319step2 = (fun i j => raw4319step1 (permutation21 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4319step1 permutation21 permutation18
    _ = injectiveMoment H node502 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
