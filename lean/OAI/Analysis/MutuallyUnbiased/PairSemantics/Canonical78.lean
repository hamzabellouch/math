import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes1
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes2
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes4
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes7
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes8
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes11
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes12
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes13
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes15
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes16

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw2496 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 2, 0, -2], ![1, -1, 1, -1], ![1, 0, -2, 1]]

def raw2496step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 2, -1, 0], ![1, 0, 1, -2], ![2, -2, -1, 1]]

def raw2496step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, -2, 1], ![0, 1, 1, -2], ![2, -1, 0, -1]]

theorem canonical2496 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2496 = injectiveMoment H node510 := by
  calc
    injectiveMoment H raw2496 = injectiveMoment H raw2496step0 := by
      have heq : raw2496step0 = raw2496.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2496).symm
    injectiveMoment H raw2496step0 = injectiveMoment H raw2496step1 := by
      have heq : raw2496step1 = (fun i j => raw2496step0 (permutation31 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2496step0 permutation31 permutation18
    _ = injectiveMoment H node510 := by rfl

def raw2497 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 2, 0, -2], ![1, 0, -2, 1], ![1, -1, 1, -1]]

def raw2497step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 2, 0, -1], ![1, 0, -2, 1], ![2, -2, 1, -1]]

def raw2497step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, -2, 1], ![0, 1, 1, -2], ![2, -1, 0, -1]]

theorem canonical2497 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2497 = injectiveMoment H node510 := by
  calc
    injectiveMoment H raw2497 = injectiveMoment H raw2497step0 := by
      have heq : raw2497step0 = raw2497.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2497).symm
    injectiveMoment H raw2497step0 = injectiveMoment H raw2497step1 := by
      have heq : raw2497step1 = (fun i j => raw2497step0 (permutation31 i) (permutation20 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2497step0 permutation31 permutation20
    _ = injectiveMoment H node510 := by rfl

def raw2498 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 2, 1, -3], ![1, -1, -2, 2], ![1, 0, 0, -1]]

def raw2498step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 2, -1, 0], ![1, 1, -2, 0], ![2, -3, 2, -1]]

def raw2498step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -3, 2, 2], ![0, 1, -2, 1], ![0, 2, -1, -1], ![1, 0, 1, -2]]

theorem canonical2498 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2498 = injectiveMoment H node731 := by
  calc
    injectiveMoment H raw2498 = injectiveMoment H raw2498step0 := by
      have heq : raw2498step0 = raw2498.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2498).symm
    injectiveMoment H raw2498step0 = injectiveMoment H raw2498step1 := by
      have heq : raw2498step1 = (fun i j => raw2498step0 (permutation32 i) (permutation30 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2498step0 permutation32 permutation30
    _ = injectiveMoment H node731 := by rfl

def raw2499 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 2, 1, -3], ![1, -1, -1, 1], ![1, 0, -1, 0]]

def raw2499step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 2, -1, 0], ![1, 1, -1, -1], ![2, -3, 1, 0]]

def raw2499step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![1, -2, 1, 0], ![-1, -1, 1, 1], ![-2, 3, -1, 0]]

def raw2499step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 3, -2], ![0, 1, -2, 1], ![1, 1, -1, -1]]

theorem canonical2499 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2499 = injectiveMoment H node1013 := by
  calc
    injectiveMoment H raw2499 = injectiveMoment H raw2499step0 := by
      have heq : raw2499step0 = raw2499.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2499).symm
    injectiveMoment H raw2499step0 = injectiveMoment H raw2499step1 := by
      have heq : raw2499step1 = -raw2499step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2499step0).symm
    injectiveMoment H raw2499step1 = injectiveMoment H raw2499step2 := by
      have heq : raw2499step2 = (fun i j => raw2499step1 (permutation13 i) (permutation32 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2499step1 permutation13 permutation32
    _ = injectiveMoment H node1013 := by rfl

def raw2500 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 2, 1, -3], ![1, -1, 0, 0], ![1, 0, -2, 1]]

def raw2500step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 2, -1, 0], ![1, 1, 0, -2], ![2, -3, 0, 1]]

def raw2500step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![1, -2, 1, 0], ![-1, -1, 0, 2], ![-2, 3, 0, -1]]

def raw2500step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 3, -2], ![0, 2, -1, -1], ![1, 0, -2, 1]]

theorem canonical2500 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2500 = injectiveMoment H node1016 := by
  calc
    injectiveMoment H raw2500 = injectiveMoment H raw2500step0 := by
      have heq : raw2500step0 = raw2500.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2500).symm
    injectiveMoment H raw2500step0 = injectiveMoment H raw2500step1 := by
      have heq : raw2500step1 = -raw2500step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2500step0).symm
    injectiveMoment H raw2500step1 = injectiveMoment H raw2500step2 := by
      have heq : raw2500step2 = (fun i j => raw2500step1 (permutation14 i) (permutation26 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2500step1 permutation14 permutation26
    _ = injectiveMoment H node1016 := by rfl

def raw2501 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 2, 1, -3], ![1, -1, 1, -1], ![1, 0, -3, 2]]

theorem canonical2501 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2501 = injectiveMoment H node519 := by
  rfl

def raw2502 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 2, 2, -4], ![1, -1, -2, 2], ![1, 0, -1, 0]]

def raw2502step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 2, -1, 0], ![1, 2, -2, -1], ![2, -4, 2, 0]]

def raw2502step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, -1, -1, 2], ![0, 2, 2, -4], ![1, 1, -2, 0]]

theorem canonical2502 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2502 = injectiveMoment H node821 := by
  calc
    injectiveMoment H raw2502 = injectiveMoment H raw2502step0 := by
      have heq : raw2502step0 = raw2502.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2502).symm
    injectiveMoment H raw2502step0 = injectiveMoment H raw2502step1 := by
      have heq : raw2502step1 = (fun i j => raw2502step0 (permutation24 i) (permutation31 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2502step0 permutation24 permutation31
    _ = injectiveMoment H node821 := by rfl

def raw2503 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 2, 2, -4], ![1, -1, -1, 1], ![1, 0, -2, 1]]

def raw2503step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 2, -1, 0], ![1, 2, -1, -2], ![2, -4, 1, 1]]

def raw2503step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, -1, 2], ![1, 1, -2, 0], ![1, 1, 2, -4]]

theorem canonical2503 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2503 = injectiveMoment H node501 := by
  calc
    injectiveMoment H raw2503 = injectiveMoment H raw2503step0 := by
      have heq : raw2503step0 = raw2503.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2503).symm
    injectiveMoment H raw2503step0 = injectiveMoment H raw2503step1 := by
      have heq : raw2503step1 = (fun i j => raw2503step0 (permutation23 i) (permutation31 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2503step0 permutation23 permutation31
    _ = injectiveMoment H node501 := by rfl

def raw2504 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 2, 2, -4], ![1, -1, 0, 0], ![1, 0, -3, 2]]

def raw2504step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 2, -1, 0], ![1, 2, 0, -3], ![2, -4, 0, 2]]

def raw2504step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, -3, 2], ![0, 2, 2, -4], ![1, -2, 1, 0]]

theorem canonical2504 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2504 = injectiveMoment H node1076 := by
  calc
    injectiveMoment H raw2504 = injectiveMoment H raw2504step0 := by
      have heq : raw2504step0 = raw2504.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2504).symm
    injectiveMoment H raw2504step0 = injectiveMoment H raw2504step1 := by
      have heq : raw2504step1 = (fun i j => raw2504step0 (permutation18 i) (permutation22 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2504step0 permutation18 permutation22
    _ = injectiveMoment H node1076 := by rfl

def raw2505 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 3, -3, 0], ![2, -2, 2, -2]]

def raw2505step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![1, -3, 2], ![2, 0, -2]]

def raw2505step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![3, -1, -2]]

theorem canonical2505 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2505 = injectiveMoment H node101 := by
  calc
    injectiveMoment H raw2505 = injectiveMoment H raw2505step0 := by
      have heq : raw2505step0 = raw2505.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2505).symm
    injectiveMoment H raw2505step0 = injectiveMoment H raw2505step1 := by
      have heq : raw2505step1 = (fun i j => raw2505step0 (permutation22 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2505step0 permutation22 permutation5
    _ = injectiveMoment H node101 := by rfl

def raw2506 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 3, -2, -1], ![2, -2, 1, -1]]

def raw2506step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![1, -2, 1], ![2, -1, -1]]

def raw2506step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -3, 2], ![-1, 2, -1], ![-2, 1, 1]]

def raw2506step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]

theorem canonical2506 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2506 = injectiveMoment H node111 := by
  calc
    injectiveMoment H raw2506 = injectiveMoment H raw2506step0 := by
      have heq : raw2506step0 = raw2506.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2506).symm
    injectiveMoment H raw2506step0 = injectiveMoment H raw2506step1 := by
      have heq : raw2506step1 = -raw2506step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2506step0).symm
    injectiveMoment H raw2506step1 = injectiveMoment H raw2506step2 := by
      have heq : raw2506step2 = (fun i j => raw2506step1 (permutation16 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2506step1 permutation16 permutation5
    _ = injectiveMoment H node111 := by rfl

def raw2507 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 4, -3, -1], ![2, -3, 2, -1]]

def raw2507step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 4, -3], ![1, -3, 2], ![2, -1, -1]]

theorem canonical2507 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2507 = injectiveMoment H node191 := by
  calc
    injectiveMoment H raw2507 = injectiveMoment H raw2507step0 := by
      have heq : raw2507step0 = raw2507.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2507).symm
    _ = injectiveMoment H node191 := by rfl

def raw2508 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![1, -2, 2, -1], ![1, 3, -3, -1]]

def raw2508step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -2, 3], ![1, 2, -3], ![2, -1, -1]]

def raw2508step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -2, 1], ![2, 1, -3]]

theorem canonical2508 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2508 = injectiveMoment H node159 := by
  calc
    injectiveMoment H raw2508 = injectiveMoment H raw2508step0 := by
      have heq : raw2508step0 = raw2508.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2508).symm
    injectiveMoment H raw2508step0 = injectiveMoment H raw2508step1 := by
      have heq : raw2508step1 = (fun i j => raw2508step0 (permutation19 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2508step0 permutation19 permutation5
    _ = injectiveMoment H node159 := by rfl

def raw2509 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![1, -1, -2, 2], ![0, 2, 0, -2], ![1, 0, 1, -2]]

def raw2509step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 2, 0, -2], ![1, -1, -2, 2], ![1, 0, 1, -2]]

theorem canonical2509 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2509 = injectiveMoment H node518 := by
  calc
    injectiveMoment H raw2509 = injectiveMoment H raw2509step0 := by
      have heq : raw2509step0 = (fun i j => raw2509 (permutation11 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2509 permutation11 permutation9
    _ = injectiveMoment H node518 := by rfl

def raw2510 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![1, -1, -2, 2], ![0, 2, 2, -4], ![1, 0, -1, 0]]

def raw2510step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![-1, -1, 2, 0], ![1, -2, 2, -1], ![2, 2, -4, 0]]

def raw2510step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, -1, -1, 2], ![0, 2, 2, -4], ![1, 1, -2, 0]]

theorem canonical2510 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2510 = injectiveMoment H node821 := by
  calc
    injectiveMoment H raw2510 = injectiveMoment H raw2510step0 := by
      have heq : raw2510step0 = raw2510.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2510).symm
    injectiveMoment H raw2510step0 = injectiveMoment H raw2510step1 := by
      have heq : raw2510step1 = (fun i j => raw2510step0 (permutation24 i) (permutation29 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2510step0 permutation24 permutation29
    _ = injectiveMoment H node821 := by rfl

def raw2511 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![1, -1, -1, 1], ![0, 1, 1, -2], ![1, 1, -1, -1]]

def raw2511step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, 1, -2], ![1, -1, -1, 1], ![1, 1, -1, -1]]

theorem canonical2511 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2511 = injectiveMoment H node514 := by
  calc
    injectiveMoment H raw2511 = injectiveMoment H raw2511step0 := by
      have heq : raw2511step0 = (fun i j => raw2511 (permutation11 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2511 permutation11 permutation9
    _ = injectiveMoment H node514 := by rfl

def raw2512 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![1, -1, -1, 1], ![0, 2, -1, -1], ![1, 0, 1, -2]]

def raw2512step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 2, -1, -1], ![1, -1, -1, 1], ![1, 0, 1, -2]]

theorem canonical2512 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2512 = injectiveMoment H node517 := by
  calc
    injectiveMoment H raw2512 = injectiveMoment H raw2512step0 := by
      have heq : raw2512step0 = (fun i j => raw2512 (permutation11 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2512 permutation11 permutation9
    _ = injectiveMoment H node517 := by rfl

def raw2513 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![1, -1, 1, -1], ![1, 2, -2, -1]]

def raw2513step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 1, -2], ![2, -1, -1]]

def raw2513step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 1, -2]]

theorem canonical2513 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2513 = injectiveMoment H node276 := by
  calc
    injectiveMoment H raw2513 = injectiveMoment H raw2513step0 := by
      have heq : raw2513step0 = raw2513.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2513).symm
    injectiveMoment H raw2513step0 = injectiveMoment H raw2513step1 := by
      have heq : raw2513step1 = (fun i j => raw2513step0 (permutation19 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2513step0 permutation19 permutation5
    _ = injectiveMoment H node276 := by rfl

def raw2514 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![1, -1, 2, -2], ![0, 2, -3, 1], ![1, 0, 0, -1]]

def raw2514step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![-1, -1, 2, 0], ![1, 2, -3, 0], ![2, -2, 1, -1]]

def raw2514step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, -1, 2, -1], ![0, 2, -3, 1], ![1, 1, 0, -2]]

theorem canonical2514 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2514 = injectiveMoment H node823 := by
  calc
    injectiveMoment H raw2514 = injectiveMoment H raw2514step0 := by
      have heq : raw2514step0 = raw2514.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2514).symm
    injectiveMoment H raw2514step0 = injectiveMoment H raw2514step1 := by
      have heq : raw2514step1 = (fun i j => raw2514step0 (permutation30 i) (permutation30 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2514step0 permutation30 permutation30
    _ = injectiveMoment H node823 := by rfl

def raw2515 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![1, 0, -3, 2], ![0, 2, 1, -3], ![1, -1, 1, -1]]

def raw2515step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 2, 1, -3], ![1, -1, 1, -1], ![1, 0, -3, 2]]

theorem canonical2515 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2515 = injectiveMoment H node519 := by
  calc
    injectiveMoment H raw2515 = injectiveMoment H raw2515step0 := by
      have heq : raw2515step0 = (fun i j => raw2515 (permutation12 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2515 permutation12 permutation9
    _ = injectiveMoment H node519 := by rfl

def raw2516 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![1, 0, -2, 1], ![0, 1, 1, -2], ![1, 0, 0, -1]]

def raw2516step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, 0, 1, -2]]

theorem canonical2516 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2516 = injectiveMoment H node845 := by
  calc
    injectiveMoment H raw2516 = injectiveMoment H raw2516step0 := by
      have heq : raw2516step0 = (fun i j => raw2516 (permutation10 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2516 permutation10 permutation15
    _ = injectiveMoment H node845 := by rfl

def raw2517 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![1, 0, -2, 1], ![0, 1, 2, -3], ![1, 0, -1, 0]]

def raw2517step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![-1, 0, 1, 0], ![1, -2, 2, -1], ![2, 1, -3, 0]]

def raw2517step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -1, 1], ![0, 1, 2, -3], ![1, 1, -2, 0]]

theorem canonical2517 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2517 = injectiveMoment H node836 := by
  calc
    injectiveMoment H raw2517 = injectiveMoment H raw2517step0 := by
      have heq : raw2517step0 = raw2517.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2517).symm
    injectiveMoment H raw2517step0 = injectiveMoment H raw2517step1 := by
      have heq : raw2517step1 = (fun i j => raw2517step0 (permutation24 i) (permutation29 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2517step0 permutation24 permutation29
    _ = injectiveMoment H node836 := by rfl

def raw2518 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![1, 0, -2, 1], ![0, 2, 0, -2], ![1, -1, 1, -1]]

def raw2518step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![-1, 0, 2, -1], ![1, -2, 0, 1], ![2, 1, -2, -1]]

def raw2518step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, -2, 1], ![0, 1, 1, -2], ![2, -1, 0, -1]]

theorem canonical2518 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2518 = injectiveMoment H node510 := by
  calc
    injectiveMoment H raw2518 = injectiveMoment H raw2518step0 := by
      have heq : raw2518step0 = raw2518.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2518).symm
    injectiveMoment H raw2518step0 = injectiveMoment H raw2518step1 := by
      have heq : raw2518step1 = (fun i j => raw2518step0 (permutation31 i) (permutation26 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2518step0 permutation31 permutation26
    _ = injectiveMoment H node510 := by rfl

def raw2519 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![1, 0, 1, -2], ![0, 2, -1, -1], ![1, -1, -1, 1]]

def raw2519step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 2, -1, -1], ![1, -1, -1, 1], ![1, 0, 1, -2]]

theorem canonical2519 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2519 = injectiveMoment H node517 := by
  calc
    injectiveMoment H raw2519 = injectiveMoment H raw2519step0 := by
      have heq : raw2519step0 = (fun i j => raw2519 (permutation12 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2519 permutation12 permutation9
    _ = injectiveMoment H node517 := by rfl

def raw2520 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![1, 0, 2, -3], ![0, 2, -2, 0], ![1, -1, -1, 1]]

def raw2520step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![-1, 0, 2, -1], ![1, 2, -2, -1], ![2, -3, 0, 1]]

def raw2520step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, -2, 1], ![0, 1, 2, -3], ![2, -1, -1, 0]]

theorem canonical2520 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2520 = injectiveMoment H node511 := by
  calc
    injectiveMoment H raw2520 = injectiveMoment H raw2520step0 := by
      have heq : raw2520step0 = raw2520.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2520).symm
    injectiveMoment H raw2520step0 = injectiveMoment H raw2520step1 := by
      have heq : raw2520step1 = (fun i j => raw2520step0 (permutation22 i) (permutation25 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2520step0 permutation22 permutation25
    _ = injectiveMoment H node511 := by rfl

def raw2521 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![1, 2, -2, -1], ![1, -1, 1, -1]]

def raw2521step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![1, -2, 1], ![2, -1, -1]]

def raw2521step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 1, -2]]

theorem canonical2521 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2521 = injectiveMoment H node276 := by
  calc
    injectiveMoment H raw2521 = injectiveMoment H raw2521step0 := by
      have heq : raw2521step0 = raw2521.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2521).symm
    injectiveMoment H raw2521step0 = injectiveMoment H raw2521step1 := by
      have heq : raw2521step1 = (fun i j => raw2521step0 (permutation19 i) (permutation7 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2521step0 permutation19 permutation7
    _ = injectiveMoment H node276 := by rfl

def raw2522 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![-3, 2, 0, 1], ![5, -1, -2, -2]]

def raw2522step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -3, 5], ![-1, 2, -1], ![2, 0, -2], ![1, 1, -2]]

def raw2522step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]

theorem canonical2522 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2522 = injectiveMoment H node74 := by
  calc
    injectiveMoment H raw2522 = injectiveMoment H raw2522step0 := by
      have heq : raw2522step0 = raw2522.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2522).symm
    injectiveMoment H raw2522step0 = injectiveMoment H raw2522step1 := by
      have heq : raw2522step1 = (fun i j => raw2522step0 (permutation12 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2522step0 permutation12 permutation5
    _ = injectiveMoment H node74 := by rfl

def raw2523 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![-2, 2, -2, 2], ![4, -1, 0, -3]]

def raw2523step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![2, -2, 0], ![1, 2, -3]]

def raw2523step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![1, 2, -3], ![2, -2, 0]]

theorem canonical2523 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2523 = injectiveMoment H node135 := by
  calc
    injectiveMoment H raw2523 = injectiveMoment H raw2523step0 := by
      have heq : raw2523step0 = raw2523.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2523).symm
    injectiveMoment H raw2523step0 = injectiveMoment H raw2523step1 := by
      have heq : raw2523step1 = (fun i j => raw2523step0 (permutation10 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2523step0 permutation10 permutation3
    _ = injectiveMoment H node135 := by rfl

def raw2524 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![-2, 2, -1, 1], ![4, -1, -1, -2]]

def raw2524step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![2, -1, -1], ![1, 1, -2]]

def raw2524step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![1, 1, -2], ![2, -1, -1]]

theorem canonical2524 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2524 = injectiveMoment H node134 := by
  calc
    injectiveMoment H raw2524 = injectiveMoment H raw2524step0 := by
      have heq : raw2524step0 = raw2524.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2524).symm
    injectiveMoment H raw2524step0 = injectiveMoment H raw2524step1 := by
      have heq : raw2524step1 = (fun i j => raw2524step0 (permutation10 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2524step0 permutation10 permutation3
    _ = injectiveMoment H node134 := by rfl

def raw2525 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![-2, 2, 1, -1], ![4, -1, -3, 0]]

def raw2525step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![2, 1, -3], ![1, -1, 0]]

def raw2525step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 2, -3], ![2, -1, -1]]

theorem canonical2525 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2525 = injectiveMoment H node132 := by
  calc
    injectiveMoment H raw2525 = injectiveMoment H raw2525step0 := by
      have heq : raw2525step0 = raw2525.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2525).symm
    injectiveMoment H raw2525step0 = injectiveMoment H raw2525step1 := by
      have heq : raw2525step1 = (fun i j => raw2525step0 (permutation14 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2525step0 permutation14 permutation5
    _ = injectiveMoment H node132 := by rfl

def raw2526 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![-2, 3, -2, 1], ![4, -2, 0, -2]]

def raw2526step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 3, -2], ![2, -2, 0], ![1, 1, -2]]

def raw2526step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 3, -2], ![1, 1, -2], ![2, -2, 0]]

theorem canonical2526 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2526 = injectiveMoment H node136 := by
  calc
    injectiveMoment H raw2526 = injectiveMoment H raw2526step0 := by
      have heq : raw2526step0 = raw2526.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2526).symm
    injectiveMoment H raw2526step0 = injectiveMoment H raw2526step1 := by
      have heq : raw2526step1 = (fun i j => raw2526step0 (permutation10 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2526step0 permutation10 permutation3
    _ = injectiveMoment H node136 := by rfl

def raw2527 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![-1, -1, -1, 3], ![3, 2, -1, -4]]

def raw2527step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![2, -1, -1], ![1, 3, -4]]

def raw2527step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![-2, 1, 1], ![-1, -3, 4]]

def raw2527step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -2, 1], ![1, 1, -2], ![1, 2, -3]]

theorem canonical2527 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2527 = injectiveMoment H node89 := by
  calc
    injectiveMoment H raw2527 = injectiveMoment H raw2527step0 := by
      have heq : raw2527step0 = raw2527.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2527).symm
    injectiveMoment H raw2527step0 = injectiveMoment H raw2527step1 := by
      have heq : raw2527step1 = -raw2527step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2527step0).symm
    injectiveMoment H raw2527step1 = injectiveMoment H raw2527step2 := by
      have heq : raw2527step2 = (fun i j => raw2527step1 (permutation32 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2527step1 permutation32 permutation5
    _ = injectiveMoment H node89 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
