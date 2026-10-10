import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes9
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes14
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes15
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes19
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes21
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes31
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes40
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes41
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes42
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes43
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes44

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw3392 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 1, 0], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, 1, 1, -3]]

theorem canonical3392 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3392 = injectiveMoment H node2016 := by
  rfl

def raw3393 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 1, 0], ![0, 1, -1, 0], ![1, -1, 1, -1], ![1, 1, -1, -1]]

theorem canonical3393 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3393 = injectiveMoment H node2017 := by
  rfl

def raw3394 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 1, 0], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 0, 1, -2]]

def raw3394step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 1, 1], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, 0, 0, -1]]

theorem canonical3394 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3394 = injectiveMoment H node2743 := by
  calc
    injectiveMoment H raw3394 = injectiveMoment H raw3394step0 := by
      have heq : raw3394step0 = (fun i j => raw3394 (permutation78 i) (permutation19 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3394 permutation78 permutation19
    _ = injectiveMoment H node2743 := by rfl

def raw3395 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def raw3395step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 1, 0, 0], ![0, 0, -2, 2], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, 0, 0]]

theorem canonical3395 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3395 = injectiveMoment H node2851 := by
  calc
    injectiveMoment H raw3395 = injectiveMoment H raw3395step0 := by
      have heq : raw3395step0 = (fun i j => raw3395 (permutation60 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3395 permutation60 permutation17
    _ = injectiveMoment H node2851 := by rfl

def raw3396 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 1, 0], ![0, 1, -1, 0], ![2, 0, 0, -2]]

def raw3396step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, 0, 0], ![0, 0, -2, 2], ![0, 0, 2, -2], ![1, -1, 0, 0]]

theorem canonical3396 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3396 = injectiveMoment H node1357 := by
  calc
    injectiveMoment H raw3396 = injectiveMoment H raw3396step0 := by
      have heq : raw3396step0 = (fun i j => raw3396 (permutation16 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3396 permutation16 permutation17
    _ = injectiveMoment H node1357 := by rfl

def raw3397 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 1, 0], ![0, 1, 0, -1], ![0, 0, 1, -1], ![2, 0, -2, 0]]

def raw3397step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 2, 0], ![0, 0, -1, 1], ![0, 2, 0, -2], ![1, 0, -1, 0]]

theorem canonical3397 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3397 = injectiveMoment H node2745 := by
  calc
    injectiveMoment H raw3397 = injectiveMoment H raw3397step0 := by
      have heq : raw3397step0 = (fun i j => raw3397 (permutation60 i) (permutation16 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3397 permutation60 permutation16
    _ = injectiveMoment H node2745 := by rfl

def raw3398 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 1, 0], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, -1, -1, 0]]

def raw3398step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 0, 0]]

theorem canonical3398 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3398 = injectiveMoment H node2613 := by
  calc
    injectiveMoment H raw3398 = injectiveMoment H raw3398step0 := by
      have heq : raw3398step0 = (fun i j => raw3398 (permutation131 i) (permutation24 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3398 permutation131 permutation24
    _ = injectiveMoment H node2613 := by rfl

def raw3399 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 1, 0], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 1, -1, -1]]

def raw3399step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, 0, 1], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, 0, 0, -1]]

theorem canonical3399 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3399 = injectiveMoment H node2629 := by
  calc
    injectiveMoment H raw3399 = injectiveMoment H raw3399step0 := by
      have heq : raw3399step0 = (fun i j => raw3399 (permutation143 i) (permutation25 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3399 permutation143 permutation25
    _ = injectiveMoment H node2629 := by rfl

def raw3400 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 1, 0], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 1, -2, 0]]

theorem canonical3400 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3400 = injectiveMoment H node2018 := by
  rfl

def raw3401 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 0, -1]]

def raw3401step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, -1, 1], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, -1, 0, 0]]

theorem canonical3401 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3401 = injectiveMoment H node2784 := by
  calc
    injectiveMoment H raw3401 = injectiveMoment H raw3401step0 := by
      have heq : raw3401step0 = (fun i j => raw3401 (permutation123 i) (permutation24 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3401 permutation123 permutation24
    _ = injectiveMoment H node2784 := by rfl

def raw3402 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 1, 0], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 0, -1, 0]]

def raw3402step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, -1, 1], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, -1, 0, 0]]

theorem canonical3402 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3402 = injectiveMoment H node2784 := by
  calc
    injectiveMoment H raw3402 = injectiveMoment H raw3402step0 := by
      have heq : raw3402step0 = (fun i j => raw3402 (permutation146 i) (permutation24 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3402 permutation146 permutation24
    _ = injectiveMoment H node2784 := by rfl

def raw3403 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 1, 0], ![0, 1, 0, -1], ![2, 0, -1, -1]]

def raw3403step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, -1, 0, 0]]

theorem canonical3403 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3403 = injectiveMoment H node1264 := by
  calc
    injectiveMoment H raw3403 = injectiveMoment H raw3403step0 := by
      have heq : raw3403step0 = (fun i j => raw3403 (permutation28 i) (permutation24 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3403 permutation28 permutation24
    _ = injectiveMoment H node1264 := by rfl

def raw3404 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 1, 0], ![0, 2, -1, -1], ![2, -1, 0, -1]]

def raw3404step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 2, -1], ![0, 2, -2, 0], ![1, 0, 0, -1]]

theorem canonical3404 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3404 = injectiveMoment H node1008 := by
  calc
    injectiveMoment H raw3404 = injectiveMoment H raw3404step0 := by
      have heq : raw3404step0 = (fun i j => raw3404 (permutation25 i) (permutation25 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3404 permutation25 permutation25
    _ = injectiveMoment H node1008 := by rfl

def raw3405 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 1, 0], ![1, 0, -2, 1], ![1, 1, 1, -3]]

def raw3405step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 1, -1, 0], ![-1, 0, 2, -1], ![-1, -1, -1, 3]]

def raw3405step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 2, -1], ![0, 2, 0, -2], ![1, 0, -1, 0]]

theorem canonical3405 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3405 = injectiveMoment H node946 := by
  calc
    injectiveMoment H raw3405 = injectiveMoment H raw3405step0 := by
      have heq : raw3405step0 = -raw3405 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3405).symm
    injectiveMoment H raw3405step0 = injectiveMoment H raw3405step1 := by
      have heq : raw3405step1 = (fun i j => raw3405step0 (permutation31 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3405step0 permutation31 permutation15
    _ = injectiveMoment H node946 := by rfl

def raw3406 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 1, 0], ![1, 0, 0, -1], ![1, 1, -1, -1]]

def raw3406step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 0, 1], ![0, 1, 0, -1], ![2, 0, -1, -1]]

def raw3406step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 1, 0], ![0, 1, -1, 0], ![1, 0, 1, -2]]

theorem canonical3406 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3406 = injectiveMoment H node1241 := by
  calc
    injectiveMoment H raw3406 = injectiveMoment H raw3406step0 := by
      have heq : raw3406step0 = raw3406.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3406).symm
    injectiveMoment H raw3406step0 = injectiveMoment H raw3406step1 := by
      have heq : raw3406step1 = (fun i j => raw3406step0 (permutation30 i) (permutation24 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3406step0 permutation30 permutation24
    _ = injectiveMoment H node1241 := by rfl

def raw3407 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 1, 0], ![1, 0, 1, -2], ![1, 1, -2, 0]]

def raw3407step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 1, -1, 0], ![-1, 0, -1, 2], ![-1, -1, 2, 0]]

def raw3407step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 2, -1], ![0, 2, -2, 0], ![1, 0, 0, -1]]

theorem canonical3407 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3407 = injectiveMoment H node1008 := by
  calc
    injectiveMoment H raw3407 = injectiveMoment H raw3407step0 := by
      have heq : raw3407step0 = -raw3407 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3407).symm
    injectiveMoment H raw3407step0 = injectiveMoment H raw3407step1 := by
      have heq : raw3407step1 = (fun i j => raw3407step0 (permutation31 i) (permutation16 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3407step0 permutation31 permutation16
    _ = injectiveMoment H node1008 := by rfl

def raw3408 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 1, 0], ![1, 1, -2, 0], ![1, 0, 1, -2]]

def raw3408step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 1, -1, 0], ![-1, -1, 2, 0], ![-1, 0, -1, 2]]

def raw3408step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 2, -1], ![0, 2, -2, 0], ![1, 0, 0, -1]]

theorem canonical3408 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3408 = injectiveMoment H node1008 := by
  calc
    injectiveMoment H raw3408 = injectiveMoment H raw3408step0 := by
      have heq : raw3408step0 = -raw3408 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3408).symm
    injectiveMoment H raw3408step0 = injectiveMoment H raw3408step1 := by
      have heq : raw3408step1 = (fun i j => raw3408step0 (permutation25 i) (permutation16 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3408step0 permutation25 permutation16
    _ = injectiveMoment H node1008 := by rfl

def raw3409 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 1, 0], ![1, 1, -1, -1], ![1, 0, 0, -1]]

def raw3409step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 1, 0], ![0, 1, -1, 0], ![2, 0, -1, -1]]

def raw3409step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 1, 0], ![0, 1, -1, 0], ![1, 0, 1, -2]]

theorem canonical3409 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3409 = injectiveMoment H node1241 := by
  calc
    injectiveMoment H raw3409 = injectiveMoment H raw3409step0 := by
      have heq : raw3409step0 = raw3409.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3409).symm
    injectiveMoment H raw3409step0 = injectiveMoment H raw3409step1 := by
      have heq : raw3409step1 = (fun i j => raw3409step0 (permutation30 i) (permutation30 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3409step0 permutation30 permutation30
    _ = injectiveMoment H node1241 := by rfl

def raw3410 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 2, -1], ![0, 1, -2, 1], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def raw3410step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -2, 0, 2], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -2, 1]]

theorem canonical3410 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3410 = injectiveMoment H node2824 := by
  calc
    injectiveMoment H raw3410 = injectiveMoment H raw3410step0 := by
      have heq : raw3410step0 = (fun i j => raw3410 (permutation60 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3410 permutation60 permutation15
    _ = injectiveMoment H node2824 := by rfl

def raw3411 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 2, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, -1, -1, 0]]

def raw3411step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 2, -1, -1], ![2, -1, -1, 0]]

theorem canonical3411 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3411 = injectiveMoment H node2015 := by
  calc
    injectiveMoment H raw3411 = injectiveMoment H raw3411step0 := by
      have heq : raw3411step0 = (fun i j => raw3411 (permutation41 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3411 permutation41 permutation11
    _ = injectiveMoment H node2015 := by rfl

def raw3412 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 2, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 1, -2, 0]]

theorem canonical3412 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3412 = injectiveMoment H node2021 := by
  rfl

def raw3413 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 2, -1], ![0, 1, 0, -1], ![1, 0, -2, 1], ![1, 0, 0, -1]]

def raw3413step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 1, -2, 1], ![0, -1, 0, 1], ![-1, 0, 2, -1], ![-1, 0, 0, 1]]

def raw3413step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, -1, 2, -1], ![0, 2, 0, -2], ![1, 0, -2, 1]]

theorem canonical3413 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3413 = injectiveMoment H node2752 := by
  calc
    injectiveMoment H raw3413 = injectiveMoment H raw3413step0 := by
      have heq : raw3413step0 = -raw3413 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3413).symm
    injectiveMoment H raw3413step0 = injectiveMoment H raw3413step1 := by
      have heq : raw3413step1 = (fun i j => raw3413step0 (permutation102 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3413step0 permutation102 permutation15
    _ = injectiveMoment H node2752 := by rfl

def raw3414 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 2, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, -1, 0]]

def raw3414step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, -1, 0, 0]]

theorem canonical3414 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3414 = injectiveMoment H node2609 := by
  calc
    injectiveMoment H raw3414 = injectiveMoment H raw3414step0 := by
      have heq : raw3414step0 = (fun i j => raw3414 (permutation72 i) (permutation19 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3414 permutation72 permutation19
    _ = injectiveMoment H node2609 := by rfl

def raw3415 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 2, -1], ![0, 1, 0, -1], ![2, 0, -2, 0]]

def raw3415step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 2, -2, 0], ![1, -1, 0, 0]]

theorem canonical3415 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3415 = injectiveMoment H node1057 := by
  calc
    injectiveMoment H raw3415 = injectiveMoment H raw3415step0 := by
      have heq : raw3415step0 = (fun i j => raw3415 (permutation19 i) (permutation19 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3415 permutation19 permutation19
    _ = injectiveMoment H node1057 := by rfl

def raw3416 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 2, -1], ![0, 1, 1, -2], ![2, 0, -3, 1]]

def raw3416step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -2, 2, 0], ![0, 2, 1, -3], ![1, 0, -2, 1]]

theorem canonical3416 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3416 = injectiveMoment H node1235 := by
  calc
    injectiveMoment H raw3416 = injectiveMoment H raw3416step0 := by
      have heq : raw3416step0 = (fun i j => raw3416 (permutation16 i) (permutation16 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3416 permutation16 permutation16
    _ = injectiveMoment H node1235 := by rfl

def raw3417 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 2, -1], ![0, 2, -3, 1], ![2, -1, 1, -2]]

def raw3417step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 1, -2, 1], ![0, -2, 3, -1], ![-2, 1, -1, 2]]

def raw3417step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 2, -2, 0], ![1, -2, 2, -1], ![1, 0, 1, -2]]

theorem canonical3417 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3417 = injectiveMoment H node602 := by
  calc
    injectiveMoment H raw3417 = injectiveMoment H raw3417step0 := by
      have heq : raw3417step0 = -raw3417 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3417).symm
    injectiveMoment H raw3417step0 = injectiveMoment H raw3417step1 := by
      have heq : raw3417step1 = (fun i j => raw3417step0 (permutation22 i) (permutation16 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3417step0 permutation22 permutation16
    _ = injectiveMoment H node602 := by rfl

def raw3418 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 2, -1], ![0, 2, -1, -1], ![2, -1, -1, 0]]

theorem canonical3418 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3418 = injectiveMoment H node609 := by
  rfl

def raw3419 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 2, -1], ![1, -1, 0, 0], ![1, 2, -2, -1]]

def raw3419step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, -1, 2], ![0, 2, 0, -2], ![2, -1, 0, -1]]

def raw3419step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 2, -1], ![0, 2, 0, -2], ![1, 0, -2, 1]]

theorem canonical3419 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3419 = injectiveMoment H node1010 := by
  calc
    injectiveMoment H raw3419 = injectiveMoment H raw3419step0 := by
      have heq : raw3419step0 = raw3419.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3419).symm
    injectiveMoment H raw3419step0 = injectiveMoment H raw3419step1 := by
      have heq : raw3419step1 = (fun i j => raw3419step0 (permutation20 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3419step0 permutation20 permutation23
    _ = injectiveMoment H node1010 := by rfl

def raw3420 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 2, -1], ![1, 0, -2, 1], ![1, 1, 0, -2]]

def raw3420step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 1, -2, 1], ![-1, 0, 2, -1], ![-1, -1, 0, 2]]

def raw3420step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 2, -1], ![0, 2, 0, -2], ![1, 0, -2, 1]]

theorem canonical3420 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3420 = injectiveMoment H node1010 := by
  calc
    injectiveMoment H raw3420 = injectiveMoment H raw3420step0 := by
      have heq : raw3420step0 = -raw3420 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3420).symm
    injectiveMoment H raw3420step0 = injectiveMoment H raw3420step1 := by
      have heq : raw3420step1 = (fun i j => raw3420step0 (permutation31 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3420step0 permutation31 permutation15
    _ = injectiveMoment H node1010 := by rfl

def raw3421 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 2, -1], ![1, 0, -1, 0], ![1, 1, -1, -1]]

def raw3421step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 0, 1], ![0, 2, -1, -1], ![2, -1, 0, -1]]

def raw3421step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 1, 0, -1], ![0, -2, 1, 1], ![-2, 1, 0, 1]]

def raw3421step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 1, 0], ![0, 1, 1, -2], ![1, 1, -2, 0]]

theorem canonical3421 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3421 = injectiveMoment H node1000 := by
  calc
    injectiveMoment H raw3421 = injectiveMoment H raw3421step0 := by
      have heq : raw3421step0 = raw3421.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3421).symm
    injectiveMoment H raw3421step0 = injectiveMoment H raw3421step1 := by
      have heq : raw3421step1 = -raw3421step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3421step0).symm
    injectiveMoment H raw3421step1 = injectiveMoment H raw3421step2 := by
      have heq : raw3421step2 = (fun i j => raw3421step1 (permutation10 i) (permutation26 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3421step1 permutation10 permutation26
    _ = injectiveMoment H node1000 := by rfl

def raw3422 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 2, -1], ![1, 0, 0, -1], ![1, 1, -2, 0]]

def raw3422step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 1, 0], ![0, 2, -2, 0], ![1, 0, 1, -2]]

theorem canonical3422 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3422 = injectiveMoment H node1002 := by
  calc
    injectiveMoment H raw3422 = injectiveMoment H raw3422step0 := by
      have heq : raw3422step0 = (fun i j => raw3422 (permutation17 i) (permutation19 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3422 permutation17 permutation19
    _ = injectiveMoment H node1002 := by rfl

def raw3423 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 2, -1], ![1, 0, 1, -2], ![1, 1, -3, 1]]

def raw3423step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 1, -2, 1], ![-1, 0, -1, 2], ![-1, -1, 3, -1]]

def raw3423step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 2, -1], ![0, 2, -2, 0], ![1, 0, 1, -2]]

theorem canonical3423 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3423 = injectiveMoment H node944 := by
  calc
    injectiveMoment H raw3423 = injectiveMoment H raw3423step0 := by
      have heq : raw3423step0 = -raw3423 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3423).symm
    injectiveMoment H raw3423step0 = injectiveMoment H raw3423step1 := by
      have heq : raw3423step1 = (fun i j => raw3423step0 (permutation31 i) (permutation16 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3423step0 permutation31 permutation16
    _ = injectiveMoment H node944 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
