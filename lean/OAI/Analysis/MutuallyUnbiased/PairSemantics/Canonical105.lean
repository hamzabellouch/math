import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes6
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes12
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes14
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes15
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes18
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes19
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes21
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes23
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes25
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes27
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes31
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes39
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes40
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes41
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes42
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes44
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes45
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes46
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes47
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes49

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw3360 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, -1, 2], ![0, 2, -2, 0], ![1, -1, 0, 0], ![1, 0, 3, -4]]

theorem canonical3360 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3360 = injectiveMoment H node2006 := by
  rfl

def raw3361 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, -1, 2], ![0, 2, -2, 0], ![2, -1, 3, -4]]

def raw3361step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 2, -1], ![0, -1, -2, 3], ![2, 2, 0, -4]]

def raw3361step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 1, -2, 1], ![0, 1, 2, -3], ![-2, -2, 0, 4]]

def raw3361step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 1, -2, 1], ![0, 1, 2, -3], ![2, 0, 0, -2]]

theorem canonical3361 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3361 = injectiveMoment H node401 := by
  calc
    injectiveMoment H raw3361 = injectiveMoment H raw3361step0 := by
      have heq : raw3361step0 = raw3361.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3361).symm
    injectiveMoment H raw3361step0 = injectiveMoment H raw3361step1 := by
      have heq : raw3361step1 = -raw3361step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3361step0).symm
    injectiveMoment H raw3361step1 = injectiveMoment H raw3361step2 := by
      have heq : raw3361step2 = (fun i j => raw3361step1 (permutation30 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3361step1 permutation30 permutation9
    _ = injectiveMoment H node401 := by rfl

def raw3362 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, -1, 2], ![0, 2, 2, -4], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def raw3362step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 1, 1, -2], ![0, -2, -2, 4], ![-1, 1, 0, 0], ![-1, 0, 1, 0]]

def raw3362step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 1, 0, -2]]

theorem canonical3362 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3362 = injectiveMoment H node1477 := by
  calc
    injectiveMoment H raw3362 = injectiveMoment H raw3362step0 := by
      have heq : raw3362step0 = -raw3362 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3362).symm
    injectiveMoment H raw3362step0 = injectiveMoment H raw3362step1 := by
      have heq : raw3362step1 = (fun i j => raw3362step0 (permutation85 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3362step0 permutation85 permutation17
    _ = injectiveMoment H node1477 := by rfl

def raw3363 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, -1, 2], ![1, 0, -1, 0], ![1, 1, 2, -4]]

def raw3363step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 1, 1, -2], ![-1, 0, 1, 0], ![-1, -1, -2, 4]]

def raw3363step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, 1, 0, -2]]

theorem canonical3363 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3363 = injectiveMoment H node771 := by
  calc
    injectiveMoment H raw3363 = injectiveMoment H raw3363step0 := by
      have heq : raw3363step0 = -raw3363 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3363).symm
    injectiveMoment H raw3363step0 = injectiveMoment H raw3363step1 := by
      have heq : raw3363step1 = (fun i j => raw3363step0 (permutation28 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3363step0 permutation28 permutation17
    _ = injectiveMoment H node771 := by rfl

def raw3364 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, -1, 2], ![1, 0, 0, -1], ![1, 1, 1, -3]]

def raw3364step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 1, 1, -2], ![-1, 0, 0, 1], ![-1, -1, -1, 3]]

def raw3364step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, -1, 1], ![0, 0, 2, -2], ![1, 1, 0, -2]]

theorem canonical3364 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3364 = injectiveMoment H node959 := by
  calc
    injectiveMoment H raw3364 = injectiveMoment H raw3364step0 := by
      have heq : raw3364step0 = -raw3364 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3364).symm
    injectiveMoment H raw3364step0 = injectiveMoment H raw3364step1 := by
      have heq : raw3364step1 = (fun i j => raw3364step0 (permutation31 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3364step0 permutation31 permutation17
    _ = injectiveMoment H node959 := by rfl

def raw3365 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, -1, 2], ![1, 0, 3, -4], ![1, 1, -2, 0]]

def raw3365step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 1, 1, -2], ![-1, 0, -3, 4], ![-1, -1, 2, 0]]

def raw3365step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![0, -1, -3, 4], ![0, 2, 0, -2], ![1, 0, 1, -2]]

theorem canonical3365 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3365 = injectiveMoment H node1155 := by
  calc
    injectiveMoment H raw3365 = injectiveMoment H raw3365step0 := by
      have heq : raw3365step0 = -raw3365 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3365).symm
    injectiveMoment H raw3365step0 = injectiveMoment H raw3365step1 := by
      have heq : raw3365step1 = (fun i j => raw3365step0 (permutation31 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3365step0 permutation31 permutation15
    _ = injectiveMoment H node1155 := by rfl

def raw3366 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, -1, 2], ![1, 1, -2, 0], ![1, 0, 3, -4]]

def raw3366step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 1, 1, -2], ![-1, -1, 2, 0], ![-1, 0, -3, 4]]

def raw3366step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![0, -1, -3, 4], ![0, 2, 0, -2], ![1, 0, 1, -2]]

theorem canonical3366 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3366 = injectiveMoment H node1155 := by
  calc
    injectiveMoment H raw3366 = injectiveMoment H raw3366step0 := by
      have heq : raw3366step0 = -raw3366 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3366).symm
    injectiveMoment H raw3366step0 = injectiveMoment H raw3366step1 := by
      have heq : raw3366step1 = (fun i j => raw3366step0 (permutation25 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3366step0 permutation25 permutation15
    _ = injectiveMoment H node1155 := by rfl

def raw3367 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 0, 1], ![0, -1, 0, 1], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 1, 2, -4]]

def raw3367step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 1, 0, -1], ![0, 1, 0, -1], ![0, -1, 1, 0], ![-1, 0, 1, 0], ![-1, -1, -2, 4]]

def raw3367step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -1, 0, 0], ![1, 0, -1, 0]]

theorem canonical3367 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3367 = injectiveMoment H node2935 := by
  calc
    injectiveMoment H raw3367 = injectiveMoment H raw3367step0 := by
      have heq : raw3367step0 = -raw3367 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3367).symm
    injectiveMoment H raw3367step0 = injectiveMoment H raw3367step1 := by
      have heq : raw3367step1 = (fun i j => raw3367step0 (permutation338 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3367step0 permutation338 permutation21
    _ = injectiveMoment H node2935 := by rfl

def raw3368 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 0, 1], ![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 1, -1, 0], ![2, 1, 1, -4]]

def raw3368step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 1, 0, -1], ![0, 1, -1, 0], ![0, 0, 1, -1], ![0, -1, 1, 0], ![-2, -1, -1, 4]]

def raw3368step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, 0, 0, -2]]

theorem canonical3368 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3368 = injectiveMoment H node2908 := by
  calc
    injectiveMoment H raw3368 = injectiveMoment H raw3368step0 := by
      have heq : raw3368step0 = -raw3368 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3368).symm
    injectiveMoment H raw3368step0 = injectiveMoment H raw3368step1 := by
      have heq : raw3368step1 = (fun i j => raw3368step0 (permutation409 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3368step0 permutation409 permutation9
    _ = injectiveMoment H node2908 := by rfl

def raw3369 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 0, 1], ![0, -1, 1, 0], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, 0, 1, -3]]

def raw3369step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 1, 0, -1], ![0, 1, -1, 0], ![0, -1, 1, 0], ![0, -1, 1, 0], ![-2, 0, -1, 3]]

def raw3369step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, 0, 0, -2]]

theorem canonical3369 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3369 = injectiveMoment H node2964 := by
  calc
    injectiveMoment H raw3369 = injectiveMoment H raw3369step0 := by
      have heq : raw3369step0 = -raw3369 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3369).symm
    injectiveMoment H raw3369step0 = injectiveMoment H raw3369step1 := by
      have heq : raw3369step1 = (fun i j => raw3369step0 (permutation360 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3369step0 permutation360 permutation11
    _ = injectiveMoment H node2964 := by rfl

def raw3370 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 0, 1], ![0, -1, 1, 0], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 1, 1, -3]]

theorem canonical3370 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3370 = injectiveMoment H node3161 := by
  rfl

def raw3371 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, 2, 2, -5]]

def raw3371step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 1, 0, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![-1, 1, 0, 0], ![-1, -2, -2, 5]]

def raw3371step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 0, 0, -1]]

theorem canonical3371 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3371 = injectiveMoment H node2868 := by
  calc
    injectiveMoment H raw3371 = injectiveMoment H raw3371step0 := by
      have heq : raw3371step0 = -raw3371 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3371).symm
    injectiveMoment H raw3371step0 = injectiveMoment H raw3371step1 := by
      have heq : raw3371step1 = (fun i j => raw3371step0 (permutation326 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3371step0 permutation326 permutation23
    _ = injectiveMoment H node2868 := by rfl

def raw3372 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 1, 2, -4]]

def raw3372step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 1, 0, -1], ![0, 0, 1, -1], ![0, -1, 1, 0], ![-1, 1, 0, 0], ![-1, -1, -2, 4]]

def raw3372step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, 0, -1, 0], ![1, 0, 0, -1]]

theorem canonical3372 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3372 = injectiveMoment H node2919 := by
  calc
    injectiveMoment H raw3372 = injectiveMoment H raw3372step0 := by
      have heq : raw3372step0 = -raw3372 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3372).symm
    injectiveMoment H raw3372step0 = injectiveMoment H raw3372step1 := by
      have heq : raw3372step1 = (fun i j => raw3372step0 (permutation399 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3372step0 permutation399 permutation21
    _ = injectiveMoment H node2919 := by rfl

def raw3373 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 0, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![0, 2, 2, -4]]

def raw3373step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 1, 0, -1], ![0, 0, 1, -1], ![-1, 1, 0, 0], ![-1, 0, 1, 0], ![0, -2, -2, 4]]

def raw3373step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 0, -1]]

theorem canonical3373 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3373 = injectiveMoment H node2881 := by
  calc
    injectiveMoment H raw3373 = injectiveMoment H raw3373step0 := by
      have heq : raw3373step0 = -raw3373 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3373).symm
    injectiveMoment H raw3373step0 = injectiveMoment H raw3373step1 := by
      have heq : raw3373step1 = (fun i j => raw3373step0 (permutation328 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3373step0 permutation328 permutation17
    _ = injectiveMoment H node2881 := by rfl

def raw3374 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 0, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 2, -3]]

def raw3374step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 1, 0, -1], ![0, -1, 1, 0], ![0, -1, 1, 0], ![-1, 1, 0, 0], ![-1, 0, -2, 3]]

def raw3374step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, 0, -1, 0], ![1, 0, -1, 0]]

theorem canonical3374 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3374 = injectiveMoment H node2970 := by
  calc
    injectiveMoment H raw3374 = injectiveMoment H raw3374step0 := by
      have heq : raw3374step0 = -raw3374 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3374).symm
    injectiveMoment H raw3374step0 = injectiveMoment H raw3374step1 := by
      have heq : raw3374step1 = (fun i j => raw3374step0 (permutation398 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3374step0 permutation398 permutation21
    _ = injectiveMoment H node2970 := by rfl

def raw3375 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 0, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, -1, 2, -3]]

def raw3375step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 1, 0, -1], ![0, -1, 1, 0], ![0, -1, 1, 0], ![-2, 1, -2, 3]]

def raw3375step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, 0, 0, -2]]

theorem canonical3375 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3375 = injectiveMoment H node1503 := by
  calc
    injectiveMoment H raw3375 = injectiveMoment H raw3375step0 := by
      have heq : raw3375step0 = -raw3375 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3375).symm
    injectiveMoment H raw3375step0 = injectiveMoment H raw3375step1 := by
      have heq : raw3375step1 = (fun i j => raw3375step0 (permutation136 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3375step0 permutation136 permutation11
    _ = injectiveMoment H node1503 := by rfl

def raw3376 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 0, 1], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, 1, 2, -4]]

def raw3376step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 1, 0, -1], ![0, -1, 1, 0], ![-1, 1, 1, -1], ![-1, -1, -2, 4]]

def raw3376step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -1, 1, -1], ![1, 0, -1, 0]]

theorem canonical3376 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3376 = injectiveMoment H node1603 := by
  calc
    injectiveMoment H raw3376 = injectiveMoment H raw3376step0 := by
      have heq : raw3376step0 = -raw3376 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3376).symm
    injectiveMoment H raw3376step0 = injectiveMoment H raw3376step1 := by
      have heq : raw3376step1 = (fun i j => raw3376step0 (permutation134 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3376step0 permutation134 permutation21
    _ = injectiveMoment H node1603 := by rfl

def raw3377 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 0, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, -1, 0], ![0, 1, 2, -3]]

def raw3377step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 1, 0, -1], ![0, -1, 1, 0], ![-1, 1, 0, 0], ![-1, 0, 1, 0], ![0, -1, -2, 3]]

def raw3377step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -1, 0]]

theorem canonical3377 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3377 = injectiveMoment H node3018 := by
  calc
    injectiveMoment H raw3377 = injectiveMoment H raw3377step0 := by
      have heq : raw3377step0 = -raw3377 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3377).symm
    injectiveMoment H raw3377step0 = injectiveMoment H raw3377step1 := by
      have heq : raw3377step1 = (fun i j => raw3377step0 (permutation320 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3377step0 permutation320 permutation23
    _ = injectiveMoment H node3018 := by rfl

def raw3378 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 0, 1], ![1, 0, -2, 1], ![1, 1, 2, -4]]

def raw3378step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 1, 0, -1], ![-1, 0, 2, -1], ![-1, -1, -2, 4]]

def raw3378step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 2, -2], ![0, 2, -1, -1], ![1, 0, 0, -1]]

theorem canonical3378 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3378 = injectiveMoment H node774 := by
  calc
    injectiveMoment H raw3378 = injectiveMoment H raw3378step0 := by
      have heq : raw3378step0 = -raw3378 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3378).symm
    injectiveMoment H raw3378step0 = injectiveMoment H raw3378step1 := by
      have heq : raw3378step1 = (fun i j => raw3378step0 (permutation28 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3378step0 permutation28 permutation17
    _ = injectiveMoment H node774 := by rfl

def raw3379 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 0, 1], ![1, 0, -1, 0], ![1, 1, 1, -3]]

def raw3379step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 1, 0, -1], ![-1, 0, 1, 0], ![-1, -1, -1, 3]]

def raw3379step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, 0, 0, -1]]

theorem canonical3379 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3379 = injectiveMoment H node974 := by
  calc
    injectiveMoment H raw3379 = injectiveMoment H raw3379step0 := by
      have heq : raw3379step0 = -raw3379 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3379).symm
    injectiveMoment H raw3379step0 = injectiveMoment H raw3379step1 := by
      have heq : raw3379step1 = (fun i j => raw3379step0 (permutation28 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3379step0 permutation28 permutation17
    _ = injectiveMoment H node974 := by rfl

def raw3380 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 0, 1], ![1, 0, 1, -2], ![1, 1, -1, -1]]

def raw3380step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 1, 0, -1], ![-1, 0, -1, 2], ![-1, -1, 1, 1]]

def raw3380step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, -1, -1, 1]]

theorem canonical3380 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3380 = injectiveMoment H node1265 := by
  calc
    injectiveMoment H raw3380 = injectiveMoment H raw3380step0 := by
      have heq : raw3380step0 = -raw3380 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3380).symm
    injectiveMoment H raw3380step0 = injectiveMoment H raw3380step1 := by
      have heq : raw3380step1 = (fun i j => raw3380step0 (permutation21 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3380step0 permutation21 permutation23
    _ = injectiveMoment H node1265 := by rfl

def raw3381 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 1, 0], ![0, 0, -1, 1], ![1, 0, -1, 0], ![1, 1, 1, -3]]

def raw3381step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 1, -1, 0], ![0, 0, 1, -1], ![-1, 0, 1, 0], ![-1, -1, -1, 3]]

def raw3381step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, 0, -1, 0]]

theorem canonical3381 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3381 = injectiveMoment H node2533 := by
  calc
    injectiveMoment H raw3381 = injectiveMoment H raw3381step0 := by
      have heq : raw3381step0 = -raw3381 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3381).symm
    injectiveMoment H raw3381step0 = injectiveMoment H raw3381step1 := by
      have heq : raw3381step1 = (fun i j => raw3381step0 (permutation149 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3381step0 permutation149 permutation15
    _ = injectiveMoment H node2533 := by rfl

def raw3382 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 1, 0], ![0, 0, 0, 0], ![0, 1, -1, 0], ![2, 0, 0, -2]]

def raw3382step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 1, 0], ![0, 1, -1, 0], ![2, 0, 0, -2]]

def raw3382step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, 0, 0], ![0, 0, -2, 2], ![0, 0, 2, -2], ![1, -1, 0, 0]]

theorem canonical3382 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3382 = injectiveMoment H node1357 := by
  calc
    injectiveMoment H raw3382 = injectiveMoment H raw3382step0 := by
      have hz : ∀ j, raw3382 (permutation80 0) j = 0 := by decide +kernel
      have heq : raw3382step0 = (fun i j => raw3382 (permutation80 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw3382 permutation80 hz
    injectiveMoment H raw3382step0 = injectiveMoment H raw3382step1 := by
      have heq : raw3382step1 = (fun i j => raw3382step0 (permutation16 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3382step0 permutation16 permutation17
    _ = injectiveMoment H node1357 := by rfl

def raw3383 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 1, 0], ![0, 0, 0, 0], ![0, 1, 0, -1], ![2, 0, -1, -1]]

def raw3383step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 1, 0], ![0, 1, 0, -1], ![2, 0, -1, -1]]

def raw3383step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, -1, 0, 0]]

theorem canonical3383 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3383 = injectiveMoment H node1264 := by
  calc
    injectiveMoment H raw3383 = injectiveMoment H raw3383step0 := by
      have hz : ∀ j, raw3383 (permutation80 0) j = 0 := by decide +kernel
      have heq : raw3383step0 = (fun i j => raw3383 (permutation80 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw3383 permutation80 hz
    injectiveMoment H raw3383step0 = injectiveMoment H raw3383step1 := by
      have heq : raw3383step1 = (fun i j => raw3383step0 (permutation28 i) (permutation24 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3383step0 permutation28 permutation24
    _ = injectiveMoment H node1264 := by rfl

def raw3384 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 1, 0], ![0, 0, 0, 0], ![1, 0, 0, -1], ![1, 1, -1, -1]]

def raw3384step0 : Matrix (Fin 4) (Fin 5) ℤ := ![![-2, 0, 0, 1, 1], ![0, -1, 0, 0, 1], ![0, 1, 0, 0, -1], ![2, 0, 0, -1, -1]]

def raw3384step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 0, 1], ![0, 1, 0, -1], ![2, 0, -1, -1]]

def raw3384step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 1, 0], ![0, 1, -1, 0], ![1, 0, 1, -2]]

theorem canonical3384 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3384 = injectiveMoment H node1241 := by
  calc
    injectiveMoment H raw3384 = injectiveMoment H raw3384step0 := by
      have heq : raw3384step0 = raw3384.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3384).symm
    injectiveMoment H raw3384step0 = injectiveMoment H raw3384step1 := by
      have hz : ∀ i, raw3384step0 i (permutation80 0) = 0 := by decide +kernel
      have heq : raw3384step1 = (fun i j => raw3384step0 i (permutation80 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw3384step0 permutation80 hz
    injectiveMoment H raw3384step1 = injectiveMoment H raw3384step2 := by
      have heq : raw3384step2 = (fun i j => raw3384step1 (permutation30 i) (permutation24 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3384step1 permutation30 permutation24
    _ = injectiveMoment H node1241 := by rfl

def raw3385 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, 0, -2, 0]]

def raw3385step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 2, 0], ![0, 0, -1, 1], ![0, 2, 0, -2], ![1, 0, -1, 0]]

theorem canonical3385 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3385 = injectiveMoment H node2745 := by
  calc
    injectiveMoment H raw3385 = injectiveMoment H raw3385step0 := by
      have heq : raw3385step0 = (fun i j => raw3385 (permutation58 i) (permutation16 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3385 permutation58 permutation16
    _ = injectiveMoment H node2745 := by rfl

def raw3386 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 1, 0], ![0, 0, 1, -1], ![1, 0, -1, 0], ![1, 1, -1, -1]]

def raw3386step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 1, -1, 0], ![0, 0, -1, 1], ![-1, 0, 1, 0], ![-1, -1, 1, 1]]

def raw3386step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, 0, 1], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, 0, 0, -1]]

theorem canonical3386 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3386 = injectiveMoment H node2629 := by
  calc
    injectiveMoment H raw3386 = injectiveMoment H raw3386step0 := by
      have heq : raw3386step0 = -raw3386 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3386).symm
    injectiveMoment H raw3386step0 = injectiveMoment H raw3386step1 := by
      have heq : raw3386step1 = (fun i j => raw3386step0 (permutation149 i) (permutation16 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3386step0 permutation149 permutation16
    _ = injectiveMoment H node2629 := by rfl

def raw3387 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 1, 0], ![0, 0, 1, -1], ![1, 0, 0, -1], ![1, 1, -2, 0]]

def raw3387step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 1, -1, 0], ![0, 0, -1, 1], ![-1, 0, 0, 1], ![-1, -1, 2, 0]]

def raw3387step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, 0, 0, -1]]

theorem canonical3387 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3387 = injectiveMoment H node2583 := by
  calc
    injectiveMoment H raw3387 = injectiveMoment H raw3387step0 := by
      have heq : raw3387step0 = -raw3387 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3387).symm
    injectiveMoment H raw3387step0 = injectiveMoment H raw3387step1 := by
      have heq : raw3387step1 = (fun i j => raw3387step0 (permutation149 i) (permutation16 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3387step0 permutation149 permutation16
    _ = injectiveMoment H node2583 := by rfl

def raw3388 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 1, 0], ![0, 1, -1, 0], ![0, 0, 0, 0], ![2, 0, 0, -2]]

def raw3388step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 1, 0], ![0, 1, -1, 0], ![2, 0, 0, -2]]

def raw3388step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, 0, 0], ![0, 0, -2, 2], ![0, 0, 2, -2], ![1, -1, 0, 0]]

theorem canonical3388 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3388 = injectiveMoment H node1357 := by
  calc
    injectiveMoment H raw3388 = injectiveMoment H raw3388step0 := by
      have hz : ∀ j, raw3388 (permutation104 0) j = 0 := by decide +kernel
      have heq : raw3388step0 = (fun i j => raw3388 (permutation104 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw3388 permutation104 hz
    injectiveMoment H raw3388step0 = injectiveMoment H raw3388step1 := by
      have heq : raw3388step1 = (fun i j => raw3388step0 (permutation16 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3388step0 permutation16 permutation17
    _ = injectiveMoment H node1357 := by rfl

def raw3389 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 1, 0], ![0, 1, -1, 0], ![0, 0, 1, -1], ![2, 0, -1, -1]]

def raw3389step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 1, -1, 0], ![0, -1, 1, 0], ![0, 0, -1, 1], ![-2, 0, 1, 1]]

def raw3389step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 1, 1], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, 0, 0, -1]]

theorem canonical3389 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3389 = injectiveMoment H node2743 := by
  calc
    injectiveMoment H raw3389 = injectiveMoment H raw3389step0 := by
      have heq : raw3389step0 = -raw3389 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3389).symm
    injectiveMoment H raw3389step0 = injectiveMoment H raw3389step1 := by
      have heq : raw3389step1 = (fun i j => raw3389step0 (permutation102 i) (permutation16 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3389step0 permutation102 permutation16
    _ = injectiveMoment H node2743 := by rfl

def raw3390 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 1, 0], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, -1, 1, -2]]

def raw3390step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 1, 0], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, 0, 0, -2]]

theorem canonical3390 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3390 = injectiveMoment H node1746 := by
  calc
    injectiveMoment H raw3390 = injectiveMoment H raw3390step0 := by
      have heq : raw3390step0 = (fun i j => raw3390 (permutation136 i) (permutation30 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3390 permutation136 permutation30
    _ = injectiveMoment H node1746 := by rfl

def raw3391 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 1, 0], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, -1, 0, -1]]

def raw3391step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 1, -1, 0], ![0, -1, 1, 0], ![0, -1, 0, 1], ![-2, 1, 0, 1]]

def raw3391step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 1, 1], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, 0, 0, -1]]

theorem canonical3391 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3391 = injectiveMoment H node2743 := by
  calc
    injectiveMoment H raw3391 = injectiveMoment H raw3391step0 := by
      have heq : raw3391step0 = -raw3391 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3391).symm
    injectiveMoment H raw3391step0 = injectiveMoment H raw3391step1 := by
      have heq : raw3391step1 = (fun i j => raw3391step0 (permutation78 i) (permutation22 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3391step0 permutation78 permutation22
    _ = injectiveMoment H node2743 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
