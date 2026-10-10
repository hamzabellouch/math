import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes0
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes2
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes10
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes15
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes37
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes44
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes45
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes48
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes51
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes52
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes53
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes54

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw8416 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, -1, 2, -1], ![0, 2, 1, -3], ![0, 0, -3, 3]]

def raw8416step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 1, -2, 1], ![0, -2, -1, 3], ![0, 0, 3, -3]]

def raw8416step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![1, -2, 1], ![-2, -1, 3], ![0, 3, -3]]

def raw8416step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 3, -3], ![1, -2, 1], ![1, 0, -1]]

theorem canonical8416 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8416 = injectiveMoment H node187 := by
  calc
    injectiveMoment H raw8416 = injectiveMoment H raw8416step0 := by
      have heq : raw8416step0 = -raw8416 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8416).symm
    injectiveMoment H raw8416step0 = injectiveMoment H raw8416step1 := by
      have hz : ∀ i, raw8416step0 i (permutation9 0) = 0 := by decide +kernel
      have heq : raw8416step1 = (fun i j => raw8416step0 i (permutation9 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8416step0 permutation9 hz
    injectiveMoment H raw8416step1 = injectiveMoment H raw8416step2 := by
      have heq : raw8416step2 = (fun i j => raw8416step1 (permutation26 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8416step1 permutation26 permutation3
    _ = injectiveMoment H node187 := by rfl

def raw8417 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, -1, 3, -2], ![0, 2, -3, 1]]

def raw8417step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 0, 0], ![-1, -1, 2], ![0, 3, -3], ![1, -2, 1]]

def raw8417step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 3, -3], ![1, -2, 1]]

theorem canonical8417 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8417 = injectiveMoment H node63 := by
  calc
    injectiveMoment H raw8417 = injectiveMoment H raw8417step0 := by
      have heq : raw8417step0 = raw8417.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw8417).symm
    injectiveMoment H raw8417step0 = injectiveMoment H raw8417step1 := by
      have hz : ∀ j, raw8417step0 (permutation9 0) j = 0 := by decide +kernel
      have heq : raw8417step1 = (fun i j => raw8417step0 (permutation9 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8417step0 permutation9 hz
    _ = injectiveMoment H node63 := by rfl

def raw8418 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![-1, 0, -1, 2], ![0, 1, -1, 0], ![-1, -1, 2, 0], ![2, 1, 1, -4]]

def raw8418step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 0, 1, -1], ![1, 0, 1, -2], ![0, -1, 1, 0], ![1, 1, -2, 0], ![-2, -1, -1, 4]]

def raw8418step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, 1, -2], ![1, 1, -2, 0]]

theorem canonical8418 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8418 = injectiveMoment H node2915 := by
  calc
    injectiveMoment H raw8418 = injectiveMoment H raw8418step0 := by
      have heq : raw8418step0 = -raw8418 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8418).symm
    injectiveMoment H raw8418step0 = injectiveMoment H raw8418step1 := by
      have heq : raw8418step1 = (fun i j => raw8418step0 (permutation377 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8418step0 permutation377 permutation9
    _ = injectiveMoment H node2915 := by rfl

def raw8419 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![-1, 0, -1, 2], ![1, -1, 0, 0], ![-1, 2, -1, 0], ![1, 0, 3, -4]]

def raw8419step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 0, 1, -1], ![1, 0, 1, -2], ![-1, 1, 0, 0], ![1, -2, 1, 0], ![-1, 0, -3, 4]]

def raw8419step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, -1, -3, 4], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, 0, 0, -1]]

theorem canonical8419 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8419 = injectiveMoment H node3298 := by
  calc
    injectiveMoment H raw8419 = injectiveMoment H raw8419step0 := by
      have heq : raw8419step0 = -raw8419 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8419).symm
    injectiveMoment H raw8419step0 = injectiveMoment H raw8419step1 := by
      have heq : raw8419step1 = (fun i j => raw8419step0 (permutation300 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8419step0 permutation300 permutation15
    _ = injectiveMoment H node3298 := by rfl

def raw8420 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![-1, 0, 3, -2], ![0, 2, -2, 0], ![1, -1, 0, 0]]

def raw8420step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0]]

theorem canonical8420 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8420 = injectiveMoment H node2428 := by
  calc
    injectiveMoment H raw8420 = injectiveMoment H raw8420step0 := by
      have heq : raw8420step0 = (fun i j => raw8420 (permutation92 i) (permutation13 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8420 permutation92 permutation13
    _ = injectiveMoment H node2428 := by rfl

def raw8421 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![-1, 1, -1, 1], ![0, 1, -1, 0], ![-1, -1, 1, 1], ![2, 0, 2, -4]]

def raw8421step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 0, 1, -1], ![1, -1, 1, -1], ![0, -1, 1, 0], ![1, 1, -1, -1], ![-2, 0, -2, 4]]

def raw8421step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 1, -1, -1]]

theorem canonical8421 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8421 = injectiveMoment H node3111 := by
  calc
    injectiveMoment H raw8421 = injectiveMoment H raw8421step0 := by
      have heq : raw8421step0 = -raw8421 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8421).symm
    injectiveMoment H raw8421step0 = injectiveMoment H raw8421step1 := by
      have heq : raw8421step1 = (fun i j => raw8421step0 (permutation377 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8421step0 permutation377 permutation9
    _ = injectiveMoment H node3111 := by rfl

def raw8422 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![-1, 2, -2, 1], ![1, -1, 3, -3]]

def raw8422step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, 0, 2, -1], ![0, -1, -2, 3], ![1, 1, 1, -3]]

def raw8422step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, 1, -1], ![1, 0, -2, 1], ![0, 1, 2, -3], ![-1, -1, -1, 3]]

def raw8422step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 1, -1], ![0, 1, -2, 1], ![1, 0, 2, -3]]

theorem canonical8422 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8422 = injectiveMoment H node968 := by
  calc
    injectiveMoment H raw8422 = injectiveMoment H raw8422step0 := by
      have heq : raw8422step0 = raw8422.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw8422).symm
    injectiveMoment H raw8422step0 = injectiveMoment H raw8422step1 := by
      have heq : raw8422step1 = -raw8422step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8422step0).symm
    injectiveMoment H raw8422step1 = injectiveMoment H raw8422step2 := by
      have heq : raw8422step2 = (fun i j => raw8422step1 (permutation27 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8422step1 permutation27 permutation15
    _ = injectiveMoment H node968 := by rfl

def raw8423 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![-1, 2, 2, -3], ![1, -1, -1, 1]]

def raw8423step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, 0, 2, -1], ![0, -1, 2, -1], ![1, 1, -3, 1]]

def raw8423step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, 1, -1], ![1, 0, -2, 1], ![0, 1, -2, 1], ![-1, -1, 3, -1]]

def raw8423step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, -1, 1], ![0, 1, 1, -2], ![1, 0, 1, -2]]

theorem canonical8423 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8423 = injectiveMoment H node964 := by
  calc
    injectiveMoment H raw8423 = injectiveMoment H raw8423step0 := by
      have heq : raw8423step0 = raw8423.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw8423).symm
    injectiveMoment H raw8423step0 = injectiveMoment H raw8423step1 := by
      have heq : raw8423step1 = -raw8423step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8423step0).symm
    injectiveMoment H raw8423step1 = injectiveMoment H raw8423step2 := by
      have heq : raw8423step2 = (fun i j => raw8423step1 (permutation28 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8423step1 permutation28 permutation10
    _ = injectiveMoment H node964 := by rfl

def raw8424 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![0, -1, -1, 2], ![0, 1, -1, 0], ![-2, 0, 2, 0], ![2, 1, 1, -4]]

def raw8424step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 0, 1, -1], ![0, 1, 1, -2], ![0, -1, 1, 0], ![2, 0, -2, 0], ![-2, -1, -1, 4]]

def raw8424step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 1, -2], ![2, 0, -2, 0]]

theorem canonical8424 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8424 = injectiveMoment H node2912 := by
  calc
    injectiveMoment H raw8424 = injectiveMoment H raw8424step0 := by
      have heq : raw8424step0 = -raw8424 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8424).symm
    injectiveMoment H raw8424step0 = injectiveMoment H raw8424step1 := by
      have heq : raw8424step1 = (fun i j => raw8424step0 (permutation377 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8424step0 permutation377 permutation9
    _ = injectiveMoment H node2912 := by rfl

def raw8425 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![0, -1, -1, 2], ![1, 0, -1, 0], ![-2, 0, 2, 0], ![1, 2, 1, -4]]

def raw8425step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 0, 1, -1], ![0, 1, 1, -2], ![-1, 0, 1, 0], ![2, 0, -2, 0], ![-1, -2, -1, 4]]

def raw8425step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, 0, 0, -1], ![1, 0, 1, -2]]

theorem canonical8425 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8425 = injectiveMoment H node2916 := by
  calc
    injectiveMoment H raw8425 = injectiveMoment H raw8425step0 := by
      have heq : raw8425step0 = -raw8425 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8425).symm
    injectiveMoment H raw8425step0 = injectiveMoment H raw8425step1 := by
      have heq : raw8425step1 = (fun i j => raw8425step0 (permutation381 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8425step0 permutation381 permutation15
    _ = injectiveMoment H node2916 := by rfl

def raw8426 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![0, -1, -1, 2], ![1, 0, -1, 0], ![-2, 1, 1, 0], ![1, 1, 2, -4]]

def raw8426step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, -1, -1, 2], ![0, -1, 0, 1], ![0, 0, -1, 1], ![1, 0, -1, 0], ![1, 1, 2, -4]]

theorem canonical8426 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8426 = injectiveMoment H node3299 := by
  calc
    injectiveMoment H raw8426 = injectiveMoment H raw8426step0 := by
      have heq : raw8426step0 = (fun i j => raw8426 (permutation283 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8426 permutation283 permutation9
    _ = injectiveMoment H node3299 := by rfl

def raw8427 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![0, -1, -1, 2], ![1, 0, -1, 0], ![-2, 2, 0, 0], ![1, 0, 3, -4]]

def raw8427step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 0, 1, -1], ![0, 1, 1, -2], ![-1, 0, 1, 0], ![2, -2, 0, 0], ![-1, 0, -3, 4]]

def raw8427step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 2, 0, 0], ![0, -1, -3, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![1, 0, 0, -1], ![1, 0, 1, -2]]

theorem canonical8427 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8427 = injectiveMoment H node3323 := by
  calc
    injectiveMoment H raw8427 = injectiveMoment H raw8427step0 := by
      have heq : raw8427step0 = -raw8427 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8427).symm
    injectiveMoment H raw8427step0 = injectiveMoment H raw8427step1 := by
      have heq : raw8427step1 = (fun i j => raw8427step0 (permutation305 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8427step0 permutation305 permutation15
    _ = injectiveMoment H node3323 := by rfl

def raw8428 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![-1, 1, -1, 1], ![-1, -1, 2, 0], ![2, 1, 1, -4]]

def raw8428step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, 1, -1], ![1, 1, -2, 0], ![-2, -1, -1, 4]]

def raw8428step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 1, -2, 0]]

theorem canonical8428 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8428 = injectiveMoment H node2929 := by
  calc
    injectiveMoment H raw8428 = injectiveMoment H raw8428step0 := by
      have heq : raw8428step0 = -raw8428 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8428).symm
    injectiveMoment H raw8428step0 = injectiveMoment H raw8428step1 := by
      have heq : raw8428step1 = (fun i j => raw8428step0 (permutation337 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8428step0 permutation337 permutation9
    _ = injectiveMoment H node2929 := by rfl

def raw8429 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, -1, 0, 1], ![-1, 2, -1, 0], ![1, 0, 3, -4]]

def raw8429step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -2, 1, 0], ![-1, 0, -3, 4]]

def raw8429step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -2, 1, 0]]

theorem canonical8429 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8429 = injectiveMoment H node3414 := by
  calc
    injectiveMoment H raw8429 = injectiveMoment H raw8429step0 := by
      have heq : raw8429step0 = -raw8429 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8429).symm
    injectiveMoment H raw8429step0 = injectiveMoment H raw8429step1 := by
      have heq : raw8429step1 = (fun i j => raw8429step0 (permutation337 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8429step0 permutation337 permutation9
    _ = injectiveMoment H node3414 := by rfl

def raw8430 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![-2, 0, 2, 0], ![2, 1, 1, -4]]

def raw8430step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![2, 0, -2, 0], ![-2, -1, -1, 4]]

def raw8430step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, 0, 0, -1]]

theorem canonical8430 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8430 = injectiveMoment H node3332 := by
  calc
    injectiveMoment H raw8430 = injectiveMoment H raw8430step0 := by
      have heq : raw8430step0 = -raw8430 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8430).symm
    injectiveMoment H raw8430step0 = injectiveMoment H raw8430step1 := by
      have heq : raw8430step1 = (fun i j => raw8430step0 (permutation340 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8430step0 permutation340 permutation15
    _ = injectiveMoment H node3332 := by rfl

def raw8431 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![-2, -1, 2, 1], ![2, 1, 1, -4]]

def raw8431step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, -1, 1, 0], ![2, 1, -2, -1], ![-2, -1, -1, 4]]

def raw8431step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, 1, -2, -1]]

theorem canonical8431 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8431 = injectiveMoment H node2901 := by
  calc
    injectiveMoment H raw8431 = injectiveMoment H raw8431step0 := by
      have heq : raw8431step0 = -raw8431 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8431).symm
    injectiveMoment H raw8431step0 = injectiveMoment H raw8431step1 := by
      have heq : raw8431step1 = (fun i j => raw8431step0 (permutation379 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8431step0 permutation379 permutation9
    _ = injectiveMoment H node2901 := by rfl

def raw8432 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![-2, 0, 1, 1], ![2, 0, 2, -4]]

def raw8432step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, 0, -1, 0]]

theorem canonical8432 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8432 = injectiveMoment H node3428 := by
  calc
    injectiveMoment H raw8432 = injectiveMoment H raw8432step0 := by
      have heq : raw8432step0 = (fun i j => raw8432 (permutation182 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8432 permutation182 permutation15
    _ = injectiveMoment H node3428 := by rfl

def raw8433 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![-2, 0, 2, 0], ![2, 0, 1, -3]]

def raw8433step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 2, 0], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, 0, -1, 0]]

theorem canonical8433 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8433 = injectiveMoment H node3435 := by
  calc
    injectiveMoment H raw8433 = injectiveMoment H raw8433step0 := by
      have heq : raw8433step0 = (fun i j => raw8433 (permutation182 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8433 permutation182 permutation15
    _ = injectiveMoment H node3435 := by rfl

def raw8434 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![-1, -1, 2, 0], ![1, 1, 1, -3]]

def raw8434step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, -1, 1, 0], ![1, 1, -2, 0], ![-1, -1, -1, 3]]

def raw8434step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 1, -2, 0]]

theorem canonical8434 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8434 = injectiveMoment H node3370 := by
  calc
    injectiveMoment H raw8434 = injectiveMoment H raw8434step0 := by
      have heq : raw8434step0 = -raw8434 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8434).symm
    injectiveMoment H raw8434step0 = injectiveMoment H raw8434step1 := by
      have heq : raw8434step1 = (fun i j => raw8434step0 (permutation379 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8434step0 permutation379 permutation9
    _ = injectiveMoment H node3370 := by rfl

def raw8435 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, -1, 1], ![-2, 0, 2, 0], ![1, 2, 1, -4]]

def raw8435step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![-1, 1, 1, -1], ![2, 0, -2, 0], ![-1, -2, -1, 4]]

def raw8435step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, -1, 1, -1], ![1, 0, 0, -1]]

theorem canonical8435 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8435 = injectiveMoment H node2932 := by
  calc
    injectiveMoment H raw8435 = injectiveMoment H raw8435step0 := by
      have heq : raw8435step0 = -raw8435 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8435).symm
    injectiveMoment H raw8435step0 = injectiveMoment H raw8435step1 := by
      have heq : raw8435step1 = (fun i j => raw8435step0 (permutation342 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8435step0 permutation342 permutation15
    _ = injectiveMoment H node2932 := by rfl

def raw8436 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, -1, 1], ![-2, 1, 1, 0], ![1, 1, 2, -4]]

def raw8436step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, -1, 1], ![1, 1, 2, -4]]

theorem canonical8436 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8436 = injectiveMoment H node3302 := by
  calc
    injectiveMoment H raw8436 = injectiveMoment H raw8436step0 := by
      have heq : raw8436step0 = (fun i j => raw8436 (permutation258 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8436 permutation258 permutation9
    _ = injectiveMoment H node3302 := by rfl

def raw8437 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, -1, 1], ![-2, 2, 0, 0], ![1, 0, 3, -4]]

def raw8437step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![-1, 1, 1, -1], ![2, -2, 0, 0], ![-1, 0, -3, 4]]

def raw8437step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 2, 0, 0], ![0, -1, -3, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, 1, -1], ![1, 0, 0, -1]]

theorem canonical8437 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8437 = injectiveMoment H node3325 := by
  calc
    injectiveMoment H raw8437 = injectiveMoment H raw8437step0 := by
      have heq : raw8437step0 = -raw8437 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8437).symm
    injectiveMoment H raw8437step0 = injectiveMoment H raw8437step1 := by
      have heq : raw8437step1 = (fun i j => raw8437step0 (permutation300 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8437step0 permutation300 permutation15
    _ = injectiveMoment H node3325 := by rfl

def raw8438 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![-2, 2, -1, 1], ![1, 0, 3, -4]]

def raw8438step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 2, -1, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, 0, 3, -4]]

theorem canonical8438 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8438 = injectiveMoment H node3314 := by
  calc
    injectiveMoment H raw8438 = injectiveMoment H raw8438step0 := by
      have heq : raw8438step0 = (fun i j => raw8438 (permutation258 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8438 permutation258 permutation9
    _ = injectiveMoment H node3314 := by rfl

def raw8439 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![-1, 2, -1, 0], ![0, 0, 3, -3]]

def raw8439step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![-1, 1, 0, 0], ![1, -2, 1, 0], ![0, 0, -3, 3]]

def raw8439step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 1, 0, 0], ![0, 0, -3, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -2, 1, 0]]

theorem canonical8439 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8439 = injectiveMoment H node3465 := by
  calc
    injectiveMoment H raw8439 = injectiveMoment H raw8439step0 := by
      have heq : raw8439step0 = -raw8439 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8439).symm
    injectiveMoment H raw8439step0 = injectiveMoment H raw8439step1 := by
      have heq : raw8439step1 = (fun i j => raw8439step0 (permutation255 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8439step0 permutation255 permutation9
    _ = injectiveMoment H node3465 := by rfl

def raw8440 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, 0, -1, 0], ![-2, -1, 2, 1], ![1, 2, 1, -4]]

def raw8440step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![-1, 0, 1, 0], ![2, 1, -2, -1], ![-1, -2, -1, 4]]

def raw8440step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, 0, 0, -1], ![1, 2, -2, -1]]

theorem canonical8440 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8440 = injectiveMoment H node2906 := by
  calc
    injectiveMoment H raw8440 = injectiveMoment H raw8440step0 := by
      have heq : raw8440step0 = -raw8440 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8440).symm
    injectiveMoment H raw8440step0 = injectiveMoment H raw8440step1 := by
      have heq : raw8440step1 = (fun i j => raw8440step0 (permutation379 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8440step0 permutation379 permutation15
    _ = injectiveMoment H node2906 := by rfl

def raw8441 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, 0, -1, 0], ![-2, 0, 1, 1], ![1, 1, 2, -4]]

def raw8441step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![-1, 0, 1, 0], ![2, 0, -1, -1], ![-1, -1, -2, 4]]

def raw8441step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, 0, 0, -1]]

theorem canonical8441 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8441 = injectiveMoment H node3348 := by
  calc
    injectiveMoment H raw8441 = injectiveMoment H raw8441step0 := by
      have heq : raw8441step0 = -raw8441 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8441).symm
    injectiveMoment H raw8441step0 = injectiveMoment H raw8441step1 := by
      have heq : raw8441step1 = (fun i j => raw8441step0 (permutation380 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8441step0 permutation380 permutation15
    _ = injectiveMoment H node3348 := by rfl

def raw8442 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, 0, -1, 0], ![-2, 0, 2, 0], ![1, 1, 1, -3]]

def raw8442step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![-1, 0, 1, 0], ![2, 0, -2, 0], ![-1, -1, -1, 3]]

def raw8442step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, 0, 0, -1]]

theorem canonical8442 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8442 = injectiveMoment H node3371 := by
  calc
    injectiveMoment H raw8442 = injectiveMoment H raw8442step0 := by
      have heq : raw8442step0 = -raw8442 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8442).symm
    injectiveMoment H raw8442step0 = injectiveMoment H raw8442step1 := by
      have heq : raw8442step1 = (fun i j => raw8442step0 (permutation380 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8442step0 permutation380 permutation15
    _ = injectiveMoment H node3371 := by rfl

def raw8443 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, 0, -1, 0], ![-2, 1, 0, 1], ![1, 0, 3, -4]]

def raw8443step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, -2, 0, 1]]

theorem canonical8443 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8443 = injectiveMoment H node3449 := by
  calc
    injectiveMoment H raw8443 = injectiveMoment H raw8443step0 := by
      have heq : raw8443step0 = (fun i j => raw8443 (permutation152 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8443 permutation152 permutation15
    _ = injectiveMoment H node3449 := by rfl

def raw8444 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, 0, -1, 0], ![-2, 1, 1, 0], ![1, 0, 2, -3]]

def raw8444step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, -2, 1, 0]]

theorem canonical8444 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8444 = injectiveMoment H node3448 := by
  calc
    injectiveMoment H raw8444 = injectiveMoment H raw8444step0 := by
      have heq : raw8444step0 = (fun i j => raw8444 (permutation152 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8444 permutation152 permutation15
    _ = injectiveMoment H node3448 := by rfl

def raw8445 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, 0, -1, 0], ![-2, 2, 0, 0], ![1, -1, 3, -3]]

def raw8445step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 2, 0, 0], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 3, -3], ![1, 0, -1, 0]]

theorem canonical8445 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8445 = injectiveMoment H node3326 := by
  calc
    injectiveMoment H raw8445 = injectiveMoment H raw8445step0 := by
      have heq : raw8445step0 = (fun i j => raw8445 (permutation259 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8445 permutation259 permutation9
    _ = injectiveMoment H node3326 := by rfl

def raw8446 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 0, 3, -3], ![-1, 2, -2, 1], ![1, -1, 0, 0]]

def raw8446step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 0, 1, -1], ![0, 0, -3, 3], ![1, -2, 2, -1], ![-1, 1, 0, 0]]

def raw8446step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 1, 0, 0], ![0, 0, -3, 3], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -2, 2, -1]]

theorem canonical8446 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8446 = injectiveMoment H node2848 := by
  calc
    injectiveMoment H raw8446 = injectiveMoment H raw8446step0 := by
      have heq : raw8446step0 = -raw8446 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8446).symm
    injectiveMoment H raw8446step0 = injectiveMoment H raw8446step1 := by
      have heq : raw8446step1 = (fun i j => raw8446step0 (permutation141 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8446step0 permutation141 permutation9
    _ = injectiveMoment H node2848 := by rfl

def raw8447 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 0, 3, -3], ![0, 2, -2, 0], ![0, -1, 0, 1]]

def raw8447step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 0, 1, -1], ![0, 0, -3, 3], ![0, -2, 2, 0], ![0, 1, 0, -1]]

def raw8447step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 0, -1], ![0, 1, -1], ![0, -3, 3], ![-2, 2, 0], ![1, 0, -1]]

def raw8447step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0]]

theorem canonical8447 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8447 = injectiveMoment H node663 := by
  calc
    injectiveMoment H raw8447 = injectiveMoment H raw8447step0 := by
      have heq : raw8447step0 = -raw8447 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8447).symm
    injectiveMoment H raw8447step0 = injectiveMoment H raw8447step1 := by
      have hz : ∀ i, raw8447step0 i (permutation9 0) = 0 := by decide +kernel
      have heq : raw8447step1 = (fun i j => raw8447step0 i (permutation9 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8447step0 permutation9 hz
    injectiveMoment H raw8447step1 = injectiveMoment H raw8447step2 := by
      have heq : raw8447step2 = (fun i j => raw8447step1 (permutation112 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8447step1 permutation112 permutation4
    _ = injectiveMoment H node663 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
