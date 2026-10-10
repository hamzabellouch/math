import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes6
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes12
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes15
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes17
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes18
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes20
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes23
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes31
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes37
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes39
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes41
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes43
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes44
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes45

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw3424 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 2, -1], ![1, 1, -1, -1], ![1, 0, -1, 0]]

def raw3424step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 1, 0], ![0, 2, -1, -1], ![2, -1, -1, 0]]

def raw3424step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 1, -1, 0], ![0, -2, 1, 1], ![-2, 1, 1, 0]]

def raw3424step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 1, 0], ![0, 1, 1, -2], ![1, 1, -2, 0]]

theorem canonical3424 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3424 = injectiveMoment H node1000 := by
  calc
    injectiveMoment H raw3424 = injectiveMoment H raw3424step0 := by
      have heq : raw3424step0 = raw3424.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3424).symm
    injectiveMoment H raw3424step0 = injectiveMoment H raw3424step1 := by
      have heq : raw3424step1 = -raw3424step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3424step0).symm
    injectiveMoment H raw3424step1 = injectiveMoment H raw3424step2 := by
      have heq : raw3424step2 = (fun i j => raw3424step1 (permutation10 i) (permutation32 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3424step1 permutation10 permutation32
    _ = injectiveMoment H node1000 := by rfl

def raw3425 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -2, 2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, -2, 3, -3]]

theorem canonical3425 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3425 = injectiveMoment H node2024 := by
  rfl

def raw3426 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -2, 2], ![0, 1, -1, 0], ![0, 1, 1, -2], ![2, -2, 2, -2]]

theorem canonical3426 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3426 = injectiveMoment H node2025 := by
  rfl

def raw3427 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -2, 2], ![0, 1, -1, 0], ![0, 1, 3, -4], ![2, -2, 0, 0]]

theorem canonical3427 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3427 = injectiveMoment H node2026 := by
  rfl

def raw3428 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -2, 2], ![0, 1, -1, 0], ![1, -2, 1, 0], ![1, 1, 2, -4]]

theorem canonical3428 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3428 = injectiveMoment H node2027 := by
  rfl

def raw3429 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -2, 2], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 3, -4]]

def raw3429step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 0, 2, -2], ![0, -1, 1, 0], ![-1, 1, 0, 0], ![-1, 0, -3, 4]]

def raw3429step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -1, -3, 4], ![0, 0, 2, -2], ![0, 2, 0, -2], ![1, -1, 0, 0]]

theorem canonical3429 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3429 = injectiveMoment H node2808 := by
  calc
    injectiveMoment H raw3429 = injectiveMoment H raw3429step0 := by
      have heq : raw3429step0 = -raw3429 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3429).symm
    injectiveMoment H raw3429step0 = injectiveMoment H raw3429step1 := by
      have heq : raw3429step1 = (fun i j => raw3429step0 (permutation100 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3429step0 permutation100 permutation15
    _ = injectiveMoment H node2808 := by rfl

def raw3430 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -2, 2], ![0, 1, -1, 0], ![1, -1, 3, -3], ![1, 0, 0, -1]]

def raw3430step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 0, 2, -2], ![0, -1, 1, 0], ![-1, 1, -3, 3], ![-1, 0, 0, 1]]

def raw3430step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -1, 0, 1], ![0, 0, 2, -2], ![0, 2, 0, -2], ![1, -1, -3, 3]]

theorem canonical3430 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3430 = injectiveMoment H node2816 := by
  calc
    injectiveMoment H raw3430 = injectiveMoment H raw3430step0 := by
      have heq : raw3430step0 = -raw3430 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3430).symm
    injectiveMoment H raw3430step0 = injectiveMoment H raw3430step1 := by
      have heq : raw3430step1 = (fun i j => raw3430step0 (permutation100 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3430step0 permutation100 permutation15
    _ = injectiveMoment H node2816 := by rfl

def raw3431 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -2, 2], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, -2, 2, -2]]

def raw3431step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 0, 2, -2], ![0, -1, 0, 1], ![0, -1, 0, 1], ![-2, 2, -2, 2]]

def raw3431step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 2, 0, -2], ![2, 0, 0, -2]]

theorem canonical3431 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3431 = injectiveMoment H node1517 := by
  calc
    injectiveMoment H raw3431 = injectiveMoment H raw3431step0 := by
      have heq : raw3431step0 = -raw3431 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3431).symm
    injectiveMoment H raw3431step0 = injectiveMoment H raw3431step1 := by
      have heq : raw3431step1 = (fun i j => raw3431step0 (permutation144 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3431step0 permutation144 permutation11
    _ = injectiveMoment H node1517 := by rfl

def raw3432 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, -2, 3, -2], ![1, 1, -1, -1]]

theorem canonical3432 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3432 = injectiveMoment H node2028 := by
  rfl

def raw3433 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, -1, 2, -2], ![1, 0, 0, -1]]

def raw3433step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 0, 2, -2], ![0, -1, 0, 1], ![-1, 1, -2, 2], ![-1, 0, 0, 1]]

def raw3433step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, 0, 2, -2], ![0, 2, 0, -2], ![1, -1, -2, 2]]

theorem canonical3433 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3433 = injectiveMoment H node2762 := by
  calc
    injectiveMoment H raw3433 = injectiveMoment H raw3433step0 := by
      have heq : raw3433step0 = -raw3433 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3433).symm
    injectiveMoment H raw3433step0 = injectiveMoment H raw3433step1 := by
      have heq : raw3433step1 = (fun i j => raw3433step0 (permutation100 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3433step0 permutation100 permutation15
    _ = injectiveMoment H node2762 := by rfl

def raw3434 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, -1, 3, -3], ![1, 0, -1, 0]]

def raw3434step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 0, 2, -2], ![0, -1, 0, 1], ![-1, 1, -3, 3], ![-1, 0, 1, 0]]

def raw3434step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 1, 0], ![0, 0, 2, -2], ![0, 2, 0, -2], ![1, -1, -3, 3]]

theorem canonical3434 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3434 = injectiveMoment H node2771 := by
  calc
    injectiveMoment H raw3434 = injectiveMoment H raw3434step0 := by
      have heq : raw3434step0 = -raw3434 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3434).symm
    injectiveMoment H raw3434step0 = injectiveMoment H raw3434step1 := by
      have heq : raw3434step1 = (fun i j => raw3434step0 (permutation100 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3434step0 permutation100 permutation15
    _ = injectiveMoment H node2771 := by rfl

def raw3435 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -2, 2], ![0, 1, 0, -1], ![2, -1, 2, -3]]

def raw3435step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 0, 2, -2], ![0, -1, 0, 1], ![-2, 1, -2, 3]]

def raw3435step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, 2, -2], ![0, 2, 0, -2], ![1, -2, -2, 3]]

theorem canonical3435 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3435 = injectiveMoment H node1285 := by
  calc
    injectiveMoment H raw3435 = injectiveMoment H raw3435step0 := by
      have heq : raw3435step0 = -raw3435 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3435).symm
    injectiveMoment H raw3435step0 = injectiveMoment H raw3435step1 := by
      have heq : raw3435step1 = (fun i j => raw3435step0 (permutation23 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3435step0 permutation23 permutation15
    _ = injectiveMoment H node1285 := by rfl

def raw3436 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -2, 2], ![0, 1, 1, -2], ![2, -1, 1, -2]]

def raw3436step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 0, 2, -2], ![0, -1, -1, 2], ![-2, 1, -1, 2]]

def raw3436step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 2, 0, -2], ![1, -1, -2, 2]]

theorem canonical3436 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3436 = injectiveMoment H node1059 := by
  calc
    injectiveMoment H raw3436 = injectiveMoment H raw3436step0 := by
      have heq : raw3436step0 = -raw3436 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3436).symm
    injectiveMoment H raw3436step0 = injectiveMoment H raw3436step1 := by
      have heq : raw3436step1 = (fun i j => raw3436step0 (permutation21 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3436step0 permutation21 permutation17
    _ = injectiveMoment H node1059 := by rfl

def raw3437 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -2, 2], ![0, 1, 3, -4], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def raw3437step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 0, 2, -2], ![0, -1, -3, 4], ![-1, 1, 0, 0], ![-1, 0, 1, 0]]

def raw3437step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, -1, 1, 0], ![0, 0, 2, -2], ![0, 2, 0, -2], ![1, -1, 0, 0]]

theorem canonical3437 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3437 = injectiveMoment H node2687 := by
  calc
    injectiveMoment H raw3437 = injectiveMoment H raw3437step0 := by
      have heq : raw3437step0 = -raw3437 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3437).symm
    injectiveMoment H raw3437step0 = injectiveMoment H raw3437step1 := by
      have heq : raw3437step1 = (fun i j => raw3437step0 (permutation100 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3437step0 permutation100 permutation15
    _ = injectiveMoment H node2687 := by rfl

def raw3438 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -2, 2], ![0, 1, 3, -4], ![1, 0, -1, 0], ![1, -1, 0, 0]]

def raw3438step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 0, 2, -2], ![0, -1, -3, 4], ![-1, 0, 1, 0], ![-1, 1, 0, 0]]

def raw3438step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, -1, 1, 0], ![0, 0, 2, -2], ![0, 2, 0, -2], ![1, -1, 0, 0]]

theorem canonical3438 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3438 = injectiveMoment H node2687 := by
  calc
    injectiveMoment H raw3438 = injectiveMoment H raw3438step0 := by
      have heq : raw3438step0 = -raw3438 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3438).symm
    injectiveMoment H raw3438step0 = injectiveMoment H raw3438step1 := by
      have heq : raw3438step1 = (fun i j => raw3438step0 (permutation94 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3438step0 permutation94 permutation15
    _ = injectiveMoment H node2687 := by rfl

def raw3439 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -2, 2], ![0, 1, 3, -4], ![2, -1, -1, 0]]

def raw3439step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 0, 2, -2], ![0, -1, -3, 4], ![-2, 1, 1, 0]]

def raw3439step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, 0, 2, -2], ![0, 2, 0, -2], ![1, -2, 1, 0]]

theorem canonical3439 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3439 = injectiveMoment H node1180 := by
  calc
    injectiveMoment H raw3439 = injectiveMoment H raw3439step0 := by
      have heq : raw3439step0 = -raw3439 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3439).symm
    injectiveMoment H raw3439step0 = injectiveMoment H raw3439step1 := by
      have heq : raw3439step1 = (fun i j => raw3439step0 (permutation23 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3439step0 permutation23 permutation15
    _ = injectiveMoment H node1180 := by rfl

def raw3440 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -2, 2], ![0, 2, -1, -1], ![1, -2, 3, -2], ![1, 0, 0, -1]]

theorem canonical3440 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3440 = injectiveMoment H node2029 := by
  rfl

def raw3441 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -2, 2], ![0, 2, -1, -1], ![2, -2, 3, -3]]

def raw3441step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, 2, -2], ![0, -2, -1, 3], ![2, 2, -1, -3]]

def raw3441step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 0, -2, 2], ![0, 2, 1, -3], ![-2, -2, 1, 3]]

def raw3441step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, -2, 2], ![0, 2, 0, -2], ![2, 0, 1, -3]]

theorem canonical3441 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3441 = injectiveMoment H node406 := by
  calc
    injectiveMoment H raw3441 = injectiveMoment H raw3441step0 := by
      have heq : raw3441step0 = raw3441.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3441).symm
    injectiveMoment H raw3441step0 = injectiveMoment H raw3441step1 := by
      have heq : raw3441step1 = -raw3441step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3441step0).symm
    injectiveMoment H raw3441step1 = injectiveMoment H raw3441step2 := by
      have heq : raw3441step2 = (fun i j => raw3441step1 (permutation29 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3441step1 permutation29 permutation15
    _ = injectiveMoment H node406 := by rfl

def raw3442 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -2, 2], ![0, 2, 0, -2], ![2, -2, 2, -2]]

def raw3442step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 0, 2, -2], ![0, -2, 0, 2], ![-2, 2, -2, 2]]

def raw3442step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 0, -2, 2], ![0, 2, 0, -2], ![2, 0, 0, -2]]

theorem canonical3442 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3442 = injectiveMoment H node412 := by
  calc
    injectiveMoment H raw3442 = injectiveMoment H raw3442step0 := by
      have heq : raw3442step0 = -raw3442 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3442).symm
    injectiveMoment H raw3442step0 = injectiveMoment H raw3442step1 := by
      have heq : raw3442step1 = (fun i j => raw3442step0 (permutation32 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3442step0 permutation32 permutation11
    _ = injectiveMoment H node412 := by rfl

def raw3443 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -2, 2], ![0, 2, 2, -4], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def raw3443step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 0, 2, -2], ![0, -2, -2, 4], ![-1, 1, 0, 0], ![-1, 1, 0, 0]]

def raw3443step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, 0, 0, -2]]

theorem canonical3443 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3443 = injectiveMoment H node1475 := by
  calc
    injectiveMoment H raw3443 = injectiveMoment H raw3443step0 := by
      have heq : raw3443step0 = -raw3443 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3443).symm
    injectiveMoment H raw3443step0 = injectiveMoment H raw3443step1 := by
      have heq : raw3443step1 = (fun i j => raw3443step0 (permutation83 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3443step0 permutation83 permutation23
    _ = injectiveMoment H node1475 := by rfl

def raw3444 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -2, 2], ![0, 2, 2, -4], ![2, -2, 0, 0]]

def raw3444step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 0, 2, -2], ![0, -2, -2, 4], ![-2, 2, 0, 0]]

def raw3444step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 2, -2], ![0, 2, -2, 0], ![2, 0, 0, -2]]

theorem canonical3444 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3444 = injectiveMoment H node395 := by
  calc
    injectiveMoment H raw3444 = injectiveMoment H raw3444step0 := by
      have heq : raw3444step0 = -raw3444 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3444).symm
    injectiveMoment H raw3444step0 = injectiveMoment H raw3444step1 := by
      have heq : raw3444step1 = (fun i j => raw3444step0 (permutation22 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3444step0 permutation22 permutation23
    _ = injectiveMoment H node395 := by rfl

def raw3445 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -2, 2], ![1, -2, 1, 0], ![1, 2, 1, -4]]

def raw3445step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, -2, 2], ![0, -2, 1, 1], ![2, 2, 0, -4]]

def raw3445step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 0, 2, -2], ![0, 2, -1, -1], ![-2, -2, 0, 4]]

def raw3445step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 2, -2], ![0, 2, -1, -1], ![2, 0, -1, -1]]

theorem canonical3445 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3445 = injectiveMoment H node396 := by
  calc
    injectiveMoment H raw3445 = injectiveMoment H raw3445step0 := by
      have heq : raw3445step0 = raw3445.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3445).symm
    injectiveMoment H raw3445step0 = injectiveMoment H raw3445step1 := by
      have heq : raw3445step1 = -raw3445step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3445step0).symm
    injectiveMoment H raw3445step1 = injectiveMoment H raw3445step2 := by
      have heq : raw3445step2 = (fun i j => raw3445step1 (permutation30 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3445step1 permutation30 permutation9
    _ = injectiveMoment H node396 := by rfl

def raw3446 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -2, 2], ![1, -2, 3, -2], ![1, 2, -1, -2]]

def raw3446step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, -2, 2], ![0, -2, 3, -1], ![2, 2, -2, -2]]

def raw3446step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 0, 2, -2], ![0, 2, -3, 1], ![-2, -2, 2, 2]]

def raw3446step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 0, -2, 2], ![0, 2, -1, -1], ![2, 0, 1, -3]]

theorem canonical3446 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3446 = injectiveMoment H node411 := by
  calc
    injectiveMoment H raw3446 = injectiveMoment H raw3446step0 := by
      have heq : raw3446step0 = raw3446.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3446).symm
    injectiveMoment H raw3446step0 = injectiveMoment H raw3446step1 := by
      have heq : raw3446step1 = -raw3446step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3446step0).symm
    injectiveMoment H raw3446step1 = injectiveMoment H raw3446step2 := by
      have heq : raw3446step2 = (fun i j => raw3446step1 (permutation29 i) (permutation16 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3446step1 permutation29 permutation16
    _ = injectiveMoment H node411 := by rfl

def raw3447 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -2, 2], ![1, -1, 0, 0], ![1, 1, 2, -4]]

def raw3447step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 0, 2, -2], ![-1, 1, 0, 0], ![-1, -1, -2, 4]]

def raw3447step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 2, -2], ![0, 2, 0, -2], ![1, 0, -1, 0]]

theorem canonical3447 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3447 = injectiveMoment H node775 := by
  calc
    injectiveMoment H raw3447 = injectiveMoment H raw3447step0 := by
      have heq : raw3447step0 = -raw3447 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3447).symm
    injectiveMoment H raw3447step0 = injectiveMoment H raw3447step1 := by
      have heq : raw3447step1 = (fun i j => raw3447step0 (permutation27 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3447step0 permutation27 permutation17
    _ = injectiveMoment H node775 := by rfl

def raw3448 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -2, 2], ![1, -1, 1, -1], ![1, 1, 1, -3]]

def raw3448step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 0, 2, -2], ![-1, 1, -1, 1], ![-1, -1, -1, 3]]

def raw3448step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 2, -2], ![0, 2, 0, -2], ![1, -1, -1, 1]]

theorem canonical3448 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3448 = injectiveMoment H node976 := by
  calc
    injectiveMoment H raw3448 = injectiveMoment H raw3448step0 := by
      have heq : raw3448step0 = -raw3448 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3448).symm
    injectiveMoment H raw3448step0 = injectiveMoment H raw3448step1 := by
      have heq : raw3448step1 = (fun i j => raw3448step0 (permutation29 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3448step0 permutation29 permutation15
    _ = injectiveMoment H node976 := by rfl

def raw3449 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -2, 2], ![1, -1, 2, -2], ![1, 1, 0, -2]]

def raw3449step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 0, 2, -2], ![-1, 1, -2, 2], ![-1, -1, 0, 2]]

def raw3449step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 2, 0, -2], ![1, -1, -2, 2]]

theorem canonical3449 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3449 = injectiveMoment H node1059 := by
  calc
    injectiveMoment H raw3449 = injectiveMoment H raw3449step0 := by
      have heq : raw3449step0 = -raw3449 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3449).symm
    injectiveMoment H raw3449step0 = injectiveMoment H raw3449step1 := by
      have heq : raw3449step1 = (fun i j => raw3449step0 (permutation29 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3449step0 permutation29 permutation15
    _ = injectiveMoment H node1059 := by rfl

def raw3450 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -2, 2], ![1, -1, 3, -3], ![1, 1, -1, -1]]

def raw3450step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 0, 2, -2], ![-1, 1, -3, 3], ![-1, -1, 1, 1]]

def raw3450step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, 2, -2], ![0, 2, 0, -2], ![1, -1, -3, 3]]

theorem canonical3450 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3450 = injectiveMoment H node1120 := by
  calc
    injectiveMoment H raw3450 = injectiveMoment H raw3450step0 := by
      have heq : raw3450step0 = -raw3450 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3450).symm
    injectiveMoment H raw3450step0 = injectiveMoment H raw3450step1 := by
      have heq : raw3450step1 = (fun i j => raw3450step0 (permutation29 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3450step0 permutation29 permutation15
    _ = injectiveMoment H node1120 := by rfl

def raw3451 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -2, 2], ![1, 2, -1, -2], ![1, -2, 3, -2]]

def raw3451step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, 2, -2], ![0, -2, -1, 3], ![2, 2, -2, -2]]

def raw3451step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 0, -2, 2], ![0, 2, 1, -3], ![-2, -2, 2, 2]]

def raw3451step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 0, -2, 2], ![0, 2, -1, -1], ![2, 0, 1, -3]]

theorem canonical3451 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3451 = injectiveMoment H node411 := by
  calc
    injectiveMoment H raw3451 = injectiveMoment H raw3451step0 := by
      have heq : raw3451step0 = raw3451.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3451).symm
    injectiveMoment H raw3451step0 = injectiveMoment H raw3451step1 := by
      have heq : raw3451step1 = -raw3451step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3451step0).symm
    injectiveMoment H raw3451step1 = injectiveMoment H raw3451step2 := by
      have heq : raw3451step2 = (fun i j => raw3451step1 (permutation29 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3451step1 permutation29 permutation15
    _ = injectiveMoment H node411 := by rfl

def raw3452 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, -1, 0, 0], ![0, 2, 2, -4]]

def raw3452step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 0, 1, -1], ![0, 0, 1, -1], ![-1, 1, 0, 0], ![-1, 1, 0, 0], ![0, -2, -2, 4]]

def raw3452step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 0, 0, -1]]

theorem canonical3452 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3452 = injectiveMoment H node2880 := by
  calc
    injectiveMoment H raw3452 = injectiveMoment H raw3452step0 := by
      have heq : raw3452step0 = -raw3452 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3452).symm
    injectiveMoment H raw3452step0 = injectiveMoment H raw3452step1 := by
      have heq : raw3452step1 = (fun i j => raw3452step0 (permutation324 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3452step0 permutation324 permutation23
    _ = injectiveMoment H node2880 := by rfl

def raw3453 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, 1, 2, -4]]

def raw3453step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 0, 1, -1], ![0, 0, 1, -1], ![-1, 1, 0, 0], ![-1, -1, -2, 4]]

def raw3453step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 2, -2], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -1, 0]]

theorem canonical3453 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3453 = injectiveMoment H node2403 := by
  calc
    injectiveMoment H raw3453 = injectiveMoment H raw3453step0 := by
      have heq : raw3453step0 = -raw3453 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3453).symm
    injectiveMoment H raw3453step0 = injectiveMoment H raw3453step1 := by
      have heq : raw3453step1 = (fun i j => raw3453step0 (permutation128 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3453step0 permutation128 permutation17
    _ = injectiveMoment H node2403 := by rfl

def raw3454 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 1, -1], ![1, 1, 1, -3]]

def raw3454step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 0, 1, -1], ![0, 0, 1, -1], ![-1, 1, -1, 1], ![-1, -1, -1, 3]]

def raw3454step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -1, -1, 1]]

theorem canonical3454 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3454 = injectiveMoment H node2553 := by
  calc
    injectiveMoment H raw3454 = injectiveMoment H raw3454step0 := by
      have heq : raw3454step0 = -raw3454 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3454).symm
    injectiveMoment H raw3454step0 = injectiveMoment H raw3454step1 := by
      have heq : raw3454step1 = (fun i j => raw3454step0 (permutation135 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3454step0 permutation135 permutation15
    _ = injectiveMoment H node2553 := by rfl

def raw3455 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -1, 1], ![0, 0, 0, 0], ![0, 1, -1, 0], ![2, -1, 2, -3]]

def raw3455step0 : Matrix (Fin 4) (Fin 5) ℤ := ![![-2, 0, 0, 0, 2], ![0, 0, 0, 1, -1], ![0, -1, 0, -1, 2], ![2, 1, 0, 0, -3]]

def raw3455step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, 1, -1], ![0, -1, -1, 2], ![2, 1, 0, -3]]

def raw3455step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, 0, 2, -3]]

theorem canonical3455 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3455 = injectiveMoment H node1032 := by
  calc
    injectiveMoment H raw3455 = injectiveMoment H raw3455step0 := by
      have heq : raw3455step0 = raw3455.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3455).symm
    injectiveMoment H raw3455step0 = injectiveMoment H raw3455step1 := by
      have hz : ∀ i, raw3455step0 i (permutation80 0) = 0 := by decide +kernel
      have heq : raw3455step1 = (fun i j => raw3455step0 i (permutation80 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw3455step0 permutation80 hz
    injectiveMoment H raw3455step1 = injectiveMoment H raw3455step2 := by
      have heq : raw3455step2 = (fun i j => raw3455step1 (permutation21 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3455step1 permutation21 permutation17
    _ = injectiveMoment H node1032 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
