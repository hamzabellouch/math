import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes4
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes10
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes19
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes21
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes43
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes44
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes47
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes48
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes49
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes50
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes51
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes52
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes53
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes54

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw9536 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-1, -1, -1, 3], ![-1, 2, 2, -3]]

def raw9536step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, -1, 1], ![-1, 1, 0, 0], ![-1, 0, 1, 0], ![1, 1, 1, -3], ![1, -2, -2, 3]]

def raw9536step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 1, 1, -3]]

theorem canonical9536 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9536 = injectiveMoment H node3226 := by
  calc
    injectiveMoment H raw9536 = injectiveMoment H raw9536step0 := by
      have heq : raw9536step0 = -raw9536 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9536).symm
    injectiveMoment H raw9536step0 = injectiveMoment H raw9536step1 := by
      have heq : raw9536step1 = (fun i j => raw9536step0 (permutation377 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9536step0 permutation377 permutation15
    _ = injectiveMoment H node3226 := by rfl

def raw9537 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-1, -1, 0, 2], ![-1, 2, 1, -2]]

def raw9537step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, -1, 1], ![-1, 1, 0, 0], ![-1, 0, 1, 0], ![1, 1, 0, -2], ![1, -2, -1, 2]]

def raw9537step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 0, 1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 1, -2]]

theorem canonical9537 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9537 = injectiveMoment H node3035 := by
  calc
    injectiveMoment H raw9537 = injectiveMoment H raw9537step0 := by
      have heq : raw9537step0 = -raw9537 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9537).symm
    injectiveMoment H raw9537step0 = injectiveMoment H raw9537step1 := by
      have heq : raw9537step1 = (fun i j => raw9537step0 (permutation343 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9537step0 permutation343 permutation17
    _ = injectiveMoment H node3035 := by rfl

def raw9538 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-1, -1, 1, 1], ![-1, 2, 0, -1]]

def raw9538step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, -1, 1], ![-1, 1, 0, 0], ![-1, 0, 1, 0], ![1, 1, -1, -1], ![1, -2, 0, 1]]

def raw9538step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 0, 1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 0, -1, 0]]

theorem canonical9538 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9538 = injectiveMoment H node3209 := by
  calc
    injectiveMoment H raw9538 = injectiveMoment H raw9538step0 := by
      have heq : raw9538step0 = -raw9538 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9538).symm
    injectiveMoment H raw9538step0 = injectiveMoment H raw9538step1 := by
      have heq : raw9538step1 = (fun i j => raw9538step0 (permutation344 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9538step0 permutation344 permutation17
    _ = injectiveMoment H node3209 := by rfl

def raw9539 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![0, -1, -1, 2], ![-2, 2, 2, -2]]

def raw9539step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, -1, 1], ![-1, 1, 0, 0], ![-1, 0, 1, 0], ![0, 1, 1, -2], ![2, -2, -2, 2]]

def raw9539step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 2, -2, 2], ![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, 1, -2]]

theorem canonical9539 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9539 = injectiveMoment H node3311 := by
  calc
    injectiveMoment H raw9539 = injectiveMoment H raw9539step0 := by
      have heq : raw9539step0 = -raw9539 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9539).symm
    injectiveMoment H raw9539step0 = injectiveMoment H raw9539step1 := by
      have heq : raw9539step1 = (fun i j => raw9539step0 (permutation377 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9539step0 permutation377 permutation15
    _ = injectiveMoment H node3311 := by rfl

def raw9540 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![0, 2, -1, -1], ![-2, -1, 2, 1]]

def raw9540step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, -1, 0, 0], ![1, 0, 0, -1]]

theorem canonical9540 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9540 = injectiveMoment H node3067 := by
  calc
    injectiveMoment H raw9540 = injectiveMoment H raw9540step0 := by
      have heq : raw9540step0 = (fun i j => raw9540 (permutation335 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9540 permutation335 permutation10
    _ = injectiveMoment H node3067 := by rfl

def raw9541 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![0, 2, 0, -2], ![-2, -1, 1, 2]]

def raw9541step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -1, 0, 0], ![1, 0, -1, 0]]

theorem canonical9541 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9541 = injectiveMoment H node3069 := by
  calc
    injectiveMoment H raw9541 = injectiveMoment H raw9541step0 := by
      have heq : raw9541step0 = (fun i j => raw9541 (permutation312 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9541 permutation312 permutation9
    _ = injectiveMoment H node3069 := by rfl

def raw9542 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-1, -1, -1, 3], ![-1, 2, 1, -2]]

def raw9542step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, -1, 1], ![-1, 1, 0, 0], ![-1, 0, 0, 1], ![1, 1, 1, -3], ![1, -2, -1, 2]]

def raw9542step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 1, 1, -3]]

theorem canonical9542 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9542 = injectiveMoment H node3024 := by
  calc
    injectiveMoment H raw9542 = injectiveMoment H raw9542step0 := by
      have heq : raw9542step0 = -raw9542 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9542).symm
    injectiveMoment H raw9542step0 = injectiveMoment H raw9542step1 := by
      have heq : raw9542step1 = (fun i j => raw9542step0 (permutation343 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9542step0 permutation343 permutation17
    _ = injectiveMoment H node3024 := by rfl

def raw9543 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-1, -1, 0, 2], ![-1, 2, 0, -1]]

def raw9543step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, -1, 1], ![-1, 1, 0, 0], ![-1, 0, 0, 1], ![1, 1, 0, -2], ![1, -2, 0, 1]]

def raw9543step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, 0, 0, -1]]

theorem canonical9543 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9543 = injectiveMoment H node3429 := by
  calc
    injectiveMoment H raw9543 = injectiveMoment H raw9543step0 := by
      have heq : raw9543step0 = -raw9543 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9543).symm
    injectiveMoment H raw9543step0 = injectiveMoment H raw9543step1 := by
      have heq : raw9543step1 = (fun i j => raw9543step0 (permutation220 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9543step0 permutation220 permutation23
    _ = injectiveMoment H node3429 := by rfl

def raw9544 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![0, -1, -2, 3], ![-2, 2, 2, -2]]

def raw9544step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, -1, 1], ![-1, 1, 0, 0], ![-1, 0, 0, 1], ![0, 1, 2, -3], ![2, -2, -2, 2]]

def raw9544step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 2, -2, 2], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, 2, -3]]

theorem canonical9544 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9544 = injectiveMoment H node3307 := by
  calc
    injectiveMoment H raw9544 = injectiveMoment H raw9544step0 := by
      have heq : raw9544step0 = -raw9544 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9544).symm
    injectiveMoment H raw9544step0 = injectiveMoment H raw9544step1 := by
      have heq : raw9544step1 = (fun i j => raw9544step0 (permutation377 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9544step0 permutation377 permutation15
    _ = injectiveMoment H node3307 := by rfl

def raw9545 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![0, -1, -1, 2], ![-2, 2, 1, -1]]

def raw9545step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, -1, 1], ![-1, 1, 0, 0], ![-1, 0, 0, 1], ![0, 1, 1, -2], ![2, -2, -1, 1]]

def raw9545step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 1, 0, -2]]

theorem canonical9545 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9545 = injectiveMoment H node3093 := by
  calc
    injectiveMoment H raw9545 = injectiveMoment H raw9545step0 := by
      have heq : raw9545step0 = -raw9545 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9545).symm
    injectiveMoment H raw9545step0 = injectiveMoment H raw9545step1 := by
      have heq : raw9545step1 = (fun i j => raw9545step0 (permutation343 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9545step0 permutation343 permutation17
    _ = injectiveMoment H node3093 := by rfl

def raw9546 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![0, -1, 2, -1], ![-2, 2, -2, 2]]

def raw9546step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, -1, 1], ![-1, 1, 0, 0], ![-1, 0, 0, 1], ![0, 1, -2, 1], ![2, -2, 2, -2]]

def raw9546step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 2, -2, 2], ![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, 1, -2]]

theorem canonical9546 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9546 = injectiveMoment H node3311 := by
  calc
    injectiveMoment H raw9546 = injectiveMoment H raw9546step0 := by
      have heq : raw9546step0 = -raw9546 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9546).symm
    injectiveMoment H raw9546step0 = injectiveMoment H raw9546step1 := by
      have heq : raw9546step1 = (fun i j => raw9546step0 (permutation373 i) (permutation16 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9546step0 permutation373 permutation16
    _ = injectiveMoment H node3311 := by rfl

def raw9547 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![0, 2, -1, -1], ![-2, -1, 1, 2]]

def raw9547step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, -1, 0, 0], ![1, 0, 0, -1]]

theorem canonical9547 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9547 = injectiveMoment H node3067 := by
  calc
    injectiveMoment H raw9547 = injectiveMoment H raw9547step0 := by
      have heq : raw9547step0 = (fun i j => raw9547 (permutation312 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9547 permutation312 permutation9
    _ = injectiveMoment H node3067 := by rfl

def raw9548 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![0, 2, 0, -2], ![-2, -1, 0, 3]]

def raw9548step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, -1, 3], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, 0, -1]]

theorem canonical9548 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9548 = injectiveMoment H node3423 := by
  calc
    injectiveMoment H raw9548 = injectiveMoment H raw9548step0 := by
      have heq : raw9548step0 = (fun i j => raw9548 (permutation201 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9548 permutation201 permutation21
    _ = injectiveMoment H node3423 := by rfl

def raw9549 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![1, 0, 0, -1], ![1, -1, 0, 0], ![0, -1, 2, -1], ![-2, 2, -2, 2]]

def raw9549step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, -1, 1], ![-1, 0, 0, 1], ![-1, 1, 0, 0], ![0, 1, -2, 1], ![2, -2, 2, -2]]

def raw9549step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 2, -2, 2], ![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, 1, -2]]

theorem canonical9549 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9549 = injectiveMoment H node3311 := by
  calc
    injectiveMoment H raw9549 = injectiveMoment H raw9549step0 := by
      have heq : raw9549step0 = -raw9549 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9549).symm
    injectiveMoment H raw9549step0 = injectiveMoment H raw9549step1 := by
      have heq : raw9549step1 = (fun i j => raw9549step0 (permutation355 i) (permutation16 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9549step0 permutation355 permutation16
    _ = injectiveMoment H node3311 := by rfl

def raw9550 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![1, 0, 0, -1], ![1, 0, 0, -1], ![0, -2, 2, 0], ![-2, 2, -2, 2]]

def raw9550step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, -2, 2, -2]]

theorem canonical9550 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9550 = injectiveMoment H node3181 := by
  calc
    injectiveMoment H raw9550 = injectiveMoment H raw9550step0 := by
      have heq : raw9550step0 = (fun i j => raw9550 (permutation277 i) (permutation16 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9550 permutation277 permutation16
    _ = injectiveMoment H node3181 := by rfl

def raw9551 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![1, 0, 0, -1], ![1, 0, 0, -1], ![0, -1, 2, -1], ![-2, 1, -2, 3]]

def raw9551step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -2, -2, 3]]

theorem canonical9551 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9551 = injectiveMoment H node3460 := by
  calc
    injectiveMoment H raw9551 = injectiveMoment H raw9551step0 := by
      have heq : raw9551step0 = (fun i j => raw9551 (permutation258 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9551 permutation258 permutation15
    _ = injectiveMoment H node3460 := by rfl

def raw9552 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 2, -2], ![-1, 1, -1, 1], ![1, -1, 0, 0]]

def raw9552step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![-1, 2, -1, 0], ![1, -2, 1, 0]]

def raw9552step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 1, 0], ![0, 1, -1, 0], ![1, 0, 1, -2]]

theorem canonical9552 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9552 = injectiveMoment H node1241 := by
  calc
    injectiveMoment H raw9552 = injectiveMoment H raw9552step0 := by
      have heq : raw9552step0 = raw9552.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw9552).symm
    injectiveMoment H raw9552step0 = injectiveMoment H raw9552step1 := by
      have heq : raw9552step1 = (fun i j => raw9552step0 (permutation23 i) (permutation14 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9552step0 permutation23 permutation14
    _ = injectiveMoment H node1241 := by rfl

def raw9553 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 2, -2], ![-1, 2, 1, -2], ![1, -2, -2, 3]]

def raw9553step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 2, 1, -2], ![0, 0, -1, 1], ![0, 0, 2, -2], ![1, -2, -2, 3]]

theorem canonical9553 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9553 = injectiveMoment H node1378 := by
  calc
    injectiveMoment H raw9553 = injectiveMoment H raw9553step0 := by
      have heq : raw9553step0 = (fun i j => raw9553 (permutation21 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9553 permutation21 permutation9
    _ = injectiveMoment H node1378 := by rfl

def raw9554 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, -1, 0, 1]]

def raw9554step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![-1, 0, 1]]

def raw9554step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0]]

theorem canonical9554 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9554 = injectiveMoment H node294 := by
  calc
    injectiveMoment H raw9554 = injectiveMoment H raw9554step0 := by
      have hz : ∀ i, raw9554 i (permutation9 0) = 0 := by decide +kernel
      have heq : raw9554step0 = (fun i j => raw9554 i (permutation9 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw9554 permutation9 hz
    injectiveMoment H raw9554step0 = injectiveMoment H raw9554step1 := by
      have heq : raw9554step1 = (fun i j => raw9554step0 (permutation27 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9554step0 permutation27 permutation3
    _ = injectiveMoment H node294 := by rfl

def raw9555 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 2, -2], ![0, 1, 1, -2], ![0, -1, -2, 3]]

def raw9555step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![-1, -2, 3]]

def raw9555step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2]]

theorem canonical9555 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9555 = injectiveMoment H node268 := by
  calc
    injectiveMoment H raw9555 = injectiveMoment H raw9555step0 := by
      have hz : ∀ i, raw9555 i (permutation9 0) = 0 := by decide +kernel
      have heq : raw9555step0 = (fun i j => raw9555 i (permutation9 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw9555 permutation9 hz
    injectiveMoment H raw9555step0 = injectiveMoment H raw9555step1 := by
      have heq : raw9555step1 = (fun i j => raw9555step0 (permutation27 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9555step0 permutation27 permutation3
    _ = injectiveMoment H node268 := by rfl

def raw9556 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 3, -3], ![-1, 1, -1, 1], ![0, 1, -1, 0], ![1, -2, 0, 1]]

def raw9556step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, -1, 1], ![0, 0, 3, -3], ![0, 1, -1, 0], ![1, -2, 0, 1]]

theorem canonical9556 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9556 = injectiveMoment H node2847 := by
  calc
    injectiveMoment H raw9556 = injectiveMoment H raw9556step0 := by
      have heq : raw9556step0 = (fun i j => raw9556 (permutation80 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9556 permutation80 permutation9
    _ = injectiveMoment H node2847 := by rfl

def raw9557 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 3, -3], ![0, 1, -1, 0], ![-1, 1, -1, 1], ![1, -2, 0, 1]]

def raw9557step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, -1, 1], ![0, 0, 3, -3], ![0, 1, -1, 0], ![1, -2, 0, 1]]

theorem canonical9557 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9557 = injectiveMoment H node2847 := by
  calc
    injectiveMoment H raw9557 = injectiveMoment H raw9557step0 := by
      have heq : raw9557step0 = (fun i j => raw9557 (permutation104 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9557 permutation104 permutation9
    _ = injectiveMoment H node2847 := by rfl

def raw9558 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 3, -3], ![0, 1, -1, 0], ![0, 1, -1, 0], ![0, -2, 0, 2]]

def raw9558step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![-2, 0, 2]]

def raw9558step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0]]

theorem canonical9558 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9558 = injectiveMoment H node663 := by
  calc
    injectiveMoment H raw9558 = injectiveMoment H raw9558step0 := by
      have hz : ∀ i, raw9558 i (permutation9 0) = 0 := by decide +kernel
      have heq : raw9558step0 = (fun i j => raw9558 i (permutation9 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw9558 permutation9 hz
    injectiveMoment H raw9558step0 = injectiveMoment H raw9558step1 := by
      have heq : raw9558step1 = (fun i j => raw9558step0 (permutation128 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9558step0 permutation128 permutation3
    _ = injectiveMoment H node663 := by rfl

def raw9559 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, -2, 1], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-2, 0, 0, 2], ![0, 1, 3, -4]]

def raw9559step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -1, 1], ![0, 1, -2, 1], ![0, 1, 3, -4], ![1, -1, 0, 0], ![1, -1, 0, 0]]

theorem canonical9559 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9559 = injectiveMoment H node3184 := by
  calc
    injectiveMoment H raw9559 = injectiveMoment H raw9559step0 := by
      have heq : raw9559step0 = (fun i j => raw9559 (permutation262 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9559 permutation262 permutation9
    _ = injectiveMoment H node3184 := by rfl

def raw9560 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, -2, 1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-2, 1, 0, 1], ![0, -1, 3, -2]]

def raw9560step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, 3, -2], ![0, 0, -1, 1], ![0, 1, -2, 1], ![1, -1, 0, 0], ![1, 0, 0, -1]]

theorem canonical9560 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9560 = injectiveMoment H node3280 := by
  calc
    injectiveMoment H raw9560 = injectiveMoment H raw9560step0 := by
      have heq : raw9560step0 = (fun i j => raw9560 (permutation294 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9560 permutation294 permutation9
    _ = injectiveMoment H node3280 := by rfl

def raw9561 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, -2, 1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-1, -1, 0, 2], ![-1, 1, 3, -3]]

def raw9561step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![-1, 1, 0, 0], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -1, 3, -3], ![1, 0, -2, 1]]

theorem canonical9561 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9561 = injectiveMoment H node3386 := by
  calc
    injectiveMoment H raw9561 = injectiveMoment H raw9561step0 := by
      have heq : raw9561step0 = (fun i j => raw9561 (permutation285 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9561 permutation285 permutation15
    _ = injectiveMoment H node3386 := by rfl

def raw9562 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, -1, 0], ![-1, 1, -1, 1], ![1, -1, 0, 0], ![-1, -1, 0, 2], ![1, 0, 3, -4]]

def raw9562step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![-1, 1, -1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 3, -4]]

theorem canonical9562 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9562 = injectiveMoment H node3378 := by
  calc
    injectiveMoment H raw9562 = injectiveMoment H raw9562step0 := by
      have heq : raw9562step0 = (fun i j => raw9562 (permutation283 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9562 permutation283 permutation9
    _ = injectiveMoment H node3378 := by rfl

def raw9563 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, -1, 0], ![0, -1, 0, 1], ![1, -1, 0, 0], ![-1, 0, -1, 2], ![0, 1, 3, -4]]

def raw9563step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, -1, 0, 0]]

theorem canonical9563 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9563 = injectiveMoment H node3420 := by
  calc
    injectiveMoment H raw9563 = injectiveMoment H raw9563step0 := by
      have heq : raw9563step0 = (fun i j => raw9563 (permutation284 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9563 permutation284 permutation9
    _ = injectiveMoment H node3420 := by rfl

def raw9564 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, -1, 0], ![0, -1, 0, 1], ![1, 0, -1, 0], ![-1, -1, 0, 2], ![0, 1, 3, -4]]

def raw9564step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, 0, -1, 0]]

theorem canonical9564 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9564 = injectiveMoment H node3389 := by
  calc
    injectiveMoment H raw9564 = injectiveMoment H raw9564step0 := by
      have heq : raw9564step0 = (fun i j => raw9564 (permutation284 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9564 permutation284 permutation9
    _ = injectiveMoment H node3389 := by rfl

def raw9565 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 0, -1, 1], ![1, -1, 0, 0], ![-2, 0, 0, 2], ![1, 0, 3, -4]]

def raw9565step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, -1, 1, 0], ![0, 0, 1, -1], ![-1, 1, 0, 0], ![2, 0, 0, -2], ![-1, 0, -3, 4]]

def raw9565step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -1, -3, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -1, 0, 0]]

theorem canonical9565 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9565 = injectiveMoment H node3456 := by
  calc
    injectiveMoment H raw9565 = injectiveMoment H raw9565step0 := by
      have heq : raw9565step0 = -raw9565 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9565).symm
    injectiveMoment H raw9565step0 = injectiveMoment H raw9565step1 := by
      have heq : raw9565step1 = (fun i j => raw9565step0 (permutation216 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9565step0 permutation216 permutation15
    _ = injectiveMoment H node3456 := by rfl

def raw9566 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 0, 0, 0], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-2, 0, 2, 0]]

def raw9566step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-2, 0, 2, 0]]

def raw9566step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, 0, -1, 0]]

theorem canonical9566 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9566 = injectiveMoment H node2759 := by
  calc
    injectiveMoment H raw9566 = injectiveMoment H raw9566step0 := by
      have hz : ∀ j, raw9566 (permutation221 0) j = 0 := by decide +kernel
      have heq : raw9566step0 = (fun i j => raw9566 (permutation221 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9566 permutation221 hz
    injectiveMoment H raw9566step0 = injectiveMoment H raw9566step1 := by
      have heq : raw9566step1 = (fun i j => raw9566step0 (permutation96 i) (permutation20 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9566step0 permutation96 permutation20
    _ = injectiveMoment H node2759 := by rfl

def raw9567 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![0, -1, 0, 1], ![-1, -1, 0, 2], ![1, 0, 3, -4]]

def raw9567step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 3, -4]]

theorem canonical9567 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9567 = injectiveMoment H node3387 := by
  calc
    injectiveMoment H raw9567 = injectiveMoment H raw9567step0 := by
      have heq : raw9567step0 = (fun i j => raw9567 (permutation288 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9567 permutation288 permutation9
    _ = injectiveMoment H node3387 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
