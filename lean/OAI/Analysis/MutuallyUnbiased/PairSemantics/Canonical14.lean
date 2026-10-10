import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes1
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes2
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes3
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes4
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes5
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes8
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes9
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes10
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes22
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes35

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw448 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]

def raw448step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]

def raw448step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -3, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]

theorem canonical448 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw448 = injectiveMoment H node2297 := by
  calc
    injectiveMoment H raw448 = injectiveMoment H raw448step0 := by
      have heq : raw448step0 = -raw448 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw448).symm
    injectiveMoment H raw448step0 = injectiveMoment H raw448step1 := by
      have heq : raw448step1 = (fun i j => raw448step0 (permutation206 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw448step0 permutation206 permutation6
    _ = injectiveMoment H node2297 := by rfl

def raw449 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]

def raw449step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]

def raw449step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -3, 3], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1]]

theorem canonical449 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw449 = injectiveMoment H node699 := by
  calc
    injectiveMoment H raw449 = injectiveMoment H raw449step0 := by
      have heq : raw449step0 = -raw449 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw449).symm
    injectiveMoment H raw449step0 = injectiveMoment H raw449step1 := by
      have heq : raw449step1 = (fun i j => raw449step0 (permutation61 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw449step0 permutation61 permutation6
    _ = injectiveMoment H node699 := by rfl

def raw450 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]

def raw450step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]

def raw450step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -3, 3], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]

theorem canonical450 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw450 = injectiveMoment H node697 := by
  calc
    injectiveMoment H raw450 = injectiveMoment H raw450step0 := by
      have heq : raw450step0 = -raw450 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw450).symm
    injectiveMoment H raw450step0 = injectiveMoment H raw450step1 := by
      have heq : raw450step1 = (fun i j => raw450step0 (permutation59 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw450step0 permutation59 permutation6
    _ = injectiveMoment H node697 := by rfl

def raw451 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]

def raw451step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 2, 0]]

def raw451step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]

theorem canonical451 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw451 = injectiveMoment H node345 := by
  calc
    injectiveMoment H raw451 = injectiveMoment H raw451step0 := by
      have heq : raw451step0 = -raw451 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw451).symm
    injectiveMoment H raw451step0 = injectiveMoment H raw451step1 := by
      have heq : raw451step1 = (fun i j => raw451step0 (permutation43 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw451step0 permutation43 permutation8
    _ = injectiveMoment H node345 := by rfl

def raw452 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![3, -1, -2]]

def raw452step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 1, 0], ![-3, 1, 2]]

def raw452step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -3, 3], ![1, 0, -1], ![1, 2, -3]]

theorem canonical452 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw452 = injectiveMoment H node222 := by
  calc
    injectiveMoment H raw452 = injectiveMoment H raw452step0 := by
      have heq : raw452step0 = -raw452 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw452).symm
    injectiveMoment H raw452step0 = injectiveMoment H raw452step1 := by
      have heq : raw452step1 = (fun i j => raw452step0 (permutation15 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw452step0 permutation15 permutation6
    _ = injectiveMoment H node222 := by rfl

def raw453 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]

def raw453step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, -1, 1], ![0, 3, -3], ![2, -1, -1]]

theorem canonical453 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw453 = injectiveMoment H node651 := by
  calc
    injectiveMoment H raw453 = injectiveMoment H raw453step0 := by
      have heq : raw453step0 = (fun i j => raw453 (permutation143 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw453 permutation143 permutation6
    _ = injectiveMoment H node651 := by rfl

def raw454 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![3, -2, -1]]

def raw454step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 3, -3], ![2, -1, -1]]

theorem canonical454 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw454 = injectiveMoment H node170 := by
  calc
    injectiveMoment H raw454 = injectiveMoment H raw454step0 := by
      have heq : raw454step0 = (fun i j => raw454 (permutation31 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw454 permutation31 permutation6
    _ = injectiveMoment H node170 := by rfl

def raw455 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 1, -2], ![3, -3, 0]]

def raw455step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![1, -2, 1], ![2, -1, -1]]

theorem canonical455 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw455 = injectiveMoment H node98 := by
  calc
    injectiveMoment H raw455 = injectiveMoment H raw455step0 := by
      have heq : raw455step0 = (fun i j => raw455 (permutation28 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw455 permutation28 permutation6
    _ = injectiveMoment H node98 := by rfl

def raw456 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -2, 0], ![2, 0, -2]]

def raw456step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 3, -3], ![2, -1, -1]]

theorem canonical456 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw456 = injectiveMoment H node198 := by
  calc
    injectiveMoment H raw456 = injectiveMoment H raw456step0 := by
      have heq : raw456step0 = (fun i j => raw456 (permutation25 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw456 permutation25 permutation6
    _ = injectiveMoment H node198 := by rfl

def raw457 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -1, -1], ![2, -1, -1]]

def raw457step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-2, 1, 1], ![-2, 1, 1]]

def raw457step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -3, 3], ![1, 1, -2], ![1, 1, -2]]

theorem canonical457 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw457 = injectiveMoment H node223 := by
  calc
    injectiveMoment H raw457 = injectiveMoment H raw457step0 := by
      have heq : raw457step0 = -raw457 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw457).symm
    injectiveMoment H raw457step0 = injectiveMoment H raw457step1 := by
      have heq : raw457step1 = (fun i j => raw457step0 (permutation15 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw457step0 permutation15 permutation6
    _ = injectiveMoment H node223 := by rfl

def raw458 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]

def raw458step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -3, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]

def raw458step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]

theorem canonical458 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw458 = injectiveMoment H node1411 := by
  calc
    injectiveMoment H raw458 = injectiveMoment H raw458step0 := by
      have heq : raw458step0 = -raw458 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw458).symm
    injectiveMoment H raw458step0 = injectiveMoment H raw458step1 := by
      have heq : raw458step1 = (fun i j => raw458step0 (permutation172 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw458step0 permutation172 permutation8
    _ = injectiveMoment H node1411 := by rfl

def raw459 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]

def raw459step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -3, 2], ![-1, 1, 0], ![-1, 1, 0], ![-2, 1, 1]]

def raw459step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]

theorem canonical459 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw459 = injectiveMoment H node343 := by
  calc
    injectiveMoment H raw459 = injectiveMoment H raw459step0 := by
      have heq : raw459step0 = -raw459 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw459).symm
    injectiveMoment H raw459step0 = injectiveMoment H raw459step1 := by
      have heq : raw459step1 = (fun i j => raw459step0 (permutation42 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw459step0 permutation42 permutation8
    _ = injectiveMoment H node343 := by rfl

def raw460 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![3, -2, -1]]

def raw460step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -3, 2], ![-1, 1, 0], ![-3, 2, 1]]

def raw460step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 2, -3], ![2, -3, 1]]

theorem canonical460 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw460 = injectiveMoment H node95 := by
  calc
    injectiveMoment H raw460 = injectiveMoment H raw460step0 := by
      have heq : raw460step0 = -raw460 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw460).symm
    injectiveMoment H raw460step0 = injectiveMoment H raw460step1 := by
      have heq : raw460step1 = (fun i j => raw460step0 (permutation12 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw460step0 permutation12 permutation8
    _ = injectiveMoment H node95 := by rfl

def raw461 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![2, -2, 0], ![2, -1, -1]]

def raw461step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -3, 2], ![-2, 2, 0], ![-2, 1, 1]]

def raw461step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 1, -2], ![2, -3, 1]]

theorem canonical461 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw461 = injectiveMoment H node97 := by
  calc
    injectiveMoment H raw461 = injectiveMoment H raw461step0 := by
      have heq : raw461step0 = -raw461 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw461).symm
    injectiveMoment H raw461step0 = injectiveMoment H raw461step1 := by
      have heq : raw461step1 = (fun i j => raw461step0 (permutation12 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw461step0 permutation12 permutation8
    _ = injectiveMoment H node97 := by rfl

def raw462 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![3, -1, -2]]

theorem canonical462 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw462 = injectiveMoment H node325 := by
  rfl

def raw463 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]

theorem canonical463 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw463 = injectiveMoment H node326 := by
  rfl

def raw464 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]

def raw464step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![0, 1, -1], ![1, 0, -1], ![1, 2, -3]]

theorem canonical464 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw464 = injectiveMoment H node633 := by
  calc
    injectiveMoment H raw464 = injectiveMoment H raw464step0 := by
      have heq : raw464step0 = (fun i j => raw464 (permutation59 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw464 permutation59 permutation5
    _ = injectiveMoment H node633 := by rfl

def raw465 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]

def raw465step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![0, 2, -2], ![1, 0, -1], ![1, 1, -2]]

theorem canonical465 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw465 = injectiveMoment H node635 := by
  calc
    injectiveMoment H raw465 = injectiveMoment H raw465step0 := by
      have heq : raw465step0 = (fun i j => raw465 (permutation61 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw465 permutation61 permutation5
    _ = injectiveMoment H node635 := by rfl

def raw466 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]

theorem canonical466 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw466 = injectiveMoment H node327 := by
  rfl

def raw467 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]

theorem canonical467 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw467 = injectiveMoment H node328 := by
  rfl

def raw468 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]

def raw468step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![0, 1, -1], ![0, 2, -2], ![2, 0, -2]]

theorem canonical468 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw468 = injectiveMoment H node631 := by
  calc
    injectiveMoment H raw468 = injectiveMoment H raw468step0 := by
      have heq : raw468step0 = (fun i j => raw468 (permutation60 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw468 permutation60 permutation5
    _ = injectiveMoment H node631 := by rfl

def raw469 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]

theorem canonical469 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw469 = injectiveMoment H node329 := by
  rfl

def raw470 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 2, -2], ![2, -1, -1], ![1, 1, -2]]

def raw470step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]

theorem canonical470 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw470 = injectiveMoment H node329 := by
  calc
    injectiveMoment H raw470 = injectiveMoment H raw470step0 := by
      have heq : raw470step0 = (fun i j => raw470 (permutation34 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw470 permutation34 permutation3
    _ = injectiveMoment H node329 := by rfl

def raw471 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 2, -2], ![3, 0, -3]]

def raw471step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![0, 3, -3], ![2, 0, -2]]

theorem canonical471 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw471 = injectiveMoment H node192 := by
  calc
    injectiveMoment H raw471 = injectiveMoment H raw471step0 := by
      have heq : raw471step0 = (fun i j => raw471 (permutation16 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw471 permutation16 permutation5
    _ = injectiveMoment H node192 := by rfl

def raw472 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 3, -3], ![1, -1, 0], ![2, 0, -2]]

theorem canonical472 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw472 = injectiveMoment H node330 := by
  rfl

def raw473 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 3, -3], ![1, 0, -1], ![2, -1, -1]]

theorem canonical473 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw473 = injectiveMoment H node331 := by
  rfl

def raw474 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 3, -3], ![2, -1, -1], ![1, 0, -1]]

def raw474step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 3, -3], ![1, 0, -1], ![2, -1, -1]]

theorem canonical474 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw474 = injectiveMoment H node331 := by
  calc
    injectiveMoment H raw474 = injectiveMoment H raw474step0 := by
      have heq : raw474step0 = (fun i j => raw474 (permutation34 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw474 permutation34 permutation3
    _ = injectiveMoment H node331 := by rfl

def raw475 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 3, -3], ![3, -1, -2]]

theorem canonical475 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw475 = injectiveMoment H node91 := by
  rfl

def raw476 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 3, -4]]

def raw476step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![-1, 1, 0], ![-1, 0, 1], ![-1, -3, 4]]

def raw476step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![2, 0, -2]]

theorem canonical476 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw476 = injectiveMoment H node309 := by
  calc
    injectiveMoment H raw476 = injectiveMoment H raw476step0 := by
      have heq : raw476step0 = -raw476 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw476).symm
    injectiveMoment H raw476step0 = injectiveMoment H raw476step1 := by
      have heq : raw476step1 = (fun i j => raw476step0 (permutation146 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw476step0 permutation146 permutation5
    _ = injectiveMoment H node309 := by rfl

def raw477 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]

theorem canonical477 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw477 = injectiveMoment H node332 := by
  rfl

def raw478 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![1, -1, 0], ![2, 3, -5]]

def raw478step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![-1, 1, 0], ![-2, -3, 5]]

def raw478step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 3, -3], ![1, -1, 0], ![2, 0, -2]]

theorem canonical478 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw478 = injectiveMoment H node75 := by
  calc
    injectiveMoment H raw478 = injectiveMoment H raw478step0 := by
      have heq : raw478step0 = -raw478 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw478).symm
    injectiveMoment H raw478step0 = injectiveMoment H raw478step1 := by
      have heq : raw478step1 = (fun i j => raw478step0 (permutation28 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw478step0 permutation28 permutation5
    _ = injectiveMoment H node75 := by rfl

def raw479 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]

def raw479step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![-1, 0, 1], ![-1, 0, 1], ![-1, -2, 3]]

def raw479step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, -1, 1], ![0, 3, -3], ![2, 0, -2]]

theorem canonical479 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw479 = injectiveMoment H node551 := by
  calc
    injectiveMoment H raw479 = injectiveMoment H raw479step0 := by
      have heq : raw479step0 = -raw479 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw479).symm
    injectiveMoment H raw479step0 = injectiveMoment H raw479step1 := by
      have heq : raw479step1 = (fun i j => raw479step0 (permutation143 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw479step0 permutation143 permutation5
    _ = injectiveMoment H node551 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
