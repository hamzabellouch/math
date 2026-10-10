import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes19
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes45
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes46
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes47
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes48
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes49
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes50
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes52
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes53

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw9600 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-2, 1, 0, 1], ![0, -1, 2, -1]]

def raw9600step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 0, 1], ![0, -1, 1, 0], ![0, 2, -1, -1], ![1, 0, -1, 0], ![1, 0, 0, -1]]

theorem canonical9600 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9600 = injectiveMoment H node3200 := by
  calc
    injectiveMoment H raw9600 = injectiveMoment H raw9600step0 := by
      have heq : raw9600step0 = (fun i j => raw9600 (permutation262 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9600 permutation262 permutation11
    _ = injectiveMoment H node3200 := by rfl

def raw9601 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-1, -1, -1, 3], ![-1, 1, 3, -3]]

def raw9601step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 1, 0, 0], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -1, 3, -3], ![1, 0, -1, 0]]

theorem canonical9601 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9601 = injectiveMoment H node3367 := by
  calc
    injectiveMoment H raw9601 = injectiveMoment H raw9601step0 := by
      have heq : raw9601step0 = (fun i j => raw9601 (permutation285 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9601 permutation285 permutation15
    _ = injectiveMoment H node3367 := by rfl

def raw9602 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-1, -1, 0, 2], ![-1, 1, 2, -2]]

def raw9602step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, -1, 1, 0], ![-1, 1, 0, 0], ![-1, 0, 0, 1], ![1, 1, 0, -2], ![1, -1, -2, 2]]

def raw9602step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, 0, 0, -1]]

theorem canonical9602 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9602 = injectiveMoment H node3077 := by
  calc
    injectiveMoment H raw9602 = injectiveMoment H raw9602step0 := by
      have heq : raw9602step0 = -raw9602 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9602).symm
    injectiveMoment H raw9602step0 = injectiveMoment H raw9602step1 := by
      have heq : raw9602step1 = (fun i j => raw9602step0 (permutation388 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9602step0 permutation388 permutation23
    _ = injectiveMoment H node3077 := by rfl

def raw9603 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 0, -1], ![0, -1, -1, 2], ![-2, 1, 3, -2]]

def raw9603step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, -1, 2, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -1, 0]]

theorem canonical9603 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9603 = injectiveMoment H node3234 := by
  calc
    injectiveMoment H raw9603 = injectiveMoment H raw9603step0 := by
      have heq : raw9603step0 = (fun i j => raw9603 (permutation395 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9603 permutation395 permutation10
    _ = injectiveMoment H node3234 := by rfl

def raw9604 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 0, 0, -1], ![-2, 1, 0, 1], ![0, -2, 3, -1]]

def raw9604step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 1, -2, 0]]

theorem canonical9604 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9604 = injectiveMoment H node2968 := by
  calc
    injectiveMoment H raw9604 = injectiveMoment H raw9604step0 := by
      have heq : raw9604step0 = (fun i j => raw9604 (permutation383 i) (permutation19 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9604 permutation383 permutation19
    _ = injectiveMoment H node2968 := by rfl

def raw9605 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 0, 0, -1], ![-1, 1, 1, -1], ![-1, -2, 2, 1]]

def raw9605step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 0, 0, -1]]

theorem canonical9605 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9605 = injectiveMoment H node3082 := by
  calc
    injectiveMoment H raw9605 = injectiveMoment H raw9605step0 := by
      have heq : raw9605step0 = (fun i j => raw9605 (permutation323 i) (permutation16 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9605 permutation323 permutation16
    _ = injectiveMoment H node3082 := by rfl

def raw9606 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 0, 0, -1], ![0, -2, 0, 2], ![-2, 1, 3, -2]]

def raw9606step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -2, 3, -2], ![1, 0, -1, 0]]

theorem canonical9606 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9606 = injectiveMoment H node3189 := by
  calc
    injectiveMoment H raw9606 = injectiveMoment H raw9606step0 := by
      have heq : raw9606step0 = (fun i j => raw9606 (permutation267 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9606 permutation267 permutation15
    _ = injectiveMoment H node3189 := by rfl

def raw9607 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 0, 0, -1], ![0, -2, 1, 1], ![-2, 1, 2, -1]]

def raw9607step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1]]

theorem canonical9607 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9607 = injectiveMoment H node3079 := by
  calc
    injectiveMoment H raw9607 = injectiveMoment H raw9607step0 := by
      have heq : raw9607step0 = (fun i j => raw9607 (permutation350 i) (permutation13 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9607 permutation350 permutation13
    _ = injectiveMoment H node3079 := by rfl

def raw9608 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![-1, 1, 2, -2], ![1, -2, -1, 2]]

def raw9608step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 1, -2], ![-1, 0, 2, -1], ![1, -1, -2, 2]]

def raw9608step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, 1, -1], ![0, 1, -2, 1], ![1, -1, 2, -2]]

theorem canonical9608 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9608 = injectiveMoment H node1261 := by
  calc
    injectiveMoment H raw9608 = injectiveMoment H raw9608step0 := by
      have heq : raw9608step0 = raw9608.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw9608).symm
    injectiveMoment H raw9608step0 = injectiveMoment H raw9608step1 := by
      have heq : raw9608step1 = (fun i j => raw9608step0 (permutation21 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9608step0 permutation21 permutation10
    _ = injectiveMoment H node1261 := by rfl

def raw9609 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![-2, -1, 0, 3], ![1, 0, 2, -3]]

def raw9609step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, -1, 0, 1], ![0, -1, 1, 0], ![-1, 1, 0, 0], ![2, 1, 0, -3], ![-1, 0, -2, 3]]

def raw9609step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, 0, -1, 0], ![1, 0, 0, -1]]

theorem canonical9609 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9609 = injectiveMoment H node2962 := by
  calc
    injectiveMoment H raw9609 = injectiveMoment H raw9609step0 := by
      have heq : raw9609step0 = -raw9609 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9609).symm
    injectiveMoment H raw9609step0 = injectiveMoment H raw9609step1 := by
      have heq : raw9609step1 = (fun i j => raw9609step0 (permutation382 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9609step0 permutation382 permutation21
    _ = injectiveMoment H node2962 := by rfl

def raw9610 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![-2, 0, 0, 2], ![1, -1, 2, -2]]

def raw9610step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, -1, 0, 1], ![0, -1, 1, 0], ![-1, 1, 0, 0], ![2, 0, 0, -2], ![-1, 1, -2, 2]]

def raw9610step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 2, 0, -2], ![1, 0, -1, 0], ![1, 0, 0, -1]]

theorem canonical9610 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9610 = injectiveMoment H node3041 := by
  calc
    injectiveMoment H raw9610 = injectiveMoment H raw9610step0 := by
      have heq : raw9610step0 = -raw9610 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9610).symm
    injectiveMoment H raw9610step0 = injectiveMoment H raw9610step1 := by
      have heq : raw9610step1 = (fun i j => raw9610step0 (permutation382 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9610step0 permutation382 permutation21
    _ = injectiveMoment H node3041 := by rfl

def raw9611 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-2, 0, 2, 0]]

def raw9611step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 2, 0], ![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -1, 0]]

theorem canonical9611 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9611 = injectiveMoment H node3437 := by
  calc
    injectiveMoment H raw9611 = injectiveMoment H raw9611step0 := by
      have heq : raw9611step0 = (fun i j => raw9611 (permutation219 i) (permutation28 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9611 permutation219 permutation28
    _ = injectiveMoment H node3437 := by rfl

def raw9612 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-2, -1, 2, 1]]

def raw9612step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -1, 0]]

theorem canonical9612 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9612 = injectiveMoment H node3083 := by
  calc
    injectiveMoment H raw9612 = injectiveMoment H raw9612step0 := by
      have heq : raw9612step0 = (fun i j => raw9612 (permutation308 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9612 permutation308 permutation10
    _ = injectiveMoment H node3083 := by rfl

def raw9613 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, -2, 0, 1], ![-2, 0, 3, -1]]

def raw9613step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 1, -2, 0]]

theorem canonical9613 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9613 = injectiveMoment H node2968 := by
  calc
    injectiveMoment H raw9613 = injectiveMoment H raw9613step0 := by
      have heq : raw9613step0 = (fun i j => raw9613 (permutation337 i) (permutation13 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9613 permutation337 permutation13
    _ = injectiveMoment H node2968 := by rfl

def raw9614 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, -1, 1, -1], ![-2, -1, 2, 1]]

def raw9614step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 0, 0, -1]]

theorem canonical9614 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9614 = injectiveMoment H node3082 := by
  calc
    injectiveMoment H raw9614 = injectiveMoment H raw9614step0 := by
      have heq : raw9614step0 = (fun i j => raw9614 (permutation309 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9614 permutation309 permutation10
    _ = injectiveMoment H node3082 := by rfl

def raw9615 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, -1, 0], ![1, 0, 0, -1], ![-2, -1, 0, 3], ![1, -1, 2, -2]]

def raw9615step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 2, -2], ![1, 0, 0, -1]]

theorem canonical9615 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9615 = injectiveMoment H node2989 := by
  calc
    injectiveMoment H raw9615 = injectiveMoment H raw9615step0 := by
      have heq : raw9615step0 = (fun i j => raw9615 (permutation265 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9615 permutation265 permutation9
    _ = injectiveMoment H node2989 := by rfl

def raw9616 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, -1, 0], ![1, 0, 0, -1], ![-2, 0, 3, -1], ![1, -2, -1, 2]]

def raw9616step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -2, 2, -1], ![1, 0, -1, 0]]

theorem canonical9616 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9616 = injectiveMoment H node3144 := by
  calc
    injectiveMoment H raw9616 = injectiveMoment H raw9616step0 := by
      have heq : raw9616step0 = (fun i j => raw9616 (permutation259 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9616 permutation259 permutation10
    _ = injectiveMoment H node3144 := by rfl

def raw9617 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, -1, 1, -1], ![-2, -1, 1, 2]]

def raw9617step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 0, 0, -1]]

theorem canonical9617 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9617 = injectiveMoment H node3076 := by
  calc
    injectiveMoment H raw9617 = injectiveMoment H raw9617step0 := by
      have heq : raw9617step0 = (fun i j => raw9617 (permutation315 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9617 permutation315 permutation9
    _ = injectiveMoment H node3076 := by rfl

def raw9618 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 0, 0, -1], ![-2, -2, 2, 2]]

def raw9618step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 0, 0, -1]]

theorem canonical9618 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9618 = injectiveMoment H node2894 := by
  calc
    injectiveMoment H raw9618 = injectiveMoment H raw9618step0 := by
      have heq : raw9618step0 = (fun i j => raw9618 (permutation314 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9618 permutation314 permutation9
    _ = injectiveMoment H node2894 := by rfl

def raw9619 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, -1, 1], ![-2, -1, 0, 3], ![1, 0, 2, -3]]

def raw9619step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, -1, 0, 1], ![0, -1, 0, 1], ![-1, 1, 1, -1], ![2, 1, 0, -3], ![-1, 0, -2, 3]]

def raw9619step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, -1, 1, -1], ![1, 0, 0, -1]]

theorem canonical9619 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9619 = injectiveMoment H node2984 := by
  calc
    injectiveMoment H raw9619 = injectiveMoment H raw9619step0 := by
      have heq : raw9619step0 = -raw9619 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9619).symm
    injectiveMoment H raw9619step0 = injectiveMoment H raw9619step1 := by
      have heq : raw9619step1 = (fun i j => raw9619step0 (permutation342 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9619step0 permutation342 permutation21
    _ = injectiveMoment H node2984 := by rfl

def raw9620 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, -1, 1], ![-2, 0, 0, 2], ![1, -1, 2, -2]]

def raw9620step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, -1, 0, 1], ![0, -1, 0, 1], ![-1, 1, 1, -1], ![2, 0, 0, -2], ![-1, 1, -2, 2]]

def raw9620step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 2, 0, -2], ![1, -1, 1, -1], ![1, 0, 0, -1]]

theorem canonical9620 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9620 = injectiveMoment H node3053 := by
  calc
    injectiveMoment H raw9620 = injectiveMoment H raw9620step0 := by
      have heq : raw9620step0 = -raw9620 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9620).symm
    injectiveMoment H raw9620step0 = injectiveMoment H raw9620step1 := by
      have heq : raw9620step1 = (fun i j => raw9620step0 (permutation342 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9620step0 permutation342 permutation21
    _ = injectiveMoment H node3053 := by rfl

def raw9621 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, -1, 0, 0], ![-2, 0, 2, 0]]

def raw9621step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 1, 0], ![0, -1, 1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 1, -1, -1]]

theorem canonical9621 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9621 = injectiveMoment H node3169 := by
  calc
    injectiveMoment H raw9621 = injectiveMoment H raw9621step0 := by
      have heq : raw9621step0 = (fun i j => raw9621 (permutation338 i) (permutation13 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9621 permutation338 permutation13
    _ = injectiveMoment H node3169 := by rfl

def raw9622 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 0, 0, -1], ![-2, -1, 2, 1]]

def raw9622step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 0, 0, -1]]

theorem canonical9622 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9622 = injectiveMoment H node3100 := by
  calc
    injectiveMoment H raw9622 = injectiveMoment H raw9622step0 := by
      have heq : raw9622step0 = (fun i j => raw9622 (permutation308 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9622 permutation308 permutation9
    _ = injectiveMoment H node3100 := by rfl

def raw9623 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![-2, -1, -1, 4], ![1, 0, 2, -3]]

def raw9623step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 0, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, 0, -1, 0], ![1, 2, 0, -3]]

theorem canonical9623 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9623 = injectiveMoment H node2896 := by
  calc
    injectiveMoment H raw9623 = injectiveMoment H raw9623step0 := by
      have heq : raw9623step0 = (fun i j => raw9623 (permutation258 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9623 permutation258 permutation11
    _ = injectiveMoment H node2896 := by rfl

def raw9624 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![-2, -1, 0, 3], ![1, 0, 1, -2]]

def raw9624step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, -1, 0, 1], ![0, -1, 0, 1], ![-1, 1, 0, 0], ![2, 1, 0, -3], ![-1, 0, -1, 2]]

def raw9624step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, 0, 0, -1]]

theorem canonical9624 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9624 = injectiveMoment H node3392 := by
  calc
    injectiveMoment H raw9624 = injectiveMoment H raw9624step0 := by
      have heq : raw9624step0 = -raw9624 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9624).symm
    injectiveMoment H raw9624step0 = injectiveMoment H raw9624step1 := by
      have heq : raw9624step1 = (fun i j => raw9624step0 (permutation380 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9624step0 permutation380 permutation21
    _ = injectiveMoment H node3392 := by rfl

def raw9625 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![-2, 0, -1, 3], ![1, -1, 2, -2]]

def raw9625step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 0, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, 0, -1, 0], ![1, 2, -1, -2]]

theorem canonical9625 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9625 = injectiveMoment H node2945 := by
  calc
    injectiveMoment H raw9625 = injectiveMoment H raw9625step0 := by
      have heq : raw9625step0 = (fun i j => raw9625 (permutation258 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9625 permutation258 permutation11
    _ = injectiveMoment H node2945 := by rfl

def raw9626 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![-2, 0, 0, 2], ![1, -1, 1, -1]]

def raw9626step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, -1, 0, 1], ![0, -1, 0, 1], ![-1, 1, 0, 0], ![2, 0, 0, -2], ![-1, 1, -1, 1]]

def raw9626step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 2, 0, -2], ![1, 0, 0, -1]]

theorem canonical9626 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9626 = injectiveMoment H node3405 := by
  calc
    injectiveMoment H raw9626 = injectiveMoment H raw9626step0 := by
      have heq : raw9626step0 = -raw9626 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9626).symm
    injectiveMoment H raw9626step0 = injectiveMoment H raw9626step1 := by
      have heq : raw9626step1 = (fun i j => raw9626step0 (permutation380 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9626step0 permutation380 permutation21
    _ = injectiveMoment H node3405 := by rfl

def raw9627 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, -1, -1, 1], ![-2, 0, 2, 0]]

def raw9627step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 1, 0], ![0, -1, 1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 1, -1, -1]]

theorem canonical9627 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9627 = injectiveMoment H node3169 := by
  calc
    injectiveMoment H raw9627 = injectiveMoment H raw9627step0 := by
      have heq : raw9627step0 = (fun i j => raw9627 (permutation337 i) (permutation13 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9627 permutation337 permutation13
    _ = injectiveMoment H node3169 := by rfl

def raw9628 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-2, 0, 1, 1]]

def raw9628step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, -1, 0, 1], ![0, -1, 0, 1], ![-1, 1, 0, 0], ![-1, 1, 0, 0], ![2, 0, -1, -1]]

def raw9628step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 0, 0]]

theorem canonical9628 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9628 = injectiveMoment H node3397 := by
  calc
    injectiveMoment H raw9628 = injectiveMoment H raw9628step0 := by
      have heq : raw9628step0 = -raw9628 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9628).symm
    injectiveMoment H raw9628step0 = injectiveMoment H raw9628step1 := by
      have heq : raw9628step1 = (fun i j => raw9628step0 (permutation392 i) (permutation26 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9628step0 permutation392 permutation26
    _ = injectiveMoment H node3397 := by rfl

def raw9629 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-2, -1, 2, 1]]

def raw9629step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 0, -1]]

theorem canonical9629 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9629 = injectiveMoment H node3081 := by
  calc
    injectiveMoment H raw9629 = injectiveMoment H raw9629step0 := by
      have heq : raw9629step0 = (fun i j => raw9629 (permutation308 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9629 permutation308 permutation10
    _ = injectiveMoment H node3081 := by rfl

def raw9630 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-2, -1, 1, 2]]

def raw9630step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, -2, 2]]

theorem canonical9630 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9630 = injectiveMoment H node3446 := by
  calc
    injectiveMoment H raw9630 = injectiveMoment H raw9630step0 := by
      have heq : raw9630step0 = (fun i j => raw9630 (permutation178 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9630 permutation178 permutation23
    _ = injectiveMoment H node3446 := by rfl

def raw9631 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -2, 1], ![1, -2, 0, 1], ![-2, 0, 3, -1]]

def raw9631step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -2, 1, 0], ![1, 0, 1, -2]]

theorem canonical9631 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9631 = injectiveMoment H node3141 := by
  calc
    injectiveMoment H raw9631 = injectiveMoment H raw9631step0 := by
      have heq : raw9631step0 = (fun i j => raw9631 (permutation309 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9631 permutation309 permutation10
    _ = injectiveMoment H node3141 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
