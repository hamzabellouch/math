import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes2
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes5
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes8
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes10
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes13
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes28
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes29
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes33
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes38

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw608 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -2, 1], ![2, -1, -1], ![2, 0, -2]]

def raw608step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -2, 0], ![-1, 2, -1], ![-2, 1, 1], ![-2, 0, 2]]

def raw608step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]

theorem canonical608 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw608 = injectiveMoment H node534 := by
  calc
    injectiveMoment H raw608 = injectiveMoment H raw608step0 := by
      have heq : raw608step0 = -raw608 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw608).symm
    injectiveMoment H raw608step0 = injectiveMoment H raw608step1 := by
      have heq : raw608step1 = (fun i j => raw608step0 (permutation39 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw608step0 permutation39 permutation8
    _ = injectiveMoment H node534 := by rfl

def raw609 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]

def raw609step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![2, -2, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]

def raw609step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]

theorem canonical609 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw609 = injectiveMoment H node1871 := by
  calc
    injectiveMoment H raw609 = injectiveMoment H raw609step0 := by
      have heq : raw609step0 = -raw609 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw609).symm
    injectiveMoment H raw609step0 = injectiveMoment H raw609step1 := by
      have heq : raw609step1 = (fun i j => raw609step0 (permutation151 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw609step0 permutation151 permutation8
    _ = injectiveMoment H node1871 := by rfl

def raw610 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]

def raw610step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -2, 0], ![-1, 1, 0], ![-1, 1, 0], ![-3, 1, 2]]

def raw610step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![2, 1, -3]]

theorem canonical610 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw610 = injectiveMoment H node541 := by
  calc
    injectiveMoment H raw610 = injectiveMoment H raw610step0 := by
      have heq : raw610step0 = -raw610 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw610).symm
    injectiveMoment H raw610step0 = injectiveMoment H raw610step1 := by
      have heq : raw610step1 = (fun i j => raw610step0 (permutation33 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw610step0 permutation33 permutation8
    _ = injectiveMoment H node541 := by rfl

def raw611 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]

def raw611step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -2, 0], ![-1, 1, 0], ![-1, 0, 1], ![-3, 2, 1]]

def raw611step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 2, -3]]

theorem canonical611 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw611 = injectiveMoment H node544 := by
  calc
    injectiveMoment H raw611 = injectiveMoment H raw611step0 := by
      have heq : raw611step0 = -raw611 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw611).symm
    injectiveMoment H raw611step0 = injectiveMoment H raw611step1 := by
      have heq : raw611step1 = (fun i j => raw611step0 (permutation33 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw611step0 permutation33 permutation8
    _ = injectiveMoment H node544 := by rfl

def raw612 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]

def raw612step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -2, 0], ![-1, 1, 0], ![-2, 2, 0], ![-2, 0, 2]]

def raw612step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![2, 0, -2]]

theorem canonical612 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw612 = injectiveMoment H node542 := by
  calc
    injectiveMoment H raw612 = injectiveMoment H raw612step0 := by
      have heq : raw612step0 = -raw612 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw612).symm
    injectiveMoment H raw612step0 = injectiveMoment H raw612step1 := by
      have heq : raw612step1 = (fun i j => raw612step0 (permutation33 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw612step0 permutation33 permutation8
    _ = injectiveMoment H node542 := by rfl

def raw613 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]

def raw613step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -2, 0], ![-1, 1, 0], ![-2, 1, 1], ![-2, 1, 1]]

def raw613step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![1, 1, -2]]

theorem canonical613 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw613 = injectiveMoment H node545 := by
  calc
    injectiveMoment H raw613 = injectiveMoment H raw613step0 := by
      have heq : raw613step0 = -raw613 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw613).symm
    injectiveMoment H raw613step0 = injectiveMoment H raw613step1 := by
      have heq : raw613step1 = (fun i j => raw613step0 (permutation33 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw613step0 permutation33 permutation8
    _ = injectiveMoment H node545 := by rfl

def raw614 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]

def raw614step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![1, 2, -3], ![2, 0, -2]]

theorem canonical614 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw614 = injectiveMoment H node353 := by
  calc
    injectiveMoment H raw614 = injectiveMoment H raw614step0 := by
      have heq : raw614step0 = (fun i j => raw614 (permutation126 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw614 permutation126 permutation6
    _ = injectiveMoment H node353 := by rfl

def raw615 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]

def raw615step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -2, 0], ![-1, 0, 1], ![-2, 2, 0], ![-2, 1, 1]]

def raw615step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![1, 1, -2]]

theorem canonical615 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw615 = injectiveMoment H node547 := by
  calc
    injectiveMoment H raw615 = injectiveMoment H raw615step0 := by
      have heq : raw615step0 = -raw615 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw615).symm
    injectiveMoment H raw615step0 = injectiveMoment H raw615step1 := by
      have heq : raw615step1 = (fun i j => raw615step0 (permutation35 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw615step0 permutation35 permutation8
    _ = injectiveMoment H node547 := by rfl

def raw616 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![2, -2, 0], ![3, -1, -2]]

def raw616step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 2, -2], ![2, 1, -3]]

theorem canonical616 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw616 = injectiveMoment H node162 := by
  calc
    injectiveMoment H raw616 = injectiveMoment H raw616step0 := by
      have heq : raw616step0 = (fun i j => raw616 (permutation32 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw616 permutation32 permutation8
    _ = injectiveMoment H node162 := by rfl

def raw617 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]

def raw617step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 2, -3]]

theorem canonical617 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw617 = injectiveMoment H node2458 := by
  calc
    injectiveMoment H raw617 = injectiveMoment H raw617step0 := by
      have heq : raw617step0 = (fun i j => raw617 (permutation392 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw617 permutation392 permutation6
    _ = injectiveMoment H node2458 := by rfl

def raw618 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]

def raw618step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-3, 2, 1]]

def raw618step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]

theorem canonical618 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw618 = injectiveMoment H node1850 := by
  calc
    injectiveMoment H raw618 = injectiveMoment H raw618step0 := by
      have heq : raw618step0 = -raw618 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw618).symm
    injectiveMoment H raw618step0 = injectiveMoment H raw618step1 := by
      have heq : raw618step1 = (fun i j => raw618step0 (permutation152 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw618step0 permutation152 permutation8
    _ = injectiveMoment H node1850 := by rfl

def raw619 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]

def raw619step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 1, 0], ![-2, 1, 1], ![-2, 0, 2]]

def raw619step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![1, 1, -2]]

theorem canonical619 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw619 = injectiveMoment H node2460 := by
  calc
    injectiveMoment H raw619 = injectiveMoment H raw619step0 := by
      have heq : raw619step0 = -raw619 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw619).symm
    injectiveMoment H raw619step0 = injectiveMoment H raw619step1 := by
      have heq : raw619step1 = (fun i j => raw619step0 (permutation168 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw619step0 permutation168 permutation6
    _ = injectiveMoment H node2460 := by rfl

def raw620 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]

def raw620step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 2, -3]]

theorem canonical620 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw620 = injectiveMoment H node1876 := by
  calc
    injectiveMoment H raw620 = injectiveMoment H raw620step0 := by
      have heq : raw620step0 = (fun i j => raw620 (permutation392 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw620 permutation392 permutation6
    _ = injectiveMoment H node1876 := by rfl

def raw621 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]

def raw621step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 2, -3]]

theorem canonical621 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw621 = injectiveMoment H node2114 := by
  calc
    injectiveMoment H raw621 = injectiveMoment H raw621step0 := by
      have heq : raw621step0 = (fun i j => raw621 (permutation306 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw621 permutation306 permutation6
    _ = injectiveMoment H node2114 := by rfl

def raw622 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]

def raw622step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![1, -1, 0], ![-1, -1, 2], ![-2, 2, 0], ![-2, 1, 1]]

def raw622step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]

theorem canonical622 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw622 = injectiveMoment H node1851 := by
  calc
    injectiveMoment H raw622 = injectiveMoment H raw622step0 := by
      have heq : raw622step0 = -raw622 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw622).symm
    injectiveMoment H raw622step0 = injectiveMoment H raw622step1 := by
      have heq : raw622step1 = (fun i j => raw622step0 (permutation154 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw622step0 permutation154 permutation8
    _ = injectiveMoment H node1851 := by rfl

def raw623 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]

def raw623step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![1, -2, 1], ![-1, 1, 0], ![-2, 2, 0], ![-2, 0, 2]]

def raw623step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]

theorem canonical623 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw623 = injectiveMoment H node1852 := by
  calc
    injectiveMoment H raw623 = injectiveMoment H raw623step0 := by
      have heq : raw623step0 = -raw623 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw623).symm
    injectiveMoment H raw623step0 = injectiveMoment H raw623step1 := by
      have heq : raw623step1 = (fun i j => raw623step0 (permutation158 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw623step0 permutation158 permutation8
    _ = injectiveMoment H node1852 := by rfl

def raw624 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]

def raw624step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![1, -2, 1], ![-1, 0, 1], ![-2, 2, 0], ![-2, 1, 1]]

def raw624step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]

theorem canonical624 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw624 = injectiveMoment H node1855 := by
  calc
    injectiveMoment H raw624 = injectiveMoment H raw624step0 := by
      have heq : raw624step0 = -raw624 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw624).symm
    injectiveMoment H raw624step0 = injectiveMoment H raw624step1 := by
      have heq : raw624step1 = (fun i j => raw624step0 (permutation162 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw624step0 permutation162 permutation8
    _ = injectiveMoment H node1855 := by rfl

def raw625 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]

def raw625step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]

theorem canonical625 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw625 = injectiveMoment H node1854 := by
  calc
    injectiveMoment H raw625 = injectiveMoment H raw625step0 := by
      have heq : raw625step0 = (fun i j => raw625 (permutation401 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw625 permutation401 permutation6
    _ = injectiveMoment H node1854 := by rfl

def raw626 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]

def raw626step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-2, 2, 0], ![-2, 1, 1]]

def raw626step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]

theorem canonical626 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw626 = injectiveMoment H node1856 := by
  calc
    injectiveMoment H raw626 = injectiveMoment H raw626step0 := by
      have heq : raw626step0 = -raw626 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw626).symm
    injectiveMoment H raw626step0 = injectiveMoment H raw626step1 := by
      have heq : raw626step1 = (fun i j => raw626step0 (permutation162 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw626step0 permutation162 permutation8
    _ = injectiveMoment H node1856 := by rfl

def raw627 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]

def raw627step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]

def raw627step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1]]

theorem canonical627 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw627 = injectiveMoment H node2467 := by
  calc
    injectiveMoment H raw627 = injectiveMoment H raw627step0 := by
      have heq : raw627step0 = -raw627 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw627).symm
    injectiveMoment H raw627step0 = injectiveMoment H raw627step1 := by
      have heq : raw627step1 = (fun i j => raw627step0 (permutation168 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw627step0 permutation168 permutation6
    _ = injectiveMoment H node2467 := by rfl

def raw628 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]

def raw628step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]

def raw628step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]

theorem canonical628 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw628 = injectiveMoment H node2466 := by
  calc
    injectiveMoment H raw628 = injectiveMoment H raw628step0 := by
      have heq : raw628step0 = -raw628 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw628).symm
    injectiveMoment H raw628step0 = injectiveMoment H raw628step1 := by
      have heq : raw628step1 = (fun i j => raw628step0 (permutation167 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw628step0 permutation167 permutation6
    _ = injectiveMoment H node2466 := by rfl

def raw629 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]

def raw629step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 2, -3]]

theorem canonical629 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw629 = injectiveMoment H node862 := by
  calc
    injectiveMoment H raw629 = injectiveMoment H raw629step0 := by
      have heq : raw629step0 = (fun i j => raw629 (permutation148 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw629 permutation148 permutation6
    _ = injectiveMoment H node862 := by rfl

def raw630 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]

def raw630step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 2, -3]]

theorem canonical630 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw630 = injectiveMoment H node2128 := by
  calc
    injectiveMoment H raw630 = injectiveMoment H raw630step0 := by
      have heq : raw630step0 = (fun i j => raw630 (permutation392 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw630 permutation392 permutation6
    _ = injectiveMoment H node2128 := by rfl

def raw631 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]

def raw631step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 2, -3]]

theorem canonical631 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw631 = injectiveMoment H node559 := by
  calc
    injectiveMoment H raw631 = injectiveMoment H raw631step0 := by
      have heq : raw631step0 = (fun i j => raw631 (permutation148 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw631 permutation148 permutation6
    _ = injectiveMoment H node559 := by rfl

def raw632 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]

def raw632step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 2, -3]]

theorem canonical632 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw632 = injectiveMoment H node645 := by
  calc
    injectiveMoment H raw632 = injectiveMoment H raw632step0 := by
      have heq : raw632step0 = (fun i j => raw632 (permutation125 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw632 permutation125 permutation6
    _ = injectiveMoment H node645 := by rfl

def raw633 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]

def raw633step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-2, 1, 1], ![-2, 1, 1]]

def raw633step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![1, 1, -2]]

theorem canonical633 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw633 = injectiveMoment H node866 := by
  calc
    injectiveMoment H raw633 = injectiveMoment H raw633step0 := by
      have heq : raw633step0 = -raw633 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw633).symm
    injectiveMoment H raw633step0 = injectiveMoment H raw633step1 := by
      have heq : raw633step1 = (fun i j => raw633step0 (permutation39 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw633step0 permutation39 permutation6
    _ = injectiveMoment H node866 := by rfl

def raw634 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]

def raw634step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 2, -3], ![2, -2, 0]]

theorem canonical634 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw634 = injectiveMoment H node527 := by
  calc
    injectiveMoment H raw634 = injectiveMoment H raw634step0 := by
      have heq : raw634step0 = (fun i j => raw634 (permutation147 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw634 permutation147 permutation6
    _ = injectiveMoment H node527 := by rfl

def raw635 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]

def raw635step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -2, 2], ![-2, 2, 0], ![-2, 1, 1]]

def raw635step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]

theorem canonical635 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw635 = injectiveMoment H node529 := by
  calc
    injectiveMoment H raw635 = injectiveMoment H raw635step0 := by
      have heq : raw635step0 = -raw635 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw635).symm
    injectiveMoment H raw635step0 = injectiveMoment H raw635step1 := by
      have heq : raw635step1 = (fun i j => raw635step0 (permutation36 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw635step0 permutation36 permutation8
    _ = injectiveMoment H node529 := by rfl

def raw636 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]

def raw636step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]

def raw636step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]

theorem canonical636 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw636 = injectiveMoment H node2471 := by
  calc
    injectiveMoment H raw636 = injectiveMoment H raw636step0 := by
      have heq : raw636step0 = -raw636 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw636).symm
    injectiveMoment H raw636step0 = injectiveMoment H raw636step1 := by
      have heq : raw636step1 = (fun i j => raw636step0 (permutation198 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw636step0 permutation198 permutation6
    _ = injectiveMoment H node2471 := by rfl

def raw637 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]

def raw637step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![-2, -1, 3]]

def raw637step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 3, -2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]

theorem canonical637 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw637 = injectiveMoment H node876 := by
  calc
    injectiveMoment H raw637 = injectiveMoment H raw637step0 := by
      have heq : raw637step0 = -raw637 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw637).symm
    injectiveMoment H raw637step0 = injectiveMoment H raw637step1 := by
      have heq : raw637step1 = (fun i j => raw637step0 (permutation51 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw637step0 permutation51 permutation6
    _ = injectiveMoment H node876 := by rfl

def raw638 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]

def raw638step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]

def raw638step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2]]

theorem canonical638 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw638 = injectiveMoment H node870 := by
  calc
    injectiveMoment H raw638 = injectiveMoment H raw638step0 := by
      have heq : raw638step0 = -raw638 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw638).symm
    injectiveMoment H raw638step0 = injectiveMoment H raw638step1 := by
      have heq : raw638step1 = (fun i j => raw638step0 (permutation45 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw638step0 permutation45 permutation6
    _ = injectiveMoment H node870 := by rfl

def raw639 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]

def raw639step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]

theorem canonical639 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw639 = injectiveMoment H node378 := by
  calc
    injectiveMoment H raw639 = injectiveMoment H raw639step0 := by
      have heq : raw639step0 = (fun i j => raw639 (permutation127 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw639 permutation127 permutation8
    _ = injectiveMoment H node378 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
