import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes1
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes2
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes3
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes4
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes11
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes14
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes20
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes43

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw7584 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, 1, 0, -1], ![0, 1, 1, -2], ![1, -2, -3, 4]]

def raw7584step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 1, 1, -2], ![2, 0, 1, -3], ![-1, -1, -2, 4]]

def raw7584step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, -1, 1], ![0, 1, 2, -3], ![1, 1, 0, -2]]

theorem canonical7584 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7584 = injectiveMoment H node762 := by
  calc
    injectiveMoment H raw7584 = injectiveMoment H raw7584step0 := by
      have heq : raw7584step0 = raw7584.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7584).symm
    injectiveMoment H raw7584step0 = injectiveMoment H raw7584step1 := by
      have heq : raw7584step1 = (fun i j => raw7584step0 (permutation28 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7584step0 permutation28 permutation17
    _ = injectiveMoment H node762 := by rfl

def raw7585 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, 1, 0, -1], ![1, -1, -2, 2]]

def raw7585step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 1, -1], ![2, 0, -2], ![-1, -1, 2]]

def raw7585step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1]]

theorem canonical7585 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7585 = injectiveMoment H node284 := by
  calc
    injectiveMoment H raw7585 = injectiveMoment H raw7585step0 := by
      have heq : raw7585step0 = raw7585.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7585).symm
    injectiveMoment H raw7585step0 = injectiveMoment H raw7585step1 := by
      have heq : raw7585step1 = (fun i j => raw7585step0 (permutation28 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7585step0 permutation28 permutation5
    _ = injectiveMoment H node284 := by rfl

def raw7586 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, 1, 1, -2], ![0, 1, 0, -1], ![1, -2, -3, 4]]

def raw7586step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 1, 1, -2], ![2, 1, 0, -3], ![-1, -2, -1, 4]]

def raw7586step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, -1, 1], ![0, 1, 2, -3], ![1, 1, 0, -2]]

theorem canonical7586 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7586 = injectiveMoment H node762 := by
  calc
    injectiveMoment H raw7586 = injectiveMoment H raw7586step0 := by
      have heq : raw7586step0 = raw7586.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7586).symm
    injectiveMoment H raw7586step0 = injectiveMoment H raw7586step1 := by
      have heq : raw7586step1 = (fun i j => raw7586step0 (permutation28 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7586step0 permutation28 permutation23
    _ = injectiveMoment H node762 := by rfl

def raw7587 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, 1, 1, -2], ![1, -1, -3, 3]]

def raw7587step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 1, -1], ![2, 1, -3], ![-1, -2, 3]]

def raw7587step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![1, 0, -1], ![1, 2, -3]]

theorem canonical7587 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7587 = injectiveMoment H node174 := by
  calc
    injectiveMoment H raw7587 = injectiveMoment H raw7587step0 := by
      have heq : raw7587step0 = raw7587.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7587).symm
    injectiveMoment H raw7587step0 = injectiveMoment H raw7587step1 := by
      have heq : raw7587step1 = (fun i j => raw7587step0 (permutation27 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7587step0 permutation27 permutation5
    _ = injectiveMoment H node174 := by rfl

def raw7588 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, 2, -4, 2], ![1, -2, 2, -1]]

def raw7588step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 2, -2], ![2, -4, 2], ![-1, 2, -1]]

def raw7588step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![0, -2, 2], ![-2, 4, -2], ![1, -2, 1]]

def raw7588step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![1, -1, 0], ![1, 1, -2]]

theorem canonical7588 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7588 = injectiveMoment H node153 := by
  calc
    injectiveMoment H raw7588 = injectiveMoment H raw7588step0 := by
      have heq : raw7588step0 = raw7588.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7588).symm
    injectiveMoment H raw7588step0 = injectiveMoment H raw7588step1 := by
      have heq : raw7588step1 = -raw7588step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7588step0).symm
    injectiveMoment H raw7588step1 = injectiveMoment H raw7588step2 := by
      have heq : raw7588step2 = (fun i j => raw7588step1 (permutation23 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7588step1 permutation23 permutation4
    _ = injectiveMoment H node153 := by rfl

def raw7589 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, 2, -3, 1], ![1, -2, 1, 0]]

def raw7589step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 2, -2], ![2, -3, 1], ![-1, 1, 0]]

def raw7589step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![0, -2, 2], ![-2, 3, -1], ![1, -1, 0]]

def raw7589step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]

theorem canonical7589 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7589 = injectiveMoment H node185 := by
  calc
    injectiveMoment H raw7589 = injectiveMoment H raw7589step0 := by
      have heq : raw7589step0 = raw7589.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7589).symm
    injectiveMoment H raw7589step0 = injectiveMoment H raw7589step1 := by
      have heq : raw7589step1 = -raw7589step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7589step0).symm
    injectiveMoment H raw7589step1 = injectiveMoment H raw7589step2 := by
      have heq : raw7589step2 = (fun i j => raw7589step1 (permutation23 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7589step1 permutation23 permutation4
    _ = injectiveMoment H node185 := by rfl

def raw7590 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, 2, -1, -1], ![1, -2, -1, 2]]

def raw7590step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 2, -2], ![2, -1, -1], ![-1, -1, 2]]

def raw7590step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![0, -2, 2], ![-2, 1, 1], ![1, 1, -2]]

def raw7590step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]

theorem canonical7590 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7590 = injectiveMoment H node210 := by
  calc
    injectiveMoment H raw7590 = injectiveMoment H raw7590step0 := by
      have heq : raw7590step0 = raw7590.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7590).symm
    injectiveMoment H raw7590step0 = injectiveMoment H raw7590step1 := by
      have heq : raw7590step1 = -raw7590step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7590step0).symm
    injectiveMoment H raw7590step1 = injectiveMoment H raw7590step2 := by
      have heq : raw7590step2 = (fun i j => raw7590step1 (permutation15 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7590step1 permutation15 permutation5
    _ = injectiveMoment H node210 := by rfl

def raw7591 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, 2, 0, -2], ![1, -2, -2, 3]]

def raw7591step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 2, -2], ![2, 0, -2], ![-1, -2, 3]]

def raw7591step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 2, -2], ![2, 0, -2]]

theorem canonical7591 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7591 = injectiveMoment H node169 := by
  calc
    injectiveMoment H raw7591 = injectiveMoment H raw7591step0 := by
      have heq : raw7591step0 = raw7591.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7591).symm
    injectiveMoment H raw7591step0 = injectiveMoment H raw7591step1 := by
      have heq : raw7591step1 = (fun i j => raw7591step0 (permutation28 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7591step0 permutation28 permutation5
    _ = injectiveMoment H node169 := by rfl

def raw7592 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, 2, 1, -3], ![1, -2, -3, 4]]

def raw7592step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 2, -2], ![2, 1, -3], ![-1, -3, 4]]

def raw7592step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![0, -2, 2], ![-2, -1, 3], ![1, 3, -4]]

def raw7592step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![1, 0, -1], ![1, 3, -4]]

theorem canonical7592 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7592 = injectiveMoment H node166 := by
  calc
    injectiveMoment H raw7592 = injectiveMoment H raw7592step0 := by
      have heq : raw7592step0 = raw7592.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7592).symm
    injectiveMoment H raw7592step0 = injectiveMoment H raw7592step1 := by
      have heq : raw7592step1 = -raw7592step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7592step0).symm
    injectiveMoment H raw7592step1 = injectiveMoment H raw7592step2 := by
      have heq : raw7592step2 = (fun i j => raw7592step1 (permutation23 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7592step1 permutation23 permutation3
    _ = injectiveMoment H node166 := by rfl

def raw7593 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, 3, -4, 1], ![1, -3, 2, 0]]

def raw7593step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 3, -3], ![2, -4, 2], ![-1, 1, 0]]

def raw7593step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![0, -3, 3], ![-2, 4, -2], ![1, -1, 0]]

def raw7593step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1]]

theorem canonical7593 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7593 = injectiveMoment H node155 := by
  calc
    injectiveMoment H raw7593 = injectiveMoment H raw7593step0 := by
      have heq : raw7593step0 = raw7593.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7593).symm
    injectiveMoment H raw7593step0 = injectiveMoment H raw7593step1 := by
      have heq : raw7593step1 = -raw7593step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7593step0).symm
    injectiveMoment H raw7593step1 = injectiveMoment H raw7593step2 := by
      have heq : raw7593step2 = (fun i j => raw7593step1 (permutation23 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7593step1 permutation23 permutation4
    _ = injectiveMoment H node155 := by rfl

def raw7594 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, 3, -2, -1], ![1, -3, 0, 2]]

def raw7594step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 3, -3], ![2, -2, 0], ![-1, -1, 2]]

def raw7594step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![0, -3, 3], ![-2, 2, 0], ![1, 1, -2]]

def raw7594step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![1, -2, 1], ![1, -1, 0]]

theorem canonical7594 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7594 = injectiveMoment H node215 := by
  calc
    injectiveMoment H raw7594 = injectiveMoment H raw7594step0 := by
      have heq : raw7594step0 = raw7594.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7594).symm
    injectiveMoment H raw7594step0 = injectiveMoment H raw7594step1 := by
      have heq : raw7594step1 = -raw7594step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7594step0).symm
    injectiveMoment H raw7594step1 = injectiveMoment H raw7594step2 := by
      have heq : raw7594step2 = (fun i j => raw7594step1 (permutation24 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7594step1 permutation24 permutation4
    _ = injectiveMoment H node215 := by rfl

def raw7595 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, 3, -1, -2], ![1, -3, -1, 3]]

def raw7595step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 3, -3], ![2, -1, -1], ![-1, -2, 3]]

def raw7595step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![0, -3, 3], ![-2, 1, 1], ![1, 2, -3]]

def raw7595step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -3, 3], ![1, 0, -1], ![1, 2, -3]]

theorem canonical7595 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7595 = injectiveMoment H node222 := by
  calc
    injectiveMoment H raw7595 = injectiveMoment H raw7595step0 := by
      have heq : raw7595step0 = raw7595.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7595).symm
    injectiveMoment H raw7595step0 = injectiveMoment H raw7595step1 := by
      have heq : raw7595step1 = -raw7595step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7595step0).symm
    injectiveMoment H raw7595step1 = injectiveMoment H raw7595step2 := by
      have heq : raw7595step2 = (fun i j => raw7595step1 (permutation23 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7595step1 permutation23 permutation3
    _ = injectiveMoment H node222 := by rfl

def raw7596 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, 3, 0, -3], ![1, -3, -2, 4]]

def raw7596step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 3, -3], ![2, 0, -2], ![-1, -3, 4]]

def raw7596step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![0, -3, 3], ![-2, 0, 2], ![1, 3, -4]]

def raw7596step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![1, 0, -1], ![1, 3, -4]]

theorem canonical7596 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7596 = injectiveMoment H node195 := by
  calc
    injectiveMoment H raw7596 = injectiveMoment H raw7596step0 := by
      have heq : raw7596step0 = raw7596.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7596).symm
    injectiveMoment H raw7596step0 = injectiveMoment H raw7596step1 := by
      have heq : raw7596step1 = -raw7596step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7596step0).symm
    injectiveMoment H raw7596step1 = injectiveMoment H raw7596step2 := by
      have heq : raw7596step2 = (fun i j => raw7596step1 (permutation23 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7596step1 permutation23 permutation3
    _ = injectiveMoment H node195 := by rfl

def raw7597 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, 4, -3, -1], ![1, -4, 1, 2]]

def raw7597step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 4, -4], ![2, -3, 1], ![-1, -1, 2]]

def raw7597step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![0, -4, 4], ![-2, 3, -1], ![1, 1, -2]]

def raw7597step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 4, -4], ![1, -2, 1], ![1, -1, 0]]

theorem canonical7597 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7597 = injectiveMoment H node190 := by
  calc
    injectiveMoment H raw7597 = injectiveMoment H raw7597step0 := by
      have heq : raw7597step0 = raw7597.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7597).symm
    injectiveMoment H raw7597step0 = injectiveMoment H raw7597step1 := by
      have heq : raw7597step1 = -raw7597step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7597step0).symm
    injectiveMoment H raw7597step1 = injectiveMoment H raw7597step2 := by
      have heq : raw7597step2 = (fun i j => raw7597step1 (permutation24 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7597step1 permutation24 permutation4
    _ = injectiveMoment H node190 := by rfl

def raw7598 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![1, -3, 1, 1], ![0, 3, -3, 0]]

def raw7598step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![0, -3, 3], ![2, 1, -3], ![-1, 1, 0]]

def raw7598step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -1, 0], ![0, 3, -3], ![-2, -1, 3], ![1, -1, 0]]

def raw7598step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0]]

theorem canonical7598 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7598 = injectiveMoment H node188 := by
  calc
    injectiveMoment H raw7598 = injectiveMoment H raw7598step0 := by
      have heq : raw7598step0 = raw7598.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7598).symm
    injectiveMoment H raw7598step0 = injectiveMoment H raw7598step1 := by
      have heq : raw7598step1 = -raw7598step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7598step0).symm
    injectiveMoment H raw7598step1 = injectiveMoment H raw7598step2 := by
      have heq : raw7598step2 = (fun i j => raw7598step1 (permutation23 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7598step1 permutation23 permutation3
    _ = injectiveMoment H node188 := by rfl

def raw7599 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![1, -2, -3, 4], ![0, 2, 1, -3]]

def raw7599step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![0, -2, 2], ![2, -3, 1], ![-1, 4, -3]]

def raw7599step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -1, 0], ![0, 2, -2], ![-2, 3, -1], ![1, -4, 3]]

def raw7599step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![1, 0, -1], ![1, 3, -4]]

theorem canonical7599 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7599 = injectiveMoment H node166 := by
  calc
    injectiveMoment H raw7599 = injectiveMoment H raw7599step0 := by
      have heq : raw7599step0 = raw7599.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7599).symm
    injectiveMoment H raw7599step0 = injectiveMoment H raw7599step1 := by
      have heq : raw7599step1 = -raw7599step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7599step0).symm
    injectiveMoment H raw7599step1 = injectiveMoment H raw7599step2 := by
      have heq : raw7599step2 = (fun i j => raw7599step1 (permutation23 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7599step1 permutation23 permutation4
    _ = injectiveMoment H node166 := by rfl

def raw7600 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![1, -2, -1, 2], ![0, 2, -1, -1]]

def raw7600step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![0, -2, 2], ![2, -1, -1], ![-1, 2, -1]]

def raw7600step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -1, 0], ![0, 2, -2], ![-2, 1, 1], ![1, -2, 1]]

def raw7600step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]

theorem canonical7600 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7600 = injectiveMoment H node210 := by
  calc
    injectiveMoment H raw7600 = injectiveMoment H raw7600step0 := by
      have heq : raw7600step0 = raw7600.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7600).symm
    injectiveMoment H raw7600step0 = injectiveMoment H raw7600step1 := by
      have heq : raw7600step1 = -raw7600step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7600step0).symm
    injectiveMoment H raw7600step1 = injectiveMoment H raw7600step2 := by
      have heq : raw7600step2 = (fun i j => raw7600step1 (permutation15 i) (permutation7 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7600step1 permutation15 permutation7
    _ = injectiveMoment H node210 := by rfl

def raw7601 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![1, -2, 0, 1], ![0, 2, -2, 0]]

def raw7601step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![0, -2, 2], ![2, 0, -2], ![-1, 1, 0]]

def raw7601step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]

theorem canonical7601 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7601 = injectiveMoment H node207 := by
  calc
    injectiveMoment H raw7601 = injectiveMoment H raw7601step0 := by
      have heq : raw7601step0 = raw7601.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7601).symm
    injectiveMoment H raw7601step0 = injectiveMoment H raw7601step1 := by
      have heq : raw7601step1 = (fun i j => raw7601step0 (permutation22 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7601step0 permutation22 permutation8
    _ = injectiveMoment H node207 := by rfl

def raw7602 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![1, -2, 2, -1], ![0, 2, -4, 2]]

def raw7602step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![0, -2, 2], ![2, 2, -4], ![-1, -1, 2]]

def raw7602step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -1, 0], ![0, 2, -2], ![-2, -2, 4], ![1, 1, -2]]

def raw7602step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![1, -1, 0], ![1, 1, -2]]

theorem canonical7602 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7602 = injectiveMoment H node153 := by
  calc
    injectiveMoment H raw7602 = injectiveMoment H raw7602step0 := by
      have heq : raw7602step0 = raw7602.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7602).symm
    injectiveMoment H raw7602step0 = injectiveMoment H raw7602step1 := by
      have heq : raw7602step1 = -raw7602step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7602step0).symm
    injectiveMoment H raw7602step1 = injectiveMoment H raw7602step2 := by
      have heq : raw7602step2 = (fun i j => raw7602step1 (permutation23 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7602step1 permutation23 permutation3
    _ = injectiveMoment H node153 := by rfl

def raw7603 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![1, 2, 0, -3], ![0, -2, -2, 4]]

def raw7603step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![0, 2, -2], ![2, 0, -2], ![-1, -3, 4]]

def raw7603step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -1, 0], ![0, -2, 2], ![-2, 0, 2], ![1, 3, -4]]

def raw7603step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![1, -1, 0], ![1, 3, -4]]

theorem canonical7603 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7603 = injectiveMoment H node201 := by
  calc
    injectiveMoment H raw7603 = injectiveMoment H raw7603step0 := by
      have heq : raw7603step0 = raw7603.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7603).symm
    injectiveMoment H raw7603step0 = injectiveMoment H raw7603step1 := by
      have heq : raw7603step1 = -raw7603step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7603step0).symm
    injectiveMoment H raw7603step1 = injectiveMoment H raw7603step2 := by
      have heq : raw7603step2 = (fun i j => raw7603step1 (permutation23 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7603step1 permutation23 permutation3
    _ = injectiveMoment H node201 := by rfl

def raw7604 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![2, -3, 1, 0], ![-1, 3, -3, 1]]

def raw7604step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 2, -1], ![0, -3, 3], ![2, 1, -3], ![-1, 0, 1]]

def raw7604step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -2, 1], ![0, 3, -3], ![-2, -1, 3], ![1, 0, -1]]

def raw7604step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 3, -3], ![1, -2, 1], ![1, 0, -1]]

theorem canonical7604 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7604 = injectiveMoment H node187 := by
  calc
    injectiveMoment H raw7604 = injectiveMoment H raw7604step0 := by
      have heq : raw7604step0 = raw7604.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7604).symm
    injectiveMoment H raw7604step0 = injectiveMoment H raw7604step1 := by
      have heq : raw7604step1 = -raw7604step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7604step0).symm
    injectiveMoment H raw7604step1 = injectiveMoment H raw7604step2 := by
      have heq : raw7604step2 = (fun i j => raw7604step1 (permutation23 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7604step1 permutation23 permutation3
    _ = injectiveMoment H node187 := by rfl

def raw7605 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![2, -2, 0, 0], ![-1, 2, -2, 1]]

def raw7605step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 2, -1], ![0, -2, 2], ![2, 0, -2], ![-1, 0, 1]]

def raw7605step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]

theorem canonical7605 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7605 = injectiveMoment H node203 := by
  calc
    injectiveMoment H raw7605 = injectiveMoment H raw7605step0 := by
      have heq : raw7605step0 = raw7605.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7605).symm
    injectiveMoment H raw7605step0 = injectiveMoment H raw7605step1 := by
      have heq : raw7605step1 = (fun i j => raw7605step0 (permutation20 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7605step0 permutation20 permutation5
    _ = injectiveMoment H node203 := by rfl

def raw7606 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![2, -2, 1, -1], ![-1, 2, -3, 2]]

def raw7606step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 2, -1], ![0, -2, 2], ![2, 1, -3], ![-1, -1, 2]]

def raw7606step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -2, 1], ![0, 2, -2], ![-2, -1, 3], ![1, 1, -2]]

def raw7606step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, -2, 1], ![1, 1, -2]]

theorem canonical7606 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7606 = injectiveMoment H node184 := by
  calc
    injectiveMoment H raw7606 = injectiveMoment H raw7606step0 := by
      have heq : raw7606step0 = raw7606.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7606).symm
    injectiveMoment H raw7606step0 = injectiveMoment H raw7606step1 := by
      have heq : raw7606step1 = -raw7606step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7606step0).symm
    injectiveMoment H raw7606step1 = injectiveMoment H raw7606step2 := by
      have heq : raw7606step2 = (fun i j => raw7606step1 (permutation23 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7606step1 permutation23 permutation3
    _ = injectiveMoment H node184 := by rfl

def raw7607 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![3, -3, 0, 0], ![-2, 3, -2, 1]]

def raw7607step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 3, -2], ![0, -3, 3], ![2, 0, -2], ![-1, 0, 1]]

def raw7607step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![0, 3, -3], ![-2, 0, 2], ![1, 0, -1]]

def raw7607step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![1, -3, 2], ![1, 0, -1]]

theorem canonical7607 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7607 = injectiveMoment H node214 := by
  calc
    injectiveMoment H raw7607 = injectiveMoment H raw7607step0 := by
      have heq : raw7607step0 = raw7607.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7607).symm
    injectiveMoment H raw7607step0 = injectiveMoment H raw7607step1 := by
      have heq : raw7607step1 = -raw7607step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7607step0).symm
    injectiveMoment H raw7607step1 = injectiveMoment H raw7607step2 := by
      have heq : raw7607step2 = (fun i j => raw7607step1 (permutation23 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7607step1 permutation23 permutation3
    _ = injectiveMoment H node214 := by rfl

def raw7608 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![3, -2, 0, -1], ![-2, 2, -2, 2]]

def raw7608step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 3, -2], ![0, -2, 2], ![2, 0, -2], ![-1, -1, 2]]

def raw7608step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![0, 2, -2], ![-2, 0, 2], ![1, 1, -2]]

def raw7608step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![1, -3, 2], ![1, 1, -2]]

theorem canonical7608 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7608 = injectiveMoment H node212 := by
  calc
    injectiveMoment H raw7608 = injectiveMoment H raw7608step0 := by
      have heq : raw7608step0 = raw7608.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7608).symm
    injectiveMoment H raw7608step0 = injectiveMoment H raw7608step1 := by
      have heq : raw7608step1 = -raw7608step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7608step0).symm
    injectiveMoment H raw7608step1 = injectiveMoment H raw7608step2 := by
      have heq : raw7608step2 = (fun i j => raw7608step1 (permutation23 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7608step1 permutation23 permutation3
    _ = injectiveMoment H node212 := by rfl

def raw7609 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 3, -2], ![-1, 0, -3, 4], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw7609step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 0, -3, 2], ![1, 0, 3, -4], ![0, -1, 0, 1], ![-1, 1, 0, 0], ![-1, 0, 0, 1]]

def raw7609step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, 1, -3, 2], ![0, 1, 3, -4], ![1, -1, 0, 0]]

theorem canonical7609 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7609 = injectiveMoment H node2766 := by
  calc
    injectiveMoment H raw7609 = injectiveMoment H raw7609step0 := by
      have heq : raw7609step0 = -raw7609 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7609).symm
    injectiveMoment H raw7609step0 = injectiveMoment H raw7609step1 := by
      have heq : raw7609step1 = (fun i j => raw7609step0 (permutation98 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7609step0 permutation98 permutation15
    _ = injectiveMoment H node2766 := by rfl

def raw7610 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 3, -2], ![-1, 0, -2, 3], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 0, 0, -1]]

def raw7610step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 0, -3, 2], ![1, 0, 2, -3], ![0, -1, 0, 1], ![-1, 1, 1, -1], ![-1, 0, 0, 1]]

def raw7610step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, 1, -3, 2], ![0, 1, 2, -3], ![1, -1, 1, -1]]

theorem canonical7610 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7610 = injectiveMoment H node2765 := by
  calc
    injectiveMoment H raw7610 = injectiveMoment H raw7610step0 := by
      have heq : raw7610step0 = -raw7610 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7610).symm
    injectiveMoment H raw7610step0 = injectiveMoment H raw7610step1 := by
      have heq : raw7610step1 = (fun i j => raw7610step0 (permutation98 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7610step0 permutation98 permutation15
    _ = injectiveMoment H node2765 := by rfl

def raw7611 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 3, -2], ![0, -3, 1, 2], ![1, 3, -4, 0]]

def raw7611step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -3, 3], ![3, 1, -4], ![-2, 2, 0]]

def raw7611step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![0, 3, -3], ![-3, -1, 4], ![2, -2, 0]]

def raw7611step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, 0, -1], ![2, -2, 0]]

theorem canonical7611 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7611 = injectiveMoment H node88 := by
  calc
    injectiveMoment H raw7611 = injectiveMoment H raw7611step0 := by
      have heq : raw7611step0 = raw7611.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7611).symm
    injectiveMoment H raw7611step0 = injectiveMoment H raw7611step1 := by
      have heq : raw7611step1 = -raw7611step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7611step0).symm
    injectiveMoment H raw7611step1 = injectiveMoment H raw7611step2 := by
      have heq : raw7611step2 = (fun i j => raw7611step1 (permutation23 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7611step1 permutation23 permutation3
    _ = injectiveMoment H node88 := by rfl

def raw7612 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 3, -2], ![0, -1, -3, 4], ![0, 1, 0, -1], ![1, 0, 0, -1]]

def raw7612step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 1, 0], ![3, -3, 0, 0], ![-2, 4, -1, -1]]

def raw7612step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 3, -3], ![0, 1, -1, 0], ![1, 0, 0, -1]]

theorem canonical7612 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7612 = injectiveMoment H node919 := by
  calc
    injectiveMoment H raw7612 = injectiveMoment H raw7612step0 := by
      have heq : raw7612step0 = raw7612.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7612).symm
    injectiveMoment H raw7612step0 = injectiveMoment H raw7612step1 := by
      have heq : raw7612step1 = (fun i j => raw7612step0 (permutation31 i) (permutation25 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7612step0 permutation31 permutation25
    _ = injectiveMoment H node919 := by rfl

def raw7613 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 3, -2], ![0, -1, -3, 4], ![0, 2, 0, -2], ![1, -1, 0, 0]]

def raw7613step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 2, -1], ![3, -3, 0, 0], ![-2, 4, -2, 0]]

def raw7613step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 0, -1], ![0, 1, -2, 1], ![-3, 3, 0, 0], ![2, -4, 2, 0]]

def raw7613step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, 0, -3, 3], ![0, 2, 2, -4], ![1, -2, 0, 1]]

theorem canonical7613 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7613 = injectiveMoment H node1300 := by
  calc
    injectiveMoment H raw7613 = injectiveMoment H raw7613step0 := by
      have heq : raw7613step0 = raw7613.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7613).symm
    injectiveMoment H raw7613step0 = injectiveMoment H raw7613step1 := by
      have heq : raw7613step1 = -raw7613step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7613step0).symm
    injectiveMoment H raw7613step1 = injectiveMoment H raw7613step2 := by
      have heq : raw7613step2 = (fun i j => raw7613step1 (permutation12 i) (permutation31 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7613step1 permutation12 permutation31
    _ = injectiveMoment H node1300 := by rfl

def raw7614 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 3, -2], ![0, -1, -1, 2], ![0, 0, -2, 2], ![1, 1, 0, -2]]

def raw7614step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, -3, 2], ![0, 1, 1, -2], ![0, 0, 2, -2], ![-1, -1, 0, 2]]

def raw7614step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 1, -3, 2], ![1, 0, 1, -2]]

theorem canonical7614 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7614 = injectiveMoment H node1052 := by
  calc
    injectiveMoment H raw7614 = injectiveMoment H raw7614step0 := by
      have heq : raw7614step0 = -raw7614 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7614).symm
    injectiveMoment H raw7614step0 = injectiveMoment H raw7614step1 := by
      have heq : raw7614step1 = (fun i j => raw7614step0 (permutation31 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7614step0 permutation31 permutation15
    _ = injectiveMoment H node1052 := by rfl

def raw7615 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 3, -2], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -2, -3, 4]]

def raw7615step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 1, 1, -2], ![3, 0, 0, -3], ![-2, -1, -1, 4]]

def raw7615step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, -1, 1], ![0, 0, 3, -3], ![1, 1, 0, -2]]

theorem canonical7615 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7615 = injectiveMoment H node905 := by
  calc
    injectiveMoment H raw7615 = injectiveMoment H raw7615step0 := by
      have heq : raw7615step0 = raw7615.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7615).symm
    injectiveMoment H raw7615step0 = injectiveMoment H raw7615step1 := by
      have heq : raw7615step1 = (fun i j => raw7615step0 (permutation28 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7615step0 permutation28 permutation17
    _ = injectiveMoment H node905 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
