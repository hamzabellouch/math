import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes0
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes1
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes2
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes3
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes8
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes10
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes13
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes29

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw576 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]

def raw576step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -3, 3], ![1, 1, -2], ![1, 1, -2]]

theorem canonical576 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw576 = injectiveMoment H node223 := by
  calc
    injectiveMoment H raw576 = injectiveMoment H raw576step0 := by
      have heq : raw576step0 = (fun i j => raw576 (permutation15 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw576 permutation15 permutation5
    _ = injectiveMoment H node223 := by rfl

def raw577 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -2, 1], ![2, 2, -4]]

def raw577step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 0, -3], ![-1, 2, -1], ![-2, -2, 4]]

def raw577step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 3, -3], ![2, -1, -1]]

theorem canonical577 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw577 = injectiveMoment H node32 := by
  calc
    injectiveMoment H raw577 = injectiveMoment H raw577step0 := by
      have heq : raw577step0 = -raw577 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw577).symm
    injectiveMoment H raw577step0 = injectiveMoment H raw577step1 := by
      have heq : raw577step1 = (fun i j => raw577step0 (permutation7 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw577step0 permutation7 permutation5
    _ = injectiveMoment H node32 := by rfl

def raw578 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]

def raw578step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![-1, 1, 0], ![-1, 1, 0], ![-1, -2, 3]]

def raw578step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0]]

theorem canonical578 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw578 = injectiveMoment H node188 := by
  calc
    injectiveMoment H raw578 = injectiveMoment H raw578step0 := by
      have heq : raw578step0 = -raw578 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw578).symm
    injectiveMoment H raw578step0 = injectiveMoment H raw578step1 := by
      have heq : raw578step1 = (fun i j => raw578step0 (permutation27 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw578step0 permutation27 permutation5
    _ = injectiveMoment H node188 := by rfl

def raw579 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![1, -2, 1], ![1, 1, -2]]

def raw579step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -3, 3], ![1, 1, -2], ![1, 1, -2]]

theorem canonical579 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw579 = injectiveMoment H node223 := by
  calc
    injectiveMoment H raw579 = injectiveMoment H raw579step0 := by
      have heq : raw579step0 = (fun i j => raw579 (permutation21 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw579 permutation21 permutation5
    _ = injectiveMoment H node223 := by rfl

def raw580 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![2, -1, -1]]

def raw580step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 3, -3], ![1, -2, 1]]

theorem canonical580 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw580 = injectiveMoment H node63 := by
  calc
    injectiveMoment H raw580 = injectiveMoment H raw580step0 := by
      have heq : raw580step0 = (fun i j => raw580 (permutation7 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw580 permutation7 permutation6
    _ = injectiveMoment H node63 := by rfl

def raw581 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 2, -3], ![1, -3, 2], ![1, 1, -2]]

def raw581step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -3, 2], ![1, 1, -2], ![1, 2, -3]]

theorem canonical581 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw581 = injectiveMoment H node100 := by
  calc
    injectiveMoment H raw581 = injectiveMoment H raw581step0 := by
      have heq : raw581step0 = (fun i j => raw581 (permutation12 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw581 permutation12 permutation3
    _ = injectiveMoment H node100 := by rfl

def raw582 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 2, -3], ![2, -2, 0]]

def raw582step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 0, -3], ![-1, -2, 3], ![-2, 2, 0]]

def raw582step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 3, -3], ![2, -2, 0]]

theorem canonical582 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw582 = injectiveMoment H node37 := by
  calc
    injectiveMoment H raw582 = injectiveMoment H raw582step0 := by
      have heq : raw582step0 = -raw582 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw582).symm
    injectiveMoment H raw582step0 = injectiveMoment H raw582step1 := by
      have heq : raw582step1 = (fun i j => raw582step0 (permutation5 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw582step0 permutation5 permutation5
    _ = injectiveMoment H node37 := by rfl

def raw583 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 3, -4], ![2, -3, 1]]

def raw583step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 0, -3], ![-1, -3, 4], ![-2, 3, -1]]

def raw583step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![3, -2, -1]]

theorem canonical583 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw583 = injectiveMoment H node18 := by
  calc
    injectiveMoment H raw583 = injectiveMoment H raw583step0 := by
      have heq : raw583step0 = -raw583 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw583).symm
    injectiveMoment H raw583step0 = injectiveMoment H raw583step1 := by
      have heq : raw583step1 = (fun i j => raw583step0 (permutation5 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw583step0 permutation5 permutation5
    _ = injectiveMoment H node18 := by rfl

def raw584 : Matrix (Fin 3) (Fin 4) ℤ := ![![-3, 0, 3, 0], ![-1, 2, -2, 1], ![4, -2, -1, -1]]

def raw584step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![3, -2, -1], ![0, 1, -1]]

def raw584step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![3, -2, -1]]

theorem canonical584 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw584 = injectiveMoment H node81 := by
  calc
    injectiveMoment H raw584 = injectiveMoment H raw584step0 := by
      have heq : raw584step0 = raw584.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw584).symm
    injectiveMoment H raw584step0 = injectiveMoment H raw584step1 := by
      have heq : raw584step1 = (fun i j => raw584step0 (permutation13 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw584step0 permutation13 permutation3
    _ = injectiveMoment H node81 := by rfl

def raw585 : Matrix (Fin 3) (Fin 4) ℤ := ![![-3, 0, 3, 0], ![0, 2, -1, -1], ![3, -2, -2, 1]]

def raw585step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![3, -1, -2], ![0, -1, 1]]

def raw585step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-3, 1, 2], ![0, 1, -1]]

def raw585step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![1, -3, 2], ![1, 0, -1]]

theorem canonical585 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw585 = injectiveMoment H node214 := by
  calc
    injectiveMoment H raw585 = injectiveMoment H raw585step0 := by
      have heq : raw585step0 = raw585.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw585).symm
    injectiveMoment H raw585step0 = injectiveMoment H raw585step1 := by
      have heq : raw585step1 = -raw585step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw585step0).symm
    injectiveMoment H raw585step1 = injectiveMoment H raw585step2 := by
      have heq : raw585step2 = (fun i j => raw585step1 (permutation15 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw585step1 permutation15 permutation5
    _ = injectiveMoment H node214 := by rfl

def raw586 : Matrix (Fin 3) (Fin 4) ℤ := ![![-3, 0, 3, 0], ![1, -2, -1, 2], ![2, 2, -2, -2]]

def raw586step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![3, -1, -2], ![0, 2, -2]]

def raw586step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![3, -1, -2]]

theorem canonical586 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw586 = injectiveMoment H node101 := by
  calc
    injectiveMoment H raw586 = injectiveMoment H raw586step0 := by
      have heq : raw586step0 = raw586.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw586).symm
    injectiveMoment H raw586step0 = injectiveMoment H raw586step1 := by
      have heq : raw586step1 = (fun i j => raw586step0 (permutation10 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw586step0 permutation10 permutation3
    _ = injectiveMoment H node101 := by rfl

def raw587 : Matrix (Fin 3) (Fin 4) ℤ := ![![-3, 0, 3, 0], ![1, 2, -1, -2], ![2, -2, -2, 2]]

def raw587step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![3, -1, -2], ![0, -2, 2]]

def raw587step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![3, -1, -2]]

theorem canonical587 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw587 = injectiveMoment H node101 := by
  calc
    injectiveMoment H raw587 = injectiveMoment H raw587step0 := by
      have heq : raw587step0 = raw587.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw587).symm
    injectiveMoment H raw587step0 = injectiveMoment H raw587step1 := by
      have heq : raw587step1 = (fun i j => raw587step0 (permutation13 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw587step0 permutation13 permutation3
    _ = injectiveMoment H node101 := by rfl

def raw588 : Matrix (Fin 3) (Fin 4) ℤ := ![![-3, 0, 3, 0], ![2, -2, -1, 1], ![1, 2, -2, -1]]

def raw588step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![3, -1, -2], ![0, 1, -1]]

def raw588step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![3, -2, -1]]

theorem canonical588 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw588 = injectiveMoment H node105 := by
  calc
    injectiveMoment H raw588 = injectiveMoment H raw588step0 := by
      have heq : raw588step0 = raw588.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw588).symm
    injectiveMoment H raw588step0 = injectiveMoment H raw588step1 := by
      have heq : raw588step1 = (fun i j => raw588step0 (permutation13 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw588step0 permutation13 permutation4
    _ = injectiveMoment H node105 := by rfl

def raw589 : Matrix (Fin 3) (Fin 4) ℤ := ![![-3, 1, 1, 1], ![-1, -2, 1, 2], ![4, 1, -2, -3]]

def raw589step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -2, 1], ![1, 1, -2], ![1, 2, -3]]

theorem canonical589 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw589 = injectiveMoment H node89 := by
  calc
    injectiveMoment H raw589 = injectiveMoment H raw589step0 := by
      have heq : raw589step0 = raw589.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw589).symm
    _ = injectiveMoment H node89 := by rfl

def raw590 : Matrix (Fin 3) (Fin 4) ℤ := ![![-3, 1, 1, 1], ![-1, -2, 2, 1], ![4, 1, -3, -2]]

def raw590step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -2, 1], ![1, 2, -3], ![1, 1, -2]]

def raw590step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -2, 1], ![1, 1, -2], ![1, 2, -3]]

theorem canonical590 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw590 = injectiveMoment H node89 := by
  calc
    injectiveMoment H raw590 = injectiveMoment H raw590step0 := by
      have heq : raw590step0 = raw590.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw590).symm
    injectiveMoment H raw590step0 = injectiveMoment H raw590step1 := by
      have heq : raw590step1 = (fun i j => raw590step0 (permutation10 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw590step0 permutation10 permutation3
    _ = injectiveMoment H node89 := by rfl

def raw591 : Matrix (Fin 3) (Fin 4) ℤ := ![![-3, 1, 1, 1], ![-1, 1, 2, -2], ![4, -2, -3, 1]]

def raw591step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, 1, -2], ![1, 2, -3], ![1, -2, 1]]

def raw591step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -2, 1], ![1, 1, -2], ![1, 2, -3]]

theorem canonical591 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw591 = injectiveMoment H node89 := by
  calc
    injectiveMoment H raw591 = injectiveMoment H raw591step0 := by
      have heq : raw591step0 = raw591.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw591).symm
    injectiveMoment H raw591step0 = injectiveMoment H raw591step1 := by
      have heq : raw591step1 = (fun i j => raw591step0 (permutation13 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw591step0 permutation13 permutation3
    _ = injectiveMoment H node89 := by rfl

def raw592 : Matrix (Fin 3) (Fin 4) ℤ := ![![-3, 1, 1, 1], ![0, -2, 1, 1], ![3, 1, -2, -2]]

def raw592step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]

def raw592step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -3, 3], ![1, 1, -2], ![1, 1, -2]]

theorem canonical592 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw592 = injectiveMoment H node223 := by
  calc
    injectiveMoment H raw592 = injectiveMoment H raw592step0 := by
      have heq : raw592step0 = raw592.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw592).symm
    injectiveMoment H raw592step0 = injectiveMoment H raw592step1 := by
      have heq : raw592step1 = (fun i j => raw592step0 (permutation15 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw592step0 permutation15 permutation5
    _ = injectiveMoment H node223 := by rfl

def raw593 : Matrix (Fin 3) (Fin 4) ℤ := ![![-3, 1, 1, 1], ![0, 1, 1, -2], ![3, -2, -2, 1]]

def raw593step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![1, 1, -2], ![1, -2, 1]]

def raw593step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -3, 3], ![1, 1, -2], ![1, 1, -2]]

theorem canonical593 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw593 = injectiveMoment H node223 := by
  calc
    injectiveMoment H raw593 = injectiveMoment H raw593step0 := by
      have heq : raw593step0 = raw593.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw593).symm
    injectiveMoment H raw593step0 = injectiveMoment H raw593step1 := by
      have heq : raw593step1 = (fun i j => raw593step0 (permutation27 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw593step0 permutation27 permutation5
    _ = injectiveMoment H node223 := by rfl

def raw594 : Matrix (Fin 3) (Fin 4) ℤ := ![![-3, 1, 1, 1], ![1, -2, 1, 0], ![2, 1, -2, -1]]

def raw594step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 1, -2], ![1, 0, -1]]

def raw594step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -2, 1], ![1, 2, -3]]

theorem canonical594 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw594 = injectiveMoment H node229 := by
  calc
    injectiveMoment H raw594 = injectiveMoment H raw594step0 := by
      have heq : raw594step0 = raw594.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw594).symm
    injectiveMoment H raw594step0 = injectiveMoment H raw594step1 := by
      have heq : raw594step1 = (fun i j => raw594step0 (permutation20 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw594step0 permutation20 permutation6
    _ = injectiveMoment H node229 := by rfl

def raw595 : Matrix (Fin 3) (Fin 4) ℤ := ![![-3, 1, 1, 1], ![1, -2, 3, -2], ![2, 1, -4, 1]]

def raw595step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 3, -4], ![1, -2, 1]]

def raw595step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, -2, 1], ![1, 3, -4]]

theorem canonical595 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw595 = injectiveMoment H node115 := by
  calc
    injectiveMoment H raw595 = injectiveMoment H raw595step0 := by
      have heq : raw595step0 = raw595.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw595).symm
    injectiveMoment H raw595step0 = injectiveMoment H raw595step1 := by
      have heq : raw595step1 = (fun i j => raw595step0 (permutation10 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw595step0 permutation10 permutation3
    _ = injectiveMoment H node115 := by rfl

def raw596 : Matrix (Fin 3) (Fin 4) ℤ := ![![-3, 1, 1, 1], ![2, -2, 1, -1], ![1, 1, -2, 0]]

def raw596step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![1, 1, -2], ![1, -1, 0]]

def raw596step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -2, 1], ![1, 2, -3]]

theorem canonical596 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw596 = injectiveMoment H node229 := by
  calc
    injectiveMoment H raw596 = injectiveMoment H raw596step0 := by
      have heq : raw596step0 = raw596.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw596).symm
    injectiveMoment H raw596step0 = injectiveMoment H raw596step1 := by
      have heq : raw596step1 = (fun i j => raw596step0 (permutation26 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw596step0 permutation26 permutation8
    _ = injectiveMoment H node229 := by rfl

def raw597 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]

def raw597step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]

def raw597step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 2, -3]]

theorem canonical597 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw597 = injectiveMoment H node855 := by
  calc
    injectiveMoment H raw597 = injectiveMoment H raw597step0 := by
      have heq : raw597step0 = -raw597 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw597).symm
    injectiveMoment H raw597step0 = injectiveMoment H raw597step1 := by
      have heq : raw597step1 = (fun i j => raw597step0 (permutation35 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw597step0 permutation35 permutation6
    _ = injectiveMoment H node855 := by rfl

def raw598 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]

def raw598step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![-1, 1, 0], ![-2, 1, 1], ![-2, 0, 2]]

def raw598step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, -1, 2], ![0, 2, -2], ![1, 0, -1], ![1, 1, -2]]

theorem canonical598 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw598 = injectiveMoment H node858 := by
  calc
    injectiveMoment H raw598 = injectiveMoment H raw598step0 := by
      have heq : raw598step0 = -raw598 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw598).symm
    injectiveMoment H raw598step0 = injectiveMoment H raw598step1 := by
      have heq : raw598step1 = (fun i j => raw598step0 (permutation37 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw598step0 permutation37 permutation6
    _ = injectiveMoment H node858 := by rfl

def raw599 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]

def raw599step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![-1, 1, 0], ![-2, 0, 2], ![-2, 1, 1]]

def raw599step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, -1, 2], ![0, 2, -2], ![1, 0, -1], ![1, 1, -2]]

theorem canonical599 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw599 = injectiveMoment H node858 := by
  calc
    injectiveMoment H raw599 = injectiveMoment H raw599step0 := by
      have heq : raw599step0 = -raw599 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw599).symm
    injectiveMoment H raw599step0 = injectiveMoment H raw599step1 := by
      have heq : raw599step1 = (fun i j => raw599step0 (permutation35 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw599step0 permutation35 permutation6
    _ = injectiveMoment H node858 := by rfl

def raw600 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]

def raw600step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![1, 2, -3]]

theorem canonical600 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw600 = injectiveMoment H node554 := by
  calc
    injectiveMoment H raw600 = injectiveMoment H raw600step0 := by
      have heq : raw600step0 = (fun i j => raw600 (permutation144 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw600 permutation144 permutation6
    _ = injectiveMoment H node554 := by rfl

def raw601 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]

def raw601step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, -1, 1], ![1, 1, -2], ![1, 2, -3]]

theorem canonical601 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw601 = injectiveMoment H node640 := by
  calc
    injectiveMoment H raw601 = injectiveMoment H raw601step0 := by
      have heq : raw601step0 = (fun i j => raw601 (permutation127 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw601 permutation127 permutation6
    _ = injectiveMoment H node640 := by rfl

def raw602 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]

def raw602step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![-1, 0, 1], ![-2, 1, 1], ![-2, 1, 1]]

def raw602step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![1, 1, -2]]

theorem canonical602 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw602 = injectiveMoment H node856 := by
  calc
    injectiveMoment H raw602 = injectiveMoment H raw602step0 := by
      have heq : raw602step0 = -raw602 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw602).symm
    injectiveMoment H raw602step0 = injectiveMoment H raw602step1 := by
      have heq : raw602step1 = (fun i j => raw602step0 (permutation33 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw602step0 permutation33 permutation6
    _ = injectiveMoment H node856 := by rfl

def raw603 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![2, 0, -2], ![3, -2, -1]]

def raw603step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![1, 1, -2], ![1, 2, -3]]

theorem canonical603 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw603 = injectiveMoment H node167 := by
  calc
    injectiveMoment H raw603 = injectiveMoment H raw603step0 := by
      have heq : raw603step0 = (fun i j => raw603 (permutation32 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw603 permutation32 permutation6
    _ = injectiveMoment H node167 := by rfl

def raw604 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]

def raw604step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![2, -2, 0], ![0, 1, -1], ![-1, 0, 1], ![-2, 2, 0], ![-2, 0, 2]]

def raw604step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]

theorem canonical604 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw604 = injectiveMoment H node1857 := by
  calc
    injectiveMoment H raw604 = injectiveMoment H raw604step0 := by
      have heq : raw604step0 = -raw604 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw604).symm
    injectiveMoment H raw604step0 = injectiveMoment H raw604step1 := by
      have heq : raw604step1 = (fun i j => raw604step0 (permutation167 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw604step0 permutation167 permutation8
    _ = injectiveMoment H node1857 := by rfl

def raw605 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]

def raw605step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -2, 2], ![1, 2, -3], ![2, 0, -2]]

theorem canonical605 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw605 = injectiveMoment H node530 := by
  calc
    injectiveMoment H raw605 = injectiveMoment H raw605step0 := by
      have heq : raw605step0 = (fun i j => raw605 (permutation143 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw605 permutation143 permutation6
    _ = injectiveMoment H node530 := by rfl

def raw606 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]

def raw606step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![2, -2, 0], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]

def raw606step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]

theorem canonical606 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw606 = injectiveMoment H node1864 := by
  calc
    injectiveMoment H raw606 = injectiveMoment H raw606step0 := by
      have heq : raw606step0 = -raw606 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw606).symm
    injectiveMoment H raw606step0 = injectiveMoment H raw606step1 := by
      have heq : raw606step1 = (fun i j => raw606step0 (permutation166 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw606step0 permutation166 permutation8
    _ = injectiveMoment H node1864 := by rfl

def raw607 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![3, -1, -2]]

def raw607step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![2, 1, -3]]

theorem canonical607 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw607 = injectiveMoment H node528 := by
  calc
    injectiveMoment H raw607 = injectiveMoment H raw607step0 := by
      have heq : raw607step0 = (fun i j => raw607 (permutation148 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw607 permutation148 permutation8
    _ = injectiveMoment H node528 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
