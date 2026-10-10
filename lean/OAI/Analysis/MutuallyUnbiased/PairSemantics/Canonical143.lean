import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes6
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes7
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes8
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes9
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes10
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes11
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes13
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes14
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes15
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes20
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes21
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes27
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes28
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes35

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw4576 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 2, -2], ![0, 1, -2, 1], ![2, -2, 1, -1]]

theorem canonical4576 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4576 = injectiveMoment H node683 := by
  rfl

def raw4577 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, -2, 0, 1], ![1, 0, 0, -1]]

def raw4577step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 1, 0], ![0, 2, 0, -2], ![1, 0, -2, 1], ![1, 0, 0, -1]]

theorem canonical4577 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4577 = injectiveMoment H node1753 := by
  calc
    injectiveMoment H raw4577 = injectiveMoment H raw4577step0 := by
      have heq : raw4577step0 = (fun i j => raw4577 (permutation39 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4577 permutation39 permutation11
    _ = injectiveMoment H node1753 := by rfl

def raw4578 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, -2, 1, 0], ![1, 0, -1, 0]]

def raw4578step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, -1, 1, -2], ![0, 0, -2, 2], ![0, -1, 1, 0], ![-1, 2, -1, 0], ![-1, 0, 1, 0]]

def raw4578step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 2, -1, -1], ![2, 0, 0, -2]]

theorem canonical4578 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4578 = injectiveMoment H node1839 := by
  calc
    injectiveMoment H raw4578 = injectiveMoment H raw4578step0 := by
      have heq : raw4578step0 = -raw4578 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4578).symm
    injectiveMoment H raw4578step0 = injectiveMoment H raw4578step1 := by
      have heq : raw4578step1 = (fun i j => raw4578step0 (permutation44 i) (permutation29 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4578step0 permutation44 permutation29
    _ = injectiveMoment H node1839 := by rfl

def raw4579 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def raw4579step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, -1, 1, -2], ![0, 0, -2, 2], ![0, -1, 1, 0], ![-1, 1, 0, 0], ![-1, 1, 0, 0]]

def raw4579step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 1, 0], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, -2, 0]]

theorem canonical4579 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4579 = injectiveMoment H node1749 := by
  calc
    injectiveMoment H raw4579 = injectiveMoment H raw4579step0 := by
      have heq : raw4579step0 = -raw4579 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4579).symm
    injectiveMoment H raw4579step0 = injectiveMoment H raw4579step1 := by
      have heq : raw4579step1 = (fun i j => raw4579step0 (permutation42 i) (permutation30 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4579step0 permutation42 permutation30
    _ = injectiveMoment H node1749 := by rfl

def raw4580 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 2, -2], ![0, 1, -1, 0], ![2, -2, 0, 0]]

def raw4580step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, 0, 1, -2], ![-1, 2, -1, 0], ![2, -2, 0, 0]]

def raw4580step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, 0, -2, 2], ![0, 2, 0, -2], ![1, -2, 0, 1]]

theorem canonical4580 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4580 = injectiveMoment H node1314 := by
  calc
    injectiveMoment H raw4580 = injectiveMoment H raw4580step0 := by
      have heq : raw4580step0 = raw4580.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4580).symm
    injectiveMoment H raw4580step0 = injectiveMoment H raw4580step1 := by
      have heq : raw4580step1 = (fun i j => raw4580step0 (permutation25 i) (permutation26 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4580step0 permutation25 permutation26
    _ = injectiveMoment H node1314 := by rfl

def raw4581 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, -2, 0, 1], ![1, 0, -1, 0]]

def raw4581step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -1, 0, 0], ![1, 0, -2, 1]]

theorem canonical4581 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4581 = injectiveMoment H node1804 := by
  calc
    injectiveMoment H raw4581 = injectiveMoment H raw4581step0 := by
      have heq : raw4581step0 = (fun i j => raw4581 (permutation40 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4581 permutation40 permutation11
    _ = injectiveMoment H node1804 := by rfl

def raw4582 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, -2, 1, 0], ![1, 0, -2, 1]]

theorem canonical4582 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4582 = injectiveMoment H node2241 := by
  rfl

def raw4583 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, -1, 0, 0]]

def raw4583step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -1, -1, 1], ![1, 0, -1, 0]]

theorem canonical4583 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4583 = injectiveMoment H node1803 := by
  calc
    injectiveMoment H raw4583 = injectiveMoment H raw4583step0 := by
      have heq : raw4583step0 = (fun i j => raw4583 (permutation39 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4583 permutation39 permutation11
    _ = injectiveMoment H node1803 := by rfl

def raw4584 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 2, -2], ![0, 1, 0, -1], ![2, -2, -1, 1]]

def raw4584step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, 0, 1, -2], ![-1, 2, 0, -1], ![2, -2, -1, 1]]

def raw4584step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, 2, -2], ![0, 2, -1, -1], ![1, 0, -2, 1]]

theorem canonical4584 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4584 = injectiveMoment H node844 := by
  calc
    injectiveMoment H raw4584 = injectiveMoment H raw4584step0 := by
      have heq : raw4584step0 = raw4584.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4584).symm
    injectiveMoment H raw4584step0 = injectiveMoment H raw4584step1 := by
      have heq : raw4584step1 = (fun i j => raw4584step0 (permutation28 i) (permutation24 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4584step0 permutation28 permutation24
    _ = injectiveMoment H node844 := by rfl

def raw4585 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 2, -2], ![0, 1, 1, -2], ![2, -2, -2, 2]]

def raw4585step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, 0, 1, -2], ![-1, 2, 1, -2], ![2, -2, -2, 2]]

def raw4585step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 0, -2, 2], ![0, 1, 1, -2], ![2, 1, -1, -2]]

theorem canonical4585 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4585 = injectiveMoment H node410 := by
  calc
    injectiveMoment H raw4585 = injectiveMoment H raw4585step0 := by
      have heq : raw4585step0 = raw4585.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4585).symm
    injectiveMoment H raw4585step0 = injectiveMoment H raw4585step1 := by
      have heq : raw4585step1 = (fun i j => raw4585step0 (permutation27 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4585step0 permutation27 permutation17
    _ = injectiveMoment H node410 := by rfl

def raw4586 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 2, -2], ![1, -2, 0, 1], ![1, 1, -1, -1]]

def raw4586step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 0, -2, 1], ![-1, 2, 0, -1], ![2, -2, 1, -1]]

def raw4586step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, -2, 1], ![0, 1, 1, -2], ![2, -1, 0, -1]]

theorem canonical4586 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4586 = injectiveMoment H node510 := by
  calc
    injectiveMoment H raw4586 = injectiveMoment H raw4586step0 := by
      have heq : raw4586step0 = raw4586.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4586).symm
    injectiveMoment H raw4586step0 = injectiveMoment H raw4586step1 := by
      have heq : raw4586step1 = (fun i j => raw4586step0 (permutation29 i) (permutation20 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4586step0 permutation29 permutation20
    _ = injectiveMoment H node510 := by rfl

def raw4587 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 2, -2], ![1, -2, 1, 0], ![1, 1, -2, 0]]

def raw4587step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, -1, 1, -2], ![0, 0, -2, 2], ![-1, 2, -1, 0], ![-1, -1, 2, 0]]

def raw4587step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, -1, -1, 2], ![0, 2, -1, -1], ![2, 0, 0, -2]]

theorem canonical4587 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4587 = injectiveMoment H node520 := by
  calc
    injectiveMoment H raw4587 = injectiveMoment H raw4587step0 := by
      have heq : raw4587step0 = -raw4587 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4587).symm
    injectiveMoment H raw4587step0 = injectiveMoment H raw4587step1 := by
      have heq : raw4587step1 = (fun i j => raw4587step0 (permutation14 i) (permutation29 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4587step0 permutation14 permutation29
    _ = injectiveMoment H node520 := by rfl

def raw4588 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 2, -2], ![1, -1, -1, 1], ![1, 0, 0, -1]]

def raw4588step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 0, -1, 0], ![-1, 2, -1, 0], ![2, -2, 1, -1]]

def raw4588step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -1, 1], ![0, 2, -1, -1], ![1, 0, 1, -2]]

theorem canonical4588 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4588 = injectiveMoment H node837 := by
  calc
    injectiveMoment H raw4588 = injectiveMoment H raw4588step0 := by
      have heq : raw4588step0 = raw4588.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4588).symm
    injectiveMoment H raw4588step0 = injectiveMoment H raw4588step1 := by
      have heq : raw4588step1 = (fun i j => raw4588step0 (permutation30 i) (permutation30 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4588step0 permutation30 permutation30
    _ = injectiveMoment H node837 := by rfl

def raw4589 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 2, -2], ![1, -1, 1, -1], ![1, 0, -2, 1]]

def raw4589step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, -2, 2], ![0, 1, 1, -2], ![1, -2, 2, -1]]

theorem canonical4589 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4589 = injectiveMoment H node1346 := by
  calc
    injectiveMoment H raw4589 = injectiveMoment H raw4589step0 := by
      have heq : raw4589step0 = (fun i j => raw4589 (permutation24 i) (permutation16 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4589 permutation24 permutation16
    _ = injectiveMoment H node1346 := by rfl

def raw4590 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 2, -2], ![1, 0, -2, 1], ![1, -1, 1, -1]]

def raw4590step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, -2, 2], ![0, 1, 1, -2], ![1, -2, 2, -1]]

theorem canonical4590 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4590 = injectiveMoment H node1346 := by
  calc
    injectiveMoment H raw4590 = injectiveMoment H raw4590step0 := by
      have heq : raw4590step0 = (fun i j => raw4590 (permutation30 i) (permutation16 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4590 permutation30 permutation16
    _ = injectiveMoment H node1346 := by rfl

def raw4591 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 3, -3], ![0, 1, -2, 1], ![1, -1, 0, 0], ![1, -1, 0, 0]]

theorem canonical4591 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4591 = injectiveMoment H node2242 := by
  rfl

def raw4592 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 3, -3], ![0, 1, -2, 1], ![2, -2, 0, 0]]

def raw4592step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, 0, 1, -2], ![-1, 3, -2, 0], ![2, -3, 1, 0]]

def raw4592step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 2, -2, 0], ![1, -2, 1, 0], ![1, 0, 2, -3]]

theorem canonical4592 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4592 = injectiveMoment H node601 := by
  calc
    injectiveMoment H raw4592 = injectiveMoment H raw4592step0 := by
      have heq : raw4592step0 = raw4592.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4592).symm
    injectiveMoment H raw4592step0 = injectiveMoment H raw4592step1 := by
      have heq : raw4592step1 = (fun i j => raw4592step0 (permutation21 i) (permutation25 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4592step0 permutation21 permutation25
    _ = injectiveMoment H node601 := by rfl

def raw4593 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 3, -3], ![0, 1, -1, 0], ![1, -2, 0, 1], ![1, 0, -1, 0]]

theorem canonical4593 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4593 = injectiveMoment H node2243 := by
  rfl

def raw4594 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 3, -3], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, -1, 0, 0]]

theorem canonical4594 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4594 = injectiveMoment H node2244 := by
  rfl

def raw4595 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 3, -3], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, -1, -1, 1]]

def raw4595step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 3, -3], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, -1, 0, 0]]

theorem canonical4595 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4595 = injectiveMoment H node2244 := by
  calc
    injectiveMoment H raw4595 = injectiveMoment H raw4595step0 := by
      have heq : raw4595step0 = (fun i j => raw4595 (permutation34 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4595 permutation34 permutation9
    _ = injectiveMoment H node2244 := by rfl

def raw4596 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 3, -3], ![0, 1, -1, 0], ![2, -2, -1, 1]]

def raw4596step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, 0, 1, -2], ![-1, 3, -1, -1], ![2, -3, 0, 1]]

def raw4596step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -2, 2, 0], ![0, 2, 1, -3], ![1, 1, -2, 0]]

theorem canonical4596 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4596 = injectiveMoment H node928 := by
  calc
    injectiveMoment H raw4596 = injectiveMoment H raw4596step0 := by
      have heq : raw4596step0 = raw4596.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4596).symm
    injectiveMoment H raw4596step0 = injectiveMoment H raw4596step1 := by
      have heq : raw4596step1 = (fun i j => raw4596step0 (permutation22 i) (permutation22 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4596step0 permutation22 permutation22
    _ = injectiveMoment H node928 := by rfl

def raw4597 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 3, -3], ![0, 1, 0, -1], ![1, -1, -2, 2], ![1, -1, 0, 0]]

theorem canonical4597 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4597 = injectiveMoment H node2245 := by
  rfl

def raw4598 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 3, -3], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, -1, -1, 1]]

theorem canonical4598 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4598 = injectiveMoment H node2246 := by
  rfl

def raw4599 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 3, -3], ![0, 1, 0, -1], ![2, -2, -2, 2]]

def raw4599step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, 0, 1, -2], ![-1, 3, 0, -2], ![2, -3, -1, 2]]

def raw4599step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -3, 2, 2], ![0, 0, -2, 2], ![0, 3, -1, -2], ![1, 0, 1, -2]]

theorem canonical4599 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4599 = injectiveMoment H node729 := by
  calc
    injectiveMoment H raw4599 = injectiveMoment H raw4599step0 := by
      have heq : raw4599step0 = raw4599.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4599).symm
    injectiveMoment H raw4599step0 = injectiveMoment H raw4599step1 := by
      have heq : raw4599step1 = (fun i j => raw4599step0 (permutation28 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4599step0 permutation28 permutation23
    _ = injectiveMoment H node729 := by rfl

def raw4600 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 3, -3], ![1, -2, 0, 1], ![1, 1, -2, 0]]

def raw4600step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 0, -2, 1], ![-1, 3, 0, -2], ![2, -3, 1, 0]]

def raw4600step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, 2, -3], ![1, -2, 1, 0], ![1, 1, -2, 0]]

theorem canonical4600 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4600 = injectiveMoment H node599 := by
  calc
    injectiveMoment H raw4600 = injectiveMoment H raw4600step0 := by
      have heq : raw4600step0 = raw4600.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4600).symm
    injectiveMoment H raw4600step0 = injectiveMoment H raw4600step1 := by
      have heq : raw4600step1 = (fun i j => raw4600step0 (permutation26 i) (permutation31 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4600step0 permutation26 permutation31
    _ = injectiveMoment H node599 := by rfl

def raw4601 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 3, -3], ![1, -1, -2, 2], ![1, 0, 0, -1]]

def raw4601step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -2, 2], ![0, 0, 3, -3], ![0, 1, 0, -1], ![1, -2, -1, 2]]

theorem canonical4601 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4601 = injectiveMoment H node1337 := by
  calc
    injectiveMoment H raw4601 = injectiveMoment H raw4601step0 := by
      have heq : raw4601step0 = (fun i j => raw4601 (permutation24 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4601 permutation24 permutation15
    _ = injectiveMoment H node1337 := by rfl

def raw4602 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 3, -3], ![1, -1, -1, 1], ![1, 0, -1, 0]]

def raw4602step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 0, -1, 0], ![-1, 3, -1, -1], ![2, -3, 1, 0]]

def raw4602step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 1, 0], ![0, 1, 2, -3], ![1, 1, -2, 0]]

theorem canonical4602 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4602 = injectiveMoment H node937 := by
  calc
    injectiveMoment H raw4602 = injectiveMoment H raw4602step0 := by
      have heq : raw4602step0 = raw4602.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4602).symm
    injectiveMoment H raw4602step0 = injectiveMoment H raw4602step1 := by
      have heq : raw4602step1 = (fun i j => raw4602step0 (permutation24 i) (permutation31 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4602step0 permutation24 permutation31
    _ = injectiveMoment H node937 := by rfl

def raw4603 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 3, -3], ![1, -1, 0, 0], ![1, 0, -2, 1]]

def raw4603step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 0, -1, 0], ![-1, 3, 0, -2], ![2, -3, 0, 1]]

def raw4603step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, 0, 1, 0], ![1, -3, 0, 2], ![-2, 3, 0, -1]]

def raw4603step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 3, -2], ![0, 2, -3, 1], ![1, 0, 0, -1]]

theorem canonical4603 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4603 = injectiveMoment H node1015 := by
  calc
    injectiveMoment H raw4603 = injectiveMoment H raw4603step0 := by
      have heq : raw4603step0 = raw4603.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4603).symm
    injectiveMoment H raw4603step0 = injectiveMoment H raw4603step1 := by
      have heq : raw4603step1 = -raw4603step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4603step0).symm
    injectiveMoment H raw4603step1 = injectiveMoment H raw4603step2 := by
      have heq : raw4603step2 = (fun i j => raw4603step1 (permutation14 i) (permutation26 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4603step1 permutation14 permutation26
    _ = injectiveMoment H node1015 := by rfl

def raw4604 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 3, -3], ![1, 0, -2, 1], ![1, -1, 0, 0]]

def raw4604step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 0, 0, -1], ![-1, 3, -2, 0], ![2, -3, 1, 0]]

def raw4604step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, 0, 0, 1], ![1, -3, 2, 0], ![-2, 3, -1, 0]]

def raw4604step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 3, -2], ![0, 2, -3, 1], ![1, 0, 0, -1]]

theorem canonical4604 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4604 = injectiveMoment H node1015 := by
  calc
    injectiveMoment H raw4604 = injectiveMoment H raw4604step0 := by
      have heq : raw4604step0 = raw4604.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4604).symm
    injectiveMoment H raw4604step0 = injectiveMoment H raw4604step1 := by
      have heq : raw4604step1 = -raw4604step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4604step0).symm
    injectiveMoment H raw4604step1 = injectiveMoment H raw4604step2 := by
      have heq : raw4604step2 = (fun i j => raw4604step1 (permutation14 i) (permutation32 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4604step1 permutation14 permutation32
    _ = injectiveMoment H node1015 := by rfl

def raw4605 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 3, -3], ![1, 0, -1, 0], ![1, -1, -1, 1]]

def raw4605step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 0, 0, -1], ![-1, 3, -1, -1], ![2, -3, 0, 1]]

def raw4605step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 1, 0], ![0, 1, 2, -3], ![1, 1, -2, 0]]

theorem canonical4605 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4605 = injectiveMoment H node937 := by
  calc
    injectiveMoment H raw4605 = injectiveMoment H raw4605step0 := by
      have heq : raw4605step0 = raw4605.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4605).symm
    injectiveMoment H raw4605step0 = injectiveMoment H raw4605step1 := by
      have heq : raw4605step1 = (fun i j => raw4605step0 (permutation24 i) (permutation25 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4605step0 permutation24 permutation25
    _ = injectiveMoment H node937 := by rfl

def raw4606 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 1, -2, 1], ![0, 0, 3, -3], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def raw4606step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 3, -3], ![0, 1, -2, 1], ![1, -1, 0, 0], ![1, -1, 0, 0]]

theorem canonical4606 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4606 = injectiveMoment H node2242 := by
  calc
    injectiveMoment H raw4606 = injectiveMoment H raw4606step0 := by
      have heq : raw4606step0 = (fun i j => raw4606 (permutation39 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4606 permutation39 permutation9
    _ = injectiveMoment H node2242 := by rfl

def raw4607 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 1, -2, 1], ![1, -2, 0, 1], ![1, 0, 3, -4]]

def raw4607step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 1, -2, 0], ![-1, -2, 0, 3], ![2, 1, 1, -4]]

def raw4607step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -2, 1], ![1, -2, 1, 0], ![1, 1, 2, -4]]

theorem canonical4607 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4607 = injectiveMoment H node596 := by
  calc
    injectiveMoment H raw4607 = injectiveMoment H raw4607step0 := by
      have heq : raw4607step0 = raw4607.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4607).symm
    injectiveMoment H raw4607step0 = injectiveMoment H raw4607step1 := by
      have heq : raw4607step1 = (fun i j => raw4607step0 (permutation21 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4607step0 permutation21 permutation17
    _ = injectiveMoment H node596 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
