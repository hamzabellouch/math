import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes0
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes17
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes20
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes22
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes29
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes33
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes35
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes36
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes37
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes38
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes41
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes43

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw8640 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![-2, 0, 2], ![1, 1, -2]]

def raw8640step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]

theorem canonical8640 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8640 = injectiveMoment H node2129 := by
  calc
    injectiveMoment H raw8640 = injectiveMoment H raw8640step0 := by
      have heq : raw8640step0 = (fun i j => raw8640 (permutation258 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8640 permutation258 permutation3
    _ = injectiveMoment H node2129 := by rfl

def raw8641 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![-1, -1, 2], ![0, 2, -2]]

def raw8641step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1]]

theorem canonical8641 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8641 = injectiveMoment H node2674 := by
  calc
    injectiveMoment H raw8641 = injectiveMoment H raw8641step0 := by
      have heq : raw8641step0 = (fun i j => raw8641 (permutation259 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8641 permutation259 permutation3
    _ = injectiveMoment H node2674 := by rfl

def raw8642 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![-2, 2, 0]]

def raw8642step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

theorem canonical8642 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8642 = injectiveMoment H node2137 := by
  calc
    injectiveMoment H raw8642 = injectiveMoment H raw8642step0 := by
      have heq : raw8642step0 = (fun i j => raw8642 (permutation355 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8642 permutation355 permutation4
    _ = injectiveMoment H node2137 := by rfl

def raw8643 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![-2, 1, 1]]

def raw8643step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]

theorem canonical8643 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8643 = injectiveMoment H node2306 := by
  calc
    injectiveMoment H raw8643 = injectiveMoment H raw8643step0 := by
      have heq : raw8643step0 = (fun i j => raw8643 (permutation308 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8643 permutation308 permutation3
    _ = injectiveMoment H node2306 := by rfl

def raw8644 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![-3, 2, 1]]

def raw8644step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]

theorem canonical8644 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8644 = injectiveMoment H node1427 := by
  calc
    injectiveMoment H raw8644 = injectiveMoment H raw8644step0 := by
      have heq : raw8644step0 = (fun i j => raw8644 (permutation355 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8644 permutation355 permutation4
    _ = injectiveMoment H node1427 := by rfl

def raw8645 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2], ![-3, 1, 2]]

def raw8645step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -3, 2], ![1, 0, -1]]

theorem canonical8645 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8645 = injectiveMoment H node2793 := by
  calc
    injectiveMoment H raw8645 = injectiveMoment H raw8645step0 := by
      have heq : raw8645step0 = (fun i j => raw8645 (permutation159 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8645 permutation159 permutation5
    _ = injectiveMoment H node2793 := by rfl

def raw8646 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, 3, -3], ![0, -1, 1]]

def raw8646step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![3, -3], ![-1, 1]]

def raw8646step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![1, -1]]

theorem canonical8646 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8646 = injectiveMoment H node26 := by
  calc
    injectiveMoment H raw8646 = injectiveMoment H raw8646step0 := by
      have hz : ∀ i, raw8646 i (permutation3 0) = 0 := by decide +kernel
      have heq : raw8646step0 = (fun i j => raw8646 i (permutation3 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8646 permutation3 hz
    injectiveMoment H raw8646step0 = injectiveMoment H raw8646step1 := by
      have heq : raw8646step1 = (fun i j => raw8646step0 (permutation21 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8646step0 permutation21 permutation2
    _ = injectiveMoment H node26 := by rfl

def raw8647 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![-2, 0, 2], ![0, 4, -4]]

def raw8647step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, -1, 1], ![0, 4, -4], ![1, -2, 1], ![1, 0, -1]]

theorem canonical8647 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8647 = injectiveMoment H node2133 := by
  calc
    injectiveMoment H raw8647 = injectiveMoment H raw8647step0 := by
      have heq : raw8647step0 = (fun i j => raw8647 (permutation262 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8647 permutation262 permutation3
    _ = injectiveMoment H node2133 := by rfl

def raw8648 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![-2, 1, 1], ![0, 3, -3]]

def raw8648step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -3, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

theorem canonical8648 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8648 = injectiveMoment H node2296 := by
  calc
    injectiveMoment H raw8648 = injectiveMoment H raw8648step0 := by
      have heq : raw8648step0 = (fun i j => raw8648 (permutation295 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8648 permutation295 permutation4
    _ = injectiveMoment H node2296 := by rfl

def raw8649 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![0, -1, 1], ![-2, 1, 1], ![1, 3, -4]]

def raw8649step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 3, -4]]

theorem canonical8649 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8649 = injectiveMoment H node2302 := by
  calc
    injectiveMoment H raw8649 = injectiveMoment H raw8649step0 := by
      have heq : raw8649step0 = (fun i j => raw8649 (permutation260 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8649 permutation260 permutation3
    _ = injectiveMoment H node2302 := by rfl

def raw8650 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![0, 0, 0], ![-1, -1, 2], ![0, 4, -4]]

def raw8650step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![-1, -1, 2], ![0, 4, -4]]

def raw8650step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 4, -4], ![1, -1, 0]]

theorem canonical8650 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8650 = injectiveMoment H node1150 := by
  calc
    injectiveMoment H raw8650 = injectiveMoment H raw8650step0 := by
      have hz : ∀ j, raw8650 (permutation241 0) j = 0 := by decide +kernel
      have heq : raw8650step0 = (fun i j => raw8650 (permutation241 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8650 permutation241 hz
    injectiveMoment H raw8650step0 = injectiveMoment H raw8650step1 := by
      have heq : raw8650step1 = (fun i j => raw8650step0 (permutation105 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8650step0 permutation105 permutation3
    _ = injectiveMoment H node1150 := by rfl

def raw8651 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![-3, 1, 2], ![1, 3, -4]]

def raw8651step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 3, -4]]

theorem canonical8651 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8651 = injectiveMoment H node1424 := by
  calc
    injectiveMoment H raw8651 = injectiveMoment H raw8651step0 := by
      have heq : raw8651step0 = (fun i j => raw8651 (permutation258 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8651 permutation258 permutation3
    _ = injectiveMoment H node1424 := by rfl

def raw8652 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![-2, 0, 2], ![0, 4, -4]]

def raw8652step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, -1, 1], ![0, 4, -4], ![1, -1, 0], ![1, -1, 0]]

theorem canonical8652 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8652 = injectiveMoment H node2134 := by
  calc
    injectiveMoment H raw8652 = injectiveMoment H raw8652step0 := by
      have heq : raw8652step0 = (fun i j => raw8652 (permutation262 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8652 permutation262 permutation3
    _ = injectiveMoment H node2134 := by rfl

def raw8653 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![0, 3, -3]]

def raw8653step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -3, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]

theorem canonical8653 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8653 = injectiveMoment H node2297 := by
  calc
    injectiveMoment H raw8653 = injectiveMoment H raw8653step0 := by
      have heq : raw8653step0 = (fun i j => raw8653 (permutation294 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8653 permutation294 permutation4
    _ = injectiveMoment H node2297 := by rfl

def raw8654 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![-3, 1, 2], ![1, 2, -3]]

def raw8654step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]

theorem canonical8654 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8654 = injectiveMoment H node1425 := by
  calc
    injectiveMoment H raw8654 = injectiveMoment H raw8654step0 := by
      have heq : raw8654step0 = (fun i j => raw8654 (permutation258 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8654 permutation258 permutation3
    _ = injectiveMoment H node1425 := by rfl

def raw8655 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![-2, -1, 3], ![0, 4, -4]]

def raw8655step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, -1, 1], ![0, 4, -4], ![1, -1, 0], ![1, 0, -1]]

theorem canonical8655 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8655 = injectiveMoment H node1879 := by
  calc
    injectiveMoment H raw8655 = injectiveMoment H raw8655step0 := by
      have heq : raw8655step0 = (fun i j => raw8655 (permutation262 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8655 permutation262 permutation3
    _ = injectiveMoment H node1879 := by rfl

def raw8656 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![-2, 0, 2], ![0, 3, -3]]

def raw8656step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1]]

theorem canonical8656 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8656 = injectiveMoment H node2132 := by
  calc
    injectiveMoment H raw8656 = injectiveMoment H raw8656step0 := by
      have heq : raw8656step0 = (fun i j => raw8656 (permutation262 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8656 permutation262 permutation3
    _ = injectiveMoment H node2132 := by rfl

def raw8657 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![-2, 1, 1], ![0, 2, -2]]

def raw8657step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

theorem canonical8657 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8657 = injectiveMoment H node2301 := by
  calc
    injectiveMoment H raw8657 = injectiveMoment H raw8657step0 := by
      have heq : raw8657step0 = (fun i j => raw8657 (permutation295 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8657 permutation295 permutation4
    _ = injectiveMoment H node2301 := by rfl

def raw8658 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![-1, -1, 2], ![-1, 4, -3]]

def raw8658step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 2, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

theorem canonical8658 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8658 = injectiveMoment H node2382 := by
  calc
    injectiveMoment H raw8658 = injectiveMoment H raw8658step0 := by
      have heq : raw8658step0 = (fun i j => raw8658 (permutation396 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8658 permutation396 permutation4
    _ = injectiveMoment H node2382 := by rfl

def raw8659 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![-3, 3, 0]]

def raw8659step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0]]

theorem canonical8659 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8659 = injectiveMoment H node2791 := by
  calc
    injectiveMoment H raw8659 = injectiveMoment H raw8659step0 := by
      have heq : raw8659step0 = (fun i j => raw8659 (permutation251 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8659 permutation251 permutation8
    _ = injectiveMoment H node2791 := by rfl

def raw8660 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![0, 0, 0], ![-1, -1, 2], ![0, 3, -3]]

def raw8660step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![-1, -1, 2], ![0, 3, -3]]

def raw8660step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 3, -3], ![1, 0, -1]]

theorem canonical8660 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8660 = injectiveMoment H node1149 := by
  calc
    injectiveMoment H raw8660 = injectiveMoment H raw8660step0 := by
      have hz : ∀ j, raw8660 (permutation241 0) j = 0 := by decide +kernel
      have heq : raw8660step0 = (fun i j => raw8660 (permutation241 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8660 permutation241 hz
    injectiveMoment H raw8660step0 = injectiveMoment H raw8660step1 := by
      have heq : raw8660step1 = (fun i j => raw8660step0 (permutation105 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8660step0 permutation105 permutation3
    _ = injectiveMoment H node1149 := by rfl

def raw8661 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![-1, 1, 0]]

def raw8661step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0]]

theorem canonical8661 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8661 = injectiveMoment H node1294 := by
  calc
    injectiveMoment H raw8661 = injectiveMoment H raw8661step0 := by
      have heq : raw8661step0 = (fun i j => raw8661 (permutation145 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8661 permutation145 permutation4
    _ = injectiveMoment H node1294 := by rfl

def raw8662 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![-3, 1, 2], ![1, 2, -3]]

def raw8662step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]

theorem canonical8662 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8662 = injectiveMoment H node1425 := by
  calc
    injectiveMoment H raw8662 = injectiveMoment H raw8662step0 := by
      have heq : raw8662step0 = (fun i j => raw8662 (permutation260 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8662 permutation260 permutation3
    _ = injectiveMoment H node1425 := by rfl

def raw8663 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![-2, 0, 2], ![0, 3, -3]]

def raw8663step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1]]

theorem canonical8663 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8663 = injectiveMoment H node2132 := by
  calc
    injectiveMoment H raw8663 = injectiveMoment H raw8663step0 := by
      have heq : raw8663step0 = (fun i j => raw8663 (permutation263 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8663 permutation263 permutation3
    _ = injectiveMoment H node2132 := by rfl

def raw8664 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![-1, -1, 2], ![-1, 4, -3]]

def raw8664step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 2, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

theorem canonical8664 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8664 = injectiveMoment H node2382 := by
  calc
    injectiveMoment H raw8664 = injectiveMoment H raw8664step0 := by
      have heq : raw8664step0 = (fun i j => raw8664 (permutation395 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8664 permutation395 permutation4
    _ = injectiveMoment H node2382 := by rfl

def raw8665 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1], ![-3, 3, 0]]

def raw8665step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0]]

theorem canonical8665 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8665 = injectiveMoment H node2791 := by
  calc
    injectiveMoment H raw8665 = injectiveMoment H raw8665step0 := by
      have heq : raw8665step0 = (fun i j => raw8665 (permutation234 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8665 permutation234 permutation8
    _ = injectiveMoment H node2791 := by rfl

def raw8666 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![-3, 0, 3], ![1, 2, -3]]

def raw8666step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![3, 0, -3], ![-1, -2, 3]]

def raw8666step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, -1, 1], ![0, 3, -3], ![1, 0, -1], ![1, 0, -1]]

theorem canonical8666 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8666 = injectiveMoment H node1878 := by
  calc
    injectiveMoment H raw8666 = injectiveMoment H raw8666step0 := by
      have heq : raw8666step0 = -raw8666 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8666).symm
    injectiveMoment H raw8666step0 = injectiveMoment H raw8666step1 := by
      have heq : raw8666step1 = (fun i j => raw8666step0 (permutation366 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8666step0 permutation366 permutation5
    _ = injectiveMoment H node1878 := by rfl

def raw8667 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![-3, 1, 2], ![1, 1, -2]]

def raw8667step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![3, -1, -2], ![-1, -1, 2]]

def raw8667step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 3, -2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]

theorem canonical8667 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8667 = injectiveMoment H node2671 := by
  calc
    injectiveMoment H raw8667 = injectiveMoment H raw8667step0 := by
      have heq : raw8667step0 = -raw8667 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8667).symm
    injectiveMoment H raw8667step0 = injectiveMoment H raw8667step1 := by
      have heq : raw8667step1 = (fun i j => raw8667step0 (permutation404 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8667step0 permutation404 permutation5
    _ = injectiveMoment H node2671 := by rfl

def raw8668 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![-2, -1, 3], ![0, 3, -3]]

def raw8668step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, -1, 1], ![0, 3, -3], ![1, 0, -1], ![1, 0, -1]]

theorem canonical8668 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8668 = injectiveMoment H node1878 := by
  calc
    injectiveMoment H raw8668 = injectiveMoment H raw8668step0 := by
      have heq : raw8668step0 = (fun i j => raw8668 (permutation262 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8668 permutation262 permutation3
    _ = injectiveMoment H node1878 := by rfl

def raw8669 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![-2, 0, 2], ![0, 2, -2]]

def raw8669step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1]]

theorem canonical8669 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8669 = injectiveMoment H node2131 := by
  calc
    injectiveMoment H raw8669 = injectiveMoment H raw8669step0 := by
      have heq : raw8669step0 = (fun i j => raw8669 (permutation262 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8669 permutation262 permutation3
    _ = injectiveMoment H node2131 := by rfl

def raw8670 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![-1, -2, 3], ![-1, 4, -3]]

def raw8670step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 4, -3], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]

theorem canonical8670 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8670 = injectiveMoment H node2475 := by
  calc
    injectiveMoment H raw8670 = injectiveMoment H raw8670step0 := by
      have heq : raw8670step0 = (fun i j => raw8670 (permutation294 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8670 permutation294 permutation3
    _ = injectiveMoment H node2475 := by rfl

def raw8671 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![-1, -1, 2], ![-1, 3, -2]]

def raw8671step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 3, -2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]

theorem canonical8671 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8671 = injectiveMoment H node2671 := by
  calc
    injectiveMoment H raw8671 = injectiveMoment H raw8671step0 := by
      have heq : raw8671step0 = (fun i j => raw8671 (permutation294 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8671 permutation294 permutation3
    _ = injectiveMoment H node2671 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
