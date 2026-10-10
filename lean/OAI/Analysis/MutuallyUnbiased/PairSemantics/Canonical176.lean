import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes1
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes2
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes3
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes11
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes12
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes15
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes18
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes37
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes42

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw5632 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 1, 2, -3], ![0, 1, 0, -1], ![1, 0, -1, 0]]

def raw5632step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, 1, 1, 0], ![-1, 2, 0, -1], ![4, -3, -1, 0]]

def raw5632step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, -1, 2, -1], ![0, 1, 0, -1], ![1, 0, 1, -2]]

theorem canonical5632 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5632 = injectiveMoment H node1170 := by
  calc
    injectiveMoment H raw5632 = injectiveMoment H raw5632step0 := by
      have heq : raw5632step0 = raw5632.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5632).symm
    injectiveMoment H raw5632step0 = injectiveMoment H raw5632step1 := by
      have heq : raw5632step1 = (fun i j => raw5632step0 (permutation31 i) (permutation26 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5632step0 permutation31 permutation26
    _ = injectiveMoment H node1170 := by rfl

def raw5633 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 1, 2, -3], ![1, 1, -1, -1]]

def raw5633step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![-1, 2, -1], ![4, -3, -1]]

def raw5633step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 2, -1], ![1, 0, -1], ![1, 1, -2]]

theorem canonical5633 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5633 = injectiveMoment H node246 := by
  calc
    injectiveMoment H raw5633 = injectiveMoment H raw5633step0 := by
      have heq : raw5633step0 = raw5633.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5633).symm
    injectiveMoment H raw5633step0 = injectiveMoment H raw5633step1 := by
      have heq : raw5633step1 = (fun i j => raw5633step0 (permutation31 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5633step0 permutation31 permutation8
    _ = injectiveMoment H node246 := by rfl

def raw5634 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 1, 3, -4], ![1, 1, -2, 0]]

def raw5634step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![-1, 3, -2], ![4, -4, 0]]

def raw5634step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 4, -4], ![1, -2, 1], ![1, -1, 0]]

theorem canonical5634 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5634 = injectiveMoment H node190 := by
  calc
    injectiveMoment H raw5634 = injectiveMoment H raw5634step0 := by
      have heq : raw5634step0 = raw5634.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5634).symm
    injectiveMoment H raw5634step0 = injectiveMoment H raw5634step1 := by
      have heq : raw5634step1 = (fun i j => raw5634step0 (permutation26 i) (permutation7 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5634step0 permutation26 permutation7
    _ = injectiveMoment H node190 := by rfl

def raw5635 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 2, -2, 0], ![1, 0, 3, -4]]

def raw5635step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 2, 0], ![-1, -2, 3], ![4, 0, -4]]

def raw5635step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 4, -4], ![2, -2, 0]]

theorem canonical5635 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5635 = injectiveMoment H node171 := by
  calc
    injectiveMoment H raw5635 = injectiveMoment H raw5635step0 := by
      have heq : raw5635step0 = raw5635.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5635).symm
    injectiveMoment H raw5635step0 = injectiveMoment H raw5635step1 := by
      have heq : raw5635step1 = (fun i j => raw5635step0 (permutation22 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5635step0 permutation22 permutation5
    _ = injectiveMoment H node171 := by rfl

def raw5636 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 2, -1, -1], ![1, 0, 2, -3]]

def raw5636step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 2, 0], ![-1, -1, 2], ![4, -1, -3]]

def raw5636step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![2, -2, 0], ![1, 1, -2], ![-4, 1, 3]]

def raw5636step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![1, -2, 1], ![1, 3, -4]]

theorem canonical5636 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw5636 = injectiveMoment H node206 := by
  calc
    injectiveMoment H raw5636 = injectiveMoment H raw5636step0 := by
      have heq : raw5636step0 = raw5636.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5636).symm
    injectiveMoment H raw5636step0 = injectiveMoment H raw5636step1 := by
      have heq : raw5636step1 = -raw5636step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw5636step0).symm
    injectiveMoment H raw5636step1 = injectiveMoment H raw5636step2 := by
      have heq : raw5636step2 = (fun i j => raw5636step1 (permutation15 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5636step1 permutation15 permutation6
    _ = injectiveMoment H node206 := by rfl

def raw5637 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 2, 0, -2], ![1, 0, 1, -2]]

def raw5637step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 2, 0], ![-1, 0, 1], ![4, -2, -2]]

def raw5637step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 1, -1], ![2, 0, -2]]

theorem canonical5637 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5637 = injectiveMoment H node145 := by
  calc
    injectiveMoment H raw5637 = injectiveMoment H raw5637step0 := by
      have heq : raw5637step0 = raw5637.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5637).symm
    injectiveMoment H raw5637step0 = injectiveMoment H raw5637step1 := by
      have heq : raw5637step1 = (fun i j => raw5637step0 (permutation28 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5637step0 permutation28 permutation6
    _ = injectiveMoment H node145 := by rfl

def raw5638 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 2, 1, -3], ![1, 0, 0, -1]]

def raw5638step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 2, 0], ![-1, 1, 0], ![4, -3, -1]]

def raw5638step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1]]

theorem canonical5638 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5638 = injectiveMoment H node254 := by
  calc
    injectiveMoment H raw5638 = injectiveMoment H raw5638step0 := by
      have heq : raw5638step0 = raw5638.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5638).symm
    injectiveMoment H raw5638step0 = injectiveMoment H raw5638step1 := by
      have heq : raw5638step1 = (fun i j => raw5638step0 (permutation32 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5638step0 permutation32 permutation8
    _ = injectiveMoment H node254 := by rfl

def raw5639 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![1, 0, 1, -2], ![0, 2, 0, -2]]

def raw5639step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![-1, 1, 0], ![4, -2, -2]]

def raw5639step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 1, -1], ![2, 0, -2]]

theorem canonical5639 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5639 = injectiveMoment H node145 := by
  calc
    injectiveMoment H raw5639 = injectiveMoment H raw5639step0 := by
      have heq : raw5639step0 = raw5639.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5639).symm
    injectiveMoment H raw5639step0 = injectiveMoment H raw5639step1 := by
      have heq : raw5639step1 = (fun i j => raw5639step0 (permutation28 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5639step0 permutation28 permutation8
    _ = injectiveMoment H node145 := by rfl

def raw5640 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![1, 0, 2, -3], ![0, 2, -1, -1]]

def raw5640step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![-1, 2, -1], ![4, -3, -1]]

def raw5640step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -1, 0], ![2, 0, -2], ![1, -2, 1], ![-4, 3, 1]]

def raw5640step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![1, -2, 1], ![1, 3, -4]]

theorem canonical5640 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw5640 = injectiveMoment H node206 := by
  calc
    injectiveMoment H raw5640 = injectiveMoment H raw5640step0 := by
      have heq : raw5640step0 = raw5640.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5640).symm
    injectiveMoment H raw5640step0 = injectiveMoment H raw5640step1 := by
      have heq : raw5640step1 = -raw5640step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw5640step0).symm
    injectiveMoment H raw5640step1 = injectiveMoment H raw5640step2 := by
      have heq : raw5640step2 = (fun i j => raw5640step1 (permutation15 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5640step1 permutation15 permutation8
    _ = injectiveMoment H node206 := by rfl

def raw5641 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![1, 0, 3, -4], ![0, 2, -2, 0]]

def raw5641step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![-1, 3, -2], ![4, -4, 0]]

def raw5641step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 4, -4], ![2, -2, 0]]

theorem canonical5641 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5641 = injectiveMoment H node171 := by
  calc
    injectiveMoment H raw5641 = injectiveMoment H raw5641step0 := by
      have heq : raw5641step0 = raw5641.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5641).symm
    injectiveMoment H raw5641step0 = injectiveMoment H raw5641step1 := by
      have heq : raw5641step1 = (fun i j => raw5641step0 (permutation22 i) (permutation7 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5641step0 permutation22 permutation7
    _ = injectiveMoment H node171 := by rfl

def raw5642 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![1, 1, 0, -2], ![0, 1, 1, -2]]

def raw5642step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 1, 1], ![-1, 0, 1], ![4, -2, -2]]

def raw5642step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]

theorem canonical5642 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5642 = injectiveMoment H node150 := by
  calc
    injectiveMoment H raw5642 = injectiveMoment H raw5642step0 := by
      have heq : raw5642step0 = raw5642.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5642).symm
    injectiveMoment H raw5642step0 = injectiveMoment H raw5642step1 := by
      have heq : raw5642step1 = (fun i j => raw5642step0 (permutation31 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5642step0 permutation31 permutation6
    _ = injectiveMoment H node150 := by rfl

def raw5643 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, -2, 2], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, 2, 0, -3]]

theorem canonical5643 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5643 = injectiveMoment H node2404 := by
  rfl

def raw5644 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, -2, 2], ![0, 0, 1, -1], ![1, 2, 1, -4]]

def raw5644step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 2, 0, -3], ![0, 0, 2, -2], ![0, 0, -1, 1], ![-1, -2, -1, 4]]

def raw5644step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, -1, 1], ![0, 0, 2, -2], ![1, 2, 0, -3]]

theorem canonical5644 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw5644 = injectiveMoment H node760 := by
  calc
    injectiveMoment H raw5644 = injectiveMoment H raw5644step0 := by
      have heq : raw5644step0 = -raw5644 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw5644).symm
    injectiveMoment H raw5644step0 = injectiveMoment H raw5644step1 := by
      have heq : raw5644step1 = (fun i j => raw5644step0 (permutation32 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5644step0 permutation32 permutation9
    _ = injectiveMoment H node760 := by rfl

def raw5645 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, -2, 2], ![0, 0, 2, -2], ![1, 2, 0, -3]]

theorem canonical5645 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5645 = injectiveMoment H node789 := by
  rfl

def raw5646 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, 1, 2, -4]]

def raw5646step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 2, 0, -3], ![0, 0, 2, -2], ![0, -1, 0, 1], ![-1, -1, -2, 4]]

def raw5646step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, -1, 1], ![0, 2, 0, -2], ![1, 0, 2, -3]]

theorem canonical5646 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw5646 = injectiveMoment H node763 := by
  calc
    injectiveMoment H raw5646 = injectiveMoment H raw5646step0 := by
      have heq : raw5646step0 = -raw5646 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw5646).symm
    injectiveMoment H raw5646step0 = injectiveMoment H raw5646step1 := by
      have heq : raw5646step1 = (fun i j => raw5646step0 (permutation32 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5646step0 permutation32 permutation11
    _ = injectiveMoment H node763 := by rfl

def raw5647 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, -2, 2], ![0, 1, 2, -3], ![1, 1, 0, -2]]

theorem canonical5647 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5647 = injectiveMoment H node791 := by
  rfl

def raw5648 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, -2, 2], ![0, 2, 0, -2], ![1, 0, 2, -3]]

theorem canonical5648 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5648 = injectiveMoment H node793 := by
  rfl

def raw5649 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, -2, 2], ![0, 2, 2, -4], ![1, 0, 0, -1]]

theorem canonical5649 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5649 = injectiveMoment H node795 := by
  rfl

def raw5650 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, -2, 2], ![1, 2, 2, -5]]

def raw5650step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![0, -2, 2], ![3, 2, -5]]

def raw5650step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![2, 0, -2], ![0, 2, -2], ![-3, -2, 5]]

def raw5650step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 1, -1], ![0, 2, -2], ![2, 0, -2]]

theorem canonical5650 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw5650 = injectiveMoment H node120 := by
  calc
    injectiveMoment H raw5650 = injectiveMoment H raw5650step0 := by
      have heq : raw5650step0 = raw5650.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5650).symm
    injectiveMoment H raw5650step0 = injectiveMoment H raw5650step1 := by
      have heq : raw5650step1 = -raw5650step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw5650step0).symm
    injectiveMoment H raw5650step1 = injectiveMoment H raw5650step2 := by
      have heq : raw5650step2 = (fun i j => raw5650step1 (permutation27 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5650step1 permutation27 permutation5
    _ = injectiveMoment H node120 := by rfl

def raw5651 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, -1, 1], ![0, 0, 0, 0], ![0, 0, 1, -1], ![1, 2, 0, -3]]

def raw5651step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, 2, 0, -3]]

def raw5651step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 0, 1], ![0, 1, 0, -1], ![1, 0, 2, -3]]

theorem canonical5651 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5651 = injectiveMoment H node1197 := by
  calc
    injectiveMoment H raw5651 = injectiveMoment H raw5651step0 := by
      have hz : ∀ j, raw5651 (permutation80 0) j = 0 := by decide +kernel
      have heq : raw5651step0 = (fun i j => raw5651 (permutation80 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5651 permutation80 hz
    injectiveMoment H raw5651step0 = injectiveMoment H raw5651step1 := by
      have heq : raw5651step1 = (fun i j => raw5651step0 (permutation9 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5651step0 permutation9 permutation11
    _ = injectiveMoment H node1197 := by rfl

def raw5652 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 0, 0], ![1, 2, 0, -3]]

def raw5652step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, 2, 0, -3]]

def raw5652step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 0, 1], ![0, 1, 0, -1], ![1, 0, 2, -3]]

theorem canonical5652 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5652 = injectiveMoment H node1197 := by
  calc
    injectiveMoment H raw5652 = injectiveMoment H raw5652step0 := by
      have hz : ∀ j, raw5652 (permutation104 0) j = 0 := by decide +kernel
      have heq : raw5652step0 = (fun i j => raw5652 (permutation104 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5652 permutation104 hz
    injectiveMoment H raw5652step0 = injectiveMoment H raw5652step1 := by
      have heq : raw5652step1 = (fun i j => raw5652step0 (permutation9 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5652step0 permutation9 permutation11
    _ = injectiveMoment H node1197 := by rfl

def raw5653 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, 2, -1, -2]]

theorem canonical5653 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5653 = injectiveMoment H node2407 := by
  rfl

def raw5654 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, 0, 0, -1]]

def raw5654step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 0, 1], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, 0, 0, -1]]

theorem canonical5654 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5654 = injectiveMoment H node2701 := by
  calc
    injectiveMoment H raw5654 = injectiveMoment H raw5654step0 := by
      have heq : raw5654step0 = (fun i j => raw5654 (permutation35 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5654 permutation35 permutation11
    _ = injectiveMoment H node2701 := by rfl

def raw5655 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, 2, 0, -3]]

def raw5655step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 0, 1], ![0, 1, 0, -1], ![1, 0, 2, -3]]

theorem canonical5655 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5655 = injectiveMoment H node1197 := by
  calc
    injectiveMoment H raw5655 = injectiveMoment H raw5655step0 := by
      have heq : raw5655step0 = (fun i j => raw5655 (permutation9 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5655 permutation9 permutation11
    _ = injectiveMoment H node1197 := by rfl

def raw5656 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 3, -4]]

theorem canonical5656 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5656 = injectiveMoment H node2414 := by
  rfl

def raw5657 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, 0, 0, -1]]

theorem canonical5657 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5657 = injectiveMoment H node2416 := by
  rfl

def raw5658 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, 0, -1, 0]]

theorem canonical5658 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5658 = injectiveMoment H node2417 := by
  rfl

def raw5659 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, 1, 2, -4]]

def raw5659step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, 0, 1, 1], ![0, -1, -1, 2], ![3, 1, 0, -4]]

def raw5659step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 1, -2, 1], ![1, 0, 3, -4]]

theorem canonical5659 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5659 = injectiveMoment H node1042 := by
  calc
    injectiveMoment H raw5659 = injectiveMoment H raw5659step0 := by
      have heq : raw5659step0 = raw5659.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5659).symm
    injectiveMoment H raw5659step0 = injectiveMoment H raw5659step1 := by
      have heq : raw5659step1 = (fun i j => raw5659step0 (permutation21 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5659step0 permutation21 permutation17
    _ = injectiveMoment H node1042 := by rfl

def raw5660 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, 1, 1, -3]]

def raw5660step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 2, 0, -3], ![0, 0, 1, -1], ![0, -1, 0, 1], ![-1, -1, -1, 3]]

def raw5660step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, 0, 2, -3]]

theorem canonical5660 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw5660 = injectiveMoment H node963 := by
  calc
    injectiveMoment H raw5660 = injectiveMoment H raw5660step0 := by
      have heq : raw5660step0 = -raw5660 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw5660).symm
    injectiveMoment H raw5660step0 = injectiveMoment H raw5660step1 := by
      have heq : raw5660step1 = (fun i j => raw5660step0 (permutation32 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5660step0 permutation32 permutation11
    _ = injectiveMoment H node963 := by rfl

def raw5661 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, -1, 1], ![0, 2, 0, -2], ![1, 0, 1, -2]]

def raw5661step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 2, 0, -3], ![0, 0, 1, -1], ![0, -2, 0, 2], ![-1, 0, -1, 2]]

def raw5661step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, 0, 2, -3]]

theorem canonical5661 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw5661 = injectiveMoment H node1032 := by
  calc
    injectiveMoment H raw5661 = injectiveMoment H raw5661step0 := by
      have heq : raw5661step0 = -raw5661 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw5661).symm
    injectiveMoment H raw5661step0 = injectiveMoment H raw5661step1 := by
      have heq : raw5661step1 = (fun i j => raw5661step0 (permutation32 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5661step0 permutation32 permutation11
    _ = injectiveMoment H node1032 := by rfl

def raw5662 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, 0, 0, -1]]

def raw5662step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 0, 1], ![0, 1, 2, -3], ![1, 0, 0, -1]]

theorem canonical5662 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5662 = injectiveMoment H node1199 := by
  calc
    injectiveMoment H raw5662 = injectiveMoment H raw5662step0 := by
      have heq : raw5662step0 = (fun i j => raw5662 (permutation9 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5662 permutation9 permutation11
    _ = injectiveMoment H node1199 := by rfl

def raw5663 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, 0, -1, 0]]

def raw5663step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, 0, 2, 0], ![0, -1, 2, -1], ![3, 1, -4, 0]]

def raw5663step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 1, -1, 0], ![1, 0, 3, -4]]

theorem canonical5663 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5663 = injectiveMoment H node1031 := by
  calc
    injectiveMoment H raw5663 = injectiveMoment H raw5663step0 := by
      have heq : raw5663step0 = raw5663.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5663).symm
    injectiveMoment H raw5663step0 = injectiveMoment H raw5663step1 := by
      have heq : raw5663step1 = (fun i j => raw5663step0 (permutation23 i) (permutation19 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5663step0 permutation23 permutation19
    _ = injectiveMoment H node1031 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
