import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes1
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes3
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes4
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes13
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes14
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes15
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes17
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes19
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes41
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes43

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw6656 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, -1, 0, 0]]

theorem canonical6656 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6656 = injectiveMoment H node2645 := by
  rfl

def raw6657 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, -1, -1, 1]]

theorem canonical6657 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6657 = injectiveMoment H node2646 := by
  rfl

def raw6658 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, 0, 1, -2]]

theorem canonical6658 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6658 = injectiveMoment H node1117 := by
  rfl

def raw6659 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, 0, 0, -1]]

theorem canonical6659 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6659 = injectiveMoment H node1118 := by
  rfl

def raw6660 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -1, 1], ![0, 1, 1, -2], ![1, 0, -1, 0]]

def raw6660step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, 0, 1, -2]]

theorem canonical6660 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6660 = injectiveMoment H node1117 := by
  calc
    injectiveMoment H raw6660 = injectiveMoment H raw6660step0 := by
      have heq : raw6660step0 = (fun i j => raw6660 (permutation10 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6660 permutation10 permutation15
    _ = injectiveMoment H node1117 := by rfl

def raw6661 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -1, 1], ![0, 2, 0, -2], ![1, -1, 0, 0]]

def raw6661step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 0, 2, -1], ![1, -1, 0, 0], ![1, 1, -2, 0]]

def raw6661step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 1, 0], ![0, 1, 1, -2], ![1, 0, -1, 0]]

theorem canonical6661 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6661 = injectiveMoment H node1242 := by
  calc
    injectiveMoment H raw6661 = injectiveMoment H raw6661step0 := by
      have heq : raw6661step0 = raw6661.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6661).symm
    injectiveMoment H raw6661step0 = injectiveMoment H raw6661step1 := by
      have heq : raw6661step1 = (fun i j => raw6661step0 (permutation18 i) (permutation29 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6661step0 permutation18 permutation29
    _ = injectiveMoment H node1242 := by rfl

def raw6662 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, -1, -1, 1]]

def raw6662step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 0, 2, -1], ![1, -1, 1, -1], ![1, 1, -3, 1]]

def raw6662step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 0, -1], ![1, 0, -2, 1], ![-1, 1, -1, 1], ![-1, -1, 3, -1]]

def raw6662step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 1, 0], ![0, 1, 1, -2], ![1, 1, -1, -1]]

theorem canonical6662 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6662 = injectiveMoment H node936 := by
  calc
    injectiveMoment H raw6662 = injectiveMoment H raw6662step0 := by
      have heq : raw6662step0 = raw6662.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6662).symm
    injectiveMoment H raw6662step0 = injectiveMoment H raw6662step1 := by
      have heq : raw6662step1 = -raw6662step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6662step0).symm
    injectiveMoment H raw6662step1 = injectiveMoment H raw6662step2 := by
      have heq : raw6662step2 = (fun i j => raw6662step1 (permutation27 i) (permutation19 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6662step1 permutation27 permutation19
    _ = injectiveMoment H node936 := by rfl

def raw6663 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, -1, -2, 2]]

def raw6663step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 0, 2, -1], ![1, -1, 2, -2], ![1, 1, -4, 2]]

def raw6663step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 0, -1], ![1, 0, -2, 1], ![-1, 1, -2, 2], ![-1, -1, 4, -2]]

def raw6663step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, -1, 2, -2]]

theorem canonical6663 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6663 = injectiveMoment H node921 := by
  calc
    injectiveMoment H raw6663 = injectiveMoment H raw6663step0 := by
      have heq : raw6663step0 = raw6663.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6663).symm
    injectiveMoment H raw6663step0 = injectiveMoment H raw6663step1 := by
      have heq : raw6663step1 = -raw6663step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6663step0).symm
    injectiveMoment H raw6663step1 = injectiveMoment H raw6663step2 := by
      have heq : raw6663step2 = (fun i j => raw6663step1 (permutation27 i) (permutation16 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6663step1 permutation27 permutation16
    _ = injectiveMoment H node921 := by rfl

def raw6664 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, 0, 0], ![0, 1, -1, 0], ![1, 0, 0, -1]]

def raw6664step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 0, 1, 0], ![1, 0, -1, 0], ![1, 0, 0, -1]]

def raw6664step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1]]

def raw6664step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1]]

theorem canonical6664 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6664 = injectiveMoment H node293 := by
  calc
    injectiveMoment H raw6664 = injectiveMoment H raw6664step0 := by
      have heq : raw6664step0 = raw6664.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6664).symm
    injectiveMoment H raw6664step0 = injectiveMoment H raw6664step1 := by
      have hz : ∀ i, raw6664step0 i (permutation15 0) = 0 := by decide +kernel
      have heq : raw6664step1 = (fun i j => raw6664step0 i (permutation15 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw6664step0 permutation15 hz
    injectiveMoment H raw6664step1 = injectiveMoment H raw6664step2 := by
      have heq : raw6664step2 = (fun i j => raw6664step1 (permutation25 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6664step1 permutation25 permutation6
    _ = injectiveMoment H node293 := by rfl

def raw6665 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, 0, 0], ![0, 2, 0, -2], ![1, -1, -1, 1]]

def raw6665step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 0, 2, -1], ![1, 0, 0, -1], ![1, 0, -2, 1]]

def raw6665step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![1, -2, 1]]

def raw6665step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]

theorem canonical6665 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6665 = injectiveMoment H node227 := by
  calc
    injectiveMoment H raw6665 = injectiveMoment H raw6665step0 := by
      have heq : raw6665step0 = raw6665.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6665).symm
    injectiveMoment H raw6665step0 = injectiveMoment H raw6665step1 := by
      have hz : ∀ i, raw6665step0 i (permutation15 0) = 0 := by decide +kernel
      have heq : raw6665step1 = (fun i j => raw6665step0 i (permutation15 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw6665step0 permutation15 hz
    injectiveMoment H raw6665step1 = injectiveMoment H raw6665step2 := by
      have heq : raw6665step2 = (fun i j => raw6665step1 (permutation28 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6665step1 permutation28 permutation5
    _ = injectiveMoment H node227 := by rfl

def raw6666 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, 0, 0], ![1, 1, -1, -1]]

def raw6666step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1]]

def raw6666step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![1, -1]]

theorem canonical6666 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6666 = injectiveMoment H node65 := by
  calc
    injectiveMoment H raw6666 = injectiveMoment H raw6666step0 := by
      have heq : raw6666step0 = raw6666.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6666).symm
    injectiveMoment H raw6666step0 = injectiveMoment H raw6666step1 := by
      have hz : ∀ i, raw6666step0 i (permutation5 0) = 0 := by decide +kernel
      have heq : raw6666step1 = (fun i j => raw6666step0 i (permutation5 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw6666step0 permutation5 hz
    _ = injectiveMoment H node65 := by rfl

def raw6667 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, 1, -1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, 0, 0, -1]]

def raw6667step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 0, 0, -1]]

theorem canonical6667 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6667 = injectiveMoment H node2642 := by
  calc
    injectiveMoment H raw6667 = injectiveMoment H raw6667step0 := by
      have heq : raw6667step0 = (fun i j => raw6667 (permutation39 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6667 permutation39 permutation9
    _ = injectiveMoment H node2642 := by rfl

def raw6668 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, 1, -1], ![0, 0, -1, 1], ![1, 1, -1, -1]]

def raw6668step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, 1, -1, -1]]

theorem canonical6668 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6668 = injectiveMoment H node1114 := by
  calc
    injectiveMoment H raw6668 = injectiveMoment H raw6668step0 := by
      have heq : raw6668step0 = (fun i j => raw6668 (permutation11 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6668 permutation11 permutation9
    _ = injectiveMoment H node1114 := by rfl

def raw6669 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -3, 1], ![1, -1, 0, 0]]

def raw6669step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, -1, 0, 0]]

theorem canonical6669 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6669 = injectiveMoment H node2640 := by
  calc
    injectiveMoment H raw6669 = injectiveMoment H raw6669step0 := by
      have heq : raw6669step0 = (fun i j => raw6669 (permutation33 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6669 permutation33 permutation10
    _ = injectiveMoment H node2640 := by rfl

def raw6670 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, 1, -1], ![0, 1, -2, 1], ![1, 0, 0, -1]]

def raw6670step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, 0, 1, -2]]

theorem canonical6670 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6670 = injectiveMoment H node1117 := by
  calc
    injectiveMoment H raw6670 = injectiveMoment H raw6670step0 := by
      have heq : raw6670step0 = (fun i j => raw6670 (permutation10 i) (permutation16 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6670 permutation10 permutation16
    _ = injectiveMoment H node1117 := by rfl

def raw6671 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 0, -1, 1], ![1, 0, 0, -1]]

def raw6671step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 0, 0, -1]]

theorem canonical6671 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6671 = injectiveMoment H node2642 := by
  calc
    injectiveMoment H raw6671 = injectiveMoment H raw6671step0 := by
      have heq : raw6671step0 = (fun i j => raw6671 (permutation45 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6671 permutation45 permutation9
    _ = injectiveMoment H node2642 := by rfl

def raw6672 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 0, 0]]

def raw6672step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, -1, 1]]

theorem canonical6672 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6672 = injectiveMoment H node2785 := by
  calc
    injectiveMoment H raw6672 = injectiveMoment H raw6672step0 := by
      have heq : raw6672step0 = (fun i j => raw6672 (permutation65 i) (permutation27 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6672 permutation65 permutation27
    _ = injectiveMoment H node2785 := by rfl

def raw6673 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 0, -1, 0]]

def raw6673step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, 0, 0, -1]]

theorem canonical6673 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6673 = injectiveMoment H node1118 := by
  calc
    injectiveMoment H raw6673 = injectiveMoment H raw6673step0 := by
      have heq : raw6673step0 = (fun i j => raw6673 (permutation9 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6673 permutation9 permutation10
    _ = injectiveMoment H node1118 := by rfl

def raw6674 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, -2, 2]]

theorem canonical6674 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6674 = injectiveMoment H node2647 := by
  rfl

def raw6675 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, 1, -1], ![0, 2, -3, 1], ![1, -1, 1, -1]]

def raw6675step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 0, 2, -1], ![1, 1, -3, 1], ![1, -1, 1, -1]]

def raw6675step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 0, -1], ![1, 0, -2, 1], ![-1, -1, 3, -1], ![-1, 1, -1, 1]]

def raw6675step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 1, 0], ![0, 1, 1, -2], ![1, 1, -1, -1]]

theorem canonical6675 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6675 = injectiveMoment H node936 := by
  calc
    injectiveMoment H raw6675 = injectiveMoment H raw6675step0 := by
      have heq : raw6675step0 = raw6675.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6675).symm
    injectiveMoment H raw6675step0 = injectiveMoment H raw6675step1 := by
      have heq : raw6675step1 = -raw6675step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6675step0).symm
    injectiveMoment H raw6675step1 = injectiveMoment H raw6675step2 := by
      have heq : raw6675step2 = (fun i j => raw6675step1 (permutation21 i) (permutation19 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6675step1 permutation21 permutation19
    _ = injectiveMoment H node936 := by rfl

def raw6676 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, -1, 0, 0]]

def raw6676step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 0, 2, -1], ![1, 1, -2, 0], ![1, -1, 0, 0]]

def raw6676step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 1, 0], ![0, 1, 1, -2], ![1, 0, -1, 0]]

theorem canonical6676 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6676 = injectiveMoment H node1242 := by
  calc
    injectiveMoment H raw6676 = injectiveMoment H raw6676step0 := by
      have heq : raw6676step0 = raw6676.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6676).symm
    injectiveMoment H raw6676step0 = injectiveMoment H raw6676step1 := by
      have heq : raw6676step1 = (fun i j => raw6676step0 (permutation20 i) (permutation29 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6676step0 permutation20 permutation29
    _ = injectiveMoment H node1242 := by rfl

def raw6677 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, -1, -1, 1]]

def raw6677step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -1, 1], ![0, 2, -1, -1], ![1, -1, 1, -1]]

theorem canonical6677 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6677 = injectiveMoment H node1119 := by
  calc
    injectiveMoment H raw6677 = injectiveMoment H raw6677step0 := by
      have heq : raw6677step0 = (fun i j => raw6677 (permutation9 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6677 permutation9 permutation10
    _ = injectiveMoment H node1119 := by rfl

def raw6678 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -1, -2, 2]]

def raw6678step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 0, 2, -1], ![1, 1, 0, -2], ![1, -1, -2, 2]]

def raw6678step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -1, 1], ![0, 2, -1, -1], ![1, 0, 1, -2]]

theorem canonical6678 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6678 = injectiveMoment H node837 := by
  calc
    injectiveMoment H raw6678 = injectiveMoment H raw6678step0 := by
      have heq : raw6678step0 = raw6678.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6678).symm
    injectiveMoment H raw6678step0 = injectiveMoment H raw6678step1 := by
      have heq : raw6678step1 = (fun i j => raw6678step0 (permutation27 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6678step0 permutation27 permutation17
    _ = injectiveMoment H node837 := by rfl

def raw6679 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, 1, -1], ![0, 2, 1, -3], ![1, -1, -3, 3]]

def raw6679step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 0, 2, -1], ![1, 1, 1, -3], ![1, -1, -3, 3]]

def raw6679step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 0, -1], ![1, 0, -2, 1], ![-1, -1, -1, 3], ![-1, 1, 3, -3]]

def raw6679step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, -1, 3, -3]]

theorem canonical6679 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6679 = injectiveMoment H node982 := by
  calc
    injectiveMoment H raw6679 = injectiveMoment H raw6679step0 := by
      have heq : raw6679step0 = raw6679.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6679).symm
    injectiveMoment H raw6679step0 = injectiveMoment H raw6679step1 := by
      have heq : raw6679step1 = -raw6679step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6679step0).symm
    injectiveMoment H raw6679step1 = injectiveMoment H raw6679step2 := by
      have heq : raw6679step2 = (fun i j => raw6679step1 (permutation23 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6679step1 permutation23 permutation15
    _ = injectiveMoment H node982 := by rfl

def raw6680 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, 1, -1], ![1, 1, -2, 0]]

def raw6680step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![1, 1, -2], ![1, -1, 0]]

def raw6680step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![1, 0, -1], ![-1, -1, 2], ![-1, 1, 0]]

def raw6680step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0]]

theorem canonical6680 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6680 = injectiveMoment H node287 := by
  calc
    injectiveMoment H raw6680 = injectiveMoment H raw6680step0 := by
      have heq : raw6680step0 = raw6680.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6680).symm
    injectiveMoment H raw6680step0 = injectiveMoment H raw6680step1 := by
      have heq : raw6680step1 = -raw6680step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6680step0).symm
    injectiveMoment H raw6680step1 = injectiveMoment H raw6680step2 := by
      have heq : raw6680step2 = (fun i j => raw6680step1 (permutation21 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6680step1 permutation21 permutation5
    _ = injectiveMoment H node287 := by rfl

def raw6681 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, 2, -2], ![0, 1, -2, 1], ![1, 0, -1, 0]]

def raw6681step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, 0, 1, -2]]

theorem canonical6681 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6681 = injectiveMoment H node1110 := by
  calc
    injectiveMoment H raw6681 = injectiveMoment H raw6681step0 := by
      have heq : raw6681step0 = (fun i j => raw6681 (permutation10 i) (permutation16 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6681 permutation10 permutation16
    _ = injectiveMoment H node1110 := by rfl

def raw6682 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, 2, -2], ![0, 2, -3, 1], ![1, -1, 0, 0]]

def raw6682step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 0, 2, -1], ![1, 2, -3, 0], ![1, -2, 1, 0]]

def raw6682step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, -2, 1], ![0, 1, 2, -3], ![1, -1, 0, 0]]

theorem canonical6682 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6682 = injectiveMoment H node1079 := by
  calc
    injectiveMoment H raw6682 = injectiveMoment H raw6682step0 := by
      have heq : raw6682step0 = raw6682.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6682).symm
    injectiveMoment H raw6682step0 = injectiveMoment H raw6682step1 := by
      have heq : raw6682step1 = (fun i j => raw6682step0 (permutation20 i) (permutation27 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6682step0 permutation20 permutation27
    _ = injectiveMoment H node1079 := by rfl

def raw6683 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, 2, -2], ![0, 2, -2, 0], ![1, -1, -1, 1]]

def raw6683step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -2, 2], ![0, 2, 0, -2], ![1, -1, 1, -1]]

theorem canonical6683 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6683 = injectiveMoment H node1112 := by
  calc
    injectiveMoment H raw6683 = injectiveMoment H raw6683step0 := by
      have heq : raw6683step0 = (fun i j => raw6683 (permutation9 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6683 permutation9 permutation10
    _ = injectiveMoment H node1112 := by rfl

def raw6684 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, 2, -2], ![0, 2, 0, -2], ![1, -1, -3, 3]]

theorem canonical6684 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6684 = injectiveMoment H node1120 := by
  rfl

def raw6685 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 1, -4, 3], ![1, 0, 3, -4]]

def raw6685step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![1, -4, 3], ![1, 3, -4]]

def raw6685step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![1, -1, 0], ![-1, 4, -3], ![-1, -3, 4]]

def raw6685step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 4, -3], ![1, -1, 0], ![1, 0, -1]]

theorem canonical6685 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6685 = injectiveMoment H node249 := by
  calc
    injectiveMoment H raw6685 = injectiveMoment H raw6685step0 := by
      have heq : raw6685step0 = raw6685.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6685).symm
    injectiveMoment H raw6685step0 = injectiveMoment H raw6685step1 := by
      have heq : raw6685step1 = -raw6685step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6685step0).symm
    injectiveMoment H raw6685step1 = injectiveMoment H raw6685step2 := by
      have heq : raw6685step2 = (fun i j => raw6685step1 (permutation32 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6685step1 permutation32 permutation3
    _ = injectiveMoment H node249 := by rfl

def raw6686 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 1, -3, 2], ![0, 1, 1, -2], ![1, -1, 1, -1]]

theorem canonical6686 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6686 = injectiveMoment H node1123 := by
  rfl

def raw6687 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 1, -3, 2], ![0, 1, 2, -3], ![1, -1, 0, 0]]

theorem canonical6687 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6687 = injectiveMoment H node1124 := by
  rfl

end MUB6.Certificate.PairSemantics

end OAI
