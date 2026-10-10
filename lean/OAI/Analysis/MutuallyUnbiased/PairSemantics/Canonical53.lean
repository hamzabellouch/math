import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes6
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes7
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes12
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes14
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes15
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes18
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes19
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes25

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw1696 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 1, 1, -2], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, 0, -1, 0]]

theorem canonical1696 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1696 = injectiveMoment H node1618 := by
  rfl

def raw1697 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 1, 1, -2], ![0, 1, 1, -2], ![2, -1, -1, 0]]

def raw1697step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-1, 1, 1, -1], ![-1, 1, 1, -1], ![4, -2, -2, 0]]

def raw1697step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 2, -2], ![1, 1, -1, -1], ![1, 1, -1, -1]]

theorem canonical1697 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1697 = injectiveMoment H node398 := by
  calc
    injectiveMoment H raw1697 = injectiveMoment H raw1697step0 := by
      have heq : raw1697step0 = raw1697.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1697).symm
    injectiveMoment H raw1697step0 = injectiveMoment H raw1697step1 := by
      have heq : raw1697step1 = (fun i j => raw1697step0 (permutation27 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1697step0 permutation27 permutation18
    _ = injectiveMoment H node398 := by rfl

def raw1698 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 1, 1, -2], ![1, -1, -1, 1], ![1, 1, 1, -3]]

theorem canonical1698 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1698 = injectiveMoment H node463 := by
  rfl

def raw1699 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, 1, 0, -2]]

def raw1699step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, 0, 1, -2]]

theorem canonical1699 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1699 = injectiveMoment H node786 := by
  calc
    injectiveMoment H raw1699 = injectiveMoment H raw1699step0 := by
      have heq : raw1699step0 = (fun i j => raw1699 (permutation12 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1699 permutation12 permutation21
    _ = injectiveMoment H node786 := by rfl

def raw1700 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 1, 1, -2], ![1, -1, 1, -1], ![1, 1, -1, -1]]

theorem canonical1700 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1700 = injectiveMoment H node464 := by
  rfl

def raw1701 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 1, 1, -2], ![1, -1, 2, -2], ![1, 1, -2, 0]]

theorem canonical1701 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1701 = injectiveMoment H node465 := by
  rfl

def raw1702 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 1, 1, -2], ![1, 0, -1, 0], ![1, 0, 1, -2]]

def raw1702step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, 0, 1, -2]]

theorem canonical1702 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1702 = injectiveMoment H node786 := by
  calc
    injectiveMoment H raw1702 = injectiveMoment H raw1702step0 := by
      have heq : raw1702step0 = (fun i j => raw1702 (permutation12 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1702 permutation12 permutation15
    _ = injectiveMoment H node786 := by rfl

def raw1703 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 1, 1, -2], ![1, 0, 1, -2], ![1, 0, -1, 0]]

def raw1703step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, 0, 1, -2]]

theorem canonical1703 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1703 = injectiveMoment H node786 := by
  calc
    injectiveMoment H raw1703 = injectiveMoment H raw1703step0 := by
      have heq : raw1703step0 = (fun i j => raw1703 (permutation14 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1703 permutation14 permutation15
    _ = injectiveMoment H node786 := by rfl

def raw1704 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 1, 2, -3], ![1, -1, -1, 1], ![1, 1, 0, -2]]

theorem canonical1704 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1704 = injectiveMoment H node466 := by
  rfl

def raw1705 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 1, 2, -3], ![1, -1, 0, 0], ![1, 1, -1, -1]]

def raw1705step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 1, -1, 1], ![-1, 2, 0, -1], ![4, -3, 0, -1]]

def raw1705step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![1, -1, 1, -1], ![1, -2, 0, 1], ![-4, 3, 0, 1]]

def raw1705step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, -2, 1], ![0, 1, 3, -4], ![1, -1, -1, 1]]

theorem canonical1705 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw1705 = injectiveMoment H node1080 := by
  calc
    injectiveMoment H raw1705 = injectiveMoment H raw1705step0 := by
      have heq : raw1705step0 = raw1705.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1705).symm
    injectiveMoment H raw1705step0 = injectiveMoment H raw1705step1 := by
      have heq : raw1705step1 = -raw1705step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw1705step0).symm
    injectiveMoment H raw1705step1 = injectiveMoment H raw1705step2 := by
      have heq : raw1705step2 = (fun i j => raw1705step1 (permutation12 i) (permutation26 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1705step1 permutation12 permutation26
    _ = injectiveMoment H node1080 := by rfl

def raw1706 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 1, 2, -3], ![1, -1, 1, -1], ![1, 1, -2, 0]]

theorem canonical1706 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1706 = injectiveMoment H node467 := by
  rfl

def raw1707 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 1, 2, -3], ![1, 0, -1, 0], ![1, 0, 0, -1]]

def raw1707step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 1, 0, 0], ![-1, 2, -1, 0], ![4, -3, 0, -1]]

def raw1707step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![1, -1, 0, 0], ![1, -2, 1, 0], ![-4, 3, 0, 1]]

def raw1707step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 1, -2, 1], ![1, 0, 3, -4]]

theorem canonical1707 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw1707 = injectiveMoment H node1042 := by
  calc
    injectiveMoment H raw1707 = injectiveMoment H raw1707step0 := by
      have heq : raw1707step0 = raw1707.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1707).symm
    injectiveMoment H raw1707step0 = injectiveMoment H raw1707step1 := by
      have heq : raw1707step1 = -raw1707step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw1707step0).symm
    injectiveMoment H raw1707step1 = injectiveMoment H raw1707step2 := by
      have heq : raw1707step2 = (fun i j => raw1707step1 (permutation9 i) (permutation32 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1707step1 permutation9 permutation32
    _ = injectiveMoment H node1042 := by rfl

def raw1708 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 1, 2, -3], ![1, 0, 0, -1], ![1, 0, -1, 0]]

def raw1708step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 1, 0, 0], ![-1, 2, 0, -1], ![4, -3, -1, 0]]

def raw1708step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![1, -1, 0, 0], ![1, -2, 0, 1], ![-4, 3, 1, 0]]

def raw1708step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 1, -2, 1], ![1, 0, 3, -4]]

theorem canonical1708 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw1708 = injectiveMoment H node1042 := by
  calc
    injectiveMoment H raw1708 = injectiveMoment H raw1708step0 := by
      have heq : raw1708step0 = raw1708.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1708).symm
    injectiveMoment H raw1708step0 = injectiveMoment H raw1708step1 := by
      have heq : raw1708step1 = -raw1708step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw1708step0).symm
    injectiveMoment H raw1708step1 = injectiveMoment H raw1708step2 := by
      have heq : raw1708step2 = (fun i j => raw1708step1 (permutation9 i) (permutation26 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1708step1 permutation9 permutation26
    _ = injectiveMoment H node1042 := by rfl

def raw1709 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 1, 3, -4], ![1, -1, 0, 0], ![1, 1, -2, 0]]

def raw1709step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 1, -1, 1], ![-1, 3, 0, -2], ![4, -4, 0, 0]]

def raw1709step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![1, -1, 1, -1], ![1, -3, 0, 2], ![-4, 4, 0, 0]]

def raw1709step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 4, -4], ![0, 2, -3, 1], ![1, -1, -1, 1]]

theorem canonical1709 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw1709 = injectiveMoment H node1071 := by
  calc
    injectiveMoment H raw1709 = injectiveMoment H raw1709step0 := by
      have heq : raw1709step0 = raw1709.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1709).symm
    injectiveMoment H raw1709step0 = injectiveMoment H raw1709step1 := by
      have heq : raw1709step1 = -raw1709step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw1709step0).symm
    injectiveMoment H raw1709step1 = injectiveMoment H raw1709step2 := by
      have heq : raw1709step2 = (fun i j => raw1709step1 (permutation14 i) (permutation26 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1709step1 permutation14 permutation26
    _ = injectiveMoment H node1071 := by rfl

def raw1710 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 1, 3, -4], ![1, 0, -1, 0], ![1, 0, -1, 0]]

def raw1710step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 1, 0, 0], ![-1, 3, -1, -1], ![4, -4, 0, 0]]

def raw1710step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, -1, 1], ![0, 0, 4, -4], ![1, 1, -2, 0]]

theorem canonical1710 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1710 = injectiveMoment H node961 := by
  calc
    injectiveMoment H raw1710 = injectiveMoment H raw1710step0 := by
      have heq : raw1710step0 = raw1710.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1710).symm
    injectiveMoment H raw1710step0 = injectiveMoment H raw1710step1 := by
      have heq : raw1710step1 = (fun i j => raw1710step0 (permutation24 i) (permutation25 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1710step0 permutation24 permutation25
    _ = injectiveMoment H node961 := by rfl

def raw1711 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 2, -2, 0], ![1, -1, 0, 0], ![1, 0, 3, -4]]

def raw1711step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 2, -1, 0], ![-1, -2, 0, 3], ![4, 0, 0, -4]]

def raw1711step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![1, -2, 1, 0], ![1, 2, 0, -3], ![-4, 0, 0, 4]]

def raw1711step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, 4, -4], ![0, 2, -3, 1], ![1, -2, 0, 1]]

theorem canonical1711 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw1711 = injectiveMoment H node1273 := by
  calc
    injectiveMoment H raw1711 = injectiveMoment H raw1711step0 := by
      have heq : raw1711step0 = raw1711.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1711).symm
    injectiveMoment H raw1711step0 = injectiveMoment H raw1711step1 := by
      have heq : raw1711step1 = -raw1711step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw1711step0).symm
    injectiveMoment H raw1711step1 = injectiveMoment H raw1711step2 := by
      have heq : raw1711step2 = (fun i j => raw1711step1 (permutation14 i) (permutation24 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1711step1 permutation14 permutation24
    _ = injectiveMoment H node1273 := by rfl

def raw1712 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 2, -2, 0], ![1, -1, 1, -1], ![1, 0, 2, -3]]

theorem canonical1712 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1712 = injectiveMoment H node468 := by
  rfl

def raw1713 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 2, -2, 0], ![1, -1, 2, -2], ![1, 0, 1, -2]]

theorem canonical1713 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1713 = injectiveMoment H node469 := by
  rfl

def raw1714 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 2, -2, 0], ![1, -1, 3, -3], ![1, 0, 0, -1]]

def raw1714step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 2, -1, 0], ![-1, -2, 3, 0], ![4, 0, -3, -1]]

def raw1714step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, -2, 3, -1], ![0, 2, -1, -1], ![1, 0, 1, -2]]

theorem canonical1714 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1714 = injectiveMoment H node1166 := by
  calc
    injectiveMoment H raw1714 = injectiveMoment H raw1714step0 := by
      have heq : raw1714step0 = raw1714.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1714).symm
    injectiveMoment H raw1714step0 = injectiveMoment H raw1714step1 := by
      have heq : raw1714step1 = (fun i j => raw1714step0 (permutation32 i) (permutation30 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1714step0 permutation32 permutation30
    _ = injectiveMoment H node1166 := by rfl

def raw1715 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 2, -1, -1], ![1, -1, 0, 0], ![1, 0, 2, -3]]

def raw1715step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 2, -1, 0], ![-1, -1, 0, 2], ![4, -1, 0, -3]]

def raw1715step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![1, -2, 1, 0], ![1, 1, 0, -2], ![-4, 1, 0, 3]]

def raw1715step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 1, -2, 1], ![0, 1, 3, -4], ![1, -2, 0, 1]]

theorem canonical1715 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw1715 = injectiveMoment H node1278 := by
  calc
    injectiveMoment H raw1715 = injectiveMoment H raw1715step0 := by
      have heq : raw1715step0 = raw1715.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1715).symm
    injectiveMoment H raw1715step0 = injectiveMoment H raw1715step1 := by
      have heq : raw1715step1 = -raw1715step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw1715step0).symm
    injectiveMoment H raw1715step1 = injectiveMoment H raw1715step2 := by
      have heq : raw1715step2 = (fun i j => raw1715step1 (permutation12 i) (permutation24 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1715step1 permutation12 permutation24
    _ = injectiveMoment H node1278 := by rfl

def raw1716 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 2, -1, -1], ![1, -1, 1, -1], ![1, 0, 1, -2]]

def raw1716step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 2, -1], ![1, 1, -1, -1], ![1, 1, 0, -2]]

theorem canonical1716 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1716 = injectiveMoment H node454 := by
  calc
    injectiveMoment H raw1716 = injectiveMoment H raw1716step0 := by
      have heq : raw1716step0 = (fun i j => raw1716 (permutation9 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1716 permutation9 permutation11
    _ = injectiveMoment H node454 := by rfl

def raw1717 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 2, -1, -1], ![1, -1, 2, -2], ![1, 0, 0, -1]]

def raw1717step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 2, -1, 0], ![-1, -1, 2, 0], ![4, -1, -2, -1]]

def raw1717step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, -1, 2, -1], ![0, 2, -1, -1], ![1, 0, 1, -2]]

theorem canonical1717 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1717 = injectiveMoment H node896 := by
  calc
    injectiveMoment H raw1717 = injectiveMoment H raw1717step0 := by
      have heq : raw1717step0 = raw1717.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1717).symm
    injectiveMoment H raw1717step0 = injectiveMoment H raw1717step1 := by
      have heq : raw1717step1 = (fun i j => raw1717step0 (permutation32 i) (permutation30 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1717step0 permutation32 permutation30
    _ = injectiveMoment H node896 := by rfl

def raw1718 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 2, -1, -1], ![1, -1, 3, -3], ![1, 0, -1, 0]]

def raw1718step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 2, -1, 0], ![-1, -1, 3, -1], ![4, -1, -3, 0]]

def raw1718step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 4, -3], ![0, 2, -1, -1], ![1, 0, -2, 1]]

theorem canonical1718 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1718 = injectiveMoment H node954 := by
  calc
    injectiveMoment H raw1718 = injectiveMoment H raw1718step0 := by
      have heq : raw1718step0 = raw1718.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1718).symm
    injectiveMoment H raw1718step0 = injectiveMoment H raw1718step1 := by
      have heq : raw1718step1 = (fun i j => raw1718step0 (permutation26 i) (permutation29 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1718step0 permutation26 permutation29
    _ = injectiveMoment H node954 := by rfl

def raw1719 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 2, -1, -1], ![1, 0, 0, -1], ![1, -1, 2, -2]]

def raw1719step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 2, 0, -1], ![-1, -1, 0, 2], ![4, -1, -1, -2]]

def raw1719step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, -1, 2, -1], ![0, 2, -1, -1], ![1, 0, 1, -2]]

theorem canonical1719 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1719 = injectiveMoment H node896 := by
  calc
    injectiveMoment H raw1719 = injectiveMoment H raw1719step0 := by
      have heq : raw1719step0 = raw1719.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1719).symm
    injectiveMoment H raw1719step0 = injectiveMoment H raw1719step1 := by
      have heq : raw1719step1 = (fun i j => raw1719step0 (permutation32 i) (permutation24 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1719step0 permutation32 permutation24
    _ = injectiveMoment H node896 := by rfl

def raw1720 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 2, 0, -2], ![1, -1, -1, 1], ![1, 0, 2, -3]]

def raw1720step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 2, -2], ![1, -1, -1, 1], ![1, 2, 0, -3]]

theorem canonical1720 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1720 = injectiveMoment H node460 := by
  calc
    injectiveMoment H raw1720 = injectiveMoment H raw1720step0 := by
      have heq : raw1720step0 = (fun i j => raw1720 (permutation9 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1720 permutation9 permutation11
    _ = injectiveMoment H node460 := by rfl

def raw1721 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 2, 0, -2], ![1, -1, 0, 0], ![1, 0, 1, -2]]

def raw1721step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, 1, 0, -2]]

theorem canonical1721 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1721 = injectiveMoment H node771 := by
  calc
    injectiveMoment H raw1721 = injectiveMoment H raw1721step0 := by
      have heq : raw1721step0 = (fun i j => raw1721 (permutation9 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1721 permutation9 permutation21
    _ = injectiveMoment H node771 := by rfl

def raw1722 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 2, 0, -2], ![1, -1, 1, -1], ![1, 0, 0, -1]]

def raw1722step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 2, -1, 0], ![-1, 0, 1, 0], ![4, -2, -1, -1]]

def raw1722step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, 0, 1, -2]]

theorem canonical1722 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1722 = injectiveMoment H node769 := by
  calc
    injectiveMoment H raw1722 = injectiveMoment H raw1722step0 := by
      have heq : raw1722step0 = raw1722.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1722).symm
    injectiveMoment H raw1722step0 = injectiveMoment H raw1722step1 := by
      have heq : raw1722step1 = (fun i j => raw1722step0 (permutation32 i) (permutation30 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1722step0 permutation32 permutation30
    _ = injectiveMoment H node769 := by rfl

def raw1723 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 2, 0, -2], ![1, -1, 2, -2], ![1, 0, -1, 0]]

def raw1723step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 2, -1, 0], ![-1, 0, 2, -1], ![4, -2, -2, 0]]

def raw1723step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![1, -2, 1, 0], ![1, 0, -2, 1], ![-4, 2, 2, 0]]

def raw1723step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -2, 1, 1], ![0, 2, 2, -4], ![1, 0, -2, 1]]

theorem canonical1723 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw1723 = injectiveMoment H node1234 := by
  calc
    injectiveMoment H raw1723 = injectiveMoment H raw1723step0 := by
      have heq : raw1723step0 = raw1723.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1723).symm
    injectiveMoment H raw1723step0 = injectiveMoment H raw1723step1 := by
      have heq : raw1723step1 = -raw1723step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw1723step0).symm
    injectiveMoment H raw1723step1 = injectiveMoment H raw1723step2 := by
      have heq : raw1723step2 = (fun i j => raw1723step1 (permutation10 i) (permutation30 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1723step1 permutation10 permutation30
    _ = injectiveMoment H node1234 := by rfl

def raw1724 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 2, 0, -2], ![1, 0, -1, 0], ![1, -1, 2, -2]]

def raw1724step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 2, 0, -1], ![-1, 0, -1, 2], ![4, -2, 0, -2]]

def raw1724step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![1, -2, 0, 1], ![1, 0, 1, -2], ![-4, 2, 0, 2]]

def raw1724step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -2, 1, 1], ![0, 2, 2, -4], ![1, 0, -2, 1]]

theorem canonical1724 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw1724 = injectiveMoment H node1234 := by
  calc
    injectiveMoment H raw1724 = injectiveMoment H raw1724step0 := by
      have heq : raw1724step0 = raw1724.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1724).symm
    injectiveMoment H raw1724step0 = injectiveMoment H raw1724step1 := by
      have heq : raw1724step1 = -raw1724step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw1724step0).symm
    injectiveMoment H raw1724step1 = injectiveMoment H raw1724step2 := by
      have heq : raw1724step2 = (fun i j => raw1724step1 (permutation10 i) (permutation24 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1724step1 permutation10 permutation24
    _ = injectiveMoment H node1234 := by rfl

def raw1725 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 2, 1, -3], ![1, -1, -1, 1], ![1, 0, 1, -2]]

def raw1725step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 1, 2, -3], ![1, -1, -1, 1], ![1, 1, 0, -2]]

theorem canonical1725 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1725 = injectiveMoment H node466 := by
  calc
    injectiveMoment H raw1725 = injectiveMoment H raw1725step0 := by
      have heq : raw1725step0 = (fun i j => raw1725 (permutation9 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1725 permutation9 permutation11
    _ = injectiveMoment H node466 := by rfl

def raw1726 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 2, 1, -3], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw1726step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 2, -1, 0], ![-1, 1, 0, 0], ![4, -3, 0, -1]]

def raw1726step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![1, -2, 1, 0], ![1, -1, 0, 0], ![-4, 3, 0, 1]]

def raw1726step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 1, -2, 1], ![1, 0, 3, -4]]

theorem canonical1726 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw1726 = injectiveMoment H node1042 := by
  calc
    injectiveMoment H raw1726 = injectiveMoment H raw1726step0 := by
      have heq : raw1726step0 = raw1726.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1726).symm
    injectiveMoment H raw1726step0 = injectiveMoment H raw1726step1 := by
      have heq : raw1726step1 = -raw1726step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw1726step0).symm
    injectiveMoment H raw1726step1 = injectiveMoment H raw1726step2 := by
      have heq : raw1726step2 = (fun i j => raw1726step1 (permutation11 i) (permutation32 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1726step1 permutation11 permutation32
    _ = injectiveMoment H node1042 := by rfl

def raw1727 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 2, 1, -3], ![1, -1, 1, -1], ![1, 0, -1, 0]]

def raw1727step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 2, -1, 0], ![-1, 1, 1, -1], ![4, -3, -1, 0]]

def raw1727step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![1, -2, 1, 0], ![1, -1, -1, 1], ![-4, 3, 1, 0]]

def raw1727step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, -2, 1], ![0, 1, 3, -4], ![1, -1, -1, 1]]

theorem canonical1727 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw1727 = injectiveMoment H node1080 := by
  calc
    injectiveMoment H raw1727 = injectiveMoment H raw1727step0 := by
      have heq : raw1727step0 = raw1727.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1727).symm
    injectiveMoment H raw1727step0 = injectiveMoment H raw1727step1 := by
      have heq : raw1727step1 = -raw1727step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw1727step0).symm
    injectiveMoment H raw1727step1 = injectiveMoment H raw1727step2 := by
      have heq : raw1727step2 = (fun i j => raw1727step1 (permutation10 i) (permutation32 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1727step1 permutation10 permutation32
    _ = injectiveMoment H node1080 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
