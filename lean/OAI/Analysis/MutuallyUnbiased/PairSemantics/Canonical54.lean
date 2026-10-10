import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes6
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes7
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes12
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes14
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes15
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes19
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes22
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes23
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes24
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes25
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes37
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes40
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes42

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw1728 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 2, 1, -3], ![1, 0, -1, 0], ![1, -1, 1, -1]]

def raw1728step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 2, 0, -1], ![-1, 1, -1, 1], ![4, -3, 0, -1]]

def raw1728step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![1, -2, 0, 1], ![1, -1, 1, -1], ![-4, 3, 0, 1]]

def raw1728step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, -2, 1], ![0, 1, 3, -4], ![1, -1, -1, 1]]

theorem canonical1728 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw1728 = injectiveMoment H node1080 := by
  calc
    injectiveMoment H raw1728 = injectiveMoment H raw1728step0 := by
      have heq : raw1728step0 = raw1728.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1728).symm
    injectiveMoment H raw1728step0 = injectiveMoment H raw1728step1 := by
      have heq : raw1728step1 = -raw1728step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw1728step0).symm
    injectiveMoment H raw1728step1 = injectiveMoment H raw1728step2 := by
      have heq : raw1728step2 = (fun i j => raw1728step1 (permutation10 i) (permutation26 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1728step1 permutation10 permutation26
    _ = injectiveMoment H node1080 := by rfl

def raw1729 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 2, 2, -4], ![1, -1, -1, 1], ![1, 0, 0, -1]]

def raw1729step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 2, -1, 0], ![-1, 2, -1, 0], ![4, -4, 1, -1]]

def raw1729step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![1, -2, 1, 0], ![1, -2, 1, 0], ![-4, 4, -1, 1]]

def raw1729step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, -2, 1], ![0, 1, -2, 1], ![1, -1, 4, -4]]

theorem canonical1729 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw1729 = injectiveMoment H node1077 := by
  calc
    injectiveMoment H raw1729 = injectiveMoment H raw1729step0 := by
      have heq : raw1729step0 = raw1729.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1729).symm
    injectiveMoment H raw1729step0 = injectiveMoment H raw1729step1 := by
      have heq : raw1729step1 = -raw1729step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw1729step0).symm
    injectiveMoment H raw1729step1 = injectiveMoment H raw1729step2 := by
      have heq : raw1729step2 = (fun i j => raw1729step1 (permutation9 i) (permutation32 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1729step1 permutation9 permutation32
    _ = injectiveMoment H node1077 := by rfl

def raw1730 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 2, 2, -4], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def raw1730step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 2, -1, 0], ![-1, 2, 0, -1], ![4, -4, 0, 0]]

def raw1730step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![1, -2, 1, 0], ![1, -2, 0, 1], ![-4, 4, 0, 0]]

def raw1730step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 4, -4], ![0, 1, -2, 1], ![1, 0, -2, 1]]

theorem canonical1730 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw1730 = injectiveMoment H node1070 := by
  calc
    injectiveMoment H raw1730 = injectiveMoment H raw1730step0 := by
      have heq : raw1730step0 = raw1730.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1730).symm
    injectiveMoment H raw1730step0 = injectiveMoment H raw1730step1 := by
      have heq : raw1730step1 = -raw1730step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw1730step0).symm
    injectiveMoment H raw1730step1 = injectiveMoment H raw1730step2 := by
      have heq : raw1730step2 = (fun i j => raw1730step1 (permutation14 i) (permutation26 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1730step1 permutation14 permutation26
    _ = injectiveMoment H node1070 := by rfl

def raw1731 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![1, -1, 1, -1], ![0, 2, -1, -1], ![1, 0, 1, -2]]

def raw1731step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 2, -1], ![1, 1, -1, -1], ![1, 1, 0, -2]]

theorem canonical1731 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1731 = injectiveMoment H node454 := by
  calc
    injectiveMoment H raw1731 = injectiveMoment H raw1731step0 := by
      have heq : raw1731step0 = (fun i j => raw1731 (permutation11 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1731 permutation11 permutation11
    _ = injectiveMoment H node454 := by rfl

def raw1732 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![1, -1, 1, -1], ![0, 2, 0, -2], ![1, 0, 0, -1]]

def raw1732step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![-1, -1, 2, 0], ![-1, 1, 0, 0], ![4, -1, -2, -1]]

def raw1732step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, 0, 1, -2]]

theorem canonical1732 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1732 = injectiveMoment H node769 := by
  calc
    injectiveMoment H raw1732 = injectiveMoment H raw1732step0 := by
      have heq : raw1732step0 = raw1732.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1732).symm
    injectiveMoment H raw1732step0 = injectiveMoment H raw1732step1 := by
      have heq : raw1732step1 = (fun i j => raw1732step0 (permutation32 i) (permutation32 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1732step0 permutation32 permutation32
    _ = injectiveMoment H node769 := by rfl

def raw1733 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![1, -1, 2, -2], ![0, 1, 1, -2], ![1, 1, -2, 0]]

def raw1733step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 1, 1, -2], ![1, -1, 2, -2], ![1, 1, -2, 0]]

theorem canonical1733 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1733 = injectiveMoment H node465 := by
  calc
    injectiveMoment H raw1733 = injectiveMoment H raw1733step0 := by
      have heq : raw1733step0 = (fun i j => raw1733 (permutation11 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1733 permutation11 permutation9
    _ = injectiveMoment H node465 := by rfl

def raw1734 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![1, -1, 2, -2], ![0, 2, -2, 0], ![1, 0, 1, -2]]

def raw1734step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 2, -2, 0], ![1, -1, 2, -2], ![1, 0, 1, -2]]

theorem canonical1734 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1734 = injectiveMoment H node469 := by
  calc
    injectiveMoment H raw1734 = injectiveMoment H raw1734step0 := by
      have heq : raw1734step0 = (fun i j => raw1734 (permutation11 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1734 permutation11 permutation9
    _ = injectiveMoment H node469 := by rfl

def raw1735 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![1, -1, 2, -2], ![0, 2, -1, -1], ![1, 0, 0, -1]]

def raw1735step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![-1, -1, 2, 0], ![-1, 2, -1, 0], ![4, -2, -1, -1]]

def raw1735step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, -1, 2, -1], ![0, 2, -1, -1], ![1, 0, 1, -2]]

theorem canonical1735 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1735 = injectiveMoment H node896 := by
  calc
    injectiveMoment H raw1735 = injectiveMoment H raw1735step0 := by
      have heq : raw1735step0 = raw1735.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1735).symm
    injectiveMoment H raw1735step0 = injectiveMoment H raw1735step1 := by
      have heq : raw1735step1 = (fun i j => raw1735step0 (permutation32 i) (permutation32 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1735step0 permutation32 permutation32
    _ = injectiveMoment H node896 := by rfl

def raw1736 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![1, -1, 2, -2], ![0, 2, 0, -2], ![1, 0, -1, 0]]

def raw1736step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![-1, -1, 2, 0], ![-1, 2, 0, -1], ![4, -2, -2, 0]]

def raw1736step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, -1, 0, -1], ![1, 1, -2, 0], ![1, -2, 0, 1], ![-4, 2, 2, 0]]

def raw1736step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -2, 1, 1], ![0, 2, 2, -4], ![1, 0, -2, 1]]

theorem canonical1736 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw1736 = injectiveMoment H node1234 := by
  calc
    injectiveMoment H raw1736 = injectiveMoment H raw1736step0 := by
      have heq : raw1736step0 = raw1736.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1736).symm
    injectiveMoment H raw1736step0 = injectiveMoment H raw1736step1 := by
      have heq : raw1736step1 = -raw1736step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw1736step0).symm
    injectiveMoment H raw1736step1 = injectiveMoment H raw1736step2 := by
      have heq : raw1736step2 = (fun i j => raw1736step1 (permutation10 i) (permutation32 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1736step1 permutation10 permutation32
    _ = injectiveMoment H node1234 := by rfl

def raw1737 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![1, 0, 1, -2], ![0, 1, 1, -2], ![1, 0, -1, 0]]

def raw1737step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, 0, 1, -2]]

theorem canonical1737 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1737 = injectiveMoment H node786 := by
  calc
    injectiveMoment H raw1737 = injectiveMoment H raw1737step0 := by
      have heq : raw1737step0 = (fun i j => raw1737 (permutation13 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1737 permutation13 permutation15
    _ = injectiveMoment H node786 := by rfl

def raw1738 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![1, 0, 1, -2], ![0, 2, -1, -1], ![1, -1, 1, -1]]

def raw1738step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 2, -1], ![1, 1, -1, -1], ![1, 1, 0, -2]]

theorem canonical1738 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1738 = injectiveMoment H node454 := by
  calc
    injectiveMoment H raw1738 = injectiveMoment H raw1738step0 := by
      have heq : raw1738step0 = (fun i j => raw1738 (permutation12 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1738 permutation12 permutation11
    _ = injectiveMoment H node454 := by rfl

def raw1739 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![1, 0, 2, -3], ![0, 2, -2, 0], ![1, -1, 1, -1]]

def raw1739step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 2, -2, 0], ![1, -1, 1, -1], ![1, 0, 2, -3]]

theorem canonical1739 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1739 = injectiveMoment H node468 := by
  calc
    injectiveMoment H raw1739 = injectiveMoment H raw1739step0 := by
      have heq : raw1739step0 = (fun i j => raw1739 (permutation12 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1739 permutation12 permutation9
    _ = injectiveMoment H node468 := by rfl

def raw1740 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![1, 0, 2, -3], ![0, 2, 0, -2], ![1, -1, -1, 1]]

def raw1740step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 2, -2], ![1, -1, -1, 1], ![1, 2, 0, -3]]

theorem canonical1740 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1740 = injectiveMoment H node460 := by
  calc
    injectiveMoment H raw1740 = injectiveMoment H raw1740step0 := by
      have heq : raw1740step0 = (fun i j => raw1740 (permutation12 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1740 permutation12 permutation11
    _ = injectiveMoment H node460 := by rfl

def raw1741 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, -1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![2, 1, 1, -4]]

def raw1741step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 1, 0, -3], ![0, 1, 1, -2], ![0, 0, -1, 1], ![0, -1, 1, 0], ![-2, -1, -1, 4]]

def raw1741step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 0, 1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![2, 0, 1, -3]]

theorem canonical1741 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw1741 = injectiveMoment H node1544 := by
  calc
    injectiveMoment H raw1741 = injectiveMoment H raw1741step0 := by
      have heq : raw1741step0 = -raw1741 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw1741).symm
    injectiveMoment H raw1741step0 = injectiveMoment H raw1741step1 := by
      have heq : raw1741step1 = (fun i j => raw1741step0 (permutation144 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1741step0 permutation144 permutation11
    _ = injectiveMoment H node1544 := by rfl

def raw1742 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, -1, 2], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, 1, 0, -3]]

def raw1742step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, -2, 3], ![0, 1, 0, -1], ![0, 1, 2, -3], ![1, 0, 0, -1]]

theorem canonical1742 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1742 = injectiveMoment H node2574 := by
  calc
    injectiveMoment H raw1742 = injectiveMoment H raw1742step0 := by
      have heq : raw1742step0 = (fun i j => raw1742 (permutation60 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1742 permutation60 permutation23
    _ = injectiveMoment H node2574 := by rfl

def raw1743 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, -1, 2], ![0, 0, 1, -1], ![0, 1, 1, -2], ![2, 1, -1, -2]]

theorem canonical1743 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1743 = injectiveMoment H node1619 := by
  rfl

def raw1744 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, -1, 2], ![0, 0, 2, -2], ![0, 1, -1, 0], ![2, 1, 0, -3]]

theorem canonical1744 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1744 = injectiveMoment H node1620 := by
  rfl

def raw1745 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, -1, 2], ![0, 0, 2, -2], ![2, 2, -1, -3]]

def raw1745step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 1, 0, -3], ![0, 1, 1, -2], ![0, 0, -2, 2], ![-2, -2, 1, 3]]

def raw1745step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, -2, 2], ![0, 1, 1, -2], ![2, 1, 0, -3]]

theorem canonical1745 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw1745 = injectiveMoment H node405 := by
  calc
    injectiveMoment H raw1745 = injectiveMoment H raw1745step0 := by
      have heq : raw1745step0 = -raw1745 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw1745).symm
    injectiveMoment H raw1745step0 = injectiveMoment H raw1745step1 := by
      have heq : raw1745step1 = (fun i j => raw1745step0 (permutation32 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1745step0 permutation32 permutation9
    _ = injectiveMoment H node405 := by rfl

def raw1746 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, -1, 2], ![0, 1, -1, 0], ![0, 1, 2, -3], ![2, 0, 0, -2]]

theorem canonical1746 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1746 = injectiveMoment H node1621 := by
  rfl

def raw1747 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, -1, 2], ![0, 1, 1, -2], ![2, 1, 0, -3]]

def raw1747step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, -2, 3], ![0, 1, 2, -3], ![1, 1, 0, -2]]

theorem canonical1747 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1747 = injectiveMoment H node991 := by
  calc
    injectiveMoment H raw1747 = injectiveMoment H raw1747step0 := by
      have heq : raw1747step0 = (fun i j => raw1747 (permutation16 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1747 permutation16 permutation23
    _ = injectiveMoment H node991 := by rfl

def raw1748 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, -1, 2], ![0, 1, 2, -3], ![1, 0, 0, -1], ![1, 1, -1, -1]]

theorem canonical1748 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1748 = injectiveMoment H node1622 := by
  rfl

def raw1749 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, -1, 2], ![0, 1, 2, -3], ![2, 1, -1, -2]]

theorem canonical1749 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1749 = injectiveMoment H node470 := by
  rfl

def raw1750 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, -1, 2], ![0, 2, 1, -3], ![2, 0, 0, -2]]

def raw1750step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 1, 0, -3], ![0, 1, 1, -2], ![0, -2, -1, 3], ![-2, 0, 0, 2]]

def raw1750step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, -2, 2], ![0, 1, 2, -3], ![1, 1, 0, -2]]

theorem canonical1750 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw1750 = injectiveMoment H node791 := by
  calc
    injectiveMoment H raw1750 = injectiveMoment H raw1750step0 := by
      have heq : raw1750step0 = -raw1750 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw1750).symm
    injectiveMoment H raw1750step0 = injectiveMoment H raw1750step1 := by
      have heq : raw1750step1 = (fun i j => raw1750step0 (permutation25 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1750step0 permutation25 permutation23
    _ = injectiveMoment H node791 := by rfl

def raw1751 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, -1, 2], ![1, 1, 2, -4], ![1, 1, -1, -1]]

def raw1751step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 1, 0, -3], ![0, 1, 1, -2], ![-1, -1, -2, 4], ![-1, -1, 1, 1]]

def raw1751step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 1, 2, -3], ![1, -1, -1, 1], ![1, 1, 0, -2]]

theorem canonical1751 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw1751 = injectiveMoment H node466 := by
  calc
    injectiveMoment H raw1751 = injectiveMoment H raw1751step0 := by
      have heq : raw1751step0 = -raw1751 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw1751).symm
    injectiveMoment H raw1751step0 = injectiveMoment H raw1751step1 := by
      have heq : raw1751step1 = (fun i j => raw1751step0 (permutation22 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1751step0 permutation22 permutation23
    _ = injectiveMoment H node466 := by rfl

def raw1752 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 2, 1, -3], ![2, 0, 0, -2]]

def raw1752step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 1, 0, -3], ![0, 1, 0, -1], ![0, 0, 1, -1], ![0, -2, -1, 3], ![-2, 0, 0, 2]]

def raw1752step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, -2, 2], ![0, 1, 0, -1], ![0, 1, 2, -3], ![1, 0, 0, -1]]

theorem canonical1752 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw1752 = injectiveMoment H node2406 := by
  calc
    injectiveMoment H raw1752 = injectiveMoment H raw1752step0 := by
      have heq : raw1752step0 = -raw1752 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw1752).symm
    injectiveMoment H raw1752step0 = injectiveMoment H raw1752step1 := by
      have heq : raw1752step1 = (fun i j => raw1752step0 (permutation124 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1752step0 permutation124 permutation23
    _ = injectiveMoment H node2406 := by rfl

def raw1753 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 0, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![2, 1, 0, -3]]

def raw1753step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 1, 0, -3], ![0, 1, 0, -1], ![0, 0, -1, 1], ![0, -1, 1, 0], ![-2, -1, 0, 3]]

def raw1753step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, -1, 3], ![0, 0, 1, -1], ![0, 2, 1, -3], ![1, 0, -1, 0]]

theorem canonical1753 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw1753 = injectiveMoment H node2737 := by
  calc
    injectiveMoment H raw1753 = injectiveMoment H raw1753step0 := by
      have heq : raw1753step0 = -raw1753 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw1753).symm
    injectiveMoment H raw1753step0 = injectiveMoment H raw1753step1 := by
      have heq : raw1753step1 = (fun i j => raw1753step0 (permutation100 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1753step0 permutation100 permutation21
    _ = injectiveMoment H node2737 := by rfl

def raw1754 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 0, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, 0, 2, -4]]

def raw1754step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 1, 0, -3], ![0, 1, 0, -1], ![0, -1, 1, 0], ![0, -1, 1, 0], ![-2, 0, -2, 4]]

def raw1754step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, 0, 1, -3]]

theorem canonical1754 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw1754 = injectiveMoment H node1467 := by
  calc
    injectiveMoment H raw1754 = injectiveMoment H raw1754step0 := by
      have heq : raw1754step0 = -raw1754 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw1754).symm
    injectiveMoment H raw1754step0 = injectiveMoment H raw1754step1 := by
      have heq : raw1754step1 = (fun i j => raw1754step0 (permutation136 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1754step0 permutation136 permutation11
    _ = injectiveMoment H node1467 := by rfl

def raw1755 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 0, 1], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 1, 2, -4]]

def raw1755step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 1, 0, -3], ![0, 1, 0, -1], ![0, -1, 1, 0], ![-1, 0, 1, 0], ![-1, -1, -2, 4]]

def raw1755step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 2, 1, -3], ![1, -1, 0, 0], ![1, 0, -1, 0]]

theorem canonical1755 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw1755 = injectiveMoment H node1605 := by
  calc
    injectiveMoment H raw1755 = injectiveMoment H raw1755step0 := by
      have heq : raw1755step0 = -raw1755 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw1755).symm
    injectiveMoment H raw1755step0 = injectiveMoment H raw1755step1 := by
      have heq : raw1755step1 = (fun i j => raw1755step0 (permutation134 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1755step0 permutation134 permutation21
    _ = injectiveMoment H node1605 := by rfl

def raw1756 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 0, 1], ![0, 1, 1, -2], ![2, 1, -1, -2]]

def raw1756step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 1, 0, -3], ![0, 1, 0, -1], ![0, -1, -1, 2], ![-2, -1, 1, 2]]

def raw1756step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, 0, -1], ![0, 1, 2, -3], ![1, -1, -2, 2]]

theorem canonical1756 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw1756 = injectiveMoment H node1083 := by
  calc
    injectiveMoment H raw1756 = injectiveMoment H raw1756step0 := by
      have heq : raw1756step0 = -raw1756 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw1756).symm
    injectiveMoment H raw1756step0 = injectiveMoment H raw1756step1 := by
      have heq : raw1756step1 = (fun i j => raw1756step0 (permutation23 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1756step0 permutation23 permutation23
    _ = injectiveMoment H node1083 := by rfl

def raw1757 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 0, 1], ![0, 2, 1, -3], ![1, 0, -1, 0], ![1, 0, 0, -1]]

def raw1757step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 1, 0, -3], ![0, 1, 0, -1], ![0, -2, -1, 3], ![-1, 0, 1, 0], ![-1, 0, 0, 1]]

def raw1757step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 2, -3], ![1, 0, -1, 0]]

theorem canonical1757 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw1757 = injectiveMoment H node2418 := by
  calc
    injectiveMoment H raw1757 = injectiveMoment H raw1757step0 := by
      have heq : raw1757step0 = -raw1757 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw1757).symm
    injectiveMoment H raw1757step0 = injectiveMoment H raw1757step1 := by
      have heq : raw1757step1 = (fun i j => raw1757step0 (permutation100 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1757step0 permutation100 permutation23
    _ = injectiveMoment H node2418 := by rfl

def raw1758 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 0, 1], ![0, 2, 1, -3], ![2, 0, -1, -1]]

def raw1758step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 1, 0, -3], ![0, 1, 0, -1], ![0, -2, -1, 3], ![-2, 0, 1, 1]]

def raw1758step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 1, 0, -1], ![0, 1, 2, -3], ![1, 0, -2, 1]]

theorem canonical1758 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw1758 = injectiveMoment H node819 := by
  calc
    injectiveMoment H raw1758 = injectiveMoment H raw1758step0 := by
      have heq : raw1758step0 = -raw1758 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw1758).symm
    injectiveMoment H raw1758step0 = injectiveMoment H raw1758step1 := by
      have heq : raw1758step1 = (fun i j => raw1758step0 (permutation23 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1758step0 permutation23 permutation23
    _ = injectiveMoment H node819 := by rfl

def raw1759 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 0, 1], ![0, 2, 2, -4], ![1, 0, -1, 0], ![1, 0, -1, 0]]

def raw1759step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 1, 0, -3], ![0, 1, 0, -1], ![0, -2, -2, 4], ![-1, 0, 1, 0], ![-1, 0, 1, 0]]

def raw1759step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 0, 2, -3]]

theorem canonical1759 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw1759 = injectiveMoment H node1484 := by
  calc
    injectiveMoment H raw1759 = injectiveMoment H raw1759step0 := by
      have heq : raw1759step0 = -raw1759 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw1759).symm
    injectiveMoment H raw1759step0 = injectiveMoment H raw1759step1 := by
      have heq : raw1759step1 = (fun i j => raw1759step0 (permutation97 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1759step0 permutation97 permutation17
    _ = injectiveMoment H node1484 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
