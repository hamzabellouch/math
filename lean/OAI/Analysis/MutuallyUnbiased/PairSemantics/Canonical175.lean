import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes1
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes2
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes3
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes11
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes12
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes14
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes15
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes18
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes37

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw5600 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, 0, 1, -2]]

theorem canonical5600 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5600 = injectiveMoment H node769 := by
  rfl

def raw5601 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, 0, 0, -1]]

def raw5601step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, 0, 0, -1]]

theorem canonical5601 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5601 = injectiveMoment H node915 := by
  calc
    injectiveMoment H raw5601 = injectiveMoment H raw5601step0 := by
      have heq : raw5601step0 = (fun i j => raw5601 (permutation11 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5601 permutation11 permutation11
    _ = injectiveMoment H node915 := by rfl

def raw5602 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 1, -1], ![0, 2, 1, -3], ![1, 0, -1, 0]]

def raw5602step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, 0, 2, 0], ![-1, 1, 1, -1], ![4, -1, -3, 0]]

def raw5602step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, -1, 1, -1]]

theorem canonical5602 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5602 = injectiveMoment H node1177 := by
  calc
    injectiveMoment H raw5602 = injectiveMoment H raw5602step0 := by
      have heq : raw5602step0 = raw5602.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5602).symm
    injectiveMoment H raw5602step0 = injectiveMoment H raw5602step1 := by
      have heq : raw5602step1 = (fun i j => raw5602step0 (permutation29 i) (permutation20 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5602step0 permutation29 permutation20
    _ = injectiveMoment H node1177 := by rfl

def raw5603 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 1, -1], ![1, 2, 0, -3]]

def raw5603step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![-1, 1, 0], ![4, -1, -3]]

def raw5603step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1]]

theorem canonical5603 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5603 = injectiveMoment H node254 := by
  calc
    injectiveMoment H raw5603 = injectiveMoment H raw5603step0 := by
      have heq : raw5603step0 = raw5603.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5603).symm
    injectiveMoment H raw5603step0 = injectiveMoment H raw5603step1 := by
      have heq : raw5603step1 = (fun i j => raw5603step0 (permutation27 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5603step0 permutation27 permutation6
    _ = injectiveMoment H node254 := by rfl

def raw5604 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 2, -2], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 1, -2, 0]]

def raw5604step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 1, -1], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, 1, -2, 0]]

theorem canonical5604 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5604 = injectiveMoment H node2396 := by
  calc
    injectiveMoment H raw5604 = injectiveMoment H raw5604step0 := by
      have heq : raw5604step0 = (fun i j => raw5604 (permutation39 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5604 permutation39 permutation9
    _ = injectiveMoment H node2396 := by rfl

def raw5605 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 2, -2], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, 0, 0, -1]]

def raw5605step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 1, -1], ![0, 0, 2, -2], ![0, 2, -2, 0], ![1, 0, 0, -1]]

theorem canonical5605 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5605 = injectiveMoment H node2397 := by
  calc
    injectiveMoment H raw5605 = injectiveMoment H raw5605step0 := by
      have heq : raw5605step0 = (fun i j => raw5605 (permutation39 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5605 permutation39 permutation9
    _ = injectiveMoment H node2397 := by rfl

def raw5606 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 2, -2], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, 0, -1, 0]]

def raw5606step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 1, -1], ![0, 0, 2, -2], ![0, 2, -1, -1], ![1, 0, -1, 0]]

theorem canonical5606 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5606 = injectiveMoment H node2398 := by
  calc
    injectiveMoment H raw5606 = injectiveMoment H raw5606step0 := by
      have heq : raw5606step0 = (fun i j => raw5606 (permutation39 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5606 permutation39 permutation9
    _ = injectiveMoment H node2398 := by rfl

def raw5607 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 2, -2], ![0, 0, 1, -1], ![1, 2, -2, -1]]

def raw5607step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 1, -1], ![0, 0, 2, -2], ![1, 2, -2, -1]]

theorem canonical5607 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5607 = injectiveMoment H node765 := by
  calc
    injectiveMoment H raw5607 = injectiveMoment H raw5607step0 := by
      have heq : raw5607step0 = (fun i j => raw5607 (permutation11 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5607 permutation11 permutation9
    _ = injectiveMoment H node765 := by rfl

def raw5608 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, 0, -1]]

theorem canonical5608 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5608 = injectiveMoment H node2402 := by
  rfl

def raw5609 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, 1, 0, -2]]

theorem canonical5609 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5609 = injectiveMoment H node771 := by
  rfl

def raw5610 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, 1, -1, -1]]

def raw5610step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, 0, 1, 1], ![-1, 2, 0, -1], ![4, -2, -1, -1]]

def raw5610step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, 0, 1, -2]]

theorem canonical5610 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5610 = injectiveMoment H node769 := by
  calc
    injectiveMoment H raw5610 = injectiveMoment H raw5610step0 := by
      have heq : raw5610step0 = raw5610.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5610).symm
    injectiveMoment H raw5610step0 = injectiveMoment H raw5610step1 := by
      have heq : raw5610step1 = (fun i j => raw5610step0 (permutation28 i) (permutation24 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5610step0 permutation28 permutation24
    _ = injectiveMoment H node769 := by rfl

def raw5611 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 2, -2], ![0, 1, 1, -2], ![1, 1, -2, 0]]

theorem canonical5611 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5611 = injectiveMoment H node772 := by
  rfl

def raw5612 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 2, -2], ![0, 2, -2, 0], ![1, 0, 1, -2]]

theorem canonical5612 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5612 = injectiveMoment H node773 := by
  rfl

def raw5613 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 2, -2], ![0, 2, -1, -1], ![1, 0, 0, -1]]

theorem canonical5613 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5613 = injectiveMoment H node774 := by
  rfl

def raw5614 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 2, -2], ![0, 2, 0, -2], ![1, 0, -1, 0]]

theorem canonical5614 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5614 = injectiveMoment H node775 := by
  rfl

def raw5615 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 2, -2], ![1, 2, -1, -2]]

def raw5615step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![-1, 2, -1], ![4, -2, -2]]

def raw5615step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 2, -2], ![2, -1, -1]]

theorem canonical5615 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5615 = injectiveMoment H node146 := by
  calc
    injectiveMoment H raw5615 = injectiveMoment H raw5615step0 := by
      have heq : raw5615step0 = raw5615.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5615).symm
    injectiveMoment H raw5615step0 = injectiveMoment H raw5615step1 := by
      have heq : raw5615step1 = (fun i j => raw5615step0 (permutation27 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5615step0 permutation27 permutation6
    _ = injectiveMoment H node146 := by rfl

def raw5616 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 3, -3], ![0, 1, 0, -1], ![1, 1, -2, 0]]

theorem canonical5616 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5616 = injectiveMoment H node780 := by
  rfl

def raw5617 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 3, -3], ![0, 2, -2, 0], ![1, 0, 0, -1]]

theorem canonical5617 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5617 = injectiveMoment H node781 := by
  rfl

def raw5618 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 3, -3], ![0, 2, -1, -1], ![1, 0, -1, 0]]

theorem canonical5618 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5618 = injectiveMoment H node782 := by
  rfl

def raw5619 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 3, -3], ![1, 2, -2, -1]]

def raw5619step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![-1, 3, -2], ![4, -3, -1]]

def raw5619step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![3, -2, -1]]

theorem canonical5619 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5619 = injectiveMoment H node81 := by
  calc
    injectiveMoment H raw5619 = injectiveMoment H raw5619step0 := by
      have heq : raw5619step0 = raw5619.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5619).symm
    injectiveMoment H raw5619step0 = injectiveMoment H raw5619step1 := by
      have heq : raw5619step1 = (fun i j => raw5619step0 (permutation27 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5619step0 permutation27 permutation6
    _ = injectiveMoment H node81 := by rfl

def raw5620 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 3, -4]]

def raw5620step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, 1, 1, 0], ![-1, -1, -1, 3], ![4, 0, 0, -4]]

def raw5620step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, -1, 1], ![0, 0, 4, -4], ![1, 1, -2, 0]]

theorem canonical5620 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5620 = injectiveMoment H node961 := by
  calc
    injectiveMoment H raw5620 = injectiveMoment H raw5620step0 := by
      have heq : raw5620step0 = raw5620.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5620).symm
    injectiveMoment H raw5620step0 = injectiveMoment H raw5620step1 := by
      have heq : raw5620step1 = (fun i j => raw5620step0 (permutation22 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5620step0 permutation22 permutation17
    _ = injectiveMoment H node961 := by rfl

def raw5621 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, 2, -3]]

def raw5621step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, 1, 1, 0], ![-1, -1, 0, 2], ![4, 0, -1, -3]]

def raw5621step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 0, -1], ![2, -1, -1, 0], ![1, 1, 0, -2], ![-4, 0, 1, 3]]

def raw5621step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 1, -2, 1], ![1, 0, 3, -4]]

theorem canonical5621 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw5621 = injectiveMoment H node1042 := by
  calc
    injectiveMoment H raw5621 = injectiveMoment H raw5621step0 := by
      have heq : raw5621step0 = raw5621.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5621).symm
    injectiveMoment H raw5621step0 = injectiveMoment H raw5621step1 := by
      have heq : raw5621step1 = -raw5621step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw5621step0).symm
    injectiveMoment H raw5621step1 = injectiveMoment H raw5621step2 := by
      have heq : raw5621step2 = (fun i j => raw5621step1 (permutation15 i) (permutation24 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5621step1 permutation15 permutation24
    _ = injectiveMoment H node1042 := by rfl

def raw5622 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, 0, 1, -2]]

theorem canonical5622 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5622 = injectiveMoment H node786 := by
  rfl

def raw5623 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, 0, 0, -1]]

def raw5623step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, 1, 1, 0], ![-1, -1, 2, 0], ![4, 0, -3, -1]]

def raw5623step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, -1, 2, -1], ![0, 1, 1, -2], ![1, 0, 0, -1]]

theorem canonical5623 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5623 = injectiveMoment H node1171 := by
  calc
    injectiveMoment H raw5623 = injectiveMoment H raw5623step0 := by
      have heq : raw5623step0 = raw5623.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5623).symm
    injectiveMoment H raw5623step0 = injectiveMoment H raw5623step1 := by
      have heq : raw5623step1 = (fun i j => raw5623step0 (permutation32 i) (permutation30 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5623step0 permutation32 permutation30
    _ = injectiveMoment H node1171 := by rfl

def raw5624 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, 0, -1, 0]]

def raw5624step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, 1, 1, 0], ![-1, -1, 3, -1], ![4, 0, -4, 0]]

def raw5624step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 4, -4], ![0, 1, -2, 1], ![1, 0, -1, 0]]

theorem canonical5624 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5624 = injectiveMoment H node981 := by
  calc
    injectiveMoment H raw5624 = injectiveMoment H raw5624step0 := by
      have heq : raw5624step0 = raw5624.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5624).symm
    injectiveMoment H raw5624step0 = injectiveMoment H raw5624step1 := by
      have heq : raw5624step1 = (fun i j => raw5624step0 (permutation26 i) (permutation29 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5624step0 permutation26 permutation29
    _ = injectiveMoment H node981 := by rfl

def raw5625 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, 1, -2]]

def raw5625step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, 1, 0, -2]]

theorem canonical5625 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5625 = injectiveMoment H node906 := by
  calc
    injectiveMoment H raw5625 = injectiveMoment H raw5625step0 := by
      have heq : raw5625step0 = (fun i j => raw5625 (permutation9 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5625 permutation9 permutation11
    _ = injectiveMoment H node906 := by rfl

def raw5626 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 1, 0, -1], ![0, 1, 1, -2], ![1, 0, 0, -1]]

def raw5626step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, 1, -2]]

theorem canonical5626 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5626 = injectiveMoment H node910 := by
  calc
    injectiveMoment H raw5626 = injectiveMoment H raw5626step0 := by
      have heq : raw5626step0 = (fun i j => raw5626 (permutation10 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5626 permutation10 permutation21
    _ = injectiveMoment H node910 := by rfl

def raw5627 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 1, 0, -1], ![0, 1, 2, -3], ![1, 0, -1, 0]]

def raw5627step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, 1, 1, 0], ![-1, 0, 2, -1], ![4, -1, -3, 0]]

def raw5627step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, -1, 2, -1], ![0, 1, 0, -1], ![1, 0, 1, -2]]

theorem canonical5627 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5627 = injectiveMoment H node1170 := by
  calc
    injectiveMoment H raw5627 = injectiveMoment H raw5627step0 := by
      have heq : raw5627step0 = raw5627.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5627).symm
    injectiveMoment H raw5627step0 = injectiveMoment H raw5627step1 := by
      have heq : raw5627step1 = (fun i j => raw5627step0 (permutation31 i) (permutation20 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5627step0 permutation31 permutation20
    _ = injectiveMoment H node1170 := by rfl

def raw5628 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 1, 0, -1], ![1, 1, 1, -3]]

def raw5628step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![-1, 0, 1], ![4, -1, -3]]

def raw5628step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2]]

theorem canonical5628 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5628 = injectiveMoment H node253 := by
  calc
    injectiveMoment H raw5628 = injectiveMoment H raw5628step0 := by
      have heq : raw5628step0 = raw5628.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5628).symm
    injectiveMoment H raw5628step0 = injectiveMoment H raw5628step1 := by
      have heq : raw5628step1 = (fun i j => raw5628step0 (permutation28 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5628step0 permutation28 permutation6
    _ = injectiveMoment H node253 := by rfl

def raw5629 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 1, 1, -2], ![0, 1, 0, -1], ![1, 0, 0, -1]]

def raw5629step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, 1, -2]]

theorem canonical5629 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5629 = injectiveMoment H node910 := by
  calc
    injectiveMoment H raw5629 = injectiveMoment H raw5629step0 := by
      have heq : raw5629step0 = (fun i j => raw5629 (permutation12 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5629 permutation12 permutation21
    _ = injectiveMoment H node910 := by rfl

def raw5630 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 1, 1, -2], ![0, 1, 1, -2], ![1, 0, -1, 0]]

theorem canonical5630 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5630 = injectiveMoment H node787 := by
  rfl

def raw5631 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 1, 1, -2], ![1, 1, 0, -2]]

def raw5631step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![-1, 1, 0], ![4, -2, -2]]

def raw5631step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]

theorem canonical5631 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5631 = injectiveMoment H node150 := by
  calc
    injectiveMoment H raw5631 = injectiveMoment H raw5631step0 := by
      have heq : raw5631step0 = raw5631.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5631).symm
    injectiveMoment H raw5631step0 = injectiveMoment H raw5631step1 := by
      have heq : raw5631step1 = (fun i j => raw5631step0 (permutation28 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5631step0 permutation28 permutation6
    _ = injectiveMoment H node150 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
