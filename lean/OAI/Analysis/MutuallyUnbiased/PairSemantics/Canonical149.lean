import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes3
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes12
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes13
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes14
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes20
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes23
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes25
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes27
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes28
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes32
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes34
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes35

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw4768 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -1, 1], ![0, 1, -2, 1], ![2, -2, 3, -3]]

def raw4768step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, 0, 1, -2], ![0, -1, -2, 3], ![1, 1, 1, -3]]

def raw4768step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, -2, 2], ![0, 1, 1, -2], ![1, 1, 1, -3]]

theorem canonical4768 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4768 = injectiveMoment H node790 := by
  calc
    injectiveMoment H raw4768 = injectiveMoment H raw4768step0 := by
      have heq : raw4768step0 = raw4768.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4768).symm
    injectiveMoment H raw4768step0 = injectiveMoment H raw4768step1 := by
      have heq : raw4768step1 = (fun i j => raw4768step0 (permutation21 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4768step0 permutation21 permutation17
    _ = injectiveMoment H node790 := by rfl

def raw4769 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -2, -1, 2], ![1, 0, 3, -4]]

def raw4769step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -1, 1], ![0, 1, 3, -4], ![1, -2, 0, 1], ![1, 0, -1, 0]]

theorem canonical4769 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4769 = injectiveMoment H node2230 := by
  calc
    injectiveMoment H raw4769 = injectiveMoment H raw4769step0 := by
      have heq : raw4769step0 = (fun i j => raw4769 (permutation114 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4769 permutation114 permutation15
    _ = injectiveMoment H node2230 := by rfl

def raw4770 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -2, 0, 1], ![1, 0, 2, -3]]

def raw4770step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, -1, 0, -1], ![0, 0, 1, -1], ![0, -1, 1, 0], ![-1, 2, 0, -1], ![-1, 0, -2, 3]]

def raw4770step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![0, 2, -1, -1], ![1, 0, -1, 0], ![1, 0, 0, -1]]

theorem canonical4770 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4770 = injectiveMoment H node1655 := by
  calc
    injectiveMoment H raw4770 = injectiveMoment H raw4770step0 := by
      have heq : raw4770step0 = -raw4770 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4770).symm
    injectiveMoment H raw4770step0 = injectiveMoment H raw4770step1 := by
      have heq : raw4770step1 = (fun i j => raw4770step0 (permutation146 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4770step0 permutation146 permutation21
    _ = injectiveMoment H node1655 := by rfl

def raw4771 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -2, 3, -2], ![1, 0, -1, 0]]

def raw4771step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 1, -2, 0]]

theorem canonical4771 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4771 = injectiveMoment H node1508 := by
  calc
    injectiveMoment H raw4771 = injectiveMoment H raw4771step0 := by
      have heq : raw4771step0 = (fun i j => raw4771 (permutation125 i) (permutation19 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4771 permutation125 permutation19
    _ = injectiveMoment H node1508 := by rfl

def raw4772 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, -1, 3, -3]]

theorem canonical4772 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4772 = injectiveMoment H node2285 := by
  rfl

def raw4773 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, -1, 2, -2]]

def raw4773step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 1, 0], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 1, -2, 0]]

theorem canonical4773 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4773 = injectiveMoment H node1751 := by
  calc
    injectiveMoment H raw4773 = injectiveMoment H raw4773step0 := by
      have heq : raw4773step0 = (fun i j => raw4773 (permutation150 i) (permutation29 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4773 permutation150 permutation29
    _ = injectiveMoment H node1751 := by rfl

def raw4774 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 3, -3], ![1, -1, -1, 1]]

def raw4774step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, -1, 3, -3]]

theorem canonical4774 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4774 = injectiveMoment H node2285 := by
  calc
    injectiveMoment H raw4774 = injectiveMoment H raw4774step0 := by
      have heq : raw4774step0 = (fun i j => raw4774 (permutation34 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4774 permutation34 permutation9
    _ = injectiveMoment H node2285 := by rfl

def raw4775 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![2, -2, 2, -2]]

def raw4775step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, 0, 1, -2], ![0, -1, -1, 2], ![1, 1, 0, -2]]

def raw4775step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 1, 1, -2], ![1, 0, 1, -2]]

theorem canonical4775 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4775 = injectiveMoment H node1033 := by
  calc
    injectiveMoment H raw4775 = injectiveMoment H raw4775step0 := by
      have heq : raw4775step0 = raw4775.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4775).symm
    injectiveMoment H raw4775step0 = injectiveMoment H raw4775step1 := by
      have heq : raw4775step1 = (fun i j => raw4775step0 (permutation21 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4775step0 permutation21 permutation17
    _ = injectiveMoment H node1033 := by rfl

def raw4776 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -1, 1], ![0, 1, 2, -3], ![1, -1, -1, 1], ![1, -1, 0, 0]]

def raw4776step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, -1, 0, -1], ![0, 0, 1, -1], ![0, -1, -2, 3], ![-1, 1, 1, -1], ![-1, 1, 0, 0]]

def raw4776step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 1, -1, -1]]

theorem canonical4776 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4776 = injectiveMoment H node1649 := by
  calc
    injectiveMoment H raw4776 = injectiveMoment H raw4776step0 := by
      have heq : raw4776step0 = -raw4776 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4776).symm
    injectiveMoment H raw4776step0 = injectiveMoment H raw4776step1 := by
      have heq : raw4776step1 = (fun i j => raw4776step0 (permutation84 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4776step0 permutation84 permutation23
    _ = injectiveMoment H node1649 := by rfl

def raw4777 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -1, 1], ![0, 1, 2, -3], ![2, -2, -1, 1]]

def raw4777step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, 0, 1, -2], ![0, -1, 2, -1], ![1, 1, -3, 1]]

def raw4777step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![-1, 0, -1, 2], ![0, 1, -2, 1], ![-1, -1, 3, -1]]

def raw4777step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 2, -1], ![0, 2, -2, 0], ![1, 0, 1, -2]]

theorem canonical4777 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4777 = injectiveMoment H node944 := by
  calc
    injectiveMoment H raw4777 = injectiveMoment H raw4777step0 := by
      have heq : raw4777step0 = raw4777.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4777).symm
    injectiveMoment H raw4777step0 = injectiveMoment H raw4777step1 := by
      have heq : raw4777step1 = -raw4777step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4777step0).symm
    injectiveMoment H raw4777step1 = injectiveMoment H raw4777step2 := by
      have heq : raw4777step2 = (fun i j => raw4777step1 (permutation29 i) (permutation16 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4777step1 permutation29 permutation16
    _ = injectiveMoment H node944 := by rfl

def raw4778 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -1, 1], ![0, 1, 3, -4], ![1, -2, -1, 2], ![1, 0, -1, 0]]

def raw4778step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -2, 0, 1], ![1, 0, 3, -4]]

theorem canonical4778 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4778 = injectiveMoment H node2226 := by
  calc
    injectiveMoment H raw4778 = injectiveMoment H raw4778step0 := by
      have heq : raw4778step0 = (fun i j => raw4778 (permutation114 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4778 permutation114 permutation15
    _ = injectiveMoment H node2226 := by rfl

def raw4779 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -1, 1], ![0, 1, 3, -4], ![1, -1, -2, 2], ![1, -1, 0, 0]]

theorem canonical4779 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4779 = injectiveMoment H node2286 := by
  rfl

def raw4780 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -1, 1], ![0, 1, 3, -4], ![1, -1, -1, 1], ![1, -1, -1, 1]]

theorem canonical4780 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4780 = injectiveMoment H node2287 := by
  rfl

def raw4781 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -1, 1], ![0, 1, 3, -4], ![2, -2, -2, 2]]

def raw4781step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, 0, 1, -2], ![0, -1, 3, -2], ![1, 1, -4, 2]]

def raw4781step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![-1, 0, -1, 2], ![0, 1, -3, 2], ![-1, -1, 4, -2]]

def raw4781step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, -1, 2, -1], ![0, 2, -2, 0], ![1, 0, 2, -3]]

theorem canonical4781 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4781 = injectiveMoment H node895 := by
  calc
    injectiveMoment H raw4781 = injectiveMoment H raw4781step0 := by
      have heq : raw4781step0 = raw4781.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4781).symm
    injectiveMoment H raw4781step0 = injectiveMoment H raw4781step1 := by
      have heq : raw4781step1 = -raw4781step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4781step0).symm
    injectiveMoment H raw4781step1 = injectiveMoment H raw4781step2 := by
      have heq : raw4781step2 = (fun i j => raw4781step1 (permutation29 i) (permutation16 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4781step1 permutation29 permutation16
    _ = injectiveMoment H node895 := by rfl

def raw4782 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -1, 1], ![1, -2, -1, 2], ![1, 1, 2, -4]]

def raw4782step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 0, -2, 1], ![0, -1, -1, 2], ![1, 1, 2, -4]]

def raw4782step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, 0, 2, -1], ![0, 1, 1, -2], ![-1, -1, -2, 4]]

def raw4782step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, -1, 2, -1], ![0, 2, -1, -1], ![1, 0, 1, -2]]

theorem canonical4782 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4782 = injectiveMoment H node896 := by
  calc
    injectiveMoment H raw4782 = injectiveMoment H raw4782step0 := by
      have heq : raw4782step0 = raw4782.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4782).symm
    injectiveMoment H raw4782step0 = injectiveMoment H raw4782step1 := by
      have heq : raw4782step1 = -raw4782step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4782step0).symm
    injectiveMoment H raw4782step1 = injectiveMoment H raw4782step2 := by
      have heq : raw4782step2 = (fun i j => raw4782step1 (permutation29 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4782step1 permutation29 permutation15
    _ = injectiveMoment H node896 := by rfl

def raw4783 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -1, 1], ![1, -2, 3, -2], ![1, 1, -2, 0]]

def raw4783step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 0, -2, 1], ![0, -1, 3, -2], ![1, 1, -2, 0]]

def raw4783step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 1, -2, 1], ![0, 1, 1, -2], ![1, 0, 1, -2]]

theorem canonical4783 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4783 = injectiveMoment H node815 := by
  calc
    injectiveMoment H raw4783 = injectiveMoment H raw4783step0 := by
      have heq : raw4783step0 = raw4783.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4783).symm
    injectiveMoment H raw4783step0 = injectiveMoment H raw4783step1 := by
      have heq : raw4783step1 = (fun i j => raw4783step0 (permutation21 i) (permutation19 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4783step0 permutation21 permutation19
    _ = injectiveMoment H node815 := by rfl

def raw4784 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -1, 1], ![1, -1, -2, 2], ![1, 0, 3, -4]]

def raw4784step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 0, -1, 0], ![0, -1, -2, 3], ![1, 1, 2, -4]]

def raw4784step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, 0, 1, 0], ![0, 1, 2, -3], ![-1, -1, -2, 4]]

def raw4784step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, -1, 1, 0], ![0, 2, -1, -1], ![1, 0, 2, -3]]

theorem canonical4784 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4784 = injectiveMoment H node892 := by
  calc
    injectiveMoment H raw4784 = injectiveMoment H raw4784step0 := by
      have heq : raw4784step0 = raw4784.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4784).symm
    injectiveMoment H raw4784step0 = injectiveMoment H raw4784step1 := by
      have heq : raw4784step1 = -raw4784step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4784step0).symm
    injectiveMoment H raw4784step1 = injectiveMoment H raw4784step2 := by
      have heq : raw4784step2 = (fun i j => raw4784step1 (permutation29 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4784step1 permutation29 permutation15
    _ = injectiveMoment H node892 := by rfl

def raw4785 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -1, 1], ![1, -1, 3, -3], ![1, 0, -2, 1]]

def raw4785step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 0, -1, 0], ![0, -1, 3, -2], ![1, 1, -3, 1]]

def raw4785step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 1, -1], ![0, 1, -2, 1], ![1, 1, 1, -3]]

theorem canonical4785 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4785 = injectiveMoment H node800 := by
  calc
    injectiveMoment H raw4785 = injectiveMoment H raw4785step0 := by
      have heq : raw4785step0 = raw4785.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4785).symm
    injectiveMoment H raw4785step0 = injectiveMoment H raw4785step1 := by
      have heq : raw4785step1 = (fun i j => raw4785step0 (permutation23 i) (permutation19 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4785step0 permutation23 permutation19
    _ = injectiveMoment H node800 := by rfl

def raw4786 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, 0, 0], ![0, 1, -2, 1], ![2, -2, 2, -2]]

def raw4786step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, 0, 1, -2], ![0, 0, -2, 2], ![1, 0, 1, -2]]

def raw4786step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![1, 1, -2], ![0, -2, 2], ![1, 1, -2]]

def raw4786step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![1, 1, -2], ![1, 1, -2]]

theorem canonical4786 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4786 = injectiveMoment H node202 := by
  calc
    injectiveMoment H raw4786 = injectiveMoment H raw4786step0 := by
      have heq : raw4786step0 = raw4786.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4786).symm
    injectiveMoment H raw4786step0 = injectiveMoment H raw4786step1 := by
      have hz : ∀ i, raw4786step0 i (permutation15 0) = 0 := by decide +kernel
      have heq : raw4786step1 = (fun i j => raw4786step0 i (permutation15 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw4786step0 permutation15 hz
    injectiveMoment H raw4786step1 = injectiveMoment H raw4786step2 := by
      have heq : raw4786step2 = (fun i j => raw4786step1 (permutation11 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4786step1 permutation11 permutation3
    _ = injectiveMoment H node202 := by rfl

def raw4787 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, 0, 0], ![0, 1, 2, -3], ![2, -2, -2, 2]]

def raw4787step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, 0, 1, -2], ![0, 0, 2, -2], ![1, 0, -3, 2]]

def raw4787step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![1, 1, -2], ![0, 2, -2], ![1, -3, 2]]

def raw4787step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![1, -3, 2], ![1, 1, -2]]

theorem canonical4787 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4787 = injectiveMoment H node212 := by
  calc
    injectiveMoment H raw4787 = injectiveMoment H raw4787step0 := by
      have heq : raw4787step0 = raw4787.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4787).symm
    injectiveMoment H raw4787step0 = injectiveMoment H raw4787step1 := by
      have hz : ∀ i, raw4787step0 i (permutation15 0) = 0 := by decide +kernel
      have heq : raw4787step1 = (fun i j => raw4787step0 i (permutation15 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw4787step0 permutation15 hz
    injectiveMoment H raw4787step1 = injectiveMoment H raw4787step2 := by
      have heq : raw4787step2 = (fun i j => raw4787step1 (permutation12 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4787step1 permutation12 permutation3
    _ = injectiveMoment H node212 := by rfl

def raw4788 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![2, -2, -1, 1]]

def raw4788step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, -1, 0, -1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, -1, 1, 0], ![-2, 2, 1, -1]]

def raw4788step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, -1, 0, -1]]

theorem canonical4788 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4788 = injectiveMoment H node1785 := by
  calc
    injectiveMoment H raw4788 = injectiveMoment H raw4788step0 := by
      have heq : raw4788step0 = -raw4788 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4788).symm
    injectiveMoment H raw4788step0 = injectiveMoment H raw4788step1 := by
      have heq : raw4788step1 = (fun i j => raw4788step0 (permutation148 i) (permutation14 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4788step0 permutation148 permutation14
    _ = injectiveMoment H node1785 := by rfl

def raw4789 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, -2, -2, 2]]

def raw4789step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 0, 0, -1]]

theorem canonical4789 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4789 = injectiveMoment H node1523 := by
  calc
    injectiveMoment H raw4789 = injectiveMoment H raw4789step0 := by
      have heq : raw4789step0 = (fun i j => raw4789 (permutation132 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4789 permutation132 permutation23
    _ = injectiveMoment H node1523 := by rfl

def raw4790 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 1, -2], ![2, -2, -3, 3]]

theorem canonical4790 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4790 = injectiveMoment H node2288 := by
  rfl

def raw4791 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, 1, -1], ![0, 0, 2, -2], ![0, 1, -1, 0], ![2, -2, -2, 2]]

theorem canonical4791 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4791 = injectiveMoment H node2289 := by
  rfl

def raw4792 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, 1, -1], ![0, 0, 2, -2], ![0, 1, 0, -1], ![2, -2, -3, 3]]

theorem canonical4792 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4792 = injectiveMoment H node2290 := by
  rfl

def raw4793 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, 1, -1], ![0, 1, -3, 2], ![2, -2, 2, -2]]

def raw4793step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, 0, 1, -2], ![0, 1, -3, 2], ![1, -1, 2, -2]]

def raw4793step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![-1, 0, -1, 2], ![0, -1, 3, -2], ![-1, 1, -2, 2]]

def raw4793step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 3, -2], ![0, -1, -1, 2], ![0, 2, 0, -2], ![1, -1, -2, 2]]

theorem canonical4793 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4793 = injectiveMoment H node1319 := by
  calc
    injectiveMoment H raw4793 = injectiveMoment H raw4793step0 := by
      have heq : raw4793step0 = raw4793.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4793).symm
    injectiveMoment H raw4793step0 = injectiveMoment H raw4793step1 := by
      have heq : raw4793step1 = -raw4793step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4793step0).symm
    injectiveMoment H raw4793step1 = injectiveMoment H raw4793step2 := by
      have heq : raw4793step2 = (fun i j => raw4793step1 (permutation23 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4793step1 permutation23 permutation15
    _ = injectiveMoment H node1319 := by rfl

def raw4794 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, 1, -1], ![0, 1, -2, 1], ![1, -1, 0, 0], ![1, -1, 1, -1]]

def raw4794step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -2, 1, 1], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 1, -1, -1]]

theorem canonical4794 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4794 = injectiveMoment H node2057 := by
  calc
    injectiveMoment H raw4794 = injectiveMoment H raw4794step0 := by
      have heq : raw4794step0 = (fun i j => raw4794 (permutation39 i) (permutation12 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4794 permutation39 permutation12
    _ = injectiveMoment H node2057 := by rfl

def raw4795 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, 1, -1], ![0, 1, -2, 1], ![2, -2, 1, -1]]

def raw4795step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, 0, 1, -2], ![0, 1, -2, 1], ![1, -1, 1, -1]]

def raw4795step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![-1, 0, -1, 2], ![0, -1, 2, -1], ![-1, 1, -1, 1]]

def raw4795step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -1, -1, 2], ![0, 2, 0, -2], ![1, -1, -1, 1]]

theorem canonical4795 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4795 = injectiveMoment H node1309 := by
  calc
    injectiveMoment H raw4795 = injectiveMoment H raw4795step0 := by
      have heq : raw4795step0 = raw4795.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4795).symm
    injectiveMoment H raw4795step0 = injectiveMoment H raw4795step1 := by
      have heq : raw4795step1 = -raw4795step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4795step0).symm
    injectiveMoment H raw4795step1 = injectiveMoment H raw4795step2 := by
      have heq : raw4795step2 = (fun i j => raw4795step1 (permutation23 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4795step1 permutation23 permutation15
    _ = injectiveMoment H node1309 := by rfl

def raw4796 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, -2, 2], ![1, -1, 2, -2]]

theorem canonical4796 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4796 = injectiveMoment H node2291 := by
  rfl

def raw4797 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, -1, 1, -1]]

def raw4797step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 0, 1], ![0, 1, -1, 0], ![1, -1, 1, -1], ![1, 1, -1, -1]]

theorem canonical4797 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4797 = injectiveMoment H node2071 := by
  calc
    injectiveMoment H raw4797 = injectiveMoment H raw4797step0 := by
      have heq : raw4797step0 = (fun i j => raw4797 (permutation39 i) (permutation12 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4797 permutation39 permutation12
    _ = injectiveMoment H node2071 := by rfl

def raw4798 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, -2, 2], ![1, -1, 1, -1]]

def raw4798step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 0, 0, -1]]

theorem canonical4798 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4798 = injectiveMoment H node1819 := by
  calc
    injectiveMoment H raw4798 = injectiveMoment H raw4798step0 := by
      have heq : raw4798step0 = (fun i j => raw4798 (permutation107 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4798 permutation107 permutation23
    _ = injectiveMoment H node1819 := by rfl

def raw4799 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, 1, -1], ![0, 1, 1, -2], ![2, -2, -2, 2]]

def raw4799step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, 0, 1, -2], ![0, 1, 1, -2], ![1, -1, -2, 2]]

def raw4799step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -2, 2], ![0, 1, 1, -2], ![1, 1, 0, -2]]

theorem canonical4799 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4799 = injectiveMoment H node828 := by
  calc
    injectiveMoment H raw4799 = injectiveMoment H raw4799step0 := by
      have heq : raw4799step0 = raw4799.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4799).symm
    injectiveMoment H raw4799step0 = injectiveMoment H raw4799step1 := by
      have heq : raw4799step1 = (fun i j => raw4799step0 (permutation27 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4799step0 permutation27 permutation17
    _ = injectiveMoment H node828 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
