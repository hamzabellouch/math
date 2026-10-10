import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes7
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes9
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes10
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes15
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes19
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes21
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes24
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes25
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes30
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes31
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes35
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes40
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes42

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw4640 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -2, -1, 3], ![0, 1, 3, -4], ![1, 0, -1, 0], ![1, 0, -1, 0]]

def raw4640step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -2, 0, 1], ![1, 0, 3, -4]]

theorem canonical4640 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4640 = injectiveMoment H node1974 := by
  calc
    injectiveMoment H raw4640 = injectiveMoment H raw4640step0 := by
      have heq : raw4640step0 = (fun i j => raw4640 (permutation72 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4640 permutation72 permutation15
    _ = injectiveMoment H node1974 := by rfl

def raw4641 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -2, 0, 2], ![0, 0, -1, 1], ![1, 0, -1, 0], ![1, 1, 2, -4]]

def raw4641step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, -1, 0, -1], ![0, 2, 0, -2], ![0, 0, 1, -1], ![-1, 0, 1, 0], ![-1, -1, -2, 4]]

def raw4641step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 2, -1], ![0, 2, 0, -2], ![1, 0, -1, 0], ![1, 0, 0, -1]]

theorem canonical4641 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4641 = injectiveMoment H node1581 := by
  calc
    injectiveMoment H raw4641 = injectiveMoment H raw4641step0 := by
      have heq : raw4641step0 = -raw4641 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4641).symm
    injectiveMoment H raw4641step0 = injectiveMoment H raw4641step1 := by
      have heq : raw4641step1 = (fun i j => raw4641step0 (permutation129 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4641step0 permutation129 permutation23
    _ = injectiveMoment H node1581 := by rfl

def raw4642 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -2, 1, 1], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def raw4642step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, -1, 0, -1], ![0, 2, -1, -1], ![0, -1, 1, 0], ![-1, 0, 0, 1], ![-1, 0, 0, 1]]

def raw4642step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 2, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1]]

theorem canonical4642 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4642 = injectiveMoment H node2587 := by
  calc
    injectiveMoment H raw4642 = injectiveMoment H raw4642step0 := by
      have heq : raw4642step0 = -raw4642 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4642).symm
    injectiveMoment H raw4642step0 = injectiveMoment H raw4642step1 := by
      have heq : raw4642step1 = (fun i j => raw4642step0 (permutation60 i) (permutation25 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4642step0 permutation60 permutation25
    _ = injectiveMoment H node2587 := by rfl

def raw4643 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -2, 1, 1], ![0, 1, 0, -1], ![2, 0, -1, -1]]

def raw4643step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 1, 0], ![0, 1, 1, -2], ![1, 1, -2, 0]]

theorem canonical4643 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4643 = injectiveMoment H node1000 := by
  calc
    injectiveMoment H raw4643 = injectiveMoment H raw4643step0 := by
      have heq : raw4643step0 = (fun i j => raw4643 (permutation31 i) (permutation26 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4643 permutation31 permutation26
    _ = injectiveMoment H node1000 := by rfl

def raw4644 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -2, 1, 1], ![1, 0, -1, 0], ![1, 1, 0, -2]]

def raw4644step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, -1, 0, -1], ![0, 2, -1, -1], ![-1, 0, 1, 0], ![-1, -1, 0, 2]]

def raw4644step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 2, -1], ![0, 2, -1, -1], ![1, 0, -1, 0]]

theorem canonical4644 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4644 = injectiveMoment H node1009 := by
  calc
    injectiveMoment H raw4644 = injectiveMoment H raw4644step0 := by
      have heq : raw4644step0 = -raw4644 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4644).symm
    injectiveMoment H raw4644step0 = injectiveMoment H raw4644step1 := by
      have heq : raw4644step1 = (fun i j => raw4644step0 (permutation16 i) (permutation25 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4644step0 permutation16 permutation25
    _ = injectiveMoment H node1009 := by rfl

def raw4645 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -2, 1, 1], ![1, 0, 0, -1], ![1, 1, -1, -1]]

def raw4645step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, -1, 0, -1], ![0, 2, -1, -1], ![-1, 0, 0, 1], ![-1, -1, 1, 1]]

def raw4645step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 2, -1], ![0, 1, -1, 0], ![1, 1, -1, -1]]

theorem canonical4645 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4645 = injectiveMoment H node1006 := by
  calc
    injectiveMoment H raw4645 = injectiveMoment H raw4645step0 := by
      have heq : raw4645step0 = -raw4645 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4645).symm
    injectiveMoment H raw4645step0 = injectiveMoment H raw4645step1 := by
      have heq : raw4645step1 = (fun i j => raw4645step0 (permutation15 i) (permutation25 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4645step0 permutation15 permutation25
    _ = injectiveMoment H node1006 := by rfl

def raw4646 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -2, 1, 1], ![1, 0, 1, -2], ![1, 1, -2, 0]]

def raw4646step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -2, 1], ![1, -2, 1, 0], ![1, 1, 0, -2]]

theorem canonical4646 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4646 = injectiveMoment H node620 := by
  calc
    injectiveMoment H raw4646 = injectiveMoment H raw4646step0 := by
      have heq : raw4646step0 = (fun i j => raw4646 (permutation10 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4646 permutation10 permutation11
    _ = injectiveMoment H node620 := by rfl

def raw4647 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -2, 2, 0], ![0, 1, 0, -1], ![1, 0, -2, 1], ![1, 0, 0, -1]]

def raw4647step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, -1, 0, -1], ![0, 2, -2, 0], ![0, -1, 0, 1], ![-1, 0, 2, -1], ![-1, 0, 0, 1]]

def raw4647step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 2, -1, -1], ![2, -1, -1, 0]]

theorem canonical4647 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4647 = injectiveMoment H node2015 := by
  calc
    injectiveMoment H raw4647 = injectiveMoment H raw4647step0 := by
      have heq : raw4647step0 = -raw4647 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4647).symm
    injectiveMoment H raw4647step0 = injectiveMoment H raw4647step1 := by
      have heq : raw4647step1 = (fun i j => raw4647step0 (permutation76 i) (permutation22 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4647step0 permutation76 permutation22
    _ = injectiveMoment H node2015 := by rfl

def raw4648 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -2, 2, 0], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, -1, 0]]

def raw4648step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, -1, 0, -1], ![0, 2, -2, 0], ![0, -1, 0, 1], ![-1, 0, 1, 0], ![-1, 0, 1, 0]]

def raw4648step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, -1, 0, 0]]

theorem canonical4648 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4648 = injectiveMoment H node2609 := by
  calc
    injectiveMoment H raw4648 = injectiveMoment H raw4648step0 := by
      have heq : raw4648step0 = -raw4648 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4648).symm
    injectiveMoment H raw4648step0 = injectiveMoment H raw4648step1 := by
      have heq : raw4648step1 = (fun i j => raw4648step0 (permutation49 i) (permutation30 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4648step0 permutation49 permutation30
    _ = injectiveMoment H node2609 := by rfl

def raw4649 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -2, 2, 0], ![0, 1, 0, -1], ![2, 0, -2, 0]]

def raw4649step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, -1, 0, -1], ![0, 2, -2, 0], ![0, -1, 0, 1], ![-2, 0, 2, 0]]

def raw4649step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 2, -2, 0], ![1, -1, 0, 0]]

theorem canonical4649 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4649 = injectiveMoment H node1057 := by
  calc
    injectiveMoment H raw4649 = injectiveMoment H raw4649step0 := by
      have heq : raw4649step0 = -raw4649 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4649).symm
    injectiveMoment H raw4649step0 = injectiveMoment H raw4649step1 := by
      have heq : raw4649step1 = (fun i j => raw4649step0 (permutation13 i) (permutation30 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4649step0 permutation13 permutation30
    _ = injectiveMoment H node1057 := by rfl

def raw4650 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -2, 2, 0], ![1, 0, -2, 1], ![1, 1, 0, -2]]

def raw4650step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, -1, 0, -1], ![0, 2, -2, 0], ![-1, 0, 2, -1], ![-1, -1, 0, 2]]

def raw4650step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 2, -1], ![0, 2, -1, -1], ![2, -1, -1, 0]]

theorem canonical4650 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4650 = injectiveMoment H node609 := by
  calc
    injectiveMoment H raw4650 = injectiveMoment H raw4650step0 := by
      have heq : raw4650step0 = -raw4650 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4650).symm
    injectiveMoment H raw4650step0 = injectiveMoment H raw4650step1 := by
      have heq : raw4650step1 = (fun i j => raw4650step0 (permutation19 i) (permutation22 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4650step0 permutation19 permutation22
    _ = injectiveMoment H node609 := by rfl

def raw4651 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -2, 2, 0], ![1, 0, -1, 0], ![1, 1, -1, -1]]

def raw4651step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, -2, 0, 1], ![0, 2, -1, -1], ![1, 0, 0, -1]]

def raw4651step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 1, 0], ![0, 1, 1, -2], ![1, 1, -2, 0]]

theorem canonical4651 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4651 = injectiveMoment H node1000 := by
  calc
    injectiveMoment H raw4651 = injectiveMoment H raw4651step0 := by
      have heq : raw4651step0 = raw4651.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4651).symm
    injectiveMoment H raw4651step0 = injectiveMoment H raw4651step1 := by
      have heq : raw4651step1 = (fun i j => raw4651step0 (permutation26 i) (permutation25 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4651step0 permutation26 permutation25
    _ = injectiveMoment H node1000 := by rfl

def raw4652 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, -2, 3], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 3, -4]]

theorem canonical4652 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4652 = injectiveMoment H node2247 := by
  rfl

def raw4653 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, -2, 3], ![0, 1, 3, -4], ![1, -1, 0, 0], ![1, 0, -1, 0]]

theorem canonical4653 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4653 = injectiveMoment H node2248 := by
  rfl

def raw4654 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, -2, 3], ![0, 1, 3, -4], ![2, -1, -1, 0]]

theorem canonical4654 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4654 = injectiveMoment H node688 := by
  rfl

def raw4655 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, -2, 3], ![1, -1, 0, 0], ![1, 1, 2, -4]]

def raw4655step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, -1, -1, 1], ![0, -2, 0, 2], ![1, 3, 0, -4]]

def raw4655step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, -2, 2], ![0, 1, 3, -4], ![1, -2, 0, 1]]

theorem canonical4655 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4655 = injectiveMoment H node1348 := by
  calc
    injectiveMoment H raw4655 = injectiveMoment H raw4655step0 := by
      have heq : raw4655step0 = raw4655.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4655).symm
    injectiveMoment H raw4655step0 = injectiveMoment H raw4655step1 := by
      have heq : raw4655step1 = (fun i j => raw4655step0 (permutation18 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4655step0 permutation18 permutation21
    _ = injectiveMoment H node1348 := by rfl

def raw4656 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, -2, 3], ![1, 0, -1, 0], ![1, 0, 3, -4]]

def raw4656step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, -2, 0, 1]]

theorem canonical4656 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4656 = injectiveMoment H node1232 := by
  calc
    injectiveMoment H raw4656 = injectiveMoment H raw4656step0 := by
      have heq : raw4656step0 = (fun i j => raw4656 (permutation18 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4656 permutation18 permutation15
    _ = injectiveMoment H node1232 := by rfl

def raw4657 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, -2, 3], ![1, 0, 3, -4], ![1, 0, -1, 0]]

def raw4657step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, -2, 0, 1]]

theorem canonical4657 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4657 = injectiveMoment H node1232 := by
  calc
    injectiveMoment H raw4657 = injectiveMoment H raw4657step0 := by
      have heq : raw4657step0 = (fun i j => raw4657 (permutation20 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4657 permutation20 permutation15
    _ = injectiveMoment H node1232 := by rfl

def raw4658 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, -1, 2], ![0, -1, 0, 1], ![1, 0, -1, 0], ![1, 1, 2, -4]]

def raw4658step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, -1, 0, -1], ![0, 1, 1, -2], ![0, 1, 0, -1], ![-1, 0, 1, 0], ![-1, -1, -2, 4]]

def raw4658step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 2, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 1, 0, -2]]

theorem canonical4658 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4658 = injectiveMoment H node1575 := by
  calc
    injectiveMoment H raw4658 = injectiveMoment H raw4658step0 := by
      have heq : raw4658step0 = -raw4658 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4658).symm
    injectiveMoment H raw4658step0 = injectiveMoment H raw4658step1 := by
      have heq : raw4658step1 = (fun i j => raw4658step0 (permutation131 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4658step0 permutation131 permutation23
    _ = injectiveMoment H node1575 := by rfl

def raw4659 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, -1, 2], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, 1, 2, -4]]

def raw4659step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, -1, 0, -1], ![0, 1, 1, -2], ![0, 0, 1, -1], ![-1, 1, 0, 0], ![-1, -1, -2, 4]]

def raw4659step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 1, 0], ![0, 2, -1, -1], ![1, 0, 0, -1], ![1, 0, 1, -2]]

theorem canonical4659 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4659 = injectiveMoment H node1561 := by
  calc
    injectiveMoment H raw4659 = injectiveMoment H raw4659step0 := by
      have heq : raw4659step0 = -raw4659 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4659).symm
    injectiveMoment H raw4659step0 = injectiveMoment H raw4659step1 := by
      have heq : raw4659step1 = (fun i j => raw4659step0 (permutation146 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4659step0 permutation146 permutation21
    _ = injectiveMoment H node1561 := by rfl

def raw4660 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, -1, 2], ![0, 0, -1, 1], ![1, 0, -1, 0], ![1, 0, 3, -4]]

def raw4660step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, -2, 0, 1]]

theorem canonical4660 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4660 = injectiveMoment H node2733 := by
  calc
    injectiveMoment H raw4660 = injectiveMoment H raw4660step0 := by
      have heq : raw4660step0 = (fun i j => raw4660 (permutation65 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4660 permutation65 permutation15
    _ = injectiveMoment H node2733 := by rfl

def raw4661 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, -1, 2], ![0, 0, 3, -3], ![1, 0, -1, 0], ![1, 0, -1, 0]]

def raw4661step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, 3, -3], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -2, 0, 1]]

theorem canonical4661 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4661 = injectiveMoment H node2735 := by
  calc
    injectiveMoment H raw4661 = injectiveMoment H raw4661step0 := by
      have heq : raw4661step0 = (fun i j => raw4661 (permutation65 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4661 permutation65 permutation15
    _ = injectiveMoment H node2735 := by rfl

def raw4662 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, -1, 2], ![0, 1, -2, 1], ![1, -1, 0, 0], ![1, 0, 3, -4]]

theorem canonical4662 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4662 = injectiveMoment H node2249 := by
  rfl

def raw4663 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, -1, 2], ![0, 1, -2, 1], ![2, -1, 3, -4]]

def raw4663step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, -1, 1, -1], ![0, -1, -2, 3], ![1, 2, 1, -4]]

def raw4663step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![-1, 1, -1, 1], ![0, 1, 2, -3], ![-1, -2, -1, 4]]

def raw4663step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 2, -2], ![1, -1, -1, 1], ![1, 2, 0, -3]]

theorem canonical4663 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4663 = injectiveMoment H node460 := by
  calc
    injectiveMoment H raw4663 = injectiveMoment H raw4663step0 := by
      have heq : raw4663step0 = raw4663.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4663).symm
    injectiveMoment H raw4663step0 = injectiveMoment H raw4663step1 := by
      have heq : raw4663step1 = -raw4663step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4663step0).symm
    injectiveMoment H raw4663step1 = injectiveMoment H raw4663step2 := by
      have heq : raw4663step2 = (fun i j => raw4663step1 (permutation27 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4663step1 permutation27 permutation17
    _ = injectiveMoment H node460 := by rfl

def raw4664 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, -1, 2], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, 0, 3, -4]]

theorem canonical4664 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4664 = injectiveMoment H node2250 := by
  rfl

def raw4665 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, -1, 2], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 2, -3]]

def raw4665step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, -1, 0, -1], ![0, 1, 1, -2], ![0, -1, 1, 0], ![-1, 1, 0, 0], ![-1, 0, -2, 3]]

def raw4665step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 2, -1, -1], ![1, 0, -1, 0], ![1, 0, 1, -2]]

theorem canonical4665 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4665 = injectiveMoment H node1643 := by
  calc
    injectiveMoment H raw4665 = injectiveMoment H raw4665step0 := by
      have heq : raw4665step0 = -raw4665 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4665).symm
    injectiveMoment H raw4665step0 = injectiveMoment H raw4665step1 := by
      have heq : raw4665step1 = (fun i j => raw4665step0 (permutation146 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4665step0 permutation146 permutation21
    _ = injectiveMoment H node1643 := by rfl

def raw4666 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, -1, 2], ![0, 1, -1, 0], ![1, -1, 3, -3], ![1, 0, -1, 0]]

theorem canonical4666 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4666 = injectiveMoment H node2251 := by
  rfl

def raw4667 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, -1, 2], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, -1, 3, -3]]

def raw4667step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, -1, 2], ![0, 1, -1, 0], ![1, -1, 3, -3], ![1, 0, -1, 0]]

theorem canonical4667 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4667 = injectiveMoment H node2251 := by
  calc
    injectiveMoment H raw4667 = injectiveMoment H raw4667step0 := by
      have heq : raw4667step0 = (fun i j => raw4667 (permutation34 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4667 permutation34 permutation9
    _ = injectiveMoment H node2251 := by rfl

def raw4668 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, -1, 2], ![0, 1, -1, 0], ![2, -1, 2, -3]]

def raw4668step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, -1, 1, -1], ![0, -1, -1, 2], ![1, 2, 0, -3]]

def raw4668step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 2, 1, -3], ![1, -1, 1, -1]]

theorem canonical4668 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4668 = injectiveMoment H node1036 := by
  calc
    injectiveMoment H raw4668 = injectiveMoment H raw4668step0 := by
      have heq : raw4668step0 = raw4668.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4668).symm
    injectiveMoment H raw4668step0 = injectiveMoment H raw4668step1 := by
      have heq : raw4668step1 = (fun i j => raw4668step0 (permutation22 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4668step0 permutation22 permutation23
    _ = injectiveMoment H node1036 := by rfl

def raw4669 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, -1, 2], ![0, 1, 2, -3], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def raw4669step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, -1, 0, -1], ![0, 1, 1, -2], ![0, -1, -2, 3], ![-1, 1, 0, 0], ![-1, 0, 1, 0]]

def raw4669step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 1, 0, -2]]

theorem canonical4669 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4669 = injectiveMoment H node1648 := by
  calc
    injectiveMoment H raw4669 = injectiveMoment H raw4669step0 := by
      have heq : raw4669step0 = -raw4669 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4669).symm
    injectiveMoment H raw4669step0 = injectiveMoment H raw4669step1 := by
      have heq : raw4669step1 = (fun i j => raw4669step0 (permutation83 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4669step0 permutation83 permutation23
    _ = injectiveMoment H node1648 := by rfl

def raw4670 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, -1, 2], ![0, 1, 3, -4], ![1, -1, -1, 1], ![1, 0, -1, 0]]

theorem canonical4670 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4670 = injectiveMoment H node2252 := by
  rfl

def raw4671 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, -1, 2], ![0, 1, 3, -4], ![1, -1, 0, 0], ![1, 0, -2, 1]]

theorem canonical4671 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4671 = injectiveMoment H node2253 := by
  rfl

end MUB6.Certificate.PairSemantics

end OAI
