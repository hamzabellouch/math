import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes1
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes2
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes3
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes7
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes11
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes12
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes14
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes15
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes18
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes19
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes25
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes28
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes33
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes34
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes36
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes42

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw5056 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 2, -1], ![0, -1, -3, 4], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, 0, 0, -1]]

theorem canonical5056 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5056 = injectiveMoment H node2322 := by
  rfl

def raw5057 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 2, -1], ![0, -1, -3, 4], ![0, 1, 1, -2], ![2, -1, 0, -1]]

def raw5057step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, -1, 1, -1], ![2, -3, 1, 0], ![-1, 4, -2, -1]]

def raw5057step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 2, -2, 0], ![1, -1, 1, -1], ![1, 0, 2, -3]]

theorem canonical5057 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5057 = injectiveMoment H node468 := by
  calc
    injectiveMoment H raw5057 = injectiveMoment H raw5057step0 := by
      have heq : raw5057step0 = raw5057.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5057).symm
    injectiveMoment H raw5057step0 = injectiveMoment H raw5057step1 := by
      have heq : raw5057step1 = (fun i j => raw5057step0 (permutation27 i) (permutation25 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5057step0 permutation27 permutation25
    _ = injectiveMoment H node468 := by rfl

def raw5058 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 2, -1], ![0, -1, -3, 4], ![1, -1, 0, 0], ![1, 1, 1, -3]]

def raw5058step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, -1, -1, 1], ![2, -3, 0, 1], ![-1, 4, 0, -3]]

def raw5058step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, 1, 1, -1], ![-2, 3, 0, -1], ![1, -4, 0, 3]]

def raw5058step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![0, -1, -2, 3], ![0, 3, 1, -4], ![1, -1, -1, 1]]

theorem canonical5058 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw5058 = injectiveMoment H node1157 := by
  calc
    injectiveMoment H raw5058 = injectiveMoment H raw5058step0 := by
      have heq : raw5058step0 = raw5058.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5058).symm
    injectiveMoment H raw5058step0 = injectiveMoment H raw5058step1 := by
      have heq : raw5058step1 = -raw5058step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw5058step0).symm
    injectiveMoment H raw5058step1 = injectiveMoment H raw5058step2 := by
      have heq : raw5058step2 = (fun i j => raw5058step1 (permutation12 i) (permutation25 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5058step1 permutation12 permutation25
    _ = injectiveMoment H node1157 := by rfl

def raw5059 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 2, -1], ![0, -1, -3, 4], ![1, -1, 1, -1], ![1, 1, 0, -2]]

def raw5059step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, -1, -1, 1], ![2, -3, 1, 0], ![-1, 4, -1, -2]]

def raw5059step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 1, 2, -3], ![1, -1, 1, -1], ![1, 1, -2, 0]]

theorem canonical5059 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5059 = injectiveMoment H node467 := by
  calc
    injectiveMoment H raw5059 = injectiveMoment H raw5059step0 := by
      have heq : raw5059step0 = raw5059.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5059).symm
    injectiveMoment H raw5059step0 = injectiveMoment H raw5059step1 := by
      have heq : raw5059step1 = (fun i j => raw5059step0 (permutation32 i) (permutation31 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5059step0 permutation32 permutation31
    _ = injectiveMoment H node467 := by rfl

def raw5060 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 2, -1], ![0, -1, -3, 4], ![1, 0, 1, -2], ![1, 0, 0, -1]]

def raw5060step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, -1, 0, 0], ![2, -3, 1, 0], ![-1, 4, -2, -1]]

def raw5060step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 1, -1], ![0, 1, 2, -3], ![1, 1, -2, 0]]

theorem canonical5060 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5060 = injectiveMoment H node767 := by
  calc
    injectiveMoment H raw5060 = injectiveMoment H raw5060step0 := by
      have heq : raw5060step0 = raw5060.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5060).symm
    injectiveMoment H raw5060step0 = injectiveMoment H raw5060step1 := by
      have heq : raw5060step1 = (fun i j => raw5060step0 (permutation30 i) (permutation31 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5060step0 permutation30 permutation31
    _ = injectiveMoment H node767 := by rfl

def raw5061 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 2, -1], ![0, -1, -2, 3], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw5061step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, 1, -2, -1]]

theorem canonical5061 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5061 = injectiveMoment H node1631 := by
  calc
    injectiveMoment H raw5061 = injectiveMoment H raw5061step0 := by
      have heq : raw5061step0 = (fun i j => raw5061 (permutation73 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5061 permutation73 permutation23
    _ = injectiveMoment H node1631 := by rfl

def raw5062 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 2, -1], ![0, -1, -2, 3], ![1, -1, 0, 0], ![1, 1, 0, -2]]

def raw5062step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, -1, -1, 1], ![2, -2, 0, 0], ![-1, 3, 0, -2]]

def raw5062step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, 1, 1, -1], ![-2, 2, 0, 0], ![1, -3, 0, 2]]

def raw5062step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 2, -3, 1], ![1, -1, 1, -1]]

theorem canonical5062 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw5062 = injectiveMoment H node1056 := by
  calc
    injectiveMoment H raw5062 = injectiveMoment H raw5062step0 := by
      have heq : raw5062step0 = raw5062.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5062).symm
    injectiveMoment H raw5062step0 = injectiveMoment H raw5062step1 := by
      have heq : raw5062step1 = -raw5062step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw5062step0).symm
    injectiveMoment H raw5062step1 = injectiveMoment H raw5062step2 := by
      have heq : raw5062step2 = (fun i j => raw5062step1 (permutation12 i) (permutation26 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5062step1 permutation12 permutation26
    _ = injectiveMoment H node1056 := by rfl

def raw5063 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 2, -1], ![0, -1, -1, 2], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 0, 0, -1]]

def raw5063step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, -1, -2, 1], ![0, 1, 1, -2], ![0, -1, 0, 1], ![-1, 1, 1, -1], ![-1, 0, 0, 1]]

def raw5063step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![1, 1, -1, -1], ![1, 1, 0, -2]]

theorem canonical5063 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw5063 = injectiveMoment H node1841 := by
  calc
    injectiveMoment H raw5063 = injectiveMoment H raw5063step0 := by
      have heq : raw5063step0 = -raw5063 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw5063).symm
    injectiveMoment H raw5063step0 = injectiveMoment H raw5063step1 := by
      have heq : raw5063step1 = (fun i j => raw5063step0 (permutation44 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5063step0 permutation44 permutation23
    _ = injectiveMoment H node1841 := by rfl

def raw5064 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 2, -1], ![0, -1, 1, 0], ![1, -1, -3, 3], ![1, 1, 0, -2]]

def raw5064step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, -1, -1, 1], ![2, 1, -3, 0], ![-1, 0, 3, -2]]

def raw5064step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, 1, 1, -1], ![-2, -1, 3, 0], ![1, 0, -3, 2]]

def raw5064step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 2, -1], ![0, 2, 1, -3], ![1, -1, -1, 1]]

theorem canonical5064 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw5064 = injectiveMoment H node1209 := by
  calc
    injectiveMoment H raw5064 = injectiveMoment H raw5064step0 := by
      have heq : raw5064step0 = raw5064.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5064).symm
    injectiveMoment H raw5064step0 = injectiveMoment H raw5064step1 := by
      have heq : raw5064step1 = -raw5064step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw5064step0).symm
    injectiveMoment H raw5064step1 = injectiveMoment H raw5064step2 := by
      have heq : raw5064step2 = (fun i j => raw5064step1 (permutation22 i) (permutation19 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5064step1 permutation22 permutation19
    _ = injectiveMoment H node1209 := by rfl

def raw5065 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 2, -1], ![0, 0, 1, -1], ![1, -2, -3, 4], ![1, 1, 0, -2]]

def raw5065step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 0, -2, 1], ![2, 1, -3, 0], ![-1, -1, 4, -2]]

def raw5065step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 1, -2, 1], ![0, 1, 1, -2], ![1, 0, 2, -3]]

theorem canonical5065 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5065 = injectiveMoment H node784 := by
  calc
    injectiveMoment H raw5065 = injectiveMoment H raw5065step0 := by
      have heq : raw5065step0 = raw5065.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5065).symm
    injectiveMoment H raw5065step0 = injectiveMoment H raw5065step1 := by
      have heq : raw5065step1 = (fun i j => raw5065step0 (permutation27 i) (permutation19 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5065step0 permutation27 permutation19
    _ = injectiveMoment H node784 := by rfl

def raw5066 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 2, -1], ![0, 0, 1, -1], ![1, -1, -3, 3], ![1, 0, 0, -1]]

def raw5066step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 0, -1, 0], ![2, 1, -3, 0], ![-1, -1, 3, -1]]

def raw5066step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 1, -1], ![0, 1, -2, 1], ![1, 0, 2, -3]]

theorem canonical5066 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5066 = injectiveMoment H node968 := by
  calc
    injectiveMoment H raw5066 = injectiveMoment H raw5066step0 := by
      have heq : raw5066step0 = raw5066.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5066).symm
    injectiveMoment H raw5066step0 = injectiveMoment H raw5066step1 := by
      have heq : raw5066step1 = (fun i j => raw5066step0 (permutation29 i) (permutation19 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5066step0 permutation29 permutation19
    _ = injectiveMoment H node968 := by rfl

def raw5067 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 1, 2, -1], ![0, 1, -3, 2], ![2, -2, 1, -1]]

def raw5067step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![1, 1, -2], ![2, -3, 1], ![-1, 2, -1]]

def raw5067step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]

theorem canonical5067 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5067 = injectiveMoment H node111 := by
  calc
    injectiveMoment H raw5067 = injectiveMoment H raw5067step0 := by
      have heq : raw5067step0 = raw5067.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5067).symm
    injectiveMoment H raw5067step0 = injectiveMoment H raw5067step1 := by
      have heq : raw5067step1 = (fun i j => raw5067step0 (permutation21 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5067step0 permutation21 permutation6
    _ = injectiveMoment H node111 := by rfl

def raw5068 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 1, 2, -1], ![0, 2, -2, 0], ![2, -3, 0, 1]]

def raw5068step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![1, 2, -3], ![2, -2, 0], ![-1, 0, 1]]

def raw5068step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![-1, -2, 3], ![-2, 2, 0], ![1, 0, -1]]

def raw5068step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]

theorem canonical5068 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw5068 = injectiveMoment H node177 := by
  calc
    injectiveMoment H raw5068 = injectiveMoment H raw5068step0 := by
      have heq : raw5068step0 = raw5068.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5068).symm
    injectiveMoment H raw5068step0 = injectiveMoment H raw5068step1 := by
      have heq : raw5068step1 = -raw5068step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw5068step0).symm
    injectiveMoment H raw5068step1 = injectiveMoment H raw5068step2 := by
      have heq : raw5068step2 = (fun i j => raw5068step1 (permutation19 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5068step1 permutation19 permutation5
    _ = injectiveMoment H node177 := by rfl

def raw5069 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 1, 2, -1], ![0, 3, -3, 0], ![2, -4, 1, 1]]

def raw5069step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![1, 3, -4], ![2, -3, 1], ![-1, 0, 1]]

def raw5069step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![-1, -3, 4], ![-2, 3, -1], ![1, 0, -1]]

def raw5069step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![3, -2, -1]]

theorem canonical5069 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw5069 = injectiveMoment H node81 := by
  calc
    injectiveMoment H raw5069 = injectiveMoment H raw5069step0 := by
      have heq : raw5069step0 = raw5069.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5069).symm
    injectiveMoment H raw5069step0 = injectiveMoment H raw5069step1 := by
      have heq : raw5069step1 = -raw5069step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw5069step0).symm
    injectiveMoment H raw5069step1 = injectiveMoment H raw5069step2 := by
      have heq : raw5069step2 = (fun i j => raw5069step1 (permutation19 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5069step1 permutation19 permutation5
    _ = injectiveMoment H node81 := by rfl

def raw5070 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 1, 2, -1], ![0, 3, -2, -1], ![2, -4, 0, 2]]

def raw5070step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![1, 3, -4], ![2, -2, 0], ![-1, -1, 2]]

def raw5070step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![-1, -3, 4], ![-2, 2, 0], ![1, 1, -2]]

def raw5070step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]

theorem canonical5070 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw5070 = injectiveMoment H node85 := by
  calc
    injectiveMoment H raw5070 = injectiveMoment H raw5070step0 := by
      have heq : raw5070step0 = raw5070.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5070).symm
    injectiveMoment H raw5070step0 = injectiveMoment H raw5070step1 := by
      have heq : raw5070step1 = -raw5070step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw5070step0).symm
    injectiveMoment H raw5070step1 = injectiveMoment H raw5070step2 := by
      have heq : raw5070step2 = (fun i j => raw5070step1 (permutation16 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5070step1 permutation16 permutation5
    _ = injectiveMoment H node85 := by rfl

def raw5071 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 1, 2, -1], ![1, -3, 2, 0], ![1, 2, -4, 1]]

def raw5071step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -3, 2], ![2, 2, -4], ![-1, 0, 1]]

def raw5071step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![2, 2, -4]]

theorem canonical5071 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5071 = injectiveMoment H node106 := by
  calc
    injectiveMoment H raw5071 = injectiveMoment H raw5071step0 := by
      have heq : raw5071step0 = raw5071.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5071).symm
    injectiveMoment H raw5071step0 = injectiveMoment H raw5071step1 := by
      have heq : raw5071step1 = (fun i j => raw5071step0 (permutation19 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5071step0 permutation19 permutation5
    _ = injectiveMoment H node106 := by rfl

def raw5072 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 2, -1], ![1, -2, -3, 4], ![0, 1, 1, -2], ![1, 0, 0, -1]]

def raw5072step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![1, -2, 1, 0], ![2, -3, 1, 0], ![-1, 4, -2, -1]]

def raw5072step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 1, 1, -2], ![0, 1, 2, -3], ![1, 0, -2, 1]]

theorem canonical5072 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5072 = injectiveMoment H node788 := by
  calc
    injectiveMoment H raw5072 = injectiveMoment H raw5072step0 := by
      have heq : raw5072step0 = raw5072.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5072).symm
    injectiveMoment H raw5072step0 = injectiveMoment H raw5072step1 := by
      have heq : raw5072step1 = (fun i j => raw5072step0 (permutation30 i) (permutation31 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5072step0 permutation30 permutation31
    _ = injectiveMoment H node788 := by rfl

def raw5073 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 1, 2, -1], ![1, -2, 2, -1], ![1, 1, -4, 2]]

def raw5073step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -2, 1], ![2, 2, -4], ![-1, -1, 2]]

def raw5073step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -1, -1], ![-1, 2, -1], ![-2, -2, 4], ![1, 1, -2]]

def raw5073step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![1, 1, -2], ![2, -1, -1]]

theorem canonical5073 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw5073 = injectiveMoment H node134 := by
  calc
    injectiveMoment H raw5073 = injectiveMoment H raw5073step0 := by
      have heq : raw5073step0 = raw5073.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5073).symm
    injectiveMoment H raw5073step0 = injectiveMoment H raw5073step1 := by
      have heq : raw5073step1 = -raw5073step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw5073step0).symm
    injectiveMoment H raw5073step1 = injectiveMoment H raw5073step2 := by
      have heq : raw5073step2 = (fun i j => raw5073step1 (permutation24 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5073step1 permutation24 permutation3
    _ = injectiveMoment H node134 := by rfl

def raw5074 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 1, 2, -1], ![1, 1, -3, 1], ![1, -2, 1, 0]]

def raw5074step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![1, 1, -2], ![2, -3, 1], ![-1, 1, 0]]

def raw5074step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -2, 1], ![1, 2, -3]]

theorem canonical5074 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5074 = injectiveMoment H node229 := by
  calc
    injectiveMoment H raw5074 = injectiveMoment H raw5074step0 := by
      have heq : raw5074step0 = raw5074.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5074).symm
    injectiveMoment H raw5074step0 = injectiveMoment H raw5074step1 := by
      have heq : raw5074step1 = (fun i j => raw5074step0 (permutation19 i) (permutation7 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5074step0 permutation19 permutation7
    _ = injectiveMoment H node229 := by rfl

def raw5075 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 1, 2, -1], ![1, 2, -2, -1], ![1, -3, 0, 2]]

def raw5075step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![1, 2, -3], ![2, -2, 0], ![-1, -1, 2]]

def raw5075step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]

theorem canonical5075 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5075 = injectiveMoment H node111 := by
  calc
    injectiveMoment H raw5075 = injectiveMoment H raw5075step0 := by
      have heq : raw5075step0 = raw5075.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5075).symm
    injectiveMoment H raw5075step0 = injectiveMoment H raw5075step1 := by
      have heq : raw5075step1 = (fun i j => raw5075step0 (permutation17 i) (permutation7 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5075step0 permutation17 permutation7
    _ = injectiveMoment H node111 := by rfl

def raw5076 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 3, -2], ![0, -1, -3, 4], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1]]

theorem canonical5076 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5076 = injectiveMoment H node2324 := by
  rfl

def raw5077 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 3, -2], ![0, -1, -3, 4], ![1, -1, 0, 0], ![1, 1, 0, -2]]

def raw5077step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, -1, -1, 1], ![3, -3, 0, 0], ![-2, 4, 0, -2]]

def raw5077step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, 1, 1, -1], ![-3, 3, 0, 0], ![2, -4, 0, 2]]

def raw5077step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 3, -3], ![0, 2, -4, 2], ![1, -1, 1, -1]]

theorem canonical5077 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw5077 = injectiveMoment H node1064 := by
  calc
    injectiveMoment H raw5077 = injectiveMoment H raw5077step0 := by
      have heq : raw5077step0 = raw5077.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5077).symm
    injectiveMoment H raw5077step0 = injectiveMoment H raw5077step1 := by
      have heq : raw5077step1 = -raw5077step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw5077step0).symm
    injectiveMoment H raw5077step1 = injectiveMoment H raw5077step2 := by
      have heq : raw5077step2 = (fun i j => raw5077step1 (permutation12 i) (permutation26 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5077step1 permutation12 permutation26
    _ = injectiveMoment H node1064 := by rfl

def raw5078 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 3, -2], ![0, -1, -3, 4], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def raw5078step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, -1, 0, 0], ![3, -3, 0, 0], ![-2, 4, -1, -1]]

def raw5078step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 1, -1], ![0, 0, 3, -3], ![1, 1, -2, 0]]

theorem canonical5078 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5078 = injectiveMoment H node908 := by
  calc
    injectiveMoment H raw5078 = injectiveMoment H raw5078step0 := by
      have heq : raw5078step0 = raw5078.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5078).symm
    injectiveMoment H raw5078step0 = injectiveMoment H raw5078step1 := by
      have heq : raw5078step1 = (fun i j => raw5078step0 (permutation30 i) (permutation25 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5078step0 permutation30 permutation25
    _ = injectiveMoment H node908 := by rfl

def raw5079 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 3, -2], ![0, -1, -2, 3], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw5079step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, -1, 3, -2], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -1, 0]]

theorem canonical5079 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5079 = injectiveMoment H node2177 := by
  calc
    injectiveMoment H raw5079 = injectiveMoment H raw5079step0 := by
      have heq : raw5079step0 = (fun i j => raw5079 (permutation33 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5079 permutation33 permutation10
    _ = injectiveMoment H node2177 := by rfl

def raw5080 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 3, -2], ![0, -1, -2, 3], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 0, 0, -1]]

theorem canonical5080 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5080 = injectiveMoment H node2325 := by
  rfl

def raw5081 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 3, -2], ![0, -1, -2, 3], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def raw5081step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, -1, 3, -2], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 0, -1]]

theorem canonical5081 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5081 = injectiveMoment H node2175 := by
  calc
    injectiveMoment H raw5081 = injectiveMoment H raw5081step0 := by
      have heq : raw5081step0 = (fun i j => raw5081 (permutation33 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5081 permutation33 permutation10
    _ = injectiveMoment H node2175 := by rfl

def raw5082 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 3, -2], ![0, -1, -2, 3], ![1, -1, -1, 1], ![1, 1, 0, -2]]

theorem canonical5082 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5082 = injectiveMoment H node713 := by
  rfl

def raw5083 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 3, -2], ![0, -1, -2, 3], ![1, 0, -1, 0], ![1, 0, 0, -1]]

def raw5083step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, -1, 0, 0], ![3, -2, -1, 0], ![-2, 3, 0, -1]]

def raw5083step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, 1, 0, 0], ![-3, 2, 1, 0], ![2, -3, 0, 1]]

def raw5083step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 1, -1], ![0, 1, -3, 2], ![1, 0, 2, -3]]

theorem canonical5083 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw5083 = injectiveMoment H node1046 := by
  calc
    injectiveMoment H raw5083 = injectiveMoment H raw5083step0 := by
      have heq : raw5083step0 = raw5083.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5083).symm
    injectiveMoment H raw5083step0 = injectiveMoment H raw5083step1 := by
      have heq : raw5083step1 = -raw5083step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw5083step0).symm
    injectiveMoment H raw5083step1 = injectiveMoment H raw5083step2 := by
      have heq : raw5083step2 = (fun i j => raw5083step1 (permutation10 i) (permutation26 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5083step1 permutation10 permutation26
    _ = injectiveMoment H node1046 := by rfl

def raw5084 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 3, -2], ![0, -1, -1, 2], ![0, 0, -2, 2], ![1, -1, 0, 0], ![1, 1, 0, -2]]

theorem canonical5084 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5084 = injectiveMoment H node2326 := by
  rfl

def raw5085 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 3, -2], ![0, -1, -1, 2], ![0, 0, -2, 2], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def raw5085step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, -2, 2], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -2, 3, -2]]

theorem canonical5085 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5085 = injectiveMoment H node2729 := by
  calc
    injectiveMoment H raw5085 = injectiveMoment H raw5085step0 := by
      have heq : raw5085step0 = (fun i j => raw5085 (permutation65 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5085 permutation65 permutation15
    _ = injectiveMoment H node2729 := by rfl

def raw5086 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 3, -2], ![0, -1, -1, 2], ![0, 0, -2, 2], ![2, 0, 0, -2]]

def raw5086step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, -2, 2], ![0, 2, 0, -2], ![1, -2, 3, -2]]

theorem canonical5086 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5086 = injectiveMoment H node1255 := by
  calc
    injectiveMoment H raw5086 = injectiveMoment H raw5086step0 := by
      have heq : raw5086step0 = (fun i j => raw5086 (permutation18 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5086 permutation18 permutation15
    _ = injectiveMoment H node1255 := by rfl

def raw5087 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 3, -2], ![0, -1, -1, 2], ![0, 1, -2, 1], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw5087step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, -1, 2, -1], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, 0, -1, 0]]

theorem canonical5087 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5087 = injectiveMoment H node2173 := by
  calc
    injectiveMoment H raw5087 = injectiveMoment H raw5087step0 := by
      have heq : raw5087step0 = (fun i j => raw5087 (permutation33 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5087 permutation33 permutation10
    _ = injectiveMoment H node2173 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
