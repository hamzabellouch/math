import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes0
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes3
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes4
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes10
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes32

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw4128 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -2, 1], ![0, 0, 0], ![1, 1, -2]]

def raw4128step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]

theorem canonical4128 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4128 = injectiveMoment H node210 := by
  calc
    injectiveMoment H raw4128 = injectiveMoment H raw4128step0 := by
      have hz : ∀ j, raw4128 (permutation104 0) j = 0 := by decide +kernel
      have heq : raw4128step0 = (fun i j => raw4128 (permutation104 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw4128 permutation104 hz
    _ = injectiveMoment H node210 := by rfl

def raw4129 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![0, 2, -2]]

def raw4129step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0]]

theorem canonical4129 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4129 = injectiveMoment H node670 := by
  calc
    injectiveMoment H raw4129 = injectiveMoment H raw4129step0 := by
      have heq : raw4129step0 = (fun i j => raw4129 (permutation37 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4129 permutation37 permutation3
    _ = injectiveMoment H node670 := by rfl

def raw4130 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]

theorem canonical4130 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4130 = injectiveMoment H node210 := by
  rfl

def raw4131 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

def raw4131step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0]]

theorem canonical4131 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4131 = injectiveMoment H node294 := by
  calc
    injectiveMoment H raw4131 = injectiveMoment H raw4131step0 := by
      have heq : raw4131step0 = (fun i j => raw4131 (permutation25 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4131 permutation25 permutation6
    _ = injectiveMoment H node294 := by rfl

def raw4132 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![-1, 3, -2], ![1, -3, 2]]

def raw4132step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![0, 1, -1], ![1, -3, 2], ![1, -1, 0], ![1, 0, -1]]

theorem canonical4132 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4132 = injectiveMoment H node2106 := by
  calc
    injectiveMoment H raw4132 = injectiveMoment H raw4132step0 := by
      have heq : raw4132step0 = (fun i j => raw4132 (permutation185 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4132 permutation185 permutation3
    _ = injectiveMoment H node2106 := by rfl

def raw4133 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]

def raw4133step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0]]

theorem canonical4133 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4133 = injectiveMoment H node294 := by
  calc
    injectiveMoment H raw4133 = injectiveMoment H raw4133step0 := by
      have heq : raw4133step0 = (fun i j => raw4133 (permutation31 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4133 permutation31 permutation6
    _ = injectiveMoment H node294 := by rfl

def raw4134 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![2, -1, -1]]

def raw4134step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 2, -2], ![1, -1, 0]]

theorem canonical4134 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4134 = injectiveMoment H node62 := by
  calc
    injectiveMoment H raw4134 = injectiveMoment H raw4134step0 := by
      have heq : raw4134step0 = (fun i j => raw4134 (permutation7 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4134 permutation7 permutation6
    _ = injectiveMoment H node62 := by rfl

def raw4135 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![0, -1, 1], ![2, -1, -1]]

def raw4135step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]

theorem canonical4135 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4135 = injectiveMoment H node203 := by
  calc
    injectiveMoment H raw4135 = injectiveMoment H raw4135step0 := by
      have heq : raw4135step0 = (fun i j => raw4135 (permutation11 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4135 permutation11 permutation3
    _ = injectiveMoment H node203 := by rfl

def raw4136 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1]]

def raw4136step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 2, -2], ![1, -3, 2], ![1, 0, -1]]

theorem canonical4136 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4136 = injectiveMoment H node669 := by
  calc
    injectiveMoment H raw4136 = injectiveMoment H raw4136step0 := by
      have heq : raw4136step0 = (fun i j => raw4136 (permutation39 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4136 permutation39 permutation3
    _ = injectiveMoment H node669 := by rfl

def raw4137 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0]]

def raw4137step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0]]

theorem canonical4137 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4137 = injectiveMoment H node670 := by
  calc
    injectiveMoment H raw4137 = injectiveMoment H raw4137step0 := by
      have heq : raw4137step0 = (fun i j => raw4137 (permutation39 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4137 permutation39 permutation3
    _ = injectiveMoment H node670 := by rfl

def raw4138 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![1, -3, 2], ![1, 1, -2]]

theorem canonical4138 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4138 = injectiveMoment H node212 := by
  rfl

def raw4139 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1]]

def raw4139step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![0, -2, 2], ![-1, 2, -1], ![-1, 0, 1]]

def raw4139step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]

theorem canonical4139 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4139 = injectiveMoment H node203 := by
  calc
    injectiveMoment H raw4139 = injectiveMoment H raw4139step0 := by
      have heq : raw4139step0 = -raw4139 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4139).symm
    injectiveMoment H raw4139step0 = injectiveMoment H raw4139step1 := by
      have heq : raw4139step1 = (fun i j => raw4139step0 (permutation19 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4139step0 permutation19 permutation5
    _ = injectiveMoment H node203 := by rfl

def raw4140 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]

def raw4140step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]

theorem canonical4140 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4140 = injectiveMoment H node207 := by
  calc
    injectiveMoment H raw4140 = injectiveMoment H raw4140step0 := by
      have heq : raw4140step0 = (fun i j => raw4140 (permutation18 i) (permutation7 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4140 permutation18 permutation7
    _ = injectiveMoment H node207 := by rfl

def raw4141 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![2, -2, 0]]

theorem canonical4141 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4141 = injectiveMoment H node41 := by
  rfl

def raw4142 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1]]

def raw4142step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1]]

theorem canonical4142 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4142 = injectiveMoment H node648 := by
  calc
    injectiveMoment H raw4142 = injectiveMoment H raw4142step0 := by
      have heq : raw4142step0 = (fun i j => raw4142 (permutation39 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4142 permutation39 permutation3
    _ = injectiveMoment H node648 := by rfl

def raw4143 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![0, -2, 2], ![2, -1, -1]]

def raw4143step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 3, -3], ![2, -1, -1]]

theorem canonical4143 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4143 = injectiveMoment H node198 := by
  calc
    injectiveMoment H raw4143 = injectiveMoment H raw4143step0 := by
      have heq : raw4143step0 = (fun i j => raw4143 (permutation11 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4143 permutation11 permutation3
    _ = injectiveMoment H node198 := by rfl

def raw4144 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![1, -3, 2], ![1, 0, -1]]

theorem canonical4144 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4144 = injectiveMoment H node214 := by
  rfl

def raw4145 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![1, -2, 1], ![1, -1, 0]]

theorem canonical4145 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4145 = injectiveMoment H node215 := by
  rfl

def raw4146 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![1, -1, 0], ![1, -2, 1]]

def raw4146step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![1, -2, 1], ![1, -1, 0]]

theorem canonical4146 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4146 = injectiveMoment H node215 := by
  calc
    injectiveMoment H raw4146 = injectiveMoment H raw4146step0 := by
      have heq : raw4146step0 = (fun i j => raw4146 (permutation10 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4146 permutation10 permutation3
    _ = injectiveMoment H node215 := by rfl

def raw4147 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![2, -3, 1]]

def raw4147step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 0, -2], ![0, -3, 3], ![-2, 3, -1]]

def raw4147step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 3, -3], ![2, -2, 0]]

theorem canonical4147 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4147 = injectiveMoment H node37 := by
  calc
    injectiveMoment H raw4147 = injectiveMoment H raw4147step0 := by
      have heq : raw4147step0 = -raw4147 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4147).symm
    injectiveMoment H raw4147step0 = injectiveMoment H raw4147step1 := by
      have heq : raw4147step1 = (fun i j => raw4147step0 (permutation8 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4147step0 permutation8 permutation4
    _ = injectiveMoment H node37 := by rfl

def raw4148 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 4, -4], ![1, -4, 3], ![1, 0, -1]]

theorem canonical4148 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4148 = injectiveMoment H node216 := by
  rfl

def raw4149 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 4, -4], ![1, -3, 2], ![1, -1, 0]]

theorem canonical4149 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4149 = injectiveMoment H node217 := by
  rfl

def raw4150 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 4, -4], ![1, -2, 1], ![1, -2, 1]]

theorem canonical4150 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4150 = injectiveMoment H node218 := by
  rfl

def raw4151 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 4, -4], ![2, -4, 2]]

def raw4151step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 0, -2], ![0, -4, 4], ![-2, 4, -2]]

def raw4151step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 4, -4], ![2, -2, 0]]

theorem canonical4151 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4151 = injectiveMoment H node33 := by
  calc
    injectiveMoment H raw4151 = injectiveMoment H raw4151step0 := by
      have heq : raw4151step0 = -raw4151 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4151).symm
    injectiveMoment H raw4151step0 = injectiveMoment H raw4151step1 := by
      have heq : raw4151step1 = (fun i j => raw4151step0 (permutation8 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4151step0 permutation8 permutation4
    _ = injectiveMoment H node33 := by rfl

def raw4152 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![1, -4, 3], ![0, 4, -4], ![1, 0, -1]]

def raw4152step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 4, -4], ![1, -4, 3], ![1, 0, -1]]

theorem canonical4152 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4152 = injectiveMoment H node216 := by
  calc
    injectiveMoment H raw4152 = injectiveMoment H raw4152step0 := by
      have heq : raw4152step0 = (fun i j => raw4152 (permutation11 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4152 permutation11 permutation3
    _ = injectiveMoment H node216 := by rfl

def raw4153 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![1, -4, 3], ![1, 4, -5]]

def raw4153step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -4, 4], ![2, 3, -5]]

def raw4153step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, -1, -1], ![0, 4, -4], ![-2, -3, 5]]

def raw4153step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 4, -4], ![2, -1, -1]]

theorem canonical4153 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4153 = injectiveMoment H node29 := by
  calc
    injectiveMoment H raw4153 = injectiveMoment H raw4153step0 := by
      have heq : raw4153step0 = raw4153.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4153).symm
    injectiveMoment H raw4153step0 = injectiveMoment H raw4153step1 := by
      have heq : raw4153step1 = -raw4153step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4153step0).symm
    injectiveMoment H raw4153step1 = injectiveMoment H raw4153step2 := by
      have heq : raw4153step2 = (fun i j => raw4153step1 (permutation8 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4153step1 permutation8 permutation3
    _ = injectiveMoment H node29 := by rfl

def raw4154 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![1, -3, 2], ![0, 2, -2], ![1, 1, -2]]

def raw4154step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![1, -3, 2], ![1, 1, -2]]

theorem canonical4154 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4154 = injectiveMoment H node212 := by
  calc
    injectiveMoment H raw4154 = injectiveMoment H raw4154step0 := by
      have heq : raw4154step0 = (fun i j => raw4154 (permutation11 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4154 permutation11 permutation3
    _ = injectiveMoment H node212 := by rfl

def raw4155 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![1, -3, 2], ![0, 3, -3], ![1, 0, -1]]

def raw4155step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![1, -3, 2], ![1, 0, -1]]

theorem canonical4155 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4155 = injectiveMoment H node214 := by
  calc
    injectiveMoment H raw4155 = injectiveMoment H raw4155step0 := by
      have heq : raw4155step0 = (fun i j => raw4155 (permutation11 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4155 permutation11 permutation3
    _ = injectiveMoment H node214 := by rfl

def raw4156 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![1, -3, 2], ![0, 4, -4], ![1, -1, 0]]

def raw4156step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 4, -4], ![1, -3, 2], ![1, -1, 0]]

theorem canonical4156 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4156 = injectiveMoment H node217 := by
  calc
    injectiveMoment H raw4156 = injectiveMoment H raw4156step0 := by
      have heq : raw4156step0 = (fun i j => raw4156 (permutation11 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4156 permutation11 permutation3
    _ = injectiveMoment H node217 := by rfl

def raw4157 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![1, -3, 2], ![1, 3, -4]]

def raw4157step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -3, 3], ![2, 2, -4]]

def raw4157step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, -1, -1], ![0, 3, -3], ![-2, -2, 4]]

def raw4157step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 3, -3], ![2, -1, -1]]

theorem canonical4157 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4157 = injectiveMoment H node32 := by
  calc
    injectiveMoment H raw4157 = injectiveMoment H raw4157step0 := by
      have heq : raw4157step0 = raw4157.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4157).symm
    injectiveMoment H raw4157step0 = injectiveMoment H raw4157step1 := by
      have heq : raw4157step1 = -raw4157step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4157step0).symm
    injectiveMoment H raw4157step1 = injectiveMoment H raw4157step2 := by
      have heq : raw4157step2 = (fun i j => raw4157step1 (permutation8 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4157step1 permutation8 permutation3
    _ = injectiveMoment H node32 := by rfl

def raw4158 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![1, -2, 1], ![0, 4, -4], ![1, -2, 1]]

def raw4158step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 4, -4], ![1, -2, 1], ![1, -2, 1]]

theorem canonical4158 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4158 = injectiveMoment H node218 := by
  calc
    injectiveMoment H raw4158 = injectiveMoment H raw4158step0 := by
      have heq : raw4158step0 = (fun i j => raw4158 (permutation11 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4158 permutation11 permutation3
    _ = injectiveMoment H node218 := by rfl

def raw4159 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![1, -2, 1], ![1, 2, -3]]

def raw4159step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 0, -2], ![-1, 2, -1], ![-1, -2, 3]]

def raw4159step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![2, -1, -1]]

theorem canonical4159 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4159 = injectiveMoment H node36 := by
  calc
    injectiveMoment H raw4159 = injectiveMoment H raw4159step0 := by
      have heq : raw4159step0 = -raw4159 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4159).symm
    injectiveMoment H raw4159step0 = injectiveMoment H raw4159step1 := by
      have heq : raw4159step1 = (fun i j => raw4159step0 (permutation7 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4159step0 permutation7 permutation5
    _ = injectiveMoment H node36 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
