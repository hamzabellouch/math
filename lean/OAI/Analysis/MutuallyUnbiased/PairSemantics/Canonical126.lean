import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes0
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes2
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes3
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes4
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes5
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes8
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes9
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes10
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes33

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw4032 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, 1, -2]]

theorem canonical4032 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4032 = injectiveMoment H node647 := by
  rfl

def raw4033 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1]]

def raw4033step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![2, 0, -2]]

theorem canonical4033 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4033 = injectiveMoment H node641 := by
  calc
    injectiveMoment H raw4033 = injectiveMoment H raw4033step0 := by
      have heq : raw4033step0 = (fun i j => raw4033 (permutation60 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4033 permutation60 permutation5
    _ = injectiveMoment H node641 := by rfl

def raw4034 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 2, -2], ![2, 0, -2]]

theorem canonical4034 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4034 = injectiveMoment H node197 := by
  rfl

def raw4035 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1]]

theorem canonical4035 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4035 = injectiveMoment H node648 := by
  rfl

def raw4036 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 3, -3], ![1, 0, -1], ![1, -1, 0]]

def raw4036step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1]]

theorem canonical4036 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4036 = injectiveMoment H node648 := by
  calc
    injectiveMoment H raw4036 = injectiveMoment H raw4036step0 := by
      have heq : raw4036step0 = (fun i j => raw4036 (permutation34 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4036 permutation34 permutation3
    _ = injectiveMoment H node648 := by rfl

def raw4037 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 3, -3], ![2, -1, -1]]

theorem canonical4037 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4037 = injectiveMoment H node198 := by
  rfl

def raw4038 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 4, -4], ![1, -2, 1], ![1, 0, -1]]

theorem canonical4038 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4038 = injectiveMoment H node649 := by
  rfl

def raw4039 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 4, -4], ![1, -1, 0], ![1, -1, 0]]

theorem canonical4039 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4039 = injectiveMoment H node650 := by
  rfl

def raw4040 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 4, -4], ![2, -2, 0]]

theorem canonical4040 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4040 = injectiveMoment H node199 := by
  rfl

def raw4041 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![1, -2, 1], ![1, 4, -5]]

theorem canonical4041 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4041 = injectiveMoment H node200 := by
  rfl

def raw4042 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![1, -1, 0], ![1, 3, -4]]

theorem canonical4042 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4042 = injectiveMoment H node201 := by
  rfl

def raw4043 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![1, 0, -1], ![1, 2, -3]]

def raw4043step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![0, 2, -2], ![-1, 0, 1], ![-1, -2, 3]]

def raw4043step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 2, -2], ![2, 0, -2]]

theorem canonical4043 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4043 = injectiveMoment H node169 := by
  calc
    injectiveMoment H raw4043 = injectiveMoment H raw4043step0 := by
      have heq : raw4043step0 = -raw4043 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4043).symm
    injectiveMoment H raw4043step0 = injectiveMoment H raw4043step1 := by
      have heq : raw4043step1 = (fun i j => raw4043step0 (permutation31 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4043step0 permutation31 permutation5
    _ = injectiveMoment H node169 := by rfl

def raw4044 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![1, 1, -2], ![1, 1, -2]]

theorem canonical4044 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4044 = injectiveMoment H node202 := by
  rfl

def raw4045 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![1, 2, -3], ![1, 0, -1]]

def raw4045step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![0, 2, -2], ![-1, -2, 3], ![-1, 0, 1]]

def raw4045step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 2, -2], ![2, 0, -2]]

theorem canonical4045 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4045 = injectiveMoment H node169 := by
  calc
    injectiveMoment H raw4045 = injectiveMoment H raw4045step0 := by
      have heq : raw4045step0 = -raw4045 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4045).symm
    injectiveMoment H raw4045step0 = injectiveMoment H raw4045step1 := by
      have heq : raw4045step1 = (fun i j => raw4045step0 (permutation25 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4045step0 permutation25 permutation5
    _ = injectiveMoment H node169 := by rfl

def raw4046 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![1, 3, -4], ![1, -1, 0]]

def raw4046step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![1, -1, 0], ![1, 3, -4]]

theorem canonical4046 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4046 = injectiveMoment H node201 := by
  calc
    injectiveMoment H raw4046 = injectiveMoment H raw4046step0 := by
      have heq : raw4046step0 = (fun i j => raw4046 (permutation10 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4046 permutation10 permutation3
    _ = injectiveMoment H node201 := by rfl

def raw4047 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![1, 4, -5], ![1, -2, 1]]

def raw4047step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![1, -2, 1], ![1, 4, -5]]

theorem canonical4047 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4047 = injectiveMoment H node200 := by
  calc
    injectiveMoment H raw4047 = injectiveMoment H raw4047step0 := by
      have heq : raw4047step0 = (fun i j => raw4047 (permutation10 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4047 permutation10 permutation3
    _ = injectiveMoment H node200 := by rfl

def raw4048 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![2, 2, -4]]

def raw4048step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 0, -2], ![0, 2, -2], ![-2, -2, 4]]

def raw4048step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![2, 0, -2]]

theorem canonical4048 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4048 = injectiveMoment H node31 := by
  calc
    injectiveMoment H raw4048 = injectiveMoment H raw4048step0 := by
      have heq : raw4048step0 = -raw4048 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4048).symm
    injectiveMoment H raw4048step0 = injectiveMoment H raw4048step1 := by
      have heq : raw4048step1 = (fun i j => raw4048step0 (permutation8 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4048step0 permutation8 permutation3
    _ = injectiveMoment H node31 := by rfl

def raw4049 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![-1, 2, -1], ![1, 1, -2], ![2, -2, 0]]

def raw4049step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]

theorem canonical4049 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4049 = injectiveMoment H node624 := by
  calc
    injectiveMoment H raw4049 = injectiveMoment H raw4049step0 := by
      have heq : raw4049step0 = (fun i j => raw4049 (permutation134 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4049 permutation134 permutation6
    _ = injectiveMoment H node624 := by rfl

def raw4050 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![-1, 3, -2], ![1, 0, -1], ![2, -2, 0]]

def raw4050step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![1, -3, 2], ![-1, 0, 1], ![-2, 2, 0]]

def raw4050step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]

theorem canonical4050 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4050 = injectiveMoment H node369 := by
  calc
    injectiveMoment H raw4050 = injectiveMoment H raw4050step0 := by
      have heq : raw4050step0 = -raw4050 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4050).symm
    injectiveMoment H raw4050step0 = injectiveMoment H raw4050step1 := by
      have heq : raw4050step1 = (fun i j => raw4050step0 (permutation92 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4050step0 permutation92 permutation5
    _ = injectiveMoment H node369 := by rfl

def raw4051 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, -2, 2], ![1, -1, 0], ![1, 4, -5]]

def raw4051step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 4, -5]]

theorem canonical4051 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4051 = injectiveMoment H node638 := by
  calc
    injectiveMoment H raw4051 = injectiveMoment H raw4051step0 := by
      have heq : raw4051step0 = (fun i j => raw4051 (permutation39 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4051 permutation39 permutation3
    _ = injectiveMoment H node638 := by rfl

def raw4052 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, -2, 2], ![1, 0, -1], ![1, 3, -4]]

def raw4052step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 3, -4]]

theorem canonical4052 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4052 = injectiveMoment H node639 := by
  calc
    injectiveMoment H raw4052 = injectiveMoment H raw4052step0 := by
      have heq : raw4052step0 = (fun i j => raw4052 (permutation39 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4052 permutation39 permutation3
    _ = injectiveMoment H node639 := by rfl

def raw4053 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 4, -5]]

theorem canonical4053 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4053 = injectiveMoment H node2123 := by
  rfl

def raw4054 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 2, -3]]

theorem canonical4054 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4054 = injectiveMoment H node2128 := by
  rfl

def raw4055 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, -1, 1], ![1, -2, 1], ![1, 4, -5]]

theorem canonical4055 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4055 = injectiveMoment H node652 := by
  rfl

def raw4056 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![0, 4, -4]]

def raw4056step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, -1, 1], ![0, 4, -4], ![1, -1, 0], ![1, -1, 0]]

theorem canonical4056 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4056 = injectiveMoment H node2134 := by
  calc
    injectiveMoment H raw4056 = injectiveMoment H raw4056step0 := by
      have heq : raw4056step0 = (fun i j => raw4056 (permutation155 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4056 permutation155 permutation3
    _ = injectiveMoment H node2134 := by rfl

def raw4057 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![0, 3, -3]]

def raw4057step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1]]

theorem canonical4057 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4057 = injectiveMoment H node2132 := by
  calc
    injectiveMoment H raw4057 = injectiveMoment H raw4057step0 := by
      have heq : raw4057step0 = (fun i j => raw4057 (permutation155 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4057 permutation155 permutation3
    _ = injectiveMoment H node2132 := by rfl

def raw4058 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 3, -4]]

theorem canonical4058 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4058 = injectiveMoment H node653 := by
  rfl

def raw4059 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 2, -3]]

def raw4059step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![0, 1, -1], ![-1, 0, 1], ![-1, -2, 3]]

def raw4059step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1]]

theorem canonical4059 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4059 = injectiveMoment H node562 := by
  calc
    injectiveMoment H raw4059 = injectiveMoment H raw4059step0 := by
      have heq : raw4059step0 = -raw4059 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4059).symm
    injectiveMoment H raw4059step0 = injectiveMoment H raw4059step1 := by
      have heq : raw4059step1 = (fun i j => raw4059step0 (permutation145 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4059step0 permutation145 permutation5
    _ = injectiveMoment H node562 := by rfl

def raw4060 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![2, 0, -2]]

def raw4060step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2]]

def raw4060step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1]]

theorem canonical4060 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4060 = injectiveMoment H node291 := by
  calc
    injectiveMoment H raw4060 = injectiveMoment H raw4060step0 := by
      have hz : ∀ j, raw4060 (permutation80 0) j = 0 := by decide +kernel
      have heq : raw4060step0 = (fun i j => raw4060 (permutation80 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw4060 permutation80 hz
    injectiveMoment H raw4060step0 = injectiveMoment H raw4060step1 := by
      have heq : raw4060step1 = (fun i j => raw4060step0 (permutation16 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4060step0 permutation16 permutation5
    _ = injectiveMoment H node291 := by rfl

def raw4061 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 0, 0], ![0, 2, -2], ![2, -1, -1]]

def raw4061step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]

theorem canonical4061 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4061 = injectiveMoment H node203 := by
  calc
    injectiveMoment H raw4061 = injectiveMoment H raw4061step0 := by
      have hz : ∀ j, raw4061 (permutation80 0) j = 0 := by decide +kernel
      have heq : raw4061step0 = (fun i j => raw4061 (permutation80 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw4061 permutation80 hz
    _ = injectiveMoment H node203 := by rfl

def raw4062 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 0, 0], ![1, -2, 1], ![1, 3, -4]]

def raw4062step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![1, -2, 1], ![1, 3, -4]]

theorem canonical4062 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4062 = injectiveMoment H node206 := by
  calc
    injectiveMoment H raw4062 = injectiveMoment H raw4062step0 := by
      have hz : ∀ j, raw4062 (permutation80 0) j = 0 := by decide +kernel
      have heq : raw4062step0 = (fun i j => raw4062 (permutation80 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw4062 permutation80 hz
    _ = injectiveMoment H node206 := by rfl

def raw4063 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![1, 2, -3]]

def raw4063step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![-1, -2, 3]]

def raw4063step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![-1, 1, 0], ![-1, -2, 3]]

def raw4063step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]

theorem canonical4063 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4063 = injectiveMoment H node185 := by
  calc
    injectiveMoment H raw4063 = injectiveMoment H raw4063step0 := by
      have heq : raw4063step0 = -raw4063 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4063).symm
    injectiveMoment H raw4063step0 = injectiveMoment H raw4063step1 := by
      have hz : ∀ j, raw4063step0 (permutation80 0) j = 0 := by decide +kernel
      have heq : raw4063step1 = (fun i j => raw4063step0 (permutation80 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw4063step0 permutation80 hz
    injectiveMoment H raw4063step1 = injectiveMoment H raw4063step2 := by
      have heq : raw4063step2 = (fun i j => raw4063step1 (permutation28 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4063step1 permutation28 permutation5
    _ = injectiveMoment H node185 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
