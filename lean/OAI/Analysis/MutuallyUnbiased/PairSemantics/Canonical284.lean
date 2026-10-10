import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes0
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes2
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes4
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes11
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes12
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes19
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes20
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes46
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes48
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes49
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes50
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes51
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes54

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw9088 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, -2, 2], ![-1, 1, 2, -2], ![1, -1, 0, 0]]

def raw9088step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![-2, 2, 0], ![2, -2, 0]]

def raw9088step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1]]

theorem canonical9088 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9088 = injectiveMoment H node291 := by
  calc
    injectiveMoment H raw9088 = injectiveMoment H raw9088step0 := by
      have heq : raw9088step0 = raw9088.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw9088).symm
    injectiveMoment H raw9088step0 = injectiveMoment H raw9088step1 := by
      have heq : raw9088step1 = (fun i j => raw9088step0 (permutation18 i) (permutation7 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9088step0 permutation18 permutation7
    _ = injectiveMoment H node291 := by rfl

def raw9089 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -2, 2], ![-1, 1, 3, -3], ![0, 1, 0, -1], ![1, -2, -1, 2]]

def raw9089step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 1, 1, -2], ![-2, 3, 0, -1], ![2, -3, -1, 2]]

def raw9089step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, -1, -1, 2], ![2, -3, 0, 1], ![-2, 3, 1, -2]]

def raw9089step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, -2, -2, 3]]

theorem canonical9089 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9089 = injectiveMoment H node1317 := by
  calc
    injectiveMoment H raw9089 = injectiveMoment H raw9089step0 := by
      have heq : raw9089step0 = raw9089.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw9089).symm
    injectiveMoment H raw9089step0 = injectiveMoment H raw9089step1 := by
      have heq : raw9089step1 = -raw9089step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9089step0).symm
    injectiveMoment H raw9089step1 = injectiveMoment H raw9089step2 := by
      have heq : raw9089step2 = (fun i j => raw9089step1 (permutation15 i) (permutation22 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9089step1 permutation15 permutation22
    _ = injectiveMoment H node1317 := by rfl

def raw9090 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, -2, 2], ![-1, 2, 2, -3], ![1, -2, 0, 1]]

def raw9090step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![0, 2, -2], ![-2, 2, 0], ![2, -3, 1]]

def raw9090step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 1, -1], ![0, -2, 2], ![2, -2, 0], ![-2, 3, -1]]

def raw9090step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 2, -2], ![2, 0, -2]]

theorem canonical9090 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9090 = injectiveMoment H node169 := by
  calc
    injectiveMoment H raw9090 = injectiveMoment H raw9090step0 := by
      have heq : raw9090step0 = raw9090.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw9090).symm
    injectiveMoment H raw9090step0 = injectiveMoment H raw9090step1 := by
      have heq : raw9090step1 = -raw9090step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9090step0).symm
    injectiveMoment H raw9090step1 = injectiveMoment H raw9090step2 := by
      have heq : raw9090step2 = (fun i j => raw9090step1 (permutation27 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9090step1 permutation27 permutation4
    _ = injectiveMoment H node169 := by rfl

def raw9091 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, -2, 2], ![-1, 2, 3, -4], ![1, -2, -1, 2]]

def raw9091step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![0, 2, -2], ![-2, 3, -1], ![2, -4, 2]]

def raw9091step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 1, -1], ![0, -2, 2], ![2, -3, 1], ![-2, 4, -2]]

def raw9091step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, -1, 1], ![0, 2, -2], ![2, 1, -3]]

theorem canonical9091 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9091 = injectiveMoment H node140 := by
  calc
    injectiveMoment H raw9091 = injectiveMoment H raw9091step0 := by
      have heq : raw9091step0 = raw9091.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw9091).symm
    injectiveMoment H raw9091step0 = injectiveMoment H raw9091step1 := by
      have heq : raw9091step1 = -raw9091step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9091step0).symm
    injectiveMoment H raw9091step1 = injectiveMoment H raw9091step2 := by
      have heq : raw9091step2 = (fun i j => raw9091step1 (permutation27 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9091step1 permutation27 permutation4
    _ = injectiveMoment H node140 := by rfl

def raw9092 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -2, 2], ![0, 0, -1, 1], ![-1, 2, 0, -1], ![1, -2, 3, -2]]

def raw9092step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 2, -2], ![-2, -1, 0, 3], ![2, 1, -1, -2]]

def raw9092step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, -1, 1], ![0, 0, 2, -2], ![1, 2, -1, -2]]

theorem canonical9092 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9092 = injectiveMoment H node796 := by
  calc
    injectiveMoment H raw9092 = injectiveMoment H raw9092step0 := by
      have heq : raw9092step0 = raw9092.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw9092).symm
    injectiveMoment H raw9092step0 = injectiveMoment H raw9092step1 := by
      have heq : raw9092step1 = (fun i j => raw9092step0 (permutation21 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9092step0 permutation21 permutation15
    _ = injectiveMoment H node796 := by rfl

def raw9093 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -2, 2], ![0, 0, -1, 1], ![-1, 2, 3, -4], ![1, -2, 0, 1]]

def raw9093step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 2, -2], ![-2, -1, 3, 0], ![2, 1, -4, 1]]

def raw9093step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, -2, 2], ![2, 1, -3, 0], ![-2, -1, 4, -1]]

def raw9093step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, -1, 1], ![0, 0, 2, -2], ![1, 2, 0, -3]]

theorem canonical9093 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9093 = injectiveMoment H node760 := by
  calc
    injectiveMoment H raw9093 = injectiveMoment H raw9093step0 := by
      have heq : raw9093step0 = raw9093.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw9093).symm
    injectiveMoment H raw9093step0 = injectiveMoment H raw9093step1 := by
      have heq : raw9093step1 = -raw9093step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9093step0).symm
    injectiveMoment H raw9093step1 = injectiveMoment H raw9093step2 := by
      have heq : raw9093step2 = (fun i j => raw9093step1 (permutation27 i) (permutation16 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9093step1 permutation27 permutation16
    _ = injectiveMoment H node760 := by rfl

def raw9094 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -2, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![-2, 2, 0, 0], ![2, -2, 1, -1]]

def raw9094step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 2, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 2, -2], ![2, -2, 0, 0]]

theorem canonical9094 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9094 = injectiveMoment H node3318 := by
  calc
    injectiveMoment H raw9094 = injectiveMoment H raw9094step0 := by
      have heq : raw9094step0 = (fun i j => raw9094 (permutation364 i) (permutation16 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9094 permutation364 permutation16
    _ = injectiveMoment H node3318 := by rfl

def raw9095 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -2, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![-2, 1, 0, 1], ![2, -2, 2, -2]]

def raw9095step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -2, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, -2, 2, -2]]

theorem canonical9095 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9095 = injectiveMoment H node3284 := by
  calc
    injectiveMoment H raw9095 = injectiveMoment H raw9095step0 := by
      have heq : raw9095step0 = (fun i j => raw9095 (permutation258 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9095 permutation258 permutation9
    _ = injectiveMoment H node3284 := by rfl

def raw9096 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -2, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, -2, 0, 0], ![-2, 1, 2, -1]]

def raw9096step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 2, -2], ![0, 1, -1, 0], ![2, -2, 0, 0]]

theorem canonical9096 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9096 = injectiveMoment H node3258 := by
  calc
    injectiveMoment H raw9096 = injectiveMoment H raw9096step0 := by
      have heq : raw9096step0 = (fun i j => raw9096 (permutation357 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9096 permutation357 permutation10
    _ = injectiveMoment H node3258 := by rfl

def raw9097 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -2, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![-2, 2, 0, 0], ![1, -1, 2, -2]]

def raw9097step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 2, 0, 0], ![0, 0, -2, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, -1, 2, -2]]

theorem canonical9097 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9097 = injectiveMoment H node3327 := by
  calc
    injectiveMoment H raw9097 = injectiveMoment H raw9097step0 := by
      have heq : raw9097step0 = (fun i j => raw9097 (permutation258 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9097 permutation258 permutation9
    _ = injectiveMoment H node3327 := by rfl

def raw9098 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -2, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-2, 2, 2, -2]]

def raw9098step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 2, -2, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 2, -2], ![1, -1, 0, 0], ![1, -1, 0, 0]]

theorem canonical9098 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9098 = injectiveMoment H node3313 := by
  calc
    injectiveMoment H raw9098 = injectiveMoment H raw9098step0 := by
      have heq : raw9098step0 = (fun i j => raw9098 (permutation357 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9098 permutation357 permutation10
    _ = injectiveMoment H node3313 := by rfl

def raw9099 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -2, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, -1, 1, -1], ![-2, 2, 1, -1]]

def raw9099step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 2, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 2, -2], ![1, -1, -1, 1], ![1, -1, 0, 0]]

theorem canonical9099 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9099 = injectiveMoment H node3322 := by
  calc
    injectiveMoment H raw9099 = injectiveMoment H raw9099step0 := by
      have heq : raw9099step0 = (fun i j => raw9099 (permutation358 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9099 permutation358 permutation10
    _ = injectiveMoment H node3322 := by rfl

def raw9100 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -2, 2], ![0, 0, -1, 1], ![0, 1, 0, -1], ![0, -1, 3, -2]]

def raw9100step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![-1, 3, -2]]

def raw9100step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0]]

theorem canonical9100 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9100 = injectiveMoment H node272 := by
  calc
    injectiveMoment H raw9100 = injectiveMoment H raw9100step0 := by
      have hz : ∀ i, raw9100 i (permutation9 0) = 0 := by decide +kernel
      have heq : raw9100step0 = (fun i j => raw9100 i (permutation9 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw9100 permutation9 hz
    injectiveMoment H raw9100step0 = injectiveMoment H raw9100step1 := by
      have heq : raw9100step1 = (fun i j => raw9100step0 (permutation29 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9100step0 permutation29 permutation4
    _ = injectiveMoment H node272 := by rfl

def raw9101 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -2, 2], ![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, -2, 0, 0], ![-2, 0, 3, -1]]

def raw9101step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 1, -1], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, -2, 0, 0]]

theorem canonical9101 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9101 = injectiveMoment H node3137 := by
  calc
    injectiveMoment H raw9101 = injectiveMoment H raw9101step0 := by
      have heq : raw9101step0 = (fun i j => raw9101 (permutation331 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9101 permutation331 permutation10
    _ = injectiveMoment H node3137 := by rfl

def raw9102 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -2, 2], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![-2, 1, 1, 0], ![1, -1, 2, -2]]

def raw9102step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, 1, -1], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, -1, -2, 2], ![1, -1, 0, 0]]

theorem canonical9102 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9102 = injectiveMoment H node3296 := by
  calc
    injectiveMoment H raw9102 = injectiveMoment H raw9102step0 := by
      have heq : raw9102step0 = (fun i j => raw9102 (permutation278 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9102 permutation278 permutation10
    _ = injectiveMoment H node3296 := by rfl

def raw9103 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -2, 2], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-2, 1, 3, -2]]

def raw9103step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 1, -1], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, -1, 0, 0]]

theorem canonical9103 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9103 = injectiveMoment H node3244 := by
  calc
    injectiveMoment H raw9103 = injectiveMoment H raw9103step0 := by
      have heq : raw9103step0 = (fun i j => raw9103 (permutation331 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9103 permutation331 permutation10
    _ = injectiveMoment H node3244 := by rfl

def raw9104 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -2, 2], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![-2, 1, 1, 0], ![1, -2, 2, -1]]

def raw9104step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 1, -1], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, -2, 0, 1], ![1, 0, -1, 0]]

theorem canonical9104 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9104 = injectiveMoment H node3268 := by
  calc
    injectiveMoment H raw9104 = injectiveMoment H raw9104step0 := by
      have heq : raw9104step0 = (fun i j => raw9104 (permutation334 i) (permutation16 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9104 permutation334 permutation16
    _ = injectiveMoment H node3268 := by rfl

def raw9105 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -2, 2], ![0, 0, -1, 1], ![0, 2, 2, -4], ![0, -2, 1, 1]]

def raw9105step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, 2, -2], ![0, 0, 1, -1], ![0, -2, -2, 4], ![0, 2, -1, -1]]

def raw9105step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![-2, -2, 4], ![2, -1, -1]]

def raw9105step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 2, -2], ![2, -1, -1]]

theorem canonical9105 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9105 = injectiveMoment H node146 := by
  calc
    injectiveMoment H raw9105 = injectiveMoment H raw9105step0 := by
      have heq : raw9105step0 = -raw9105 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9105).symm
    injectiveMoment H raw9105step0 = injectiveMoment H raw9105step1 := by
      have hz : ∀ i, raw9105step0 i (permutation9 0) = 0 := by decide +kernel
      have heq : raw9105step1 = (fun i j => raw9105step0 i (permutation9 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw9105step0 permutation9 hz
    injectiveMoment H raw9105step1 = injectiveMoment H raw9105step2 := by
      have heq : raw9105step2 = (fun i j => raw9105step1 (permutation23 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9105step1 permutation23 permutation3
    _ = injectiveMoment H node146 := by rfl

def raw9106 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -2, 2], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-2, 0, 1, 1], ![0, 2, 2, -4]]

def raw9106step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 2, -2], ![0, 0, 1, -1], ![-1, 1, 0, 0], ![-1, 1, 0, 0], ![2, 0, -1, -1], ![0, -2, -2, 4]]

def raw9106step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 0, 1, -1], ![0, 0, 2, -2], ![0, 2, -1, -1], ![1, -1, 0, 0], ![1, -1, 0, 0]]

theorem canonical9106 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9106 = injectiveMoment H node3121 := by
  calc
    injectiveMoment H raw9106 = injectiveMoment H raw9106step0 := by
      have heq : raw9106step0 = -raw9106 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9106).symm
    injectiveMoment H raw9106step0 = injectiveMoment H raw9106step1 := by
      have heq : raw9106step1 = (fun i j => raw9106step0 (permutation335 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9106step0 permutation335 permutation15
    _ = injectiveMoment H node3121 := by rfl

def raw9107 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -2, 2], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-2, 0, 2, 0], ![0, 2, 1, -3]]

def raw9107step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 2, -2], ![0, 0, 1, -1], ![-1, 1, 0, 0], ![-1, 1, 0, 0], ![2, 0, -2, 0], ![0, -2, -1, 3]]

def raw9107step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 1, -1], ![0, 0, 2, -2], ![0, 2, -2, 0], ![1, -1, 0, 0], ![1, -1, 0, 0]]

theorem canonical9107 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9107 = injectiveMoment H node3138 := by
  calc
    injectiveMoment H raw9107 = injectiveMoment H raw9107step0 := by
      have heq : raw9107step0 = -raw9107 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9107).symm
    injectiveMoment H raw9107step0 = injectiveMoment H raw9107step1 := by
      have heq : raw9107step1 = (fun i j => raw9107step0 (permutation335 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9107step0 permutation335 permutation15
    _ = injectiveMoment H node3138 := by rfl

def raw9108 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -2, 2], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-2, 1, 0, 1], ![0, 1, 3, -4]]

def raw9108step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -2, 2], ![0, 0, -1, 1], ![0, 1, 3, -4], ![1, -1, 0, 0], ![1, -1, 0, 0]]

theorem canonical9108 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9108 = injectiveMoment H node3285 := by
  calc
    injectiveMoment H raw9108 = injectiveMoment H raw9108step0 := by
      have heq : raw9108step0 = (fun i j => raw9108 (permutation262 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9108 permutation262 permutation9
    _ = injectiveMoment H node3285 := by rfl

def raw9109 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -2, 2], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-1, 0, 2, -1], ![-1, 2, 1, -2]]

def raw9109step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 2, -2], ![0, 0, 1, -1], ![-1, 1, 0, 0], ![-1, 1, 0, 0], ![1, 0, -2, 1], ![1, -2, -1, 2]]

def raw9109step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 1, -1], ![0, 0, 2, -2], ![0, 1, -2, 1], ![1, -1, 0, 0], ![1, -1, 0, 0]]

theorem canonical9109 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9109 = injectiveMoment H node3267 := by
  calc
    injectiveMoment H raw9109 = injectiveMoment H raw9109step0 := by
      have heq : raw9109step0 = -raw9109 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9109).symm
    injectiveMoment H raw9109step0 = injectiveMoment H raw9109step1 := by
      have heq : raw9109step1 = (fun i j => raw9109step0 (permutation335 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9109step0 permutation335 permutation15
    _ = injectiveMoment H node3267 := by rfl

def raw9110 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -2, 2], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-1, 1, 1, -1], ![-1, 1, 2, -2]]

def raw9110step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 1, -2, 2], ![-1, 1, -1, 1], ![0, 0, 1, -1], ![0, 0, 2, -2], ![1, -1, 0, 0], ![1, -1, 0, 0]]

theorem canonical9110 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9110 = injectiveMoment H node3463 := by
  calc
    injectiveMoment H raw9110 = injectiveMoment H raw9110step0 := by
      have heq : raw9110step0 = (fun i j => raw9110 (permutation398 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9110 permutation398 permutation10
    _ = injectiveMoment H node3463 := by rfl

def raw9111 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -2, 2], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, -1, 0, 0], ![0, 0, 2, -2], ![-2, 2, 1, -1]]

def raw9111step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 2, -1, 1], ![0, 0, -2, 2], ![0, 0, 1, -1], ![0, 0, 2, -2], ![1, -1, 0, 0], ![1, -1, 0, 0]]

theorem canonical9111 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9111 = injectiveMoment H node3316 := by
  calc
    injectiveMoment H raw9111 = injectiveMoment H raw9111step0 := by
      have heq : raw9111step0 = (fun i j => raw9111 (permutation398 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9111 permutation398 permutation10
    _ = injectiveMoment H node3316 := by rfl

def raw9112 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -2, 2], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-1, -1, 1, 1], ![-1, 2, 2, -3]]

def raw9112step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 2, -2], ![0, 0, 1, -1], ![-1, 1, 0, 0], ![-1, 0, 0, 1], ![1, 1, -1, -1], ![1, -2, -2, 3]]

def raw9112step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, -1, 0, 1], ![0, 0, 1, -1], ![0, 0, 2, -2], ![1, -1, 0, 0], ![1, 1, -1, -1]]

theorem canonical9112 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9112 = injectiveMoment H node3225 := by
  calc
    injectiveMoment H raw9112 = injectiveMoment H raw9112step0 := by
      have heq : raw9112step0 = -raw9112 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9112).symm
    injectiveMoment H raw9112step0 = injectiveMoment H raw9112step1 := by
      have heq : raw9112step1 = (fun i j => raw9112step0 (permutation377 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9112step0 permutation377 permutation15
    _ = injectiveMoment H node3225 := by rfl

def raw9113 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -2, 2], ![0, 0, 1, -1], ![-1, 1, 0, 0], ![1, -1, 1, -1]]

def raw9113step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![-2, 1, 0, 1], ![2, -1, 0, -1]]

def raw9113step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 1, 0], ![0, 1, -1, 0], ![1, 0, 1, -2]]

theorem canonical9113 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9113 = injectiveMoment H node1241 := by
  calc
    injectiveMoment H raw9113 = injectiveMoment H raw9113step0 := by
      have heq : raw9113step0 = raw9113.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw9113).symm
    injectiveMoment H raw9113step0 = injectiveMoment H raw9113step1 := by
      have heq : raw9113step1 = (fun i j => raw9113step0 (permutation27 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9113step0 permutation27 permutation18
    _ = injectiveMoment H node1241 := by rfl

def raw9114 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -2, 2], ![0, 0, 1, -1], ![-1, 1, 1, -1], ![1, -1, 0, 0]]

def raw9114step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![-2, 1, 1, 0], ![2, -1, -1, 0]]

def raw9114step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 1, 0], ![0, 1, -1, 0], ![1, 0, 1, -2]]

theorem canonical9114 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9114 = injectiveMoment H node1241 := by
  calc
    injectiveMoment H raw9114 = injectiveMoment H raw9114step0 := by
      have heq : raw9114step0 = raw9114.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw9114).symm
    injectiveMoment H raw9114step0 = injectiveMoment H raw9114step1 := by
      have heq : raw9114step1 = (fun i j => raw9114step0 (permutation29 i) (permutation20 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9114step0 permutation29 permutation20
    _ = injectiveMoment H node1241 := by rfl

def raw9115 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -2, 2], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 0, 0, 0]]

def raw9115step0 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, -2, 2], ![0, 0, 1, -1], ![0, 0, 1, -1]]

def raw9115step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, -2, 2], ![0, 1, -1], ![0, 1, -1]]

def raw9115step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]

theorem canonical9115 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9115 = injectiveMoment H node11 := by
  calc
    injectiveMoment H raw9115 = injectiveMoment H raw9115step0 := by
      have hz : ∀ j, raw9115 (permutation27 0) j = 0 := by decide +kernel
      have heq : raw9115step0 = (fun i j => raw9115 (permutation27 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9115 permutation27 hz
    injectiveMoment H raw9115step0 = injectiveMoment H raw9115step1 := by
      have hz : ∀ i, raw9115step0 i (permutation15 0) = 0 := by decide +kernel
      have heq : raw9115step1 = (fun i j => raw9115step0 i (permutation15 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw9115step0 permutation15 hz
    injectiveMoment H raw9115step1 = injectiveMoment H raw9115step2 := by
      have hz : ∀ i, raw9115step1 i (permutation3 0) = 0 := by decide +kernel
      have heq : raw9115step2 = (fun i j => raw9115step1 i (permutation3 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw9115step1 permutation3 hz
    _ = injectiveMoment H node11 := by rfl

def raw9116 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -2, 2], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![-2, 1, 0, 1], ![2, -2, 0, 0]]

def raw9116step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 1, 1], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, 0, 0, -1], ![1, 0, 0, -1]]

theorem canonical9116 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9116 = injectiveMoment H node3154 := by
  calc
    injectiveMoment H raw9116 = injectiveMoment H raw9116step0 := by
      have heq : raw9116step0 = (fun i j => raw9116 (permutation194 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9116 permutation194 permutation21
    _ = injectiveMoment H node3154 := by rfl

def raw9117 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -2, 2], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![-2, 1, 1, 0], ![2, -2, -1, 1]]

def raw9117step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 2, -2], ![0, 1, -1, 0], ![2, -2, 1, -1]]

theorem canonical9117 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9117 = injectiveMoment H node3289 := by
  calc
    injectiveMoment H raw9117 = injectiveMoment H raw9117step0 := by
      have heq : raw9117step0 = (fun i j => raw9117 (permutation280 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9117 permutation280 permutation10
    _ = injectiveMoment H node3289 := by rfl

def raw9118 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -2, 2], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![-2, -1, 0, 3], ![1, 2, 0, -3]]

def raw9118step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, -2, 2], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 2, 0, -3]]

theorem canonical9118 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9118 = injectiveMoment H node2980 := by
  calc
    injectiveMoment H raw9118 = injectiveMoment H raw9118step0 := by
      have heq : raw9118step0 = (fun i j => raw9118 (permutation258 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9118 permutation258 permutation9
    _ = injectiveMoment H node2980 := by rfl

def raw9119 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -2, 2], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-2, 2, 0, 0]]

def raw9119step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 2, 0], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 0, 0, -1]]

theorem canonical9119 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9119 = injectiveMoment H node3155 := by
  calc
    injectiveMoment H raw9119 = injectiveMoment H raw9119step0 := by
      have heq : raw9119step0 = (fun i j => raw9119 (permutation308 i) (permutation12 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9119 permutation308 permutation12
    _ = injectiveMoment H node3155 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
