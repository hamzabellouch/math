import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes45
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes46
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes47
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes48
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes49
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes50
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes51
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes52
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes53

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw9568 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -2, 0, 1], ![-2, 0, 0, 2], ![1, 0, 3, -4]]

def raw9568step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -2, 0, 1], ![1, 0, 3, -4]]

theorem canonical9568 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9568 = injectiveMoment H node3185 := by
  calc
    injectiveMoment H raw9568 = injectiveMoment H raw9568step0 := by
      have heq : raw9568step0 = (fun i j => raw9568 (permutation258 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9568 permutation258 permutation9
    _ = injectiveMoment H node3185 := by rfl

def raw9569 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 0, 0], ![-2, -1, 0, 3], ![1, 0, 3, -4]]

def raw9569step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 3, -4]]

theorem canonical9569 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9569 = injectiveMoment H node2988 := by
  calc
    injectiveMoment H raw9569 = injectiveMoment H raw9569step0 := by
      have heq : raw9569step0 = (fun i j => raw9569 (permutation258 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9569 permutation258 permutation9
    _ = injectiveMoment H node2988 := by rfl

def raw9570 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 0, 0], ![-2, 0, 0, 2], ![1, -1, 3, -3]]

def raw9570step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, -1, 3, -3]]

theorem canonical9570 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9570 = injectiveMoment H node3188 := by
  calc
    injectiveMoment H raw9570 = injectiveMoment H raw9570step0 := by
      have heq : raw9570step0 = (fun i j => raw9570 (permutation258 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9570 permutation258 permutation9
    _ = injectiveMoment H node3188 := by rfl

def raw9571 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 0, 0], ![-1, -1, 0, 2], ![0, 0, 3, -3]]

def raw9571step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 0, 3, -3], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 0, 0]]

theorem canonical9571 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9571 = injectiveMoment H node3395 := by
  calc
    injectiveMoment H raw9571 = injectiveMoment H raw9571step0 := by
      have heq : raw9571step0 = (fun i j => raw9571 (permutation275 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9571 permutation275 permutation9
    _ = injectiveMoment H node3395 := by rfl

def raw9572 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -2, 0, 1], ![1, 0, 0, -1], ![-2, 0, 2, 0]]

def raw9572step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 1, -2, 0]]

theorem canonical9572 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9572 = injectiveMoment H node3174 := by
  calc
    injectiveMoment H raw9572 = injectiveMoment H raw9572step0 := by
      have heq : raw9572step0 = (fun i j => raw9572 (permutation358 i) (permutation13 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9572 permutation358 permutation13
    _ = injectiveMoment H node3174 := by rfl

def raw9573 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 0, 0], ![-2, -1, 0, 3], ![1, 0, 2, -3]]

def raw9573step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, -1, 1, 0], ![0, -1, 0, 1], ![-1, 1, 0, 0], ![2, 1, 0, -3], ![-1, 0, -2, 3]]

def raw9573step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, 0, -1, 0], ![1, 0, 0, -1]]

theorem canonical9573 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9573 = injectiveMoment H node2962 := by
  calc
    injectiveMoment H raw9573 = injectiveMoment H raw9573step0 := by
      have heq : raw9573step0 = -raw9573 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9573).symm
    injectiveMoment H raw9573step0 = injectiveMoment H raw9573step1 := by
      have heq : raw9573step1 = (fun i j => raw9573step0 (permutation388 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9573step0 permutation388 permutation21
    _ = injectiveMoment H node2962 := by rfl

def raw9574 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 0, 0], ![-2, 0, 0, 2], ![1, -1, 2, -2]]

def raw9574step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, -1, 1, 0], ![0, -1, 0, 1], ![-1, 1, 0, 0], ![2, 0, 0, -2], ![-1, 1, -2, 2]]

def raw9574step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 2, 0, -2], ![1, 0, -1, 0], ![1, 0, 0, -1]]

theorem canonical9574 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9574 = injectiveMoment H node3041 := by
  calc
    injectiveMoment H raw9574 = injectiveMoment H raw9574step0 := by
      have heq : raw9574step0 = -raw9574 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9574).symm
    injectiveMoment H raw9574step0 = injectiveMoment H raw9574step1 := by
      have heq : raw9574step1 = (fun i j => raw9574step0 (permutation388 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9574step0 permutation388 permutation21
    _ = injectiveMoment H node3041 := by rfl

def raw9575 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-2, 0, 2, 0]]

def raw9575step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 2, 0], ![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -1, 0]]

theorem canonical9575 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9575 = injectiveMoment H node3437 := by
  calc
    injectiveMoment H raw9575 = injectiveMoment H raw9575step0 := by
      have heq : raw9575step0 = (fun i j => raw9575 (permutation237 i) (permutation28 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9575 permutation237 permutation28
    _ = injectiveMoment H node3437 := by rfl

def raw9576 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-2, -1, 2, 1]]

def raw9576step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -1, 0]]

theorem canonical9576 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9576 = injectiveMoment H node3083 := by
  calc
    injectiveMoment H raw9576 = injectiveMoment H raw9576step0 := by
      have heq : raw9576step0 = (fun i j => raw9576 (permutation314 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9576 permutation314 permutation10
    _ = injectiveMoment H node3083 := by rfl

def raw9577 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, -2, 0, 1], ![-2, 0, 3, -1]]

def raw9577step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 1, -2, 0]]

theorem canonical9577 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9577 = injectiveMoment H node2968 := by
  calc
    injectiveMoment H raw9577 = injectiveMoment H raw9577step0 := by
      have heq : raw9577step0 = (fun i j => raw9577 (permutation357 i) (permutation13 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9577 permutation357 permutation13
    _ = injectiveMoment H node2968 := by rfl

def raw9578 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, -1, 1, -1], ![-2, -1, 2, 1]]

def raw9578step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 0, 0, -1]]

theorem canonical9578 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9578 = injectiveMoment H node3082 := by
  calc
    injectiveMoment H raw9578 = injectiveMoment H raw9578step0 := by
      have heq : raw9578step0 = (fun i j => raw9578 (permutation315 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9578 permutation315 permutation10
    _ = injectiveMoment H node3082 := by rfl

def raw9579 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, 0, -1], ![-2, -1, 0, 3], ![1, -1, 2, -2]]

def raw9579step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 2, -2], ![1, 0, 0, -1]]

theorem canonical9579 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9579 = injectiveMoment H node2989 := by
  calc
    injectiveMoment H raw9579 = injectiveMoment H raw9579step0 := by
      have heq : raw9579step0 = (fun i j => raw9579 (permutation259 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9579 permutation259 permutation9
    _ = injectiveMoment H node2989 := by rfl

def raw9580 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, 0, -1], ![-2, 0, 3, -1], ![1, -2, -1, 2]]

def raw9580step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -2, 2, -1], ![1, 0, -1, 0]]

theorem canonical9580 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9580 = injectiveMoment H node3144 := by
  calc
    injectiveMoment H raw9580 = injectiveMoment H raw9580step0 := by
      have heq : raw9580step0 = (fun i j => raw9580 (permutation265 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9580 permutation265 permutation10
    _ = injectiveMoment H node3144 := by rfl

def raw9581 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, -1, 1, -1], ![-2, -1, 1, 2]]

def raw9581step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 0, 0, -1]]

theorem canonical9581 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9581 = injectiveMoment H node3076 := by
  calc
    injectiveMoment H raw9581 = injectiveMoment H raw9581step0 := by
      have heq : raw9581step0 = (fun i j => raw9581 (permutation309 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9581 permutation309 permutation9
    _ = injectiveMoment H node3076 := by rfl

def raw9582 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 0, 0, -1], ![-2, -2, 2, 2]]

def raw9582step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 0, 0, -1]]

theorem canonical9582 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9582 = injectiveMoment H node2894 := by
  calc
    injectiveMoment H raw9582 = injectiveMoment H raw9582step0 := by
      have heq : raw9582step0 = (fun i j => raw9582 (permutation308 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9582 permutation308 permutation9
    _ = injectiveMoment H node2894 := by rfl

def raw9583 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -2, 0, 1], ![1, 0, -1, 0], ![-2, 0, 0, 2], ![0, 1, 3, -4]]

def raw9583step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, -2, 0, 1], ![1, 0, -1, 0]]

theorem canonical9583 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9583 = injectiveMoment H node3191 := by
  calc
    injectiveMoment H raw9583 = injectiveMoment H raw9583step0 := by
      have heq : raw9583step0 = (fun i j => raw9583 (permutation262 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9583 permutation262 permutation9
    _ = injectiveMoment H node3191 := by rfl

def raw9584 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, -1, 0, 0], ![-2, 0, 0, 2], ![0, 1, 3, -4]]

def raw9584step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, -1, -1, 1], ![1, -1, 0, 0]]

theorem canonical9584 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9584 = injectiveMoment H node3192 := by
  calc
    injectiveMoment H raw9584 = injectiveMoment H raw9584step0 := by
      have heq : raw9584step0 = (fun i j => raw9584 (permutation262 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9584 permutation262 permutation9
    _ = injectiveMoment H node3192 := by rfl

def raw9585 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, 0, 0, -1], ![-2, 1, 0, 1], ![0, -1, 3, -2]]

def raw9585step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, 3, -2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, 0, 0, -1]]

theorem canonical9585 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9585 = injectiveMoment H node3281 := by
  calc
    injectiveMoment H raw9585 = injectiveMoment H raw9585step0 := by
      have heq : raw9585step0 = (fun i j => raw9585 (permutation294 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9585 permutation294 permutation9
    _ = injectiveMoment H node3281 := by rfl

def raw9586 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, 0, 0, -1], ![-1, -1, 0, 2], ![-1, 1, 3, -3]]

def raw9586step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![-1, 1, -1, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -1, 3, -3], ![1, 0, -1, 0]]

theorem canonical9586 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9586 = injectiveMoment H node3380 := by
  calc
    injectiveMoment H raw9586 = injectiveMoment H raw9586step0 := by
      have heq : raw9586step0 = (fun i j => raw9586 (permutation285 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9586 permutation285 permutation15
    _ = injectiveMoment H node3380 := by rfl

def raw9587 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![0, -1, 0, 1], ![-1, 0, -1, 2], ![0, 1, 3, -4]]

def raw9587step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, -1, 0, 0]]

theorem canonical9587 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9587 = injectiveMoment H node3420 := by
  calc
    injectiveMoment H raw9587 = injectiveMoment H raw9587step0 := by
      have heq : raw9587step0 = (fun i j => raw9587 (permutation289 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9587 permutation289 permutation9
    _ = injectiveMoment H node3420 := by rfl

def raw9588 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![0, 0, -1, 1], ![-1, -1, 0, 2], ![0, 1, 3, -4]]

def raw9588step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, -1, 0, 0]]

theorem canonical9588 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9588 = injectiveMoment H node3394 := by
  calc
    injectiveMoment H raw9588 = injectiveMoment H raw9588step0 := by
      have heq : raw9588step0 = (fun i j => raw9588 (permutation271 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9588 permutation271 permutation9
    _ = injectiveMoment H node3394 := by rfl

def raw9589 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, -1, -1, 1], ![-2, 0, 0, 2], ![0, 1, 3, -4]]

def raw9589step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, -1, -1, 1], ![1, -1, 0, 0]]

theorem canonical9589 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9589 = injectiveMoment H node3192 := by
  calc
    injectiveMoment H raw9589 = injectiveMoment H raw9589step0 := by
      have heq : raw9589step0 = (fun i j => raw9589 (permutation263 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9589 permutation263 permutation9
    _ = injectiveMoment H node3192 := by rfl

def raw9590 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-2, 0, -1, 3], ![0, 1, 3, -4]]

def raw9590step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, -1, 0, 0], ![1, -1, 0, 0]]

theorem canonical9590 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9590 = injectiveMoment H node3133 := by
  calc
    injectiveMoment H raw9590 = injectiveMoment H raw9590step0 := by
      have heq : raw9590step0 = (fun i j => raw9590 (permutation262 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9590 permutation262 permutation9
    _ = injectiveMoment H node3133 := by rfl

def raw9591 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-2, 0, 0, 2], ![0, 1, 2, -3]]

def raw9591step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, -1, 1, 0], ![-1, 1, 0, 0], ![-1, 1, 0, 0], ![2, 0, 0, -2], ![0, -1, -2, 3]]

def raw9591step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 0, -1]]

theorem canonical9591 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9591 = injectiveMoment H node3017 := by
  calc
    injectiveMoment H raw9591 = injectiveMoment H raw9591step0 := by
      have heq : raw9591step0 = -raw9591 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9591).symm
    injectiveMoment H raw9591step0 = injectiveMoment H raw9591step1 := by
      have heq : raw9591step1 = (fun i j => raw9591step0 (permutation405 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9591step0 permutation405 permutation23
    _ = injectiveMoment H node3017 := by rfl

def raw9592 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-2, 1, -1, 2], ![0, 0, 3, -3]]

def raw9592step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -1, 1], ![0, 0, 3, -3], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, -1, 0, 0]]

theorem canonical9592 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9592 = injectiveMoment H node3263 := by
  calc
    injectiveMoment H raw9592 = injectiveMoment H raw9592step0 := by
      have heq : raw9592step0 = (fun i j => raw9592 (permutation275 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9592 permutation275 permutation9
    _ = injectiveMoment H node3263 := by rfl

def raw9593 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-1, 0, -1, 2], ![-1, 1, 3, -3]]

def raw9593step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![-1, 1, 3, -3], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, -1, 0, 0]]

theorem canonical9593 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9593 = injectiveMoment H node3418 := by
  calc
    injectiveMoment H raw9593 = injectiveMoment H raw9593step0 := by
      have heq : raw9593step0 = (fun i j => raw9593 (permutation294 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9593 permutation294 permutation9
    _ = injectiveMoment H node3418 := by rfl

def raw9594 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-2, -1, 0, 3], ![0, 1, 3, -4]]

def raw9594step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, -1, 0, 0], ![1, 0, -1, 0]]

theorem canonical9594 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9594 = injectiveMoment H node2991 := by
  calc
    injectiveMoment H raw9594 = injectiveMoment H raw9594step0 := by
      have heq : raw9594step0 = (fun i j => raw9594 (permutation262 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9594 permutation262 permutation9
    _ = injectiveMoment H node2991 := by rfl

def raw9595 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-2, 0, 0, 2], ![0, 0, 3, -3]]

def raw9595step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, -1, 1, 0], ![-1, 1, 0, 0], ![-1, 0, 1, 0], ![2, 0, 0, -2], ![0, 0, -3, 3]]

def raw9595step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 0, 3, -3], ![0, 2, -2, 0], ![1, -1, 0, 0]]

theorem canonical9595 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9595 = injectiveMoment H node3443 := by
  calc
    injectiveMoment H raw9595 = injectiveMoment H raw9595step0 := by
      have heq : raw9595step0 = -raw9595 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9595).symm
    injectiveMoment H raw9595step0 = injectiveMoment H raw9595step1 := by
      have heq : raw9595step1 = (fun i j => raw9595step0 (permutation212 i) (permutation16 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9595step0 permutation212 permutation16
    _ = injectiveMoment H node3443 := by rfl

def raw9596 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-2, 1, 0, 1], ![0, -1, 3, -2]]

def raw9596step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 1, -2, 0]]

theorem canonical9596 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9596 = injectiveMoment H node2968 := by
  calc
    injectiveMoment H raw9596 = injectiveMoment H raw9596step0 := by
      have heq : raw9596step0 = (fun i j => raw9596 (permutation364 i) (permutation29 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9596 permutation364 permutation29
    _ = injectiveMoment H node2968 := by rfl

def raw9597 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-1, -1, 0, 2], ![-1, 1, 3, -3]]

def raw9597step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![-1, 1, 0, 0], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 3, -3], ![1, 0, -1, 0]]

theorem canonical9597 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9597 = injectiveMoment H node3385 := by
  calc
    injectiveMoment H raw9597 = injectiveMoment H raw9597step0 := by
      have heq : raw9597step0 = (fun i j => raw9597 (permutation285 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9597 permutation285 permutation15
    _ = injectiveMoment H node3385 := by rfl

def raw9598 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-2, -1, 0, 3], ![0, 1, 2, -3]]

def raw9598step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, -1, 0, 0], ![1, 0, 0, -1]]

theorem canonical9598 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9598 = injectiveMoment H node2990 := by
  calc
    injectiveMoment H raw9598 = injectiveMoment H raw9598step0 := by
      have heq : raw9598step0 = (fun i j => raw9598 (permutation262 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9598 permutation262 permutation9
    _ = injectiveMoment H node2990 := by rfl

def raw9599 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-2, 1, -1, 2], ![0, -1, 3, -2]]

def raw9599step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -1, 3, -2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 0, -1]]

theorem canonical9599 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9599 = injectiveMoment H node3251 := by
  calc
    injectiveMoment H raw9599 = injectiveMoment H raw9599step0 := by
      have heq : raw9599step0 = (fun i j => raw9599 (permutation294 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9599 permutation294 permutation9
    _ = injectiveMoment H node3251 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
