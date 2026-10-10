import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes1
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes2
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes3
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes4
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes6
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes7
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes8
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes10
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes12
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes13
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes15
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes16

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw2624 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, 2, -3, 1], ![1, -1, 1, -1], ![1, 0, 0, -1]]

def raw2624step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 2, -1, 0], ![2, -3, 1, 0], ![1, 1, -1, -1]]

def raw2624step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![1, -2, 1, 0], ![-2, 3, -1, 0], ![-1, -1, 1, 1]]

def raw2624step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 3, -2], ![0, 1, -2, 1], ![1, 1, -1, -1]]

theorem canonical2624 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2624 = injectiveMoment H node1013 := by
  calc
    injectiveMoment H raw2624 = injectiveMoment H raw2624step0 := by
      have heq : raw2624step0 = raw2624.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2624).symm
    injectiveMoment H raw2624step0 = injectiveMoment H raw2624step1 := by
      have heq : raw2624step1 = -raw2624step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2624step0).symm
    injectiveMoment H raw2624step1 = injectiveMoment H raw2624step2 := by
      have heq : raw2624step2 = (fun i j => raw2624step1 (permutation11 i) (permutation32 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2624step1 permutation11 permutation32
    _ = injectiveMoment H node1013 := by rfl

def raw2625 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, 2, -3, 1], ![2, -1, 1, -2]]

def raw2625step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![2, -3, 1], ![1, 1, -2]]

def raw2625step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]

theorem canonical2625 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2625 = injectiveMoment H node111 := by
  calc
    injectiveMoment H raw2625 = injectiveMoment H raw2625step0 := by
      have heq : raw2625step0 = raw2625.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2625).symm
    injectiveMoment H raw2625step0 = injectiveMoment H raw2625step1 := by
      have heq : raw2625step1 = (fun i j => raw2625step0 (permutation22 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2625step0 permutation22 permutation6
    _ = injectiveMoment H node111 := by rfl

def raw2626 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, 2, -2, 0], ![1, -1, -1, 1], ![1, 0, 1, -2]]

def raw2626step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 2, -1, 0], ![2, -2, -1, 1], ![1, 0, 1, -2]]

def raw2626step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, -2, 1], ![0, 1, 1, -2], ![2, -1, 0, -1]]

theorem canonical2626 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2626 = injectiveMoment H node510 := by
  calc
    injectiveMoment H raw2626 = injectiveMoment H raw2626step0 := by
      have heq : raw2626step0 = raw2626.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2626).symm
    injectiveMoment H raw2626step0 = injectiveMoment H raw2626step1 := by
      have heq : raw2626step1 = (fun i j => raw2626step0 (permutation25 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2626step0 permutation25 permutation18
    _ = injectiveMoment H node510 := by rfl

def raw2627 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, 2, -2, 0], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw2627step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 2, -1, 0], ![2, -2, 0, 0], ![1, 0, 0, -1]]

def raw2627step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![1, -2, 1, 0], ![-2, 2, 0, 0], ![-1, 0, 0, 1]]

def raw2627step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 1, -2, 1], ![1, 0, 0, -1]]

theorem canonical2627 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2627 = injectiveMoment H node1053 := by
  calc
    injectiveMoment H raw2627 = injectiveMoment H raw2627step0 := by
      have heq : raw2627step0 = raw2627.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2627).symm
    injectiveMoment H raw2627step0 = injectiveMoment H raw2627step1 := by
      have heq : raw2627step1 = -raw2627step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2627step0).symm
    injectiveMoment H raw2627step1 = injectiveMoment H raw2627step2 := by
      have heq : raw2627step2 = (fun i j => raw2627step1 (permutation11 i) (permutation32 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2627step1 permutation11 permutation32
    _ = injectiveMoment H node1053 := by rfl

def raw2628 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, 2, -1, -1], ![1, -1, -1, 1], ![1, 0, 0, -1]]

def raw2628step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 2, -1, 0], ![2, -1, -1, 0], ![1, -1, 1, -1]]

def raw2628step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![1, -2, 1, 0], ![-2, 1, 1, 0], ![-1, 1, -1, 1]]

def raw2628step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, -2, 1], ![0, 1, 1, -2], ![1, -1, 1, -1]]

theorem canonical2628 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2628 = injectiveMoment H node1078 := by
  calc
    injectiveMoment H raw2628 = injectiveMoment H raw2628step0 := by
      have heq : raw2628step0 = raw2628.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2628).symm
    injectiveMoment H raw2628step0 = injectiveMoment H raw2628step1 := by
      have heq : raw2628step1 = -raw2628step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2628step0).symm
    injectiveMoment H raw2628step1 = injectiveMoment H raw2628step2 := by
      have heq : raw2628step2 = (fun i j => raw2628step1 (permutation9 i) (permutation32 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2628step1 permutation9 permutation32
    _ = injectiveMoment H node1078 := by rfl

def raw2629 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, 2, 0, -2], ![1, -1, -2, 2], ![1, 0, 0, -1]]

def raw2629step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 2, -1, 0], ![2, 0, -2, 0], ![1, -2, 2, -1]]

def raw2629step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, 2, -2], ![0, 2, -1, -1], ![1, 0, -2, 1]]

theorem canonical2629 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2629 = injectiveMoment H node844 := by
  calc
    injectiveMoment H raw2629 = injectiveMoment H raw2629step0 := by
      have heq : raw2629step0 = raw2629.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2629).symm
    injectiveMoment H raw2629step0 = injectiveMoment H raw2629step1 := by
      have heq : raw2629step1 = (fun i j => raw2629step0 (permutation32 i) (permutation29 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2629step0 permutation32 permutation29
    _ = injectiveMoment H node844 := by rfl

def raw2630 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, 2, 0, -2], ![1, -1, -1, 1], ![1, 0, -1, 0]]

def raw2630step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 2, -1, 0], ![2, 0, -1, -1], ![1, -2, 1, 0]]

def raw2630step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 2, -1], ![0, 1, -2, 1], ![1, 1, 0, -2]]

theorem canonical2630 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2630 = injectiveMoment H node1005 := by
  calc
    injectiveMoment H raw2630 = injectiveMoment H raw2630step0 := by
      have heq : raw2630step0 = raw2630.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2630).symm
    injectiveMoment H raw2630step0 = injectiveMoment H raw2630step1 := by
      have heq : raw2630step1 = (fun i j => raw2630step0 (permutation24 i) (permutation32 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2630step0 permutation24 permutation32
    _ = injectiveMoment H node1005 := by rfl

def raw2631 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, 2, 0, -2], ![1, -1, 0, 0], ![1, 0, -2, 1]]

def raw2631step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 2, -1, 0], ![2, 0, 0, -2], ![1, -2, 0, 1]]

def raw2631step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![1, -2, 1, 0], ![-2, 0, 0, 2], ![-1, 2, 0, -1]]

def raw2631step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 2, -1], ![0, 2, 0, -2], ![1, 0, -2, 1]]

theorem canonical2631 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2631 = injectiveMoment H node1010 := by
  calc
    injectiveMoment H raw2631 = injectiveMoment H raw2631step0 := by
      have heq : raw2631step0 = raw2631.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2631).symm
    injectiveMoment H raw2631step0 = injectiveMoment H raw2631step1 := by
      have heq : raw2631step1 = -raw2631step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2631step0).symm
    injectiveMoment H raw2631step1 = injectiveMoment H raw2631step2 := by
      have heq : raw2631step2 = (fun i j => raw2631step1 (permutation14 i) (permutation26 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2631step1 permutation14 permutation26
    _ = injectiveMoment H node1010 := by rfl

def raw2632 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, 2, 0, -2], ![2, -1, -2, 1]]

def raw2632step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![2, 0, -2], ![1, -2, 1]]

def raw2632step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 2, -2], ![2, -1, -1]]

theorem canonical2632 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2632 = injectiveMoment H node224 := by
  calc
    injectiveMoment H raw2632 = injectiveMoment H raw2632step0 := by
      have heq : raw2632step0 = raw2632.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2632).symm
    injectiveMoment H raw2632step0 = injectiveMoment H raw2632step1 := by
      have heq : raw2632step1 = (fun i j => raw2632step0 (permutation28 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2632step0 permutation28 permutation5
    _ = injectiveMoment H node224 := by rfl

def raw2633 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, 2, 1, -3], ![1, -1, -2, 2], ![1, 0, -1, 0]]

def raw2633step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 2, -1, 0], ![2, 1, -2, -1], ![1, -3, 2, 0]]

def raw2633step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, -1, 2, -1], ![0, 2, -3, 1], ![1, 1, 0, -2]]

theorem canonical2633 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2633 = injectiveMoment H node823 := by
  calc
    injectiveMoment H raw2633 = injectiveMoment H raw2633step0 := by
      have heq : raw2633step0 = raw2633.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2633).symm
    injectiveMoment H raw2633step0 = injectiveMoment H raw2633step1 := by
      have heq : raw2633step1 = (fun i j => raw2633step0 (permutation24 i) (permutation32 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2633step0 permutation24 permutation32
    _ = injectiveMoment H node823 := by rfl

def raw2634 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, 2, 1, -3], ![1, -1, -1, 1], ![1, 0, -2, 1]]

def raw2634step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 2, -1, 0], ![2, 1, -1, -2], ![1, -3, 1, 1]]

def raw2634step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 2, -1], ![1, 1, -3, 1], ![1, 1, 0, -2]]

theorem canonical2634 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2634 = injectiveMoment H node505 := by
  calc
    injectiveMoment H raw2634 = injectiveMoment H raw2634step0 := by
      have heq : raw2634step0 = raw2634.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2634).symm
    injectiveMoment H raw2634step0 = injectiveMoment H raw2634step1 := by
      have heq : raw2634step1 = (fun i j => raw2634step0 (permutation24 i) (permutation32 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2634step0 permutation24 permutation32
    _ = injectiveMoment H node505 := by rfl

def raw2635 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, 2, 1, -3], ![1, -1, 0, 0], ![1, 0, -3, 2]]

def raw2635step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 2, -1, 0], ![2, 1, 0, -3], ![1, -3, 0, 2]]

def raw2635step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![1, -2, 1, 0], ![-2, -1, 0, 3], ![-1, 3, 0, -2]]

def raw2635step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -2, 3, -1], ![0, 3, -1, -2], ![1, 0, -2, 1]]

theorem canonical2635 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2635 = injectiveMoment H node990 := by
  calc
    injectiveMoment H raw2635 = injectiveMoment H raw2635step0 := by
      have heq : raw2635step0 = raw2635.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2635).symm
    injectiveMoment H raw2635step0 = injectiveMoment H raw2635step1 := by
      have heq : raw2635step1 = -raw2635step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2635step0).symm
    injectiveMoment H raw2635step1 = injectiveMoment H raw2635step2 := by
      have heq : raw2635step2 = (fun i j => raw2635step1 (permutation14 i) (permutation26 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2635step1 permutation14 permutation26
    _ = injectiveMoment H node990 := by rfl

def raw2636 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, 2, 1, -3], ![2, -1, -3, 2]]

def raw2636step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![2, 1, -3], ![1, -3, 2]]

def raw2636step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 2, -3], ![2, -1, -1]]

theorem canonical2636 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2636 = injectiveMoment H node103 := by
  calc
    injectiveMoment H raw2636 = injectiveMoment H raw2636step0 := by
      have heq : raw2636step0 = raw2636.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2636).symm
    injectiveMoment H raw2636step0 = injectiveMoment H raw2636step1 := by
      have heq : raw2636step1 = (fun i j => raw2636step0 (permutation28 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2636step0 permutation28 permutation5
    _ = injectiveMoment H node103 := by rfl

def raw2637 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, 3, -4, 1], ![2, -2, 2, -2]]

def raw2637step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![2, -4, 2], ![1, 1, -2]]

def raw2637step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -3, 2], ![-2, 4, -2], ![-1, -1, 2]]

def raw2637step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![1, 2, -3], ![2, -2, 0]]

theorem canonical2637 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2637 = injectiveMoment H node135 := by
  calc
    injectiveMoment H raw2637 = injectiveMoment H raw2637step0 := by
      have heq : raw2637step0 = raw2637.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2637).symm
    injectiveMoment H raw2637step0 = injectiveMoment H raw2637step1 := by
      have heq : raw2637step1 = -raw2637step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2637step0).symm
    injectiveMoment H raw2637step1 = injectiveMoment H raw2637step2 := by
      have heq : raw2637step2 = (fun i j => raw2637step1 (permutation26 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2637step1 permutation26 permutation4
    _ = injectiveMoment H node135 := by rfl

def raw2638 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, 3, -1, -2], ![2, -2, -1, 1]]

def raw2638step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![2, -1, -1], ![1, -2, 1]]

def raw2638step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -3, 2], ![-2, 1, 1], ![-1, 2, -1]]

def raw2638step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]

theorem canonical2638 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2638 = injectiveMoment H node111 := by
  calc
    injectiveMoment H raw2638 = injectiveMoment H raw2638step0 := by
      have heq : raw2638step0 = raw2638.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2638).symm
    injectiveMoment H raw2638step0 = injectiveMoment H raw2638step1 := by
      have heq : raw2638step1 = -raw2638step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2638step0).symm
    injectiveMoment H raw2638step1 = injectiveMoment H raw2638step2 := by
      have heq : raw2638step2 = (fun i j => raw2638step1 (permutation15 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2638step1 permutation15 permutation5
    _ = injectiveMoment H node111 := by rfl

def raw2639 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, 3, 0, -3], ![2, -2, -2, 2]]

def raw2639step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![2, 0, -2], ![1, -3, 2]]

def raw2639step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![3, -1, -2]]

theorem canonical2639 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2639 = injectiveMoment H node101 := by
  calc
    injectiveMoment H raw2639 = injectiveMoment H raw2639step0 := by
      have heq : raw2639step0 = raw2639.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2639).symm
    injectiveMoment H raw2639step0 = injectiveMoment H raw2639step1 := by
      have heq : raw2639step1 = (fun i j => raw2639step0 (permutation28 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2639step0 permutation28 permutation5
    _ = injectiveMoment H node101 := by rfl

def raw2640 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, 4, -1, -3], ![2, -3, -1, 2]]

def raw2640step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 4, -3], ![2, -1, -1], ![1, -3, 2]]

def raw2640step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 4, -3], ![1, -3, 2], ![2, -1, -1]]

theorem canonical2640 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2640 = injectiveMoment H node191 := by
  calc
    injectiveMoment H raw2640 = injectiveMoment H raw2640step0 := by
      have heq : raw2640step0 = raw2640.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2640).symm
    injectiveMoment H raw2640step0 = injectiveMoment H raw2640step1 := by
      have heq : raw2640step1 = (fun i j => raw2640step0 (permutation10 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2640step0 permutation10 permutation3
    _ = injectiveMoment H node191 := by rfl

def raw2641 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![1, -3, 1, 1], ![1, 4, -3, -2]]

def raw2641step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -3, 4], ![2, 1, -3], ![1, 1, -2]]

def raw2641step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -2, 1], ![1, 1, -2], ![1, 2, -3]]

theorem canonical2641 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2641 = injectiveMoment H node89 := by
  calc
    injectiveMoment H raw2641 = injectiveMoment H raw2641step0 := by
      have heq : raw2641step0 = raw2641.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2641).symm
    injectiveMoment H raw2641step0 = injectiveMoment H raw2641step1 := by
      have heq : raw2641step1 = (fun i j => raw2641step0 (permutation16 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2641step0 permutation16 permutation5
    _ = injectiveMoment H node89 := by rfl

def raw2642 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![1, -2, -1, 2], ![1, 3, -1, -3]]

def raw2642step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -2, 3], ![2, -1, -1], ![1, 2, -3]]

def raw2642step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -2, 1], ![2, 1, -3]]

theorem canonical2642 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2642 = injectiveMoment H node159 := by
  calc
    injectiveMoment H raw2642 = injectiveMoment H raw2642step0 := by
      have heq : raw2642step0 = raw2642.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2642).symm
    injectiveMoment H raw2642step0 = injectiveMoment H raw2642step1 := by
      have heq : raw2642step1 = (fun i j => raw2642step0 (permutation17 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2642step0 permutation17 permutation5
    _ = injectiveMoment H node159 := by rfl

def raw2643 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![1, -1, -3, 3], ![1, 2, 1, -4]]

def raw2643step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![2, -3, 1], ![1, 3, -4]]

def raw2643step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![-2, 3, -1], ![-1, -3, 4]]

def raw2643step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 4, -3], ![1, -2, 1], ![2, -1, -1]]

theorem canonical2643 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2643 = injectiveMoment H node161 := by
  calc
    injectiveMoment H raw2643 = injectiveMoment H raw2643step0 := by
      have heq : raw2643step0 = raw2643.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2643).symm
    injectiveMoment H raw2643step0 = injectiveMoment H raw2643step1 := by
      have heq : raw2643step1 = -raw2643step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2643step0).symm
    injectiveMoment H raw2643step1 = injectiveMoment H raw2643step2 := by
      have heq : raw2643step2 = (fun i j => raw2643step1 (permutation26 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2643step1 permutation26 permutation4
    _ = injectiveMoment H node161 := by rfl

def raw2644 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![1, -1, -2, 2], ![0, 2, 0, -2], ![1, 0, 0, -1]]

def raw2644step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![-1, -1, 2, 0], ![2, -2, 0, 0], ![1, 2, -2, -1]]

def raw2644step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, 2, -2], ![0, 2, -1, -1], ![1, 0, -2, 1]]

theorem canonical2644 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2644 = injectiveMoment H node844 := by
  calc
    injectiveMoment H raw2644 = injectiveMoment H raw2644step0 := by
      have heq : raw2644step0 = raw2644.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2644).symm
    injectiveMoment H raw2644step0 = injectiveMoment H raw2644step1 := by
      have heq : raw2644step1 = (fun i j => raw2644step0 (permutation32 i) (permutation31 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2644step0 permutation32 permutation31
    _ = injectiveMoment H node844 := by rfl

def raw2645 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![1, -1, -2, 2], ![1, 2, 0, -3]]

def raw2645step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![2, -2, 0], ![1, 2, -3]]

def raw2645step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]

theorem canonical2645 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2645 = injectiveMoment H node111 := by
  calc
    injectiveMoment H raw2645 = injectiveMoment H raw2645step0 := by
      have heq : raw2645step0 = raw2645.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2645).symm
    injectiveMoment H raw2645step0 = injectiveMoment H raw2645step1 := by
      have heq : raw2645step1 = (fun i j => raw2645step0 (permutation31 i) (permutation7 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2645step0 permutation31 permutation7
    _ = injectiveMoment H node111 := by rfl

def raw2646 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![1, -1, -1, 1], ![0, 2, -1, -1], ![1, 0, 0, -1]]

def raw2646step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![-1, -1, 2, 0], ![2, -1, -1, 0], ![1, 1, -1, -1]]

def raw2646step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, -1, 0, -1], ![1, 1, -2, 0], ![-2, 1, 1, 0], ![-1, -1, 1, 1]]

def raw2646step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, -2, 1], ![0, 1, 1, -2], ![1, -1, 1, -1]]

theorem canonical2646 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2646 = injectiveMoment H node1078 := by
  calc
    injectiveMoment H raw2646 = injectiveMoment H raw2646step0 := by
      have heq : raw2646step0 = raw2646.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2646).symm
    injectiveMoment H raw2646step0 = injectiveMoment H raw2646step1 := by
      have heq : raw2646step1 = -raw2646step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2646step0).symm
    injectiveMoment H raw2646step1 = injectiveMoment H raw2646step2 := by
      have heq : raw2646step2 = (fun i j => raw2646step1 (permutation9 i) (permutation30 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2646step1 permutation9 permutation30
    _ = injectiveMoment H node1078 := by rfl

def raw2647 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![1, -1, 2, -2], ![1, 2, -4, 1]]

def raw2647step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![2, 2, -4], ![1, -2, 1]]

def raw2647step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![-2, -2, 4], ![-1, 2, -1]]

def raw2647step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![1, 1, -2], ![2, -1, -1]]

theorem canonical2647 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2647 = injectiveMoment H node134 := by
  calc
    injectiveMoment H raw2647 = injectiveMoment H raw2647step0 := by
      have heq : raw2647step0 = raw2647.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2647).symm
    injectiveMoment H raw2647step0 = injectiveMoment H raw2647step1 := by
      have heq : raw2647step1 = -raw2647step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2647step0).symm
    injectiveMoment H raw2647step1 = injectiveMoment H raw2647step2 := by
      have heq : raw2647step2 = (fun i j => raw2647step1 (permutation26 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2647step1 permutation26 permutation3
    _ = injectiveMoment H node134 := by rfl

def raw2648 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![1, 2, -3, 0], ![1, -1, 1, -1]]

def raw2648step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![2, -3, 1], ![1, 0, -1]]

def raw2648step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -1, -1], ![1, -2, 1], ![-2, 3, -1], ![-1, 0, 1]]

def raw2648step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2]]

theorem canonical2648 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2648 = injectiveMoment H node261 := by
  calc
    injectiveMoment H raw2648 = injectiveMoment H raw2648step0 := by
      have heq : raw2648step0 = raw2648.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2648).symm
    injectiveMoment H raw2648step0 = injectiveMoment H raw2648step1 := by
      have heq : raw2648step1 = -raw2648step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2648step0).symm
    injectiveMoment H raw2648step1 = injectiveMoment H raw2648step2 := by
      have heq : raw2648step2 = (fun i j => raw2648step1 (permutation22 i) (permutation7 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2648step1 permutation22 permutation7
    _ = injectiveMoment H node261 := by rfl

def raw2649 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![2, -3, 0, 1], ![0, 4, -2, -2]]

def raw2649step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -3, 4], ![2, 0, -2], ![1, 1, -2]]

def raw2649step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]

theorem canonical2649 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2649 = injectiveMoment H node85 := by
  calc
    injectiveMoment H raw2649 = injectiveMoment H raw2649step0 := by
      have heq : raw2649step0 = raw2649.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2649).symm
    injectiveMoment H raw2649step0 = injectiveMoment H raw2649step1 := by
      have heq : raw2649step1 = (fun i j => raw2649step0 (permutation18 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2649step0 permutation18 permutation5
    _ = injectiveMoment H node85 := by rfl

def raw2650 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]

def raw2650step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![0, -1, 1], ![-1, 1, 0], ![-2, -2, 4]]

def raw2650step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]

theorem canonical2650 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2650 = injectiveMoment H node418 := by
  calc
    injectiveMoment H raw2650 = injectiveMoment H raw2650step0 := by
      have heq : raw2650step0 = -raw2650 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2650).symm
    injectiveMoment H raw2650step0 = injectiveMoment H raw2650step1 := by
      have heq : raw2650step1 = (fun i j => raw2650step0 (permutation144 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2650step0 permutation144 permutation5
    _ = injectiveMoment H node418 := by rfl

def raw2651 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]

def raw2651step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 2, -3]]

theorem canonical2651 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2651 = injectiveMoment H node855 := by
  calc
    injectiveMoment H raw2651 = injectiveMoment H raw2651step0 := by
      have heq : raw2651step0 = (fun i j => raw2651 (permutation35 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2651 permutation35 permutation5
    _ = injectiveMoment H node855 := by rfl

def raw2652 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]

def raw2652step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, -1, 2], ![0, 2, -2], ![1, 0, -1], ![1, 1, -2]]

theorem canonical2652 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2652 = injectiveMoment H node858 := by
  calc
    injectiveMoment H raw2652 = injectiveMoment H raw2652step0 := by
      have heq : raw2652step0 = (fun i j => raw2652 (permutation37 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2652 permutation37 permutation5
    _ = injectiveMoment H node858 := by rfl

def raw2653 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]

theorem canonical2653 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2653 = injectiveMoment H node524 := by
  rfl

def raw2654 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]

theorem canonical2654 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2654 = injectiveMoment H node525 := by
  rfl

def raw2655 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]

def raw2655step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![0, -2, 2], ![-1, 0, 1], ![-2, 0, 2]]

def raw2655step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, -1, 1], ![1, 1, -2], ![1, 2, -3]]

theorem canonical2655 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2655 = injectiveMoment H node640 := by
  calc
    injectiveMoment H raw2655 = injectiveMoment H raw2655step0 := by
      have heq : raw2655step0 = -raw2655 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2655).symm
    injectiveMoment H raw2655step0 = injectiveMoment H raw2655step1 := by
      have heq : raw2655step1 = (fun i j => raw2655step0 (permutation103 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2655step0 permutation103 permutation5
    _ = injectiveMoment H node640 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
