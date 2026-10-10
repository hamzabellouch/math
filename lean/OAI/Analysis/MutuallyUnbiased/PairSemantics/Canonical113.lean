import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes1
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes2
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes3
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes6
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes7
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes8
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes9
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes12
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes15
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes18
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes19
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes20

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw3616 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 2, -3, 1], ![1, -1, 1, -1], ![1, -1, 2, -2]]

def raw3616step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, -2, 3, -1], ![-1, 1, -1, 1], ![-1, 1, -2, 2]]

def raw3616step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 2, -2, 0], ![1, -1, 1, -1], ![1, -1, 2, -2]]

theorem canonical3616 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3616 = injectiveMoment H node603 := by
  calc
    injectiveMoment H raw3616 = injectiveMoment H raw3616step0 := by
      have heq : raw3616step0 = -raw3616 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3616).symm
    injectiveMoment H raw3616step0 = injectiveMoment H raw3616step1 := by
      have heq : raw3616step1 = (fun i j => raw3616step0 (permutation15 i) (permutation16 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3616step0 permutation15 permutation16
    _ = injectiveMoment H node603 := by rfl

def raw3617 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 2, -2, 0], ![1, -2, -1, 2], ![1, 0, 3, -4]]

def raw3617step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 2, -2, 0], ![0, -2, -1, 3], ![2, 0, 2, -4]]

def raw3617step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, -2, 2, 0], ![0, 2, 1, -3], ![-2, 0, -2, 4]]

def raw3617step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -2, 2, 0], ![0, 2, 1, -3], ![2, 0, -1, -1]]

theorem canonical3617 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3617 = injectiveMoment H node577 := by
  calc
    injectiveMoment H raw3617 = injectiveMoment H raw3617step0 := by
      have heq : raw3617step0 = raw3617.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3617).symm
    injectiveMoment H raw3617step0 = injectiveMoment H raw3617step1 := by
      have heq : raw3617step1 = -raw3617step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3617step0).symm
    injectiveMoment H raw3617step1 = injectiveMoment H raw3617step2 := by
      have heq : raw3617step2 = (fun i j => raw3617step1 (permutation30 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3617step1 permutation30 permutation9
    _ = injectiveMoment H node577 := by rfl

def raw3618 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 2, -2, 0], ![1, -2, 3, -2], ![1, 0, -1, 0]]

def raw3618step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 2, -2, 0], ![0, -2, 3, -1], ![2, 0, -2, 0]]

def raw3618step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 2, -2], ![0, 2, 0, -2], ![1, 0, -2, 1]]

theorem canonical3618 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3618 = injectiveMoment H node808 := by
  calc
    injectiveMoment H raw3618 = injectiveMoment H raw3618step0 := by
      have heq : raw3618step0 = raw3618.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3618).symm
    injectiveMoment H raw3618step0 = injectiveMoment H raw3618step1 := by
      have heq : raw3618step1 = (fun i j => raw3618step0 (permutation26 i) (permutation29 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3618step0 permutation26 permutation29
    _ = injectiveMoment H node808 := by rfl

def raw3619 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 2, -2, 0], ![1, -1, -1, 1], ![1, -1, 3, -3]]

def raw3619step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 2, -1, -1], ![0, -2, -1, 3], ![2, 0, 1, -3]]

def raw3619step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -2, 1], ![0, 1, 2, -3], ![2, -1, 0, -1]]

theorem canonical3619 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3619 = injectiveMoment H node485 := by
  calc
    injectiveMoment H raw3619 = injectiveMoment H raw3619step0 := by
      have heq : raw3619step0 = raw3619.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3619).symm
    injectiveMoment H raw3619step0 = injectiveMoment H raw3619step1 := by
      have heq : raw3619step1 = (fun i j => raw3619step0 (permutation22 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3619step0 permutation22 permutation17
    _ = injectiveMoment H node485 := by rfl

def raw3620 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 2, -2, 0], ![1, -1, 0, 0], ![1, -1, 2, -2]]

def raw3620step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 2, -1, -1], ![0, -2, 0, 2], ![2, 0, 0, -2]]

def raw3620step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, 0, -2, 2], ![0, 2, 0, -2], ![1, -2, 0, 1]]

theorem canonical3620 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3620 = injectiveMoment H node1314 := by
  calc
    injectiveMoment H raw3620 = injectiveMoment H raw3620step0 := by
      have heq : raw3620step0 = raw3620.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3620).symm
    injectiveMoment H raw3620step0 = injectiveMoment H raw3620step1 := by
      have heq : raw3620step1 = (fun i j => raw3620step0 (permutation18 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3620step0 permutation18 permutation21
    _ = injectiveMoment H node1314 := by rfl

def raw3621 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 2, -2, 0], ![1, -1, 1, -1], ![1, -1, 1, -1]]

def raw3621step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 2, 0], ![1, 1, -1, -1], ![1, 1, -1, -1]]

theorem canonical3621 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3621 = injectiveMoment H node608 := by
  calc
    injectiveMoment H raw3621 = injectiveMoment H raw3621step0 := by
      have heq : raw3621step0 = (fun i j => raw3621 (permutation9 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3621 permutation9 permutation11
    _ = injectiveMoment H node608 := by rfl

def raw3622 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 2, -1, -1], ![1, -2, 3, -2], ![1, 0, -2, 1]]

def raw3622step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 2, -2, 0], ![0, -1, 3, -2], ![2, -1, -2, 1]]

def raw3622step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 2, 0, -2], ![1, -1, 2, -2], ![1, 0, -2, 1]]

theorem canonical3622 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3622 = injectiveMoment H node496 := by
  calc
    injectiveMoment H raw3622 = injectiveMoment H raw3622step0 := by
      have heq : raw3622step0 = raw3622.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3622).symm
    injectiveMoment H raw3622step0 = injectiveMoment H raw3622step1 := by
      have heq : raw3622step1 = (fun i j => raw3622step0 (permutation24 i) (permutation29 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3622step0 permutation24 permutation29
    _ = injectiveMoment H node496 := by rfl

def raw3623 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 2, -1, -1], ![1, -1, 0, 0], ![1, -1, 1, -1]]

def raw3623step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 2, -1, -1], ![0, -1, 0, 1], ![2, -1, 0, -1]]

def raw3623step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, -2, 1, 1], ![0, 1, 0, -1], ![-2, 1, 0, 1]]

def raw3623step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 1, 0], ![0, 1, 1, -2], ![1, 1, -2, 0]]

theorem canonical3623 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3623 = injectiveMoment H node1000 := by
  calc
    injectiveMoment H raw3623 = injectiveMoment H raw3623step0 := by
      have heq : raw3623step0 = raw3623.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3623).symm
    injectiveMoment H raw3623step0 = injectiveMoment H raw3623step1 := by
      have heq : raw3623step1 = -raw3623step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3623step0).symm
    injectiveMoment H raw3623step1 = injectiveMoment H raw3623step2 := by
      have heq : raw3623step2 = (fun i j => raw3623step1 (permutation12 i) (permutation26 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3623step1 permutation12 permutation26
    _ = injectiveMoment H node1000 := by rfl

def raw3624 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 2, 0, -2], ![1, -2, 2, -1], ![1, 0, -2, 1]]

def raw3624step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, -2, 0, 2], ![-1, 2, -2, 1], ![-1, 0, 2, -1]]

def raw3624step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, 0, -2, 2], ![0, 2, 0, -2], ![2, -1, 0, -1]]

theorem canonical3624 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3624 = injectiveMoment H node523 := by
  calc
    injectiveMoment H raw3624 = injectiveMoment H raw3624step0 := by
      have heq : raw3624step0 = -raw3624 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3624).symm
    injectiveMoment H raw3624step0 = injectiveMoment H raw3624step1 := by
      have heq : raw3624step1 = (fun i j => raw3624step0 (permutation23 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3624step0 permutation23 permutation21
    _ = injectiveMoment H node523 := by rfl

def raw3625 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 2, 2, -4], ![1, -2, -1, 2], ![1, 0, -1, 0]]

def raw3625step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 2, -2, 0], ![0, 2, -1, -1], ![2, -4, 2, 0]]

def raw3625step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, -2, 2], ![0, 2, 2, -4], ![1, -2, 1, 0]]

theorem canonical3625 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3625 = injectiveMoment H node1257 := by
  calc
    injectiveMoment H raw3625 = injectiveMoment H raw3625step0 := by
      have heq : raw3625step0 = raw3625.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3625).symm
    injectiveMoment H raw3625step0 = injectiveMoment H raw3625step1 := by
      have heq : raw3625step1 = (fun i j => raw3625step0 (permutation24 i) (permutation28 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3625step0 permutation24 permutation28
    _ = injectiveMoment H node1257 := by rfl

def raw3626 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 2, 2, -4], ![1, -2, 0, 1], ![1, 0, -2, 1]]

def raw3626step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, -2, -2, 4], ![-1, 2, 0, -1], ![-1, 0, 2, -1]]

def raw3626step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 2, -2], ![0, 2, -1, -1], ![2, 0, -1, -1]]

theorem canonical3626 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3626 = injectiveMoment H node396 := by
  calc
    injectiveMoment H raw3626 = injectiveMoment H raw3626step0 := by
      have heq : raw3626step0 = -raw3626 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3626).symm
    injectiveMoment H raw3626step0 = injectiveMoment H raw3626step1 := by
      have heq : raw3626step1 = (fun i j => raw3626step0 (permutation16 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3626step0 permutation16 permutation17
    _ = injectiveMoment H node396 := by rfl

def raw3627 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 2, 2, -4], ![1, -1, -2, 2], ![1, -1, 0, 0]]

def raw3627step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 2, -1, -1], ![0, 2, -2, 0], ![2, -4, 2, 0]]

def raw3627step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, -2, 2], ![0, 2, 2, -4], ![1, -2, 1, 0]]

theorem canonical3627 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3627 = injectiveMoment H node1257 := by
  calc
    injectiveMoment H raw3627 = injectiveMoment H raw3627step0 := by
      have heq : raw3627step0 = raw3627.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3627).symm
    injectiveMoment H raw3627step0 = injectiveMoment H raw3627step1 := by
      have heq : raw3627step1 = (fun i j => raw3627step0 (permutation18 i) (permutation28 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3627step0 permutation18 permutation28
    _ = injectiveMoment H node1257 := by rfl

def raw3628 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 2, 2, -4], ![1, -1, -1, 1], ![1, -1, -1, 1]]

def raw3628step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, -2, -2, 4], ![-1, 1, 1, -1], ![-1, 1, 1, -1]]

def raw3628step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 2, -2], ![1, 1, -1, -1], ![1, 1, -1, -1]]

theorem canonical3628 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3628 = injectiveMoment H node398 := by
  calc
    injectiveMoment H raw3628 = injectiveMoment H raw3628step0 := by
      have heq : raw3628step0 = -raw3628 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3628).symm
    injectiveMoment H raw3628step0 = injectiveMoment H raw3628step1 := by
      have heq : raw3628step1 = (fun i j => raw3628step0 (permutation15 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3628step0 permutation15 permutation17
    _ = injectiveMoment H node398 := by rfl

def raw3629 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, -3, 3, -1], ![1, 3, -3, -1]]

def raw3629step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -3, 3], ![0, 3, -3], ![2, -1, -1]]

theorem canonical3629 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3629 = injectiveMoment H node220 := by
  calc
    injectiveMoment H raw3629 = injectiveMoment H raw3629step0 := by
      have heq : raw3629step0 = raw3629.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3629).symm
    _ = injectiveMoment H node220 := by rfl

def raw3630 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, -2, -1, 2], ![0, 1, 3, -4], ![1, 1, -2, 0]]

def raw3630step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -2, 1, 1], ![0, -1, 3, -2], ![2, 2, -4, 0]]

def raw3630step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, -1, 0, -1], ![0, 2, -1, -1], ![0, 1, -3, 2], ![-2, -2, 4, 0]]

def raw3630step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -1, 2, -1], ![0, 2, 1, -3], ![2, -1, -1, 0]]

theorem canonical3630 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3630 = injectiveMoment H node580 := by
  calc
    injectiveMoment H raw3630 = injectiveMoment H raw3630step0 := by
      have heq : raw3630step0 = raw3630.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3630).symm
    injectiveMoment H raw3630step0 = injectiveMoment H raw3630step1 := by
      have heq : raw3630step1 = -raw3630step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3630step0).symm
    injectiveMoment H raw3630step1 = injectiveMoment H raw3630step2 := by
      have heq : raw3630step2 = (fun i j => raw3630step1 (permutation30 i) (permutation13 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3630step1 permutation30 permutation13
    _ = injectiveMoment H node580 := by rfl

def raw3631 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, -2, -1, 2], ![0, 2, -2, 0], ![1, 0, 3, -4]]

def raw3631step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -2, 2, 0], ![0, -1, -2, 3], ![2, 2, 0, -4]]

def raw3631step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, -1, 0, -1], ![0, 2, -2, 0], ![0, 1, 2, -3], ![-2, -2, 0, 4]]

def raw3631step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -2, 2, 0], ![0, 2, 1, -3], ![2, 0, -1, -1]]

theorem canonical3631 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3631 = injectiveMoment H node577 := by
  calc
    injectiveMoment H raw3631 = injectiveMoment H raw3631step0 := by
      have heq : raw3631step0 = raw3631.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3631).symm
    injectiveMoment H raw3631step0 = injectiveMoment H raw3631step1 := by
      have heq : raw3631step1 = -raw3631step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3631step0).symm
    injectiveMoment H raw3631step1 = injectiveMoment H raw3631step2 := by
      have heq : raw3631step2 = (fun i j => raw3631step1 (permutation30 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3631step1 permutation30 permutation11
    _ = injectiveMoment H node577 := by rfl

def raw3632 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, -2, 0, 1], ![0, 1, -2, 1], ![1, 1, 2, -4]]

def raw3632step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![-1, 2, 0, -1], ![0, -1, 2, -1], ![-1, -1, -2, 4]]

def raw3632step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 2, -1], ![0, 2, 0, -2], ![2, 0, -1, -1]]

theorem canonical3632 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3632 = injectiveMoment H node450 := by
  calc
    injectiveMoment H raw3632 = injectiveMoment H raw3632step0 := by
      have heq : raw3632step0 = -raw3632 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3632).symm
    injectiveMoment H raw3632step0 = injectiveMoment H raw3632step1 := by
      have heq : raw3632step1 = (fun i j => raw3632step0 (permutation29 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3632step0 permutation29 permutation21
    _ = injectiveMoment H node450 := by rfl

def raw3633 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, -2, 1, 0], ![0, 1, 1, -2], ![1, 1, -2, 0]]

def raw3633step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![-1, 2, -1, 0], ![0, -1, -1, 2], ![-1, -1, 2, 0]]

def raw3633step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 2, -1], ![0, 2, -1, -1], ![2, -1, -1, 0]]

theorem canonical3633 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3633 = injectiveMoment H node609 := by
  calc
    injectiveMoment H raw3633 = injectiveMoment H raw3633step0 := by
      have heq : raw3633step0 = -raw3633 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3633).symm
    injectiveMoment H raw3633step0 = injectiveMoment H raw3633step1 := by
      have heq : raw3633step1 = (fun i j => raw3633step0 (permutation13 i) (permutation30 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3633step0 permutation13 permutation30
    _ = injectiveMoment H node609 := by rfl

def raw3634 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, -2, 1, 0], ![0, 2, -2, 0], ![1, 0, 1, -2]]

def raw3634step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![-1, 2, -1, 0], ![0, -2, 2, 0], ![-1, 0, -1, 2]]

def raw3634step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 2, 0], ![0, 2, -1, -1], ![2, 0, -1, -1]]

theorem canonical3634 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3634 = injectiveMoment H node606 := by
  calc
    injectiveMoment H raw3634 = injectiveMoment H raw3634step0 := by
      have heq : raw3634step0 = -raw3634 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3634).symm
    injectiveMoment H raw3634step0 = injectiveMoment H raw3634step1 := by
      have heq : raw3634step1 = (fun i j => raw3634step0 (permutation22 i) (permutation19 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3634step0 permutation22 permutation19
    _ = injectiveMoment H node606 := by rfl

def raw3635 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, -2, 2, -1], ![0, 1, 1, -2], ![1, 1, -3, 1]]

def raw3635step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, 1, -2], ![1, -2, 2, -1], ![1, 1, -3, 1]]

theorem canonical3635 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3635 = injectiveMoment H node612 := by
  calc
    injectiveMoment H raw3635 = injectiveMoment H raw3635step0 := by
      have heq : raw3635step0 = (fun i j => raw3635 (permutation11 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3635 permutation11 permutation9
    _ = injectiveMoment H node612 := by rfl

def raw3636 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, -2, 2, -1], ![0, 2, -1, -1], ![1, 0, -1, 0]]

def raw3636step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -2, 2, 0], ![0, 2, -1, -1], ![2, -1, -1, 0]]

def raw3636step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 2, -1], ![0, 2, 0, -2], ![1, 0, -2, 1]]

theorem canonical3636 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3636 = injectiveMoment H node1010 := by
  calc
    injectiveMoment H raw3636 = injectiveMoment H raw3636step0 := by
      have heq : raw3636step0 = raw3636.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3636).symm
    injectiveMoment H raw3636step0 = injectiveMoment H raw3636step1 := by
      have heq : raw3636step1 = (fun i j => raw3636step0 (permutation26 i) (permutation31 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3636step0 permutation26 permutation31
    _ = injectiveMoment H node1010 := by rfl

def raw3637 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, -2, 2, -1], ![0, 2, 0, -2], ![1, 0, -2, 1]]

def raw3637step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![-1, 2, -2, 1], ![0, -2, 0, 2], ![-1, 0, 2, -1]]

def raw3637step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, 0, -2, 2], ![0, 2, 0, -2], ![2, -1, 0, -1]]

theorem canonical3637 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3637 = injectiveMoment H node523 := by
  calc
    injectiveMoment H raw3637 = injectiveMoment H raw3637step0 := by
      have heq : raw3637step0 = -raw3637 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3637).symm
    injectiveMoment H raw3637step0 = injectiveMoment H raw3637step1 := by
      have heq : raw3637step1 = (fun i j => raw3637step0 (permutation17 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3637step0 permutation17 permutation21
    _ = injectiveMoment H node523 := by rfl

def raw3638 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, -2, 2, -1], ![1, 2, -2, -1]]

def raw3638step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 2, -2], ![2, -1, -1]]

theorem canonical3638 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3638 = injectiveMoment H node224 := by
  calc
    injectiveMoment H raw3638 = injectiveMoment H raw3638step0 := by
      have heq : raw3638step0 = raw3638.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3638).symm
    _ = injectiveMoment H node224 := by rfl

def raw3639 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, 0, -3, 2], ![0, 1, 3, -4], ![1, -1, 0, 0]]

def raw3639step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![-1, 0, 3, -2], ![0, -1, -3, 4], ![-1, 1, 0, 0]]

def raw3639step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, -1, 3, -2], ![0, 2, 0, -2], ![1, -1, 0, 0]]

theorem canonical3639 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3639 = injectiveMoment H node1175 := by
  calc
    injectiveMoment H raw3639 = injectiveMoment H raw3639step0 := by
      have heq : raw3639step0 = -raw3639 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3639).symm
    injectiveMoment H raw3639step0 = injectiveMoment H raw3639step1 := by
      have heq : raw3639step1 = (fun i j => raw3639step0 (permutation23 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3639step0 permutation23 permutation15
    _ = injectiveMoment H node1175 := by rfl

def raw3640 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, 0, -2, 1], ![0, 1, 3, -4], ![1, -1, -1, 1]]

def raw3640step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![-1, 0, 2, -1], ![0, -1, -3, 4], ![-1, 1, 1, -1]]

def raw3640step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, -1, 2, -1], ![0, 2, 0, -2], ![1, -1, 1, -1]]

theorem canonical3640 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3640 = injectiveMoment H node1173 := by
  calc
    injectiveMoment H raw3640 = injectiveMoment H raw3640step0 := by
      have heq : raw3640step0 = -raw3640 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3640).symm
    injectiveMoment H raw3640step0 = injectiveMoment H raw3640step1 := by
      have heq : raw3640step1 = (fun i j => raw3640step0 (permutation23 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3640step0 permutation23 permutation15
    _ = injectiveMoment H node1173 := by rfl

def raw3641 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, 0, -2, 1], ![0, 2, -1, -1], ![1, -2, 3, -2]]

def raw3641step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, 2, -2], ![0, -2, -1, 3], ![2, 1, -1, -2]]

def raw3641step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 2, 0, -2], ![1, -1, 2, -2], ![1, 0, -2, 1]]

theorem canonical3641 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3641 = injectiveMoment H node496 := by
  calc
    injectiveMoment H raw3641 = injectiveMoment H raw3641step0 := by
      have heq : raw3641step0 = raw3641.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3641).symm
    injectiveMoment H raw3641step0 = injectiveMoment H raw3641step1 := by
      have heq : raw3641step1 = (fun i j => raw3641step0 (permutation24 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3641step0 permutation24 permutation17
    _ = injectiveMoment H node496 := by rfl

def raw3642 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, 1, -3, 1], ![0, 1, 1, -2], ![1, -2, 2, -1]]

def raw3642step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, 1, -2], ![1, -2, 2, -1], ![1, 1, -3, 1]]

theorem canonical3642 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3642 = injectiveMoment H node612 := by
  calc
    injectiveMoment H raw3642 = injectiveMoment H raw3642step0 := by
      have heq : raw3642step0 = (fun i j => raw3642 (permutation12 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3642 permutation12 permutation9
    _ = injectiveMoment H node612 := by rfl

def raw3643 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, 1, -3, 1], ![0, 1, 3, -4], ![1, -2, 0, 1]]

def raw3643step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 1, 1, -2], ![0, -3, 3, 0], ![2, 1, -4, 1]]

def raw3643step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, -1, 0, -1], ![0, -1, -1, 2], ![0, 3, -3, 0], ![-2, -1, 4, -1]]

def raw3643step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 3, -3], ![0, 2, -1, -1], ![2, -1, -1, 0]]

theorem canonical3643 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3643 = injectiveMoment H node462 := by
  calc
    injectiveMoment H raw3643 = injectiveMoment H raw3643step0 := by
      have heq : raw3643step0 = raw3643.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3643).symm
    injectiveMoment H raw3643step0 = injectiveMoment H raw3643step1 := by
      have heq : raw3643step1 = -raw3643step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3643step0).symm
    injectiveMoment H raw3643step1 = injectiveMoment H raw3643step2 := by
      have heq : raw3643step2 = (fun i j => raw3643step1 (permutation32 i) (permutation13 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3643step1 permutation32 permutation13
    _ = injectiveMoment H node462 := by rfl

def raw3644 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-3, 2, 1, 0], ![5, -2, -2, -1]]

def raw3644step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 2, -2], ![1, 1, -2], ![1, 0, -1]]

def raw3644step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 2, -2], ![1, 0, -1], ![1, 1, -2]]

theorem canonical3644 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3644 = injectiveMoment H node127 := by
  calc
    injectiveMoment H raw3644 = injectiveMoment H raw3644step0 := by
      have heq : raw3644step0 = raw3644.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3644).symm
    injectiveMoment H raw3644step0 = injectiveMoment H raw3644step1 := by
      have heq : raw3644step1 = (fun i j => raw3644step0 (permutation10 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3644step0 permutation10 permutation3
    _ = injectiveMoment H node127 := by rfl

def raw3645 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-2, 2, -2, 2], ![4, -2, 1, -3]]

def raw3645step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![1, -2, 1], ![1, 2, -3]]

theorem canonical3645 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3645 = injectiveMoment H node152 := by
  calc
    injectiveMoment H raw3645 = injectiveMoment H raw3645step0 := by
      have heq : raw3645step0 = raw3645.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3645).symm
    _ = injectiveMoment H node152 := by rfl

def raw3646 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-2, 2, 1, -1], ![4, -2, -2, 0]]

def raw3646step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![1, 1, -2], ![1, -1, 0]]

def raw3646step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![1, -1, 0], ![1, 1, -2]]

theorem canonical3646 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3646 = injectiveMoment H node153 := by
  calc
    injectiveMoment H raw3646 = injectiveMoment H raw3646step0 := by
      have heq : raw3646step0 = raw3646.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3646).symm
    injectiveMoment H raw3646step0 = injectiveMoment H raw3646step1 := by
      have heq : raw3646step1 = (fun i j => raw3646step0 (permutation10 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3646step0 permutation10 permutation3
    _ = injectiveMoment H node153 := by rfl

def raw3647 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-2, 3, -2, 1], ![4, -3, 1, -2]]

def raw3647step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 3, -3], ![1, -2, 1], ![1, 1, -2]]

theorem canonical3647 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3647 = injectiveMoment H node154 := by
  calc
    injectiveMoment H raw3647 = injectiveMoment H raw3647step0 := by
      have heq : raw3647step0 = raw3647.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3647).symm
    _ = injectiveMoment H node154 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
