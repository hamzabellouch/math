import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes8
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes9
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes10
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes14
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes17
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes20
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes24
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes27
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes28
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes34
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes44

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw4448 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -1, -1, 2], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 3, -4]]

theorem canonical4448 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4448 = injectiveMoment H node2202 := by
  rfl

def raw4449 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -1, -1, 2], ![0, 1, 3, -4], ![1, -1, 0, 0], ![1, 0, -1, 0]]

theorem canonical4449 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4449 = injectiveMoment H node2203 := by
  rfl

def raw4450 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -1, -1, 2], ![0, 1, 3, -4], ![2, -1, -1, 0]]

def raw4450step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, -1, 1, -1], ![-1, -1, 3, -1], ![2, 2, -4, 0]]

def raw4450step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![-1, 1, -1, 1], ![1, 1, -3, 1], ![-2, -2, 4, 0]]

def raw4450step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -2, 2, 0], ![1, 1, -1, -1], ![1, 1, 1, -3]]

theorem canonical4450 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4450 = injectiveMoment H node578 := by
  calc
    injectiveMoment H raw4450 = injectiveMoment H raw4450step0 := by
      have heq : raw4450step0 = raw4450.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4450).symm
    injectiveMoment H raw4450step0 = injectiveMoment H raw4450step1 := by
      have heq : raw4450step1 = -raw4450step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4450step0).symm
    injectiveMoment H raw4450step1 = injectiveMoment H raw4450step2 := by
      have heq : raw4450step2 = (fun i j => raw4450step1 (permutation27 i) (permutation19 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4450step1 permutation27 permutation19
    _ = injectiveMoment H node578 := by rfl

def raw4451 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -1, -1, 2], ![1, -1, 0, 0], ![1, 1, 2, -4]]

def raw4451step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, -1, -1, 1], ![-1, -1, 0, 2], ![2, 2, 0, -4]]

def raw4451step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, -1, 2], ![0, 2, 2, -4], ![1, 0, -2, 1]]

theorem canonical4451 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4451 = injectiveMoment H node1100 := by
  calc
    injectiveMoment H raw4451 = injectiveMoment H raw4451step0 := by
      have heq : raw4451step0 = raw4451.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4451).symm
    injectiveMoment H raw4451step0 = injectiveMoment H raw4451step1 := by
      have heq : raw4451step1 = (fun i j => raw4451step0 (permutation18 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4451step0 permutation18 permutation23
    _ = injectiveMoment H node1100 := by rfl

def raw4452 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -1, -1, 2], ![1, 0, -1, 0], ![1, 0, 3, -4]]

def raw4452step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, -1, 0, 0], ![-1, -1, -1, 3], ![2, 2, 0, -4]]

def raw4452step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 1, 0], ![0, 2, 2, -4], ![1, 0, -2, 1]]

theorem canonical4452 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4452 = injectiveMoment H node940 := by
  calc
    injectiveMoment H raw4452 = injectiveMoment H raw4452step0 := by
      have heq : raw4452step0 = raw4452.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4452).symm
    injectiveMoment H raw4452step0 = injectiveMoment H raw4452step1 := by
      have heq : raw4452step1 = (fun i j => raw4452step0 (permutation24 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4452step0 permutation24 permutation23
    _ = injectiveMoment H node940 := by rfl

def raw4453 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -1, -1, 2], ![1, 0, 3, -4], ![1, 0, -1, 0]]

def raw4453step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, -1, 0, 0], ![-1, -1, 3, -1], ![2, 2, -4, 0]]

def raw4453step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 1, 0], ![0, 2, 2, -4], ![1, 0, -2, 1]]

theorem canonical4453 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4453 = injectiveMoment H node940 := by
  calc
    injectiveMoment H raw4453 = injectiveMoment H raw4453step0 := by
      have heq : raw4453step0 = raw4453.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4453).symm
    injectiveMoment H raw4453step0 = injectiveMoment H raw4453step1 := by
      have heq : raw4453step1 = (fun i j => raw4453step0 (permutation24 i) (permutation29 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4453step0 permutation24 permutation29
    _ = injectiveMoment H node940 := by rfl

def raw4454 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -1, 0, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, 1, 2, -4]]

def raw4454step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, -1, 1, -2], ![0, 1, 0, -1], ![0, 0, 1, -1], ![-1, 1, 0, 0], ![-1, -1, -2, 4]]

def raw4454step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![1, 0, 0, -1], ![1, 2, -1, -2]]

theorem canonical4454 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4454 = injectiveMoment H node1552 := by
  calc
    injectiveMoment H raw4454 = injectiveMoment H raw4454step0 := by
      have heq : raw4454step0 = -raw4454 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4454).symm
    injectiveMoment H raw4454step0 = injectiveMoment H raw4454step1 := by
      have heq : raw4454step1 = (fun i j => raw4454step0 (permutation148 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4454step0 permutation148 permutation21
    _ = injectiveMoment H node1552 := by rfl

def raw4455 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -1, 0, 1], ![0, 0, -1, 1], ![1, -1, 1, -1], ![1, 1, 1, -3]]

def raw4455step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 0, 1], ![0, 0, -1, 1], ![1, 1, -1, -1], ![1, 1, 1, -3]]

theorem canonical4455 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4455 = injectiveMoment H node1736 := by
  calc
    injectiveMoment H raw4455 = injectiveMoment H raw4455step0 := by
      have heq : raw4455step0 = (fun i j => raw4455 (permutation39 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4455 permutation39 permutation11
    _ = injectiveMoment H node1736 := by rfl

def raw4456 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -1, 0, 1], ![0, 0, 1, -1], ![1, -1, 1, -1], ![1, 1, -1, -1]]

def raw4456step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 1, -1, -1]]

theorem canonical4456 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4456 = injectiveMoment H node1771 := by
  calc
    injectiveMoment H raw4456 = injectiveMoment H raw4456step0 := by
      have heq : raw4456step0 = (fun i j => raw4456 (permutation34 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4456 permutation34 permutation11
    _ = injectiveMoment H node1771 := by rfl

def raw4457 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -1, 0, 1], ![0, 0, 2, -2], ![1, -1, 0, 0], ![1, 1, -1, -1]]

def raw4457step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 2, 0, -2], ![1, -1, 1, -1], ![1, 0, -1, 0]]

theorem canonical4457 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4457 = injectiveMoment H node1776 := by
  calc
    injectiveMoment H raw4457 = injectiveMoment H raw4457step0 := by
      have heq : raw4457step0 = (fun i j => raw4457 (permutation34 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4457 permutation34 permutation11
    _ = injectiveMoment H node1776 := by rfl

def raw4458 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -1, 1, 0], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, 1, 1, -3]]

def raw4458step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 0, 1], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 1, 1, -3]]

theorem canonical4458 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4458 = injectiveMoment H node1739 := by
  calc
    injectiveMoment H raw4458 = injectiveMoment H raw4458step0 := by
      have heq : raw4458step0 = (fun i j => raw4458 (permutation39 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4458 permutation39 permutation11
    _ = injectiveMoment H node1739 := by rfl

def raw4459 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -1, 1, 0], ![0, 0, -1, 1], ![1, 0, 0, -1], ![1, 0, 1, -2]]

def raw4459step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 1, -2], ![1, -2, -1, 2]]

theorem canonical4459 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4459 = injectiveMoment H node2822 := by
  calc
    injectiveMoment H raw4459 = injectiveMoment H raw4459step0 := by
      have heq : raw4459step0 = (fun i j => raw4459 (permutation65 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4459 permutation65 permutation15
    _ = injectiveMoment H node2822 := by rfl

def raw4460 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -1, 1, 0], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 1, -1, -1]]

def raw4460step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 0, -1, 0]]

theorem canonical4460 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4460 = injectiveMoment H node1825 := by
  calc
    injectiveMoment H raw4460 = injectiveMoment H raw4460step0 := by
      have heq : raw4460step0 = (fun i j => raw4460 (permutation34 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4460 permutation34 permutation11
    _ = injectiveMoment H node1825 := by rfl

def raw4461 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -1, 1, 0], ![1, -1, -1, 1], ![1, 1, 1, -3]]

def raw4461step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, -1, -1, 1], ![-1, 1, -1, 1], ![2, 0, 1, -3]]

def raw4461step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 1, -3, 2], ![0, 1, 1, -2], ![1, -1, 1, -1]]

theorem canonical4461 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4461 = injectiveMoment H node1123 := by
  calc
    injectiveMoment H raw4461 = injectiveMoment H raw4461step0 := by
      have heq : raw4461step0 = raw4461.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4461).symm
    injectiveMoment H raw4461step0 = injectiveMoment H raw4461step1 := by
      have heq : raw4461step1 = (fun i j => raw4461step0 (permutation19 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4461step0 permutation19 permutation18
    _ = injectiveMoment H node1123 := by rfl

def raw4462 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -1, 1, 0], ![1, -1, 1, -1], ![1, 1, -1, -1]]

def raw4462step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, -1, -1, 1], ![-1, 1, 1, -1], ![2, 0, -1, -1]]

def raw4462step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, -1, 2], ![0, 1, 1, -2], ![1, 1, -1, -1]]

theorem canonical4462 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4462 = injectiveMoment H node1096 := by
  calc
    injectiveMoment H raw4462 = injectiveMoment H raw4462step0 := by
      have heq : raw4462step0 = raw4462.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4462).symm
    injectiveMoment H raw4462step0 = injectiveMoment H raw4462step1 := by
      have heq : raw4462step1 = (fun i j => raw4462step0 (permutation19 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4462step0 permutation19 permutation18
    _ = injectiveMoment H node1096 := by rfl

def raw4463 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -1, 2, -1], ![0, 0, -2, 2], ![1, -1, 0, 0], ![1, 1, 1, -3]]

theorem canonical4463 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4463 = injectiveMoment H node2205 := by
  rfl

def raw4464 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -1, 2, -1], ![0, 0, -2, 2], ![2, 0, 1, -3]]

def raw4464step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, 0, -2, 2], ![0, 2, 1, -3], ![1, -2, -1, 2]]

theorem canonical4464 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4464 = injectiveMoment H node1315 := by
  calc
    injectiveMoment H raw4464 = injectiveMoment H raw4464step0 := by
      have heq : raw4464step0 = (fun i j => raw4464 (permutation18 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4464 permutation18 permutation15
    _ = injectiveMoment H node1315 := by rfl

def raw4465 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -1, 2, -1], ![0, 0, -1, 1], ![1, -1, -1, 1], ![1, 1, 1, -3]]

theorem canonical4465 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4465 = injectiveMoment H node2206 := by
  rfl

def raw4466 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -1, 2, -1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, 1, 0, -2]]

def raw4466step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 0, 1], ![0, 2, -1, -1], ![1, 0, -1, 0], ![1, 0, 1, -2]]

theorem canonical4466 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4466 = injectiveMoment H node1741 := by
  calc
    injectiveMoment H raw4466 = injectiveMoment H raw4466step0 := by
      have heq : raw4466step0 = (fun i j => raw4466 (permutation39 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4466 permutation39 permutation11
    _ = injectiveMoment H node1741 := by rfl

def raw4467 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -1, 2, -1], ![0, 0, 0, 0], ![1, -1, 0, 0], ![1, 1, -1, -1]]

def raw4467step0 : Matrix (Fin 4) (Fin 5) ℤ := ![![-2, 0, 0, 1, 1], ![1, -1, 0, -1, 1], ![-1, 2, 0, 0, -1], ![2, -1, 0, 0, -1]]

def raw4467step1 : Matrix (Fin 4) (Fin 5) ℤ := ![![2, 0, 0, -1, -1], ![-1, 1, 0, 1, -1], ![1, -2, 0, 0, 1], ![-2, 1, 0, 0, 1]]

def raw4467step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, 1, 1, -1], ![1, -2, 0, 1], ![-2, 1, 0, 1]]

def raw4467step3 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, -2, 1], ![0, 1, 1, -2], ![1, -1, 1, -1]]

theorem canonical4467 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4467 = injectiveMoment H node1078 := by
  calc
    injectiveMoment H raw4467 = injectiveMoment H raw4467step0 := by
      have heq : raw4467step0 = raw4467.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4467).symm
    injectiveMoment H raw4467step0 = injectiveMoment H raw4467step1 := by
      have heq : raw4467step1 = -raw4467step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4467step0).symm
    injectiveMoment H raw4467step1 = injectiveMoment H raw4467step2 := by
      have hz : ∀ i, raw4467step1 i (permutation80 0) = 0 := by decide +kernel
      have heq : raw4467step2 = (fun i j => raw4467step1 i (permutation80 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw4467step1 permutation80 hz
    injectiveMoment H raw4467step2 = injectiveMoment H raw4467step3 := by
      have heq : raw4467step3 = (fun i j => raw4467step2 (permutation12 i) (permutation26 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4467step2 permutation12 permutation26
    _ = injectiveMoment H node1078 := by rfl

def raw4468 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -1, 2, -1], ![0, 0, 1, -1], ![1, -1, -1, 1], ![1, 1, -1, -1]]

theorem canonical4468 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4468 = injectiveMoment H node2208 := by
  rfl

def raw4469 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -1, 2, -1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 1, -2, 0]]

def raw4469step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, -1, 1, -2], ![0, 1, -2, 1], ![0, 0, -1, 1], ![-1, 1, 0, 0], ![-1, -1, 2, 0]]

def raw4469step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, -1, -1, 2], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 1, 0, -2]]

theorem canonical4469 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4469 = injectiveMoment H node1834 := by
  calc
    injectiveMoment H raw4469 = injectiveMoment H raw4469step0 := by
      have heq : raw4469step0 = -raw4469 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4469).symm
    injectiveMoment H raw4469step0 = injectiveMoment H raw4469step1 := by
      have heq : raw4469step1 = (fun i j => raw4469step0 (permutation56 i) (permutation29 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4469step0 permutation56 permutation29
    _ = injectiveMoment H node1834 := by rfl

def raw4470 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -1, 2, -1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw4470step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, -1, 1, -2], ![0, 1, -2, 1], ![0, -1, 1, 0], ![-1, 1, 0, 0], ![-1, 0, 0, 1]]

def raw4470step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 1, 0], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 1, -2, 0]]

theorem canonical4470 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4470 = injectiveMoment H node1751 := by
  calc
    injectiveMoment H raw4470 = injectiveMoment H raw4470step0 := by
      have heq : raw4470step0 = -raw4470 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4470).symm
    injectiveMoment H raw4470step0 = injectiveMoment H raw4470step1 := by
      have heq : raw4470step1 = (fun i j => raw4470step0 (permutation42 i) (permutation30 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4470step0 permutation42 permutation30
    _ = injectiveMoment H node1751 := by rfl

def raw4471 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -1, 2, -1], ![0, 1, -1, 0], ![2, -1, 0, -1]]

def raw4471step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, -1, 1, -1], ![-1, 2, -1, 0], ![2, -1, 0, -1]]

def raw4471step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -1, -1, 2], ![0, 2, 0, -2], ![1, -1, -1, 1]]

theorem canonical4471 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4471 = injectiveMoment H node1309 := by
  calc
    injectiveMoment H raw4471 = injectiveMoment H raw4471step0 := by
      have heq : raw4471step0 = raw4471.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4471).symm
    injectiveMoment H raw4471step0 = injectiveMoment H raw4471step1 := by
      have heq : raw4471step1 = (fun i j => raw4471step0 (permutation25 i) (permutation26 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4471step0 permutation25 permutation26
    _ = injectiveMoment H node1309 := by rfl

def raw4472 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -1, 2, -1], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 0, 0, -1]]

def raw4472step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, -1, -1, 1], ![1, 0, 0, -1]]

theorem canonical4472 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4472 = injectiveMoment H node1801 := by
  calc
    injectiveMoment H raw4472 = injectiveMoment H raw4472step0 := by
      have heq : raw4472step0 = (fun i j => raw4472 (permutation39 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4472 permutation39 permutation11
    _ = injectiveMoment H node1801 := by rfl

def raw4473 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -1, 2, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def raw4473step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, -1, 1, -2], ![0, 1, -2, 1], ![0, -1, 0, 1], ![-1, 1, 0, 0], ![-1, 0, 1, 0]]

def raw4473step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 1, -2, 0]]

theorem canonical4473 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4473 = injectiveMoment H node1793 := by
  calc
    injectiveMoment H raw4473 = injectiveMoment H raw4473step0 := by
      have heq : raw4473step0 = -raw4473 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4473).symm
    injectiveMoment H raw4473step0 = injectiveMoment H raw4473step1 := by
      have heq : raw4473step1 = (fun i j => raw4473step0 (permutation56 i) (permutation30 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4473step0 permutation56 permutation30
    _ = injectiveMoment H node1793 := by rfl

def raw4474 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -1, 2, -1], ![1, -1, -2, 2], ![1, 1, 1, -3]]

theorem canonical4474 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4474 = injectiveMoment H node679 := by
  rfl

def raw4475 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -1, 2, -1], ![1, -1, -1, 1], ![1, 1, 0, -2]]

def raw4475step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 2, -1, -1], ![1, -1, -1, 1], ![1, 0, 1, -2]]

theorem canonical4475 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4475 = injectiveMoment H node517 := by
  calc
    injectiveMoment H raw4475 = injectiveMoment H raw4475step0 := by
      have heq : raw4475step0 = (fun i j => raw4475 (permutation9 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4475 permutation9 permutation11
    _ = injectiveMoment H node517 := by rfl

def raw4476 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -1, 2, -1], ![1, -1, 0, 0], ![1, 1, -1, -1]]

def raw4476step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, -1, -1, 1], ![-1, 2, 0, -1], ![2, -1, 0, -1]]

def raw4476step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, 1, 1, -1], ![1, -2, 0, 1], ![-2, 1, 0, 1]]

def raw4476step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, -2, 1], ![0, 1, 1, -2], ![1, -1, 1, -1]]

theorem canonical4476 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4476 = injectiveMoment H node1078 := by
  calc
    injectiveMoment H raw4476 = injectiveMoment H raw4476step0 := by
      have heq : raw4476step0 = raw4476.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4476).symm
    injectiveMoment H raw4476step0 = injectiveMoment H raw4476step1 := by
      have heq : raw4476step1 = -raw4476step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4476step0).symm
    injectiveMoment H raw4476step1 = injectiveMoment H raw4476step2 := by
      have heq : raw4476step2 = (fun i j => raw4476step1 (permutation12 i) (permutation26 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4476step1 permutation12 permutation26
    _ = injectiveMoment H node1078 := by rfl

def raw4477 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -1, 2, -1], ![1, -1, 1, -1], ![1, 1, -2, 0]]

def raw4477step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, -1, 1, -2], ![0, 1, -2, 1], ![-1, 1, -1, 1], ![-1, -1, 2, 0]]

def raw4477step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, -1, -1, 2], ![1, 1, -1, -1], ![1, 1, 0, -2]]

theorem canonical4477 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4477 = injectiveMoment H node522 := by
  calc
    injectiveMoment H raw4477 = injectiveMoment H raw4477step0 := by
      have heq : raw4477step0 = -raw4477 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4477).symm
    injectiveMoment H raw4477step0 = injectiveMoment H raw4477step1 := by
      have heq : raw4477step1 = (fun i j => raw4477step0 (permutation14 i) (permutation29 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4477step0 permutation14 permutation29
    _ = injectiveMoment H node522 := by rfl

def raw4478 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -1, 3, -2], ![0, 1, -2, 1], ![1, -1, 0, 0], ![1, 0, 0, -1]]

theorem canonical4478 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4478 = injectiveMoment H node2210 := by
  rfl

def raw4479 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -1, 3, -2], ![0, 1, -2, 1], ![2, -1, 0, -1]]

def raw4479step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, -1, 1, -1], ![-1, 3, -2, 0], ![2, -2, 1, -1]]

def raw4479step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 2, -2, 0], ![1, -1, 1, -1], ![1, -1, 2, -2]]

theorem canonical4479 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4479 = injectiveMoment H node603 := by
  calc
    injectiveMoment H raw4479 = injectiveMoment H raw4479step0 := by
      have heq : raw4479step0 = raw4479.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4479).symm
    injectiveMoment H raw4479step0 = injectiveMoment H raw4479step1 := by
      have heq : raw4479step1 = (fun i j => raw4479step0 (permutation21 i) (permutation25 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4479step0 permutation21 permutation25
    _ = injectiveMoment H node603 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
