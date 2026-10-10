import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes2
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes3
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes4
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes17
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes19
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes40
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes41
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes43

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw6624 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, 1, 0], ![0, 2, -2, 0], ![1, 0, 0, -1]]

def raw6624step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, -1, 2, 0], ![1, 1, -2, 0], ![1, 0, 0, -1]]

def raw6624step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 1, 0], ![0, 1, -1, 0], ![1, 0, 1, -2]]

theorem canonical6624 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6624 = injectiveMoment H node1241 := by
  calc
    injectiveMoment H raw6624 = injectiveMoment H raw6624step0 := by
      have heq : raw6624step0 = raw6624.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6624).symm
    injectiveMoment H raw6624step0 = injectiveMoment H raw6624step1 := by
      have heq : raw6624step1 = (fun i j => raw6624step0 (permutation19 i) (permutation19 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6624step0 permutation19 permutation19
    _ = injectiveMoment H node1241 := by rfl

def raw6625 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, 1, 0], ![0, 2, -1, -1], ![1, 0, -1, 0]]

def raw6625step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 1, -1]]

theorem canonical6625 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6625 = injectiveMoment H node1262 := by
  calc
    injectiveMoment H raw6625 = injectiveMoment H raw6625step0 := by
      have heq : raw6625step0 = (fun i j => raw6625 (permutation24 i) (permutation28 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6625 permutation24 permutation28
    _ = injectiveMoment H node1262 := by rfl

def raw6626 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, 1, 0], ![1, 2, -2, -1]]

def raw6626step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![1, 1, -2], ![1, 0, -1]]

def raw6626step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2]]

theorem canonical6626 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6626 = injectiveMoment H node283 := by
  calc
    injectiveMoment H raw6626 = injectiveMoment H raw6626step0 := by
      have heq : raw6626step0 = raw6626.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6626).symm
    injectiveMoment H raw6626step0 = injectiveMoment H raw6626step1 := by
      have heq : raw6626step1 = (fun i j => raw6626step0 (permutation16 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6626step0 permutation16 permutation5
    _ = injectiveMoment H node283 := by rfl

def raw6627 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, 2, -1], ![1, 2, -3, 0]]

def raw6627step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![1, 2, -3], ![1, -1, 0]]

def raw6627step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![1, 1, -2], ![-1, -2, 3], ![-1, 1, 0]]

def raw6627step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

theorem canonical6627 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6627 = injectiveMoment H node181 := by
  calc
    injectiveMoment H raw6627 = injectiveMoment H raw6627step0 := by
      have heq : raw6627step0 = raw6627.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6627).symm
    injectiveMoment H raw6627step0 = injectiveMoment H raw6627step1 := by
      have heq : raw6627step1 = -raw6627step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6627step0).symm
    injectiveMoment H raw6627step1 = injectiveMoment H raw6627step2 := by
      have heq : raw6627step2 = (fun i j => raw6627step1 (permutation22 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6627step1 permutation22 permutation5
    _ = injectiveMoment H node181 := by rfl

def raw6628 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, 3, -2], ![1, 2, -4, 1]]

def raw6628step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![1, 3, -4], ![1, -2, 1]]

def raw6628step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![1, 1, -2], ![-1, -3, 4], ![-1, 2, -1]]

def raw6628step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 2, -1], ![1, 0, -1], ![1, 1, -2]]

theorem canonical6628 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6628 = injectiveMoment H node246 := by
  calc
    injectiveMoment H raw6628 = injectiveMoment H raw6628step0 := by
      have heq : raw6628step0 = raw6628.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6628).symm
    injectiveMoment H raw6628step0 = injectiveMoment H raw6628step1 := by
      have heq : raw6628step1 = -raw6628step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6628step0).symm
    injectiveMoment H raw6628step1 = injectiveMoment H raw6628step2 := by
      have heq : raw6628step2 = (fun i j => raw6628step1 (permutation25 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6628step1 permutation25 permutation3
    _ = injectiveMoment H node246 := by rfl

def raw6629 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -3, 3], ![0, 2, 2, -4], ![1, -1, 0, 0]]

def raw6629step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 0, 2, -1], ![1, -3, 2, 0], ![1, 3, -4, 0]]

def raw6629step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, -3, 2], ![0, 1, 3, -4], ![1, -1, 0, 0]]

theorem canonical6629 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6629 = injectiveMoment H node1075 := by
  calc
    injectiveMoment H raw6629 = injectiveMoment H raw6629step0 := by
      have heq : raw6629step0 = raw6629.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6629).symm
    injectiveMoment H raw6629step0 = injectiveMoment H raw6629step1 := by
      have heq : raw6629step1 = (fun i j => raw6629step0 (permutation18 i) (permutation27 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6629step0 permutation18 permutation27
    _ = injectiveMoment H node1075 := by rfl

def raw6630 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -3, 3], ![1, 1, 2, -4]]

def raw6630step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![1, -3, 2], ![1, 3, -4]]

def raw6630step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![1, 0, -1], ![-1, 3, -2], ![-1, -3, 4]]

def raw6630step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 3, -2], ![1, 0, -1], ![1, 0, -1]]

theorem canonical6630 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6630 = injectiveMoment H node248 := by
  calc
    injectiveMoment H raw6630 = injectiveMoment H raw6630step0 := by
      have heq : raw6630step0 = raw6630.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6630).symm
    injectiveMoment H raw6630step0 = injectiveMoment H raw6630step1 := by
      have heq : raw6630step1 = -raw6630step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6630step0).symm
    injectiveMoment H raw6630step1 = injectiveMoment H raw6630step2 := by
      have heq : raw6630step2 = (fun i j => raw6630step1 (permutation31 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6630step1 permutation31 permutation3
    _ = injectiveMoment H node248 := by rfl

def raw6631 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -2, 2], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, -1, 0, 0]]

theorem canonical6631 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6631 = injectiveMoment H node2634 := by
  rfl

def raw6632 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -2, 2], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, -1, 0, 0]]

theorem canonical6632 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6632 = injectiveMoment H node2636 := by
  rfl

def raw6633 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -2, 2], ![0, 1, -1, 0], ![1, 0, 2, -3]]

theorem canonical6633 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6633 = injectiveMoment H node1109 := by
  rfl

def raw6634 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, 0, 1, -2]]

theorem canonical6634 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6634 = injectiveMoment H node1110 := by
  rfl

def raw6635 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -2, 2], ![0, 1, 1, -2], ![1, 0, 0, -1]]

def raw6635step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, 0, 1, -2]]

theorem canonical6635 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6635 = injectiveMoment H node1110 := by
  calc
    injectiveMoment H raw6635 = injectiveMoment H raw6635step0 := by
      have heq : raw6635step0 = (fun i j => raw6635 (permutation10 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6635 permutation10 permutation15
    _ = injectiveMoment H node1110 := by rfl

def raw6636 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -2, 2], ![0, 1, 2, -3], ![1, 0, -1, 0]]

def raw6636step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -2, 2], ![0, 1, -1, 0], ![1, 0, 2, -3]]

theorem canonical6636 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6636 = injectiveMoment H node1109 := by
  calc
    injectiveMoment H raw6636 = injectiveMoment H raw6636step0 := by
      have heq : raw6636step0 = (fun i j => raw6636 (permutation10 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6636 permutation10 permutation15
    _ = injectiveMoment H node1109 := by rfl

def raw6637 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -2, 2], ![0, 2, 0, -2], ![1, -1, 1, -1]]

theorem canonical6637 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6637 = injectiveMoment H node1112 := by
  rfl

def raw6638 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -2, 2], ![0, 2, 1, -3], ![1, -1, 0, 0]]

def raw6638step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 0, 2, -1], ![1, -2, 1, 0], ![1, 2, -3, 0]]

def raw6638step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, -2, 1], ![0, 1, 2, -3], ![1, -1, 0, 0]]

theorem canonical6638 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6638 = injectiveMoment H node1079 := by
  calc
    injectiveMoment H raw6638 = injectiveMoment H raw6638step0 := by
      have heq : raw6638step0 = raw6638.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6638).symm
    injectiveMoment H raw6638step0 = injectiveMoment H raw6638step1 := by
      have heq : raw6638step1 = (fun i j => raw6638step0 (permutation18 i) (permutation27 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6638step0 permutation18 permutation27
    _ = injectiveMoment H node1079 := by rfl

def raw6639 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -2, 2], ![0, 2, 2, -4], ![1, -1, -1, 1]]

theorem canonical6639 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6639 = injectiveMoment H node1113 := by
  rfl

def raw6640 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -2, 2], ![1, 1, 1, -3]]

def raw6640step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 2, -3]]

def raw6640step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![1, 0, -1], ![-1, 2, -1], ![-1, -2, 3]]

def raw6640step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]

theorem canonical6640 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6640 = injectiveMoment H node176 := by
  calc
    injectiveMoment H raw6640 = injectiveMoment H raw6640step0 := by
      have heq : raw6640step0 = raw6640.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6640).symm
    injectiveMoment H raw6640step0 = injectiveMoment H raw6640step1 := by
      have heq : raw6640step1 = -raw6640step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6640step0).symm
    injectiveMoment H raw6640step1 = injectiveMoment H raw6640step2 := by
      have heq : raw6640step2 = (fun i j => raw6640step1 (permutation27 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6640step1 permutation27 permutation5
    _ = injectiveMoment H node176 := by rfl

def raw6641 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -1, 1], ![0, -1, -1, 2], ![0, 2, 1, -3], ![1, 0, 0, -1]]

def raw6641step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, -1, 2], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, 0, 0, -1]]

theorem canonical6641 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6641 = injectiveMoment H node2621 := by
  calc
    injectiveMoment H raw6641 = injectiveMoment H raw6641step0 := by
      have heq : raw6641step0 = (fun i j => raw6641 (permutation39 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6641 permutation39 permutation9
    _ = injectiveMoment H node2621 := by rfl

def raw6642 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -1, 1], ![0, -1, -1, 2], ![0, 2, 2, -4], ![1, 0, -1, 0]]

def raw6642step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, -1, 2], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, 0, -1, 0]]

theorem canonical6642 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6642 = injectiveMoment H node2622 := by
  calc
    injectiveMoment H raw6642 = injectiveMoment H raw6642step0 := by
      have heq : raw6642step0 = (fun i j => raw6642 (permutation39 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6642 permutation39 permutation9
    _ = injectiveMoment H node2622 := by rfl

def raw6643 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -1, 1], ![0, -1, 0, 1], ![0, 2, 0, -2], ![1, 0, 0, -1]]

def raw6643step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 1, -1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, -2, 0, 2], ![-1, 0, 0, 1]]

def raw6643step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, -2, 2], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 1, -1]]

theorem canonical6643 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6643 = injectiveMoment H node2780 := by
  calc
    injectiveMoment H raw6643 = injectiveMoment H raw6643step0 := by
      have heq : raw6643step0 = -raw6643 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6643).symm
    injectiveMoment H raw6643step0 = injectiveMoment H raw6643step1 := by
      have heq : raw6643step1 = (fun i j => raw6643step0 (permutation150 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6643step0 permutation150 permutation11
    _ = injectiveMoment H node2780 := by rfl

def raw6644 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -1, 1], ![0, 0, -2, 2], ![0, 2, 2, -4], ![1, -1, 0, 0]]

def raw6644step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -2, 2], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, -1, 0, 0]]

theorem canonical6644 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6644 = injectiveMoment H node2634 := by
  calc
    injectiveMoment H raw6644 = injectiveMoment H raw6644step0 := by
      have heq : raw6644step0 = (fun i j => raw6644 (permutation39 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6644 permutation39 permutation9
    _ = injectiveMoment H node2634 := by rfl

def raw6645 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, 0, 2, -3]]

theorem canonical6645 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6645 = injectiveMoment H node2638 := by
  rfl

def raw6646 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 1, -2], ![1, 0, 0, -1]]

def raw6646step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, 0, 1, -2]]

theorem canonical6646 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6646 = injectiveMoment H node2639 := by
  calc
    injectiveMoment H raw6646 = injectiveMoment H raw6646step0 := by
      have heq : raw6646step0 = (fun i j => raw6646 (permutation34 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6646 permutation34 permutation15
    _ = injectiveMoment H node2639 := by rfl

def raw6647 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 2, -3], ![1, 0, -1, 0]]

def raw6647step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, 0, 2, -3]]

theorem canonical6647 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6647 = injectiveMoment H node2638 := by
  calc
    injectiveMoment H raw6647 = injectiveMoment H raw6647step0 := by
      have heq : raw6647step0 = (fun i j => raw6647 (permutation34 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6647 permutation34 permutation15
    _ = injectiveMoment H node2638 := by rfl

def raw6648 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 2, 0, -2], ![1, -1, 1, -1]]

def raw6648step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 1, -1, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, -2, 0, 2], ![-1, 1, -1, 1]]

def raw6648step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -2, 2], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, 1, -1]]

theorem canonical6648 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6648 = injectiveMoment H node2637 := by
  calc
    injectiveMoment H raw6648 = injectiveMoment H raw6648step0 := by
      have heq : raw6648step0 = -raw6648 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6648).symm
    injectiveMoment H raw6648step0 = injectiveMoment H raw6648step1 := by
      have heq : raw6648step1 = (fun i j => raw6648step0 (permutation148 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6648step0 permutation148 permutation11
    _ = injectiveMoment H node2637 := by rfl

def raw6649 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, -1, 0, 0]]

theorem canonical6649 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6649 = injectiveMoment H node2640 := by
  rfl

def raw6650 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, -1, -1, 1]]

theorem canonical6650 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6650 = injectiveMoment H node2641 := by
  rfl

def raw6651 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -1, 1], ![0, 1, -2, 1], ![0, 1, 2, -3], ![1, -1, 0, 0]]

theorem canonical6651 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6651 = injectiveMoment H node2644 := by
  rfl

def raw6652 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -1, 1], ![0, 1, -2, 1], ![1, 0, 2, -3]]

theorem canonical6652 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6652 = injectiveMoment H node1116 := by
  rfl

def raw6653 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 0, -1, 1], ![1, 0, 2, -3]]

def raw6653step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, 0, 2, -3]]

theorem canonical6653 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6653 = injectiveMoment H node2638 := by
  calc
    injectiveMoment H raw6653 = injectiveMoment H raw6653step0 := by
      have heq : raw6653step0 = (fun i j => raw6653 (permutation35 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6653 permutation35 permutation9
    _ = injectiveMoment H node2638 := by rfl

def raw6654 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 0, 1, -1], ![1, 0, 0, -1]]

def raw6654step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 0, 0, -1]]

theorem canonical6654 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6654 = injectiveMoment H node2642 := by
  calc
    injectiveMoment H raw6654 = injectiveMoment H raw6654step0 := by
      have heq : raw6654step0 = (fun i j => raw6654 (permutation35 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6654 permutation35 permutation9
    _ = injectiveMoment H node2642 := by rfl

def raw6655 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 2, -2]]

def raw6655step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, -2, 2]]

theorem canonical6655 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6655 = injectiveMoment H node2647 := by
  calc
    injectiveMoment H raw6655 = injectiveMoment H raw6655step0 := by
      have heq : raw6655step0 = (fun i j => raw6655 (permutation33 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6655 permutation33 permutation10
    _ = injectiveMoment H node2647 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
