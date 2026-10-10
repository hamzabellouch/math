import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes2
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes3
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes4
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes13
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes14
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes15
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes17
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes19
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes21
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes40
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes41
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes43
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes44

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw6592 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![-1, 2, 1, -2], ![2, -1, -2, 1]]

def raw6592step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![1, 1, -2], ![1, -2, 1]]

def raw6592step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 1, -2]]

theorem canonical6592 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6592 = injectiveMoment H node276 := by
  calc
    injectiveMoment H raw6592 = injectiveMoment H raw6592step0 := by
      have heq : raw6592step0 = raw6592.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6592).symm
    injectiveMoment H raw6592step0 = injectiveMoment H raw6592step1 := by
      have heq : raw6592step1 = (fun i j => raw6592step0 (permutation10 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6592step0 permutation10 permutation3
    _ = injectiveMoment H node276 := by rfl

def raw6593 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![-1, 3, -3, 1], ![2, -2, 2, -2]]

def raw6593step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 3, -2], ![1, -3, 2], ![1, 1, -2]]

def raw6593step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 2, -3]]

theorem canonical6593 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6593 = injectiveMoment H node260 := by
  calc
    injectiveMoment H raw6593 = injectiveMoment H raw6593step0 := by
      have heq : raw6593step0 = raw6593.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6593).symm
    injectiveMoment H raw6593step0 = injectiveMoment H raw6593step1 := by
      have heq : raw6593step1 = (fun i j => raw6593step0 (permutation16 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6593step0 permutation16 permutation4
    _ = injectiveMoment H node260 := by rfl

def raw6594 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![-1, 3, -2, 0], ![2, -2, 1, -1]]

def raw6594step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 3, -2], ![1, -2, 1], ![1, 0, -1]]

def raw6594step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2]]

theorem canonical6594 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6594 = injectiveMoment H node261 := by
  calc
    injectiveMoment H raw6594 = injectiveMoment H raw6594step0 := by
      have heq : raw6594step0 = raw6594.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6594).symm
    injectiveMoment H raw6594step0 = injectiveMoment H raw6594step1 := by
      have heq : raw6594step1 = (fun i j => raw6594step0 (permutation16 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6594step0 permutation16 permutation4
    _ = injectiveMoment H node261 := by rfl

def raw6595 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![-1, 4, -3, 0], ![2, -3, 2, -1]]

def raw6595step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 4, -3], ![1, -3, 2], ![1, 0, -1]]

def raw6595step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 2, -1], ![1, -1, 0], ![1, 2, -3]]

theorem canonical6595 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6595 = injectiveMoment H node245 := by
  calc
    injectiveMoment H raw6595 = injectiveMoment H raw6595step0 := by
      have heq : raw6595step0 = raw6595.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6595).symm
    injectiveMoment H raw6595step0 = injectiveMoment H raw6595step1 := by
      have heq : raw6595step1 = (fun i j => raw6595step0 (permutation16 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6595step0 permutation16 permutation4
    _ = injectiveMoment H node245 := by rfl

def raw6596 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -2, 2, 0], ![1, 3, -3, -1]]

def raw6596step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -2, 3], ![1, 2, -3], ![1, 0, -1]]

def raw6596step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![2, 1, -3]]

theorem canonical6596 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6596 = injectiveMoment H node168 := by
  calc
    injectiveMoment H raw6596 = injectiveMoment H raw6596step0 := by
      have heq : raw6596step0 = raw6596.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6596).symm
    injectiveMoment H raw6596step0 = injectiveMoment H raw6596step1 := by
      have heq : raw6596step1 = (fun i j => raw6596step0 (permutation16 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6596step0 permutation16 permutation5
    _ = injectiveMoment H node168 := by rfl

def raw6597 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -2, 3, -1], ![1, 3, -4, 0]]

def raw6597step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -2, 3], ![1, 3, -4], ![1, -1, 0]]

def raw6597step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![1, 2, -3], ![-1, -3, 4], ![-1, 1, 0]]

def raw6597step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 1, 0], ![1, 0, -1], ![1, 2, -3]]

theorem canonical6597 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6597 = injectiveMoment H node243 := by
  calc
    injectiveMoment H raw6597 = injectiveMoment H raw6597step0 := by
      have heq : raw6597step0 = raw6597.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6597).symm
    injectiveMoment H raw6597step0 = injectiveMoment H raw6597step1 := by
      have heq : raw6597step1 = -raw6597step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6597step0).symm
    injectiveMoment H raw6597step1 = injectiveMoment H raw6597step2 := by
      have heq : raw6597step2 = (fun i j => raw6597step1 (permutation25 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6597step1 permutation25 permutation3
    _ = injectiveMoment H node243 := by rfl

def raw6598 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, -2, 3], ![0, 1, 1, -2], ![1, 1, 0, -2]]

def raw6598step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 1, -1, -1], ![0, 1, 2, -3], ![0, -1, -1, 2], ![-1, -1, 0, 2]]

def raw6598step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, -1, 2], ![0, 1, 2, -3], ![1, 1, -1, -1]]

theorem canonical6598 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6598 = injectiveMoment H node995 := by
  calc
    injectiveMoment H raw6598 = injectiveMoment H raw6598step0 := by
      have heq : raw6598step0 = -raw6598 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6598).symm
    injectiveMoment H raw6598step0 = injectiveMoment H raw6598step1 := by
      have heq : raw6598step1 = (fun i j => raw6598step0 (permutation32 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6598step0 permutation32 permutation9
    _ = injectiveMoment H node995 := by rfl

def raw6599 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, -2, 3], ![0, 2, 0, -2], ![1, 0, 1, -2]]

def raw6599step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 1, -1, -1], ![0, 1, 2, -3], ![0, -2, 0, 2], ![-1, 0, -1, 2]]

def raw6599step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 2, 1, -3], ![1, -1, 1, -1]]

theorem canonical6599 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6599 = injectiveMoment H node1036 := by
  calc
    injectiveMoment H raw6599 = injectiveMoment H raw6599step0 := by
      have heq : raw6599step0 = -raw6599 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6599).symm
    injectiveMoment H raw6599step0 = injectiveMoment H raw6599step1 := by
      have heq : raw6599step1 = (fun i j => raw6599step0 (permutation32 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6599step0 permutation32 permutation11
    _ = injectiveMoment H node1036 := by rfl

def raw6600 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, -2, 3], ![0, 2, 1, -3], ![1, 0, 0, -1]]

theorem canonical6600 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6600 = injectiveMoment H node1094 := by
  rfl

def raw6601 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, -2, 3], ![0, 2, 2, -4], ![1, 0, -1, 0]]

theorem canonical6601 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6601 = injectiveMoment H node1095 := by
  rfl

def raw6602 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, -2, 3], ![1, 2, 1, -4]]

def raw6602step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![1, -2, 1], ![1, 3, -4]]

def raw6602step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![1, 1, -2], ![-1, 2, -1], ![-1, -3, 4]]

def raw6602step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 2, -1], ![1, 0, -1], ![1, 1, -2]]

theorem canonical6602 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6602 = injectiveMoment H node246 := by
  calc
    injectiveMoment H raw6602 = injectiveMoment H raw6602step0 := by
      have heq : raw6602step0 = raw6602.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6602).symm
    injectiveMoment H raw6602step0 = injectiveMoment H raw6602step1 := by
      have heq : raw6602step1 = -raw6602step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6602step0).symm
    injectiveMoment H raw6602step1 = injectiveMoment H raw6602step2 := by
      have heq : raw6602step2 = (fun i j => raw6602step1 (permutation31 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6602step1 permutation31 permutation3
    _ = injectiveMoment H node246 := by rfl

def raw6603 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, -1, 2], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, 0, 0, -1]]

theorem canonical6603 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6603 = injectiveMoment H node2621 := by
  rfl

def raw6604 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, -1, 2], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, 0, -1, 0]]

theorem canonical6604 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6604 = injectiveMoment H node2622 := by
  rfl

def raw6605 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, -1, 2], ![0, 1, -2, 1], ![1, 1, 2, -4]]

def raw6605step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 1, -1, -1], ![0, 1, 1, -2], ![0, -1, 2, -1], ![-1, -1, -2, 4]]

def raw6605step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, -1, 2, -1], ![0, 1, 1, -2], ![1, 1, -1, -1]]

theorem canonical6605 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6605 = injectiveMoment H node894 := by
  calc
    injectiveMoment H raw6605 = injectiveMoment H raw6605step0 := by
      have heq : raw6605step0 = -raw6605 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6605).symm
    injectiveMoment H raw6605step0 = injectiveMoment H raw6605step1 := by
      have heq : raw6605step1 = (fun i j => raw6605step0 (permutation32 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6605step0 permutation32 permutation9
    _ = injectiveMoment H node894 := by rfl

def raw6606 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, -1, 2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 2, -3]]

theorem canonical6606 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6606 = injectiveMoment H node2624 := by
  rfl

def raw6607 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, -1, 2], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, 0, 0, -1]]

theorem canonical6607 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6607 = injectiveMoment H node2625 := by
  rfl

def raw6608 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, -1, 2], ![0, 1, -1, 0], ![1, 1, 1, -3]]

def raw6608step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 1, -1, -1], ![0, 1, 1, -2], ![0, -1, 1, 0], ![-1, -1, -1, 3]]

def raw6608step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 1, 0], ![0, 1, 1, -2], ![1, 1, -1, -1]]

theorem canonical6608 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6608 = injectiveMoment H node936 := by
  calc
    injectiveMoment H raw6608 = injectiveMoment H raw6608step0 := by
      have heq : raw6608step0 = -raw6608 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6608).symm
    injectiveMoment H raw6608step0 = injectiveMoment H raw6608step1 := by
      have heq : raw6608step1 = (fun i j => raw6608step0 (permutation32 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6608step0 permutation32 permutation9
    _ = injectiveMoment H node936 := by rfl

def raw6609 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, -1, 2], ![0, 1, 1, -2], ![1, 1, -1, -1]]

theorem canonical6609 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6609 = injectiveMoment H node1096 := by
  rfl

def raw6610 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, -1, 2], ![0, 2, -2, 0], ![1, 0, 2, -3]]

theorem canonical6610 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6610 = injectiveMoment H node1098 := by
  rfl

def raw6611 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, -1, 2], ![0, 2, -1, -1], ![1, 0, 1, -2]]

def raw6611step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 1, -1, -1], ![0, 1, 1, -2], ![0, -2, 1, 1], ![-1, 0, -1, 2]]

def raw6611step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, -2, 1], ![0, 1, 1, -2], ![1, -1, 1, -1]]

theorem canonical6611 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6611 = injectiveMoment H node1078 := by
  calc
    injectiveMoment H raw6611 = injectiveMoment H raw6611step0 := by
      have heq : raw6611step0 = -raw6611 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6611).symm
    injectiveMoment H raw6611step0 = injectiveMoment H raw6611step1 := by
      have heq : raw6611step1 = (fun i j => raw6611step0 (permutation32 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6611step0 permutation32 permutation11
    _ = injectiveMoment H node1078 := by rfl

def raw6612 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, -1, 2], ![0, 2, 0, -2], ![1, 0, 0, -1]]

def raw6612step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, -1, -1, 1]]

theorem canonical6612 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6612 = injectiveMoment H node1265 := by
  calc
    injectiveMoment H raw6612 = injectiveMoment H raw6612step0 := by
      have heq : raw6612step0 = (fun i j => raw6612 (permutation18 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6612 permutation18 permutation21
    _ = injectiveMoment H node1265 := by rfl

def raw6613 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, -1, 2], ![0, 2, 1, -3], ![1, 0, -1, 0]]

theorem canonical6613 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6613 = injectiveMoment H node1099 := by
  rfl

def raw6614 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, -1, 2], ![0, 2, 2, -4], ![1, 0, -2, 1]]

theorem canonical6614 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6614 = injectiveMoment H node1100 := by
  rfl

def raw6615 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, -1, 2], ![1, 2, 0, -3]]

def raw6615step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 2, -3]]

def raw6615step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![1, 1, -2], ![-1, 1, 0], ![-1, -2, 3]]

def raw6615step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

theorem canonical6615 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6615 = injectiveMoment H node181 := by
  calc
    injectiveMoment H raw6615 = injectiveMoment H raw6615step0 := by
      have heq : raw6615step0 = raw6615.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6615).symm
    injectiveMoment H raw6615step0 = injectiveMoment H raw6615step1 := by
      have heq : raw6615step1 = -raw6615step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6615step0).symm
    injectiveMoment H raw6615step1 = injectiveMoment H raw6615step2 := by
      have heq : raw6615step2 = (fun i j => raw6615step1 (permutation28 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6615step1 permutation28 permutation5
    _ = injectiveMoment H node181 := by rfl

def raw6616 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 2, 0, -2], ![1, 0, 0, -1]]

def raw6616step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 1, -1, -1], ![0, 1, 0, -1], ![0, 0, 1, -1], ![0, -2, 0, 2], ![-1, 0, 0, 1]]

def raw6616step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, -2, 2], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 1, -1]]

theorem canonical6616 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6616 = injectiveMoment H node2780 := by
  calc
    injectiveMoment H raw6616 = injectiveMoment H raw6616step0 := by
      have heq : raw6616step0 = -raw6616 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6616).symm
    injectiveMoment H raw6616step0 = injectiveMoment H raw6616step1 := by
      have heq : raw6616step1 = (fun i j => raw6616step0 (permutation148 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6616step0 permutation148 permutation11
    _ = injectiveMoment H node2780 := by rfl

def raw6617 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, 0, 1], ![0, 2, -1, -1], ![1, 0, 0, -1]]

def raw6617step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 1, -1]]

theorem canonical6617 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6617 = injectiveMoment H node1262 := by
  calc
    injectiveMoment H raw6617 = injectiveMoment H raw6617step0 := by
      have heq : raw6617step0 = (fun i j => raw6617 (permutation24 i) (permutation22 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6617 permutation24 permutation22
    _ = injectiveMoment H node1262 := by rfl

def raw6618 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, 0, 1], ![0, 2, 1, -3], ![1, 0, -2, 1]]

def raw6618step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, -1, 2, 0], ![1, 0, 1, -2], ![1, 1, -3, 1]]

def raw6618step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 0, -1], ![1, 1, -2, 0], ![-1, 0, -1, 2], ![-1, -1, 3, -1]]

def raw6618step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 1, 0], ![0, 2, -1, -1], ![1, 0, 1, -2]]

theorem canonical6618 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6618 = injectiveMoment H node939 := by
  calc
    injectiveMoment H raw6618 = injectiveMoment H raw6618step0 := by
      have heq : raw6618step0 = raw6618.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6618).symm
    injectiveMoment H raw6618step0 = injectiveMoment H raw6618step1 := by
      have heq : raw6618step1 = -raw6618step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6618step0).symm
    injectiveMoment H raw6618step1 = injectiveMoment H raw6618step2 := by
      have heq : raw6618step2 = (fun i j => raw6618step1 (permutation28 i) (permutation19 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6618step1 permutation28 permutation19
    _ = injectiveMoment H node939 := by rfl

def raw6619 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, 1, 0], ![-1, 1, 0, 0], ![1, 0, -1, 0], ![1, 1, -1, -1]]

def raw6619step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, 0, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 1, -1, -1]]

theorem canonical6619 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6619 = injectiveMoment H node2628 := by
  calc
    injectiveMoment H raw6619 = injectiveMoment H raw6619step0 := by
      have heq : raw6619step0 = (fun i j => raw6619 (permutation150 i) (permutation32 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6619 permutation150 permutation32
    _ = injectiveMoment H node2628 := by rfl

def raw6620 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, 1, 0], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1]]

def raw6620step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, 0, 0]]

theorem canonical6620 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6620 = injectiveMoment H node2846 := by
  calc
    injectiveMoment H raw6620 = injectiveMoment H raw6620step0 := by
      have heq : raw6620step0 = (fun i j => raw6620 (permutation33 i) (permutation13 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6620 permutation33 permutation13
    _ = injectiveMoment H node2846 := by rfl

def raw6621 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, 1, 0], ![0, 1, -1, 0], ![1, 1, -1, -1]]

def raw6621step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 1, -1]]

theorem canonical6621 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6621 = injectiveMoment H node1349 := by
  calc
    injectiveMoment H raw6621 = injectiveMoment H raw6621step0 := by
      have heq : raw6621step0 = (fun i j => raw6621 (permutation9 i) (permutation13 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6621 permutation9 permutation13
    _ = injectiveMoment H node1349 := by rfl

def raw6622 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, 1, 0], ![0, 1, 0, -1], ![0, 0, -1, 1], ![1, 1, -1, -1]]

def raw6622step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, 0, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 1, -1, -1]]

theorem canonical6622 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6622 = injectiveMoment H node2628 := by
  calc
    injectiveMoment H raw6622 = injectiveMoment H raw6622step0 := by
      have heq : raw6622step0 = (fun i j => raw6622 (permutation35 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6622 permutation35 permutation10
    _ = injectiveMoment H node2628 := by rfl

def raw6623 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, 1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0], ![0, 1, -1, 0]]

def raw6623step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 1, -1]]

theorem canonical6623 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6623 = injectiveMoment H node2783 := by
  calc
    injectiveMoment H raw6623 = injectiveMoment H raw6623step0 := by
      have heq : raw6623step0 = (fun i j => raw6623 (permutation101 i) (permutation28 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6623 permutation101 permutation28
    _ = injectiveMoment H node2783 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
