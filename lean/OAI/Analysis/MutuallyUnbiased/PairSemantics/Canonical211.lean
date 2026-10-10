import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes0
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes2
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes3
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes4
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes11
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes13
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes17

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw6752 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]

def raw6752step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1]]

def raw6752step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]

theorem canonical6752 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6752 = injectiveMoment H node1141 := by
  calc
    injectiveMoment H raw6752 = injectiveMoment H raw6752step0 := by
      have heq : raw6752step0 = -raw6752 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6752).symm
    injectiveMoment H raw6752step0 = injectiveMoment H raw6752step1 := by
      have heq : raw6752step1 = (fun i j => raw6752step0 (permutation126 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6752step0 permutation126 permutation4
    _ = injectiveMoment H node1141 := by rfl

def raw6753 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]

def raw6753step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0]]

def raw6753step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2]]

theorem canonical6753 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6753 = injectiveMoment H node709 := by
  calc
    injectiveMoment H raw6753 = injectiveMoment H raw6753step0 := by
      have heq : raw6753step0 = -raw6753 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6753).symm
    injectiveMoment H raw6753step0 = injectiveMoment H raw6753step1 := by
      have heq : raw6753step1 = (fun i j => raw6753step0 (permutation50 i) (permutation7 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6753step0 permutation50 permutation7
    _ = injectiveMoment H node709 := by rfl

def raw6754 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 1, -2]]

theorem canonical6754 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6754 = injectiveMoment H node276 := by
  rfl

def raw6755 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1]]

def raw6755step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1]]

def raw6755step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]

theorem canonical6755 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6755 = injectiveMoment H node230 := by
  calc
    injectiveMoment H raw6755 = injectiveMoment H raw6755step0 := by
      have heq : raw6755step0 = -raw6755 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6755).symm
    injectiveMoment H raw6755step0 = injectiveMoment H raw6755step1 := by
      have heq : raw6755step1 = (fun i j => raw6755step0 (permutation20 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6755step0 permutation20 permutation5
    _ = injectiveMoment H node230 := by rfl

def raw6756 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 3, -2], ![0, -3, 3], ![1, 0, -1], ![1, 1, -2]]

def raw6756step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![1, -3, 2], ![0, 3, -3], ![-1, 0, 1], ![-1, -1, 2]]

def raw6756step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, 3, -3], ![1, -3, 2], ![1, 1, -2]]

theorem canonical6756 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6756 = injectiveMoment H node1137 := by
  calc
    injectiveMoment H raw6756 = injectiveMoment H raw6756step0 := by
      have heq : raw6756step0 = -raw6756 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6756).symm
    injectiveMoment H raw6756step0 = injectiveMoment H raw6756step1 := by
      have heq : raw6756step1 = (fun i j => raw6756step0 (permutation150 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6756step0 permutation150 permutation3
    _ = injectiveMoment H node1137 := by rfl

def raw6757 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 3, -2], ![0, -3, 3], ![1, 1, -2], ![1, 0, -1]]

def raw6757step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![1, -3, 2], ![0, 3, -3], ![-1, -1, 2], ![-1, 0, 1]]

def raw6757step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, 3, -3], ![1, -3, 2], ![1, 1, -2]]

theorem canonical6757 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6757 = injectiveMoment H node1137 := by
  calc
    injectiveMoment H raw6757 = injectiveMoment H raw6757step0 := by
      have heq : raw6757step0 = -raw6757 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6757).symm
    injectiveMoment H raw6757step0 = injectiveMoment H raw6757step1 := by
      have heq : raw6757step1 = (fun i j => raw6757step0 (permutation127 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6757step0 permutation127 permutation3
    _ = injectiveMoment H node1137 := by rfl

def raw6758 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 3, -2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1]]

theorem canonical6758 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6758 = injectiveMoment H node1143 := by
  rfl

def raw6759 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 3, -2], ![0, -2, 2], ![2, 0, -2]]

def raw6759step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![1, -3, 2], ![0, 2, -2], ![-2, 0, 2]]

def raw6759step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![1, -3, 2], ![1, 1, -2]]

theorem canonical6759 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6759 = injectiveMoment H node212 := by
  calc
    injectiveMoment H raw6759 = injectiveMoment H raw6759step0 := by
      have heq : raw6759step0 = -raw6759 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6759).symm
    injectiveMoment H raw6759step0 = injectiveMoment H raw6759step1 := by
      have heq : raw6759step1 = (fun i j => raw6759step0 (permutation32 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6759step0 permutation32 permutation3
    _ = injectiveMoment H node212 := by rfl

def raw6760 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 3, -2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1]]

def raw6760step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

theorem canonical6760 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6760 = injectiveMoment H node872 := by
  calc
    injectiveMoment H raw6760 = injectiveMoment H raw6760step0 := by
      have heq : raw6760step0 = (fun i j => raw6760 (permutation58 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6760 permutation58 permutation4
    _ = injectiveMoment H node872 := by rfl

def raw6761 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 3, -2], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0]]

def raw6761step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

theorem canonical6761 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6761 = injectiveMoment H node872 := by
  calc
    injectiveMoment H raw6761 = injectiveMoment H raw6761step0 := by
      have heq : raw6761step0 = (fun i j => raw6761 (permutation57 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6761 permutation57 permutation4
    _ = injectiveMoment H node872 := by rfl

def raw6762 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 3, -2], ![1, -3, 2], ![1, 1, -2]]

def raw6762step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 2, -3]]

theorem canonical6762 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6762 = injectiveMoment H node260 := by
  calc
    injectiveMoment H raw6762 = injectiveMoment H raw6762step0 := by
      have heq : raw6762step0 = (fun i j => raw6762 (permutation16 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6762 permutation16 permutation4
    _ = injectiveMoment H node260 := by rfl

def raw6763 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 3, -2], ![1, -2, 1], ![1, 0, -1]]

def raw6763step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2]]

theorem canonical6763 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6763 = injectiveMoment H node261 := by
  calc
    injectiveMoment H raw6763 = injectiveMoment H raw6763step0 := by
      have heq : raw6763step0 = (fun i j => raw6763 (permutation16 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6763 permutation16 permutation4
    _ = injectiveMoment H node261 := by rfl

def raw6764 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 3, -2], ![1, -1, 0], ![1, -1, 0]]

def raw6764step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]

theorem canonical6764 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6764 = injectiveMoment H node176 := by
  calc
    injectiveMoment H raw6764 = injectiveMoment H raw6764step0 := by
      have heq : raw6764step0 = (fun i j => raw6764 (permutation18 i) (permutation7 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6764 permutation18 permutation7
    _ = injectiveMoment H node176 := by rfl

def raw6765 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 4, -3], ![0, -3, 3], ![1, 0, -1], ![1, 0, -1]]

theorem canonical6765 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6765 = injectiveMoment H node1144 := by
  rfl

def raw6766 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 4, -3], ![0, -3, 3], ![2, 0, -2]]

def raw6766step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![1, -4, 3], ![0, 3, -3], ![-2, 0, 2]]

def raw6766step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![1, -4, 3], ![1, 1, -2]]

theorem canonical6766 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6766 = injectiveMoment H node213 := by
  calc
    injectiveMoment H raw6766 = injectiveMoment H raw6766step0 := by
      have heq : raw6766step0 = -raw6766 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6766).symm
    injectiveMoment H raw6766step0 = injectiveMoment H raw6766step1 := by
      have heq : raw6766step1 = (fun i j => raw6766step0 (permutation32 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6766step0 permutation32 permutation3
    _ = injectiveMoment H node213 := by rfl

def raw6767 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 4, -3], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1]]

def raw6767step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 2, -1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]

theorem canonical6767 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6767 = injectiveMoment H node743 := by
  calc
    injectiveMoment H raw6767 = injectiveMoment H raw6767step0 := by
      have heq : raw6767step0 = (fun i j => raw6767 (permutation58 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6767 permutation58 permutation4
    _ = injectiveMoment H node743 := by rfl

def raw6768 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 4, -3], ![0, -2, 2], ![1, 0, -1], ![1, -1, 0]]

def raw6768step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 2, -1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]

theorem canonical6768 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6768 = injectiveMoment H node743 := by
  calc
    injectiveMoment H raw6768 = injectiveMoment H raw6768step0 := by
      have heq : raw6768step0 = (fun i j => raw6768 (permutation57 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6768 permutation57 permutation4
    _ = injectiveMoment H node743 := by rfl

def raw6769 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 4, -3], ![0, -2, 2], ![2, -1, -1]]

def raw6769step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![1, -4, 3], ![0, 2, -2], ![-2, 1, 1]]

def raw6769step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![1, -2, 1], ![1, 3, -4]]

theorem canonical6769 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6769 = injectiveMoment H node225 := by
  calc
    injectiveMoment H raw6769 = injectiveMoment H raw6769step0 := by
      have heq : raw6769step0 = -raw6769 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6769).symm
    injectiveMoment H raw6769step0 = injectiveMoment H raw6769step1 := by
      have heq : raw6769step1 = (fun i j => raw6769step0 (permutation31 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6769step0 permutation31 permutation4
    _ = injectiveMoment H node225 := by rfl

def raw6770 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 4, -3], ![1, -3, 2], ![1, 0, -1]]

def raw6770step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 2, -1], ![1, -1, 0], ![1, 2, -3]]

theorem canonical6770 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6770 = injectiveMoment H node245 := by
  calc
    injectiveMoment H raw6770 = injectiveMoment H raw6770step0 := by
      have heq : raw6770step0 = (fun i j => raw6770 (permutation16 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6770 permutation16 permutation4
    _ = injectiveMoment H node245 := by rfl

def raw6771 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 4, -3], ![1, -2, 1], ![1, -1, 0]]

def raw6771step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 2, -1], ![1, 0, -1], ![1, 1, -2]]

theorem canonical6771 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6771 = injectiveMoment H node246 := by
  calc
    injectiveMoment H raw6771 = injectiveMoment H raw6771step0 := by
      have heq : raw6771step0 = (fun i j => raw6771 (permutation16 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6771 permutation16 permutation4
    _ = injectiveMoment H node246 := by rfl

def raw6772 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -3, 3], ![0, 4, -4], ![1, 0, -1]]

theorem canonical6772 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6772 = injectiveMoment H node278 := by
  rfl

def raw6773 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -3, 3], ![1, 4, -5]]

def raw6773step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 1, -2], ![0, 3, -3], ![-1, -4, 5]]

def raw6773step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -4, 5], ![0, 3, -3], ![1, 1, -2]]

theorem canonical6773 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6773 = injectiveMoment H node49 := by
  calc
    injectiveMoment H raw6773 = injectiveMoment H raw6773step0 := by
      have heq : raw6773step0 = -raw6773 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6773).symm
    injectiveMoment H raw6773step0 = injectiveMoment H raw6773step1 := by
      have heq : raw6773step1 = (fun i j => raw6773step0 (permutation8 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6773step0 permutation8 permutation3
    _ = injectiveMoment H node49 := by rfl

def raw6774 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -2, 2], ![-1, 2, -1], ![1, 0, -1], ![1, 1, -2]]

def raw6774step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 2, -2], ![1, -2, 1], ![-1, 0, 1], ![-1, -1, 2]]

def raw6774step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![1, 1, -2]]

theorem canonical6774 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6774 = injectiveMoment H node1136 := by
  calc
    injectiveMoment H raw6774 = injectiveMoment H raw6774step0 := by
      have heq : raw6774step0 = -raw6774 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6774).symm
    injectiveMoment H raw6774step0 = injectiveMoment H raw6774step1 := by
      have heq : raw6774step1 = (fun i j => raw6774step0 (permutation148 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6774step0 permutation148 permutation3
    _ = injectiveMoment H node1136 := by rfl

def raw6775 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -2, 2], ![-1, 3, -2], ![1, 0, -1], ![1, 0, -1]]

def raw6775step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 3, -2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1]]

theorem canonical6775 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6775 = injectiveMoment H node1143 := by
  calc
    injectiveMoment H raw6775 = injectiveMoment H raw6775step0 := by
      have heq : raw6775step0 = (fun i j => raw6775 (permutation39 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6775 permutation39 permutation3
    _ = injectiveMoment H node1143 := by rfl

def raw6776 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -2, 2], ![-1, 4, -3], ![1, -1, 0], ![1, 0, -1]]

def raw6776step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 2, -1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]

theorem canonical6776 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6776 = injectiveMoment H node743 := by
  calc
    injectiveMoment H raw6776 = injectiveMoment H raw6776step0 := by
      have heq : raw6776step0 = (fun i j => raw6776 (permutation81 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6776 permutation81 permutation4
    _ = injectiveMoment H node743 := by rfl

def raw6777 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -2, 2], ![0, -1, 1], ![0, 4, -4], ![1, 0, -1]]

theorem canonical6777 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6777 = injectiveMoment H node1145 := by
  rfl

def raw6778 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1]]

theorem canonical6778 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6778 = injectiveMoment H node1147 := by
  rfl

def raw6779 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 2, -3]]

def raw6779step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![0, 2, -2], ![0, -1, 1], ![-1, -2, 3]]

def raw6779step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2]]

theorem canonical6779 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6779 = injectiveMoment H node268 := by
  calc
    injectiveMoment H raw6779 = injectiveMoment H raw6779step0 := by
      have heq : raw6779step0 = -raw6779 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6779).symm
    injectiveMoment H raw6779step0 = injectiveMoment H raw6779step1 := by
      have heq : raw6779step1 = (fun i j => raw6779step0 (permutation32 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6779step0 permutation32 permutation3
    _ = injectiveMoment H node268 := by rfl

def raw6780 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -2, 2], ![0, 2, -2], ![0, 0, 0], ![1, 1, -2]]

def raw6780step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 1, -2]]

theorem canonical6780 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6780 = injectiveMoment H node279 := by
  calc
    injectiveMoment H raw6780 = injectiveMoment H raw6780step0 := by
      have hz : ∀ j, raw6780 (permutation104 0) j = 0 := by decide +kernel
      have heq : raw6780step0 = (fun i j => raw6780 (permutation104 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw6780 permutation104 hz
    _ = injectiveMoment H node279 := by rfl

def raw6781 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -2, 2], ![0, 2, -2], ![0, 1, -1], ![1, 0, -1]]

def raw6781step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1]]

theorem canonical6781 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6781 = injectiveMoment H node1147 := by
  calc
    injectiveMoment H raw6781 = injectiveMoment H raw6781step0 := by
      have heq : raw6781step0 = (fun i j => raw6781 (permutation35 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6781 permutation35 permutation3
    _ = injectiveMoment H node1147 := by rfl

def raw6782 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![0, 1, -1]]

def raw6782step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1]]

theorem canonical6782 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6782 = injectiveMoment H node1147 := by
  calc
    injectiveMoment H raw6782 = injectiveMoment H raw6782step0 := by
      have heq : raw6782step0 = (fun i j => raw6782 (permutation37 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6782 permutation37 permutation3
    _ = injectiveMoment H node1147 := by rfl

def raw6783 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 1, -2]]

theorem canonical6783 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6783 = injectiveMoment H node279 := by
  rfl

end MUB6.Certificate.PairSemantics

end OAI
