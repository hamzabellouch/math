import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes0
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes2
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes3
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes4
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes12
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes13
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes14
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes17
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes19

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw6528 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, -1, 2, -2]]

def raw6528step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 1, 0, -2], ![0, -1, 2, -1], ![0, -1, 0, 1], ![-1, 1, -2, 2]]

def raw6528step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -1, 1], ![0, 2, -1, -1], ![1, 0, 1, -2]]

theorem canonical6528 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6528 = injectiveMoment H node837 := by
  calc
    injectiveMoment H raw6528 = injectiveMoment H raw6528step0 := by
      have heq : raw6528step0 = -raw6528 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6528).symm
    injectiveMoment H raw6528step0 = injectiveMoment H raw6528step1 := by
      have heq : raw6528step1 = (fun i j => raw6528step0 (permutation32 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6528step0 permutation32 permutation11
    _ = injectiveMoment H node837 := by rfl

def raw6529 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, -2, 1], ![0, 1, 1, -2], ![1, -1, 1, -1]]

theorem canonical6529 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6529 = injectiveMoment H node1078 := by
  rfl

def raw6530 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, -2, 1], ![0, 1, 2, -3], ![1, -1, 0, 0]]

theorem canonical6530 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6530 = injectiveMoment H node1079 := by
  rfl

def raw6531 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, -2, 1], ![0, 1, 3, -4], ![1, -1, -1, 1]]

theorem canonical6531 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6531 = injectiveMoment H node1080 := by
  rfl

def raw6532 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, -2, 1], ![1, 0, 2, -3]]

def raw6532step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -2, 2], ![2, 1, -3]]

def raw6532step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![1, -1, 0], ![0, 2, -2], ![-2, -1, 3]]

def raw6532step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]

theorem canonical6532 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6532 = injectiveMoment H node185 := by
  calc
    injectiveMoment H raw6532 = injectiveMoment H raw6532step0 := by
      have heq : raw6532step0 = raw6532.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6532).symm
    injectiveMoment H raw6532step0 = injectiveMoment H raw6532step1 := by
      have heq : raw6532step1 = -raw6532step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6532step0).symm
    injectiveMoment H raw6532step1 = injectiveMoment H raw6532step2 := by
      have heq : raw6532step2 = (fun i j => raw6532step1 (permutation32 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6532step1 permutation32 permutation3
    _ = injectiveMoment H node185 := by rfl

def raw6533 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, -1, 0], ![0, 0, 2, -2], ![1, 0, -1, 0]]

def raw6533step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, 0, -1, 0]]

theorem canonical6533 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6533 = injectiveMoment H node1054 := by
  calc
    injectiveMoment H raw6533 = injectiveMoment H raw6533step0 := by
      have heq : raw6533step0 = (fun i j => raw6533 (permutation11 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6533 permutation11 permutation9
    _ = injectiveMoment H node1054 := by rfl

def raw6534 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, -1, 0], ![0, 1, -2, 1], ![1, -1, 3, -3]]

def raw6534step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 1, 1, -1], ![0, -1, -2, 3], ![2, 0, 1, -3]]

def raw6534step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, -1, 1], ![0, 1, 2, -3], ![1, 1, -1, -1]]

theorem canonical6534 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6534 = injectiveMoment H node797 := by
  calc
    injectiveMoment H raw6534 = injectiveMoment H raw6534step0 := by
      have heq : raw6534step0 = raw6534.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6534).symm
    injectiveMoment H raw6534step0 = injectiveMoment H raw6534step1 := by
      have heq : raw6534step1 = (fun i j => raw6534step0 (permutation22 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6534step0 permutation22 permutation17
    _ = injectiveMoment H node797 := by rfl

def raw6535 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 2, -2]]

def raw6535step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 1, 1, -1], ![0, -1, -1, 2], ![2, 0, 0, -2]]

def raw6535step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 0, 2, -2], ![1, 1, -1, -1]]

theorem canonical6535 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6535 = injectiveMoment H node1040 := by
  calc
    injectiveMoment H raw6535 = injectiveMoment H raw6535step0 := by
      have heq : raw6535step0 = raw6535.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6535).symm
    injectiveMoment H raw6535step0 = injectiveMoment H raw6535step1 := by
      have heq : raw6535step1 = (fun i j => raw6535step0 (permutation22 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6535step0 permutation22 permutation17
    _ = injectiveMoment H node1040 := by rfl

def raw6536 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 1, -1]]

def raw6536step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 1, 0, -2], ![0, -1, 1, 0], ![0, -1, 0, 1], ![-1, 1, -1, 1]]

def raw6536step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, 0, 1, -2]]

theorem canonical6536 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6536 = injectiveMoment H node1117 := by
  calc
    injectiveMoment H raw6536 = injectiveMoment H raw6536step0 := by
      have heq : raw6536step0 = -raw6536 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6536).symm
    injectiveMoment H raw6536step0 = injectiveMoment H raw6536step1 := by
      have heq : raw6536step1 = (fun i j => raw6536step0 (permutation32 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6536step0 permutation32 permutation11
    _ = injectiveMoment H node1117 := by rfl

def raw6537 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, -1, 0, 0]]

def raw6537step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 1, 0], ![0, 1, 1, -2], ![1, 0, -1, 0]]

theorem canonical6537 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6537 = injectiveMoment H node1242 := by
  calc
    injectiveMoment H raw6537 = injectiveMoment H raw6537step0 := by
      have heq : raw6537step0 = (fun i j => raw6537 (permutation9 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6537 permutation9 permutation11
    _ = injectiveMoment H node1242 := by rfl

def raw6538 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, -1, -1, 1]]

theorem canonical6538 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6538 = injectiveMoment H node1081 := by
  rfl

def raw6539 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, -1, -2, 2]]

theorem canonical6539 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6539 = injectiveMoment H node1082 := by
  rfl

def raw6540 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, -1, 0], ![1, 0, 1, -2]]

def raw6540step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2]]

def raw6540step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0]]

theorem canonical6540 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6540 = injectiveMoment H node294 := by
  calc
    injectiveMoment H raw6540 = injectiveMoment H raw6540step0 := by
      have heq : raw6540step0 = raw6540.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6540).symm
    injectiveMoment H raw6540step0 = injectiveMoment H raw6540step1 := by
      have heq : raw6540step1 = (fun i j => raw6540step0 (permutation22 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6540step0 permutation22 permutation5
    _ = injectiveMoment H node294 := by rfl

def raw6541 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, 0, -1], ![0, 1, -1, 0], ![1, -1, 1, -1]]

def raw6541step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 1, 0, -2], ![0, -1, 0, 1], ![0, -1, 1, 0], ![-1, 1, -1, 1]]

def raw6541step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, 0, 1, -2]]

theorem canonical6541 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6541 = injectiveMoment H node1117 := by
  calc
    injectiveMoment H raw6541 = injectiveMoment H raw6541step0 := by
      have heq : raw6541step0 = -raw6541 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6541).symm
    injectiveMoment H raw6541step0 = injectiveMoment H raw6541step1 := by
      have heq : raw6541step1 = (fun i j => raw6541step0 (permutation30 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6541step0 permutation30 permutation11
    _ = injectiveMoment H node1117 := by rfl

def raw6542 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, 0, -1], ![0, 1, 1, -2], ![1, -1, -1, 1]]

def raw6542step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 1, 0, -2], ![0, -1, 0, 1], ![0, -1, -1, 2], ![-1, 1, 1, -1]]

def raw6542step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, -1, 1], ![0, 1, 1, -2], ![1, -1, 1, -1]]

theorem canonical6542 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6542 = injectiveMoment H node1260 := by
  calc
    injectiveMoment H raw6542 = injectiveMoment H raw6542step0 := by
      have heq : raw6542step0 = -raw6542 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6542).symm
    injectiveMoment H raw6542step0 = injectiveMoment H raw6542step1 := by
      have heq : raw6542step1 = (fun i j => raw6542step0 (permutation23 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6542step0 permutation23 permutation21
    _ = injectiveMoment H node1260 := by rfl

def raw6543 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, 0, -1], ![1, 0, 0, -1]]

def raw6543step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 1, -1], ![1, 0, -1]]

theorem canonical6543 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6543 = injectiveMoment H node61 := by
  calc
    injectiveMoment H raw6543 = injectiveMoment H raw6543step0 := by
      have hz : ∀ i, raw6543 i (permutation21 0) = 0 := by decide +kernel
      have heq : raw6543step0 = (fun i j => raw6543 i (permutation21 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw6543 permutation21 hz
    _ = injectiveMoment H node61 := by rfl

def raw6544 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, 1, -2], ![0, 1, -1, 0], ![1, -1, 0, 0]]

def raw6544step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 1, 0], ![0, 1, 1, -2], ![1, 0, -1, 0]]

theorem canonical6544 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6544 = injectiveMoment H node1242 := by
  calc
    injectiveMoment H raw6544 = injectiveMoment H raw6544step0 := by
      have heq : raw6544step0 = (fun i j => raw6544 (permutation11 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6544 permutation11 permutation11
    _ = injectiveMoment H node1242 := by rfl

def raw6545 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, 1, -2], ![0, 1, 0, -1], ![1, -1, -1, 1]]

def raw6545step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 1, 0, -2], ![0, -1, -1, 2], ![0, -1, 0, 1], ![-1, 1, 1, -1]]

def raw6545step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, -1, 1], ![0, 1, 1, -2], ![1, -1, 1, -1]]

theorem canonical6545 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6545 = injectiveMoment H node1260 := by
  calc
    injectiveMoment H raw6545 = injectiveMoment H raw6545step0 := by
      have heq : raw6545step0 = -raw6545 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6545).symm
    injectiveMoment H raw6545step0 = injectiveMoment H raw6545step1 := by
      have heq : raw6545step1 = (fun i j => raw6545step0 (permutation17 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6545step0 permutation17 permutation21
    _ = injectiveMoment H node1260 := by rfl

def raw6546 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, 1, -2], ![1, 0, -1, 0]]

def raw6546step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0]]

def raw6546step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0]]

theorem canonical6546 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6546 = injectiveMoment H node294 := by
  calc
    injectiveMoment H raw6546 = injectiveMoment H raw6546step0 := by
      have heq : raw6546step0 = raw6546.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6546).symm
    injectiveMoment H raw6546step0 = injectiveMoment H raw6546step1 := by
      have heq : raw6546step1 = (fun i j => raw6546step0 (permutation24 i) (permutation7 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6546step0 permutation24 permutation7
    _ = injectiveMoment H node294 := by rfl

def raw6547 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, 2, -3], ![0, -1, 1, 0], ![1, 1, -3, 1]]

def raw6547step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 1, 0, -2], ![0, -1, -2, 3], ![0, 1, -1, 0], ![-1, -1, 3, -1]]

def raw6547step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 3, -2], ![0, 1, 0, -1], ![1, 1, -2, 0]]

theorem canonical6547 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6547 = injectiveMoment H node950 := by
  calc
    injectiveMoment H raw6547 = injectiveMoment H raw6547step0 := by
      have heq : raw6547step0 = -raw6547 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6547).symm
    injectiveMoment H raw6547step0 = injectiveMoment H raw6547step1 := by
      have heq : raw6547step1 = (fun i j => raw6547step0 (permutation30 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6547step0 permutation30 permutation10
    _ = injectiveMoment H node950 := by rfl

def raw6548 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, 2, -3], ![0, 1, -2, 1], ![1, -1, 0, 0]]

def raw6548step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, -2, 1], ![0, 1, 2, -3], ![1, -1, 0, 0]]

theorem canonical6548 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6548 = injectiveMoment H node1079 := by
  calc
    injectiveMoment H raw6548 = injectiveMoment H raw6548step0 := by
      have heq : raw6548step0 = (fun i j => raw6548 (permutation11 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6548 permutation11 permutation9
    _ = injectiveMoment H node1079 := by rfl

def raw6549 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, 2, -3], ![0, 1, -1, 0], ![1, -1, -1, 1]]

def raw6549step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, -1, -1, 1]]

theorem canonical6549 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6549 = injectiveMoment H node1081 := by
  calc
    injectiveMoment H raw6549 = injectiveMoment H raw6549step0 := by
      have heq : raw6549step0 = (fun i j => raw6549 (permutation11 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6549 permutation11 permutation9
    _ = injectiveMoment H node1081 := by rfl

def raw6550 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, 2, -3], ![0, 1, 0, -1], ![1, -1, -2, 2]]

def raw6550step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, 0, -1], ![0, 1, 2, -3], ![1, -1, -2, 2]]

theorem canonical6550 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6550 = injectiveMoment H node1083 := by
  calc
    injectiveMoment H raw6550 = injectiveMoment H raw6550step0 := by
      have heq : raw6550step0 = (fun i j => raw6550 (permutation11 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6550 permutation11 permutation9
    _ = injectiveMoment H node1083 := by rfl

def raw6551 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, 2, -3], ![1, -1, 1, -1], ![0, 1, -3, 2]]

def raw6551step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, -3, 2], ![0, 1, 2, -3], ![1, -1, 1, -1]]

theorem canonical6551 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6551 = injectiveMoment H node1074 := by
  calc
    injectiveMoment H raw6551 = injectiveMoment H raw6551step0 := by
      have heq : raw6551step0 = (fun i j => raw6551 (permutation13 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6551 permutation13 permutation9
    _ = injectiveMoment H node1074 := by rfl

def raw6552 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, 2, -3], ![1, 0, -2, 1]]

def raw6552step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, 2, -2], ![2, -3, 1]]

def raw6552step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![1, -1, 0], ![0, -2, 2], ![-2, 3, -1]]

def raw6552step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]

theorem canonical6552 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6552 = injectiveMoment H node185 := by
  calc
    injectiveMoment H raw6552 = injectiveMoment H raw6552step0 := by
      have heq : raw6552step0 = raw6552.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6552).symm
    injectiveMoment H raw6552step0 = injectiveMoment H raw6552step1 := by
      have heq : raw6552step1 = -raw6552step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6552step0).symm
    injectiveMoment H raw6552step1 = injectiveMoment H raw6552step2 := by
      have heq : raw6552step2 = (fun i j => raw6552step1 (permutation31 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6552step1 permutation31 permutation4
    _ = injectiveMoment H node185 := by rfl

def raw6553 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, 3, -4], ![0, -1, 0, 1], ![1, 1, -3, 1]]

def raw6553step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 1, -1, 1], ![0, 3, 0, -3], ![2, -4, 1, 1]]

def raw6553step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 0, -1], ![1, -1, 1, -1], ![0, -3, 0, 3], ![-2, 4, -1, -1]]

def raw6553step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 3, -3], ![0, 1, -1, 0], ![1, 1, -1, -1]]

theorem canonical6553 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6553 = injectiveMoment H node779 := by
  calc
    injectiveMoment H raw6553 = injectiveMoment H raw6553step0 := by
      have heq : raw6553step0 = raw6553.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6553).symm
    injectiveMoment H raw6553step0 = injectiveMoment H raw6553step1 := by
      have heq : raw6553step1 = -raw6553step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6553step0).symm
    injectiveMoment H raw6553step1 = injectiveMoment H raw6553step2 := by
      have heq : raw6553step2 = (fun i j => raw6553step1 (permutation31 i) (permutation22 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6553step1 permutation31 permutation22
    _ = injectiveMoment H node779 := by rfl

def raw6554 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, 3, -4], ![1, -1, 0, 0], ![0, 1, -3, 2]]

def raw6554step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, -3, 2], ![0, 1, 3, -4], ![1, -1, 0, 0]]

theorem canonical6554 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6554 = injectiveMoment H node1075 := by
  calc
    injectiveMoment H raw6554 = injectiveMoment H raw6554step0 := by
      have heq : raw6554step0 = (fun i j => raw6554 (permutation13 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6554 permutation13 permutation9
    _ = injectiveMoment H node1075 := by rfl

def raw6555 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, 3, -4], ![1, 0, -3, 2]]

def raw6555step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, 3, -3], ![2, -4, 2]]

def raw6555step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![1, -1, 0], ![0, -3, 3], ![-2, 4, -2]]

def raw6555step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1]]

theorem canonical6555 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6555 = injectiveMoment H node155 := by
  calc
    injectiveMoment H raw6555 = injectiveMoment H raw6555step0 := by
      have heq : raw6555step0 = raw6555.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6555).symm
    injectiveMoment H raw6555step0 = injectiveMoment H raw6555step1 := by
      have heq : raw6555step1 = -raw6555step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6555step0).symm
    injectiveMoment H raw6555step1 = injectiveMoment H raw6555step2 := by
      have heq : raw6555step2 = (fun i j => raw6555step1 (permutation31 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6555step1 permutation31 permutation4
    _ = injectiveMoment H node155 := by rfl

def raw6556 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 2, -3, 1], ![1, -1, 3, -3]]

def raw6556step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 2, -1], ![0, -3, 3], ![2, 1, -3]]

def raw6556step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![1, -2, 1], ![0, 3, -3], ![-2, -1, 3]]

def raw6556step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 3, -3], ![1, -2, 1], ![1, 0, -1]]

theorem canonical6556 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6556 = injectiveMoment H node187 := by
  calc
    injectiveMoment H raw6556 = injectiveMoment H raw6556step0 := by
      have heq : raw6556step0 = raw6556.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6556).symm
    injectiveMoment H raw6556step0 = injectiveMoment H raw6556step1 := by
      have heq : raw6556step1 = -raw6556step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6556step0).symm
    injectiveMoment H raw6556step1 = injectiveMoment H raw6556step2 := by
      have heq : raw6556step2 = (fun i j => raw6556step1 (permutation32 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6556step1 permutation32 permutation3
    _ = injectiveMoment H node187 := by rfl

def raw6557 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 2, -2, 0], ![1, -1, 2, -2]]

def raw6557step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 2, -1], ![0, -2, 2], ![2, 0, -2]]

def raw6557step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]

theorem canonical6557 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6557 = injectiveMoment H node203 := by
  calc
    injectiveMoment H raw6557 = injectiveMoment H raw6557step0 := by
      have heq : raw6557step0 = raw6557.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6557).symm
    injectiveMoment H raw6557step0 = injectiveMoment H raw6557step1 := by
      have heq : raw6557step1 = (fun i j => raw6557step0 (permutation22 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6557step0 permutation22 permutation5
    _ = injectiveMoment H node203 := by rfl

def raw6558 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 2, -1, -1], ![1, -1, 1, -1]]

def raw6558step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 2, -1], ![0, -1, 1], ![2, -1, -1]]

def raw6558step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![1, -2, 1], ![0, 1, -1], ![-2, 1, 1]]

def raw6558step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]

theorem canonical6558 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6558 = injectiveMoment H node230 := by
  calc
    injectiveMoment H raw6558 = injectiveMoment H raw6558step0 := by
      have heq : raw6558step0 = raw6558.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6558).symm
    injectiveMoment H raw6558step0 = injectiveMoment H raw6558step1 := by
      have heq : raw6558step1 = -raw6558step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6558step0).symm
    injectiveMoment H raw6558step1 = injectiveMoment H raw6558step2 := by
      have heq : raw6558step2 = (fun i j => raw6558step1 (permutation31 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6558step1 permutation31 permutation4
    _ = injectiveMoment H node230 := by rfl

def raw6559 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 2, 1, -3], ![1, -1, -1, 1]]

def raw6559step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 2, -1], ![0, 1, -1], ![2, -3, 1]]

def raw6559step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![1, -2, 1], ![0, -1, 1], ![-2, 3, -1]]

def raw6559step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

theorem canonical6559 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6559 = injectiveMoment H node181 := by
  calc
    injectiveMoment H raw6559 = injectiveMoment H raw6559step0 := by
      have heq : raw6559step0 = raw6559.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6559).symm
    injectiveMoment H raw6559step0 = injectiveMoment H raw6559step1 := by
      have heq : raw6559step1 = -raw6559step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6559step0).symm
    injectiveMoment H raw6559step1 = injectiveMoment H raw6559step2 := by
      have heq : raw6559step2 = (fun i j => raw6559step1 (permutation31 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6559step1 permutation31 permutation4
    _ = injectiveMoment H node181 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
