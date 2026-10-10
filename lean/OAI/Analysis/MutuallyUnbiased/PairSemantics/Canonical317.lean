import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes1
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes2
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes3
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes4

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw10144 : Matrix (Fin 3) (Fin 4) ℤ := ![![1, 0, 0, -1], ![1, -2, 2, -1], ![-2, 2, -2, 2]]

def raw10144step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![0, -2, 2], ![0, 2, -2], ![-1, -1, 2]]

def raw10144step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 1, -2]]

theorem canonical10144 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw10144 = injectiveMoment H node279 := by
  calc
    injectiveMoment H raw10144 = injectiveMoment H raw10144step0 := by
      have heq : raw10144step0 = raw10144.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw10144).symm
    injectiveMoment H raw10144step0 = injectiveMoment H raw10144step1 := by
      have heq : raw10144step1 = (fun i j => raw10144step0 (permutation30 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw10144step0 permutation30 permutation3
    _ = injectiveMoment H node279 := by rfl

def raw10145 : Matrix (Fin 3) (Fin 4) ℤ := ![![1, 0, 1, -2], ![-5, 2, 1, 2], ![4, -2, -2, 0]]

def raw10145step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -5, 4], ![0, 2, -2], ![1, 1, -2], ![-2, 2, 0]]

def raw10145step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![1, -2, 1], ![1, 4, -5]]

theorem canonical10145 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw10145 = injectiveMoment H node200 := by
  calc
    injectiveMoment H raw10145 = injectiveMoment H raw10145step0 := by
      have heq : raw10145step0 = raw10145.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw10145).symm
    injectiveMoment H raw10145step0 = injectiveMoment H raw10145step1 := by
      have heq : raw10145step1 = (fun i j => raw10145step0 (permutation30 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw10145step0 permutation30 permutation4
    _ = injectiveMoment H node200 := by rfl

def raw10146 : Matrix (Fin 3) (Fin 4) ℤ := ![![1, 0, 1, -2], ![-4, 2, 1, 1], ![3, -2, -2, 1]]

def raw10146step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -4, 3], ![0, 2, -2], ![1, 1, -2], ![-2, 1, 1]]

def raw10146step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![1, -2, 1], ![1, 3, -4]]

theorem canonical10146 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw10146 = injectiveMoment H node225 := by
  calc
    injectiveMoment H raw10146 = injectiveMoment H raw10146step0 := by
      have heq : raw10146step0 = raw10146.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw10146).symm
    injectiveMoment H raw10146step0 = injectiveMoment H raw10146step1 := by
      have heq : raw10146step1 = (fun i j => raw10146step0 (permutation30 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw10146step0 permutation30 permutation4
    _ = injectiveMoment H node225 := by rfl

def raw10147 : Matrix (Fin 3) (Fin 4) ℤ := ![![1, 0, 1, -2], ![-3, 2, 1, 0], ![2, -2, -2, 2]]

def raw10147step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![0, 2, -2], ![1, 1, -2], ![-2, 0, 2]]

def raw10147step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![1, -3, 2], ![1, 1, -2]]

theorem canonical10147 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw10147 = injectiveMoment H node212 := by
  calc
    injectiveMoment H raw10147 = injectiveMoment H raw10147step0 := by
      have heq : raw10147step0 = raw10147.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw10147).symm
    injectiveMoment H raw10147step0 = injectiveMoment H raw10147step1 := by
      have heq : raw10147step1 = (fun i j => raw10147step0 (permutation29 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw10147step0 permutation29 permutation3
    _ = injectiveMoment H node212 := by rfl

def raw10148 : Matrix (Fin 3) (Fin 4) ℤ := ![![1, 0, 1, -2], ![-3, 4, -2, 1], ![2, -4, 1, 1]]

def raw10148step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![0, 4, -4], ![1, -2, 1], ![-2, 1, 1]]

def raw10148step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -4, 4], ![1, 1, -2], ![1, 2, -3]]

theorem canonical10148 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw10148 = injectiveMoment H node219 := by
  calc
    injectiveMoment H raw10148 = injectiveMoment H raw10148step0 := by
      have heq : raw10148step0 = raw10148.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw10148).symm
    injectiveMoment H raw10148step0 = injectiveMoment H raw10148step1 := by
      have heq : raw10148step1 = (fun i j => raw10148step0 (permutation30 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw10148step0 permutation30 permutation4
    _ = injectiveMoment H node219 := by rfl

def raw10149 : Matrix (Fin 3) (Fin 4) ℤ := ![![1, 0, 1, -2], ![-2, -3, 1, 4], ![1, 3, -2, -2]]

def raw10149step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -2, 1], ![0, -3, 3], ![1, 1, -2], ![-2, 4, -2]]

def raw10149step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 3, -3], ![1, -2, 1], ![1, 1, -2]]

theorem canonical10149 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw10149 = injectiveMoment H node154 := by
  calc
    injectiveMoment H raw10149 = injectiveMoment H raw10149step0 := by
      have heq : raw10149step0 = raw10149.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw10149).symm
    injectiveMoment H raw10149step0 = injectiveMoment H raw10149step1 := by
      have heq : raw10149step1 = (fun i j => raw10149step0 (permutation30 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw10149step0 permutation30 permutation4
    _ = injectiveMoment H node154 := by rfl

def raw10150 : Matrix (Fin 3) (Fin 4) ℤ := ![![1, 0, 1, -2], ![-2, -3, 3, 2], ![1, 3, -4, 0]]

def raw10150step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -2, 1], ![0, -3, 3], ![1, 3, -4], ![-2, 2, 0]]

def raw10150step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![1, -4, 3], ![1, 1, -2]]

theorem canonical10150 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw10150 = injectiveMoment H node213 := by
  calc
    injectiveMoment H raw10150 = injectiveMoment H raw10150step0 := by
      have heq : raw10150step0 = raw10150.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw10150).symm
    injectiveMoment H raw10150step0 = injectiveMoment H raw10150step1 := by
      have heq : raw10150step1 = (fun i j => raw10150step0 (permutation30 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw10150step0 permutation30 permutation4
    _ = injectiveMoment H node213 := by rfl

def raw10151 : Matrix (Fin 3) (Fin 4) ℤ := ![![1, 0, 1, -2], ![-2, -2, 1, 3], ![1, 2, -2, -1]]

def raw10151step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -2, 1], ![0, -2, 2], ![1, 1, -2], ![-2, 3, -1]]

def raw10151step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, -2, 1], ![1, 1, -2]]

theorem canonical10151 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw10151 = injectiveMoment H node184 := by
  calc
    injectiveMoment H raw10151 = injectiveMoment H raw10151step0 := by
      have heq : raw10151step0 = raw10151.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw10151).symm
    injectiveMoment H raw10151step0 = injectiveMoment H raw10151step1 := by
      have heq : raw10151step1 = (fun i j => raw10151step0 (permutation30 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw10151step0 permutation30 permutation4
    _ = injectiveMoment H node184 := by rfl

def raw10152 : Matrix (Fin 3) (Fin 4) ℤ := ![![1, 0, 1, -2], ![-2, -2, 2, 2], ![1, 2, -3, 0]]

def raw10152step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -2, 1], ![0, -2, 2], ![1, 2, -3], ![-2, 2, 0]]

def raw10152step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![1, -3, 2], ![1, 1, -2]]

theorem canonical10152 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw10152 = injectiveMoment H node212 := by
  calc
    injectiveMoment H raw10152 = injectiveMoment H raw10152step0 := by
      have heq : raw10152step0 = raw10152.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw10152).symm
    injectiveMoment H raw10152step0 = injectiveMoment H raw10152step1 := by
      have heq : raw10152step1 = (fun i j => raw10152step0 (permutation30 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw10152step0 permutation30 permutation4
    _ = injectiveMoment H node212 := by rfl

def raw10153 : Matrix (Fin 3) (Fin 4) ℤ := ![![1, 0, 1, -2], ![-2, -2, 3, 1], ![1, 2, -4, 1]]

def raw10153step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -2, 1], ![0, -2, 2], ![1, 3, -4], ![-2, 1, 1]]

def raw10153step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![1, -2, 1], ![1, 3, -4]]

theorem canonical10153 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw10153 = injectiveMoment H node225 := by
  calc
    injectiveMoment H raw10153 = injectiveMoment H raw10153step0 := by
      have heq : raw10153step0 = raw10153.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw10153).symm
    injectiveMoment H raw10153step0 = injectiveMoment H raw10153step1 := by
      have heq : raw10153step1 = (fun i j => raw10153step0 (permutation29 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw10153step0 permutation29 permutation3
    _ = injectiveMoment H node225 := by rfl

def raw10154 : Matrix (Fin 3) (Fin 4) ℤ := ![![1, 0, 1, -2], ![-2, 2, 1, -1], ![1, -2, -2, 3]]

def raw10154step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -2, 1], ![0, 2, -2], ![1, 1, -2], ![-2, -1, 3]]

def raw10154step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, -2, 1], ![1, 1, -2]]

theorem canonical10154 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw10154 = injectiveMoment H node184 := by
  calc
    injectiveMoment H raw10154 = injectiveMoment H raw10154step0 := by
      have heq : raw10154step0 = raw10154.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw10154).symm
    injectiveMoment H raw10154step0 = injectiveMoment H raw10154step1 := by
      have heq : raw10154step1 = (fun i j => raw10154step0 (permutation29 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw10154step0 permutation29 permutation3
    _ = injectiveMoment H node184 := by rfl

def raw10155 : Matrix (Fin 3) (Fin 4) ℤ := ![![1, 0, 1, -2], ![-2, 3, -2, 1], ![1, -3, 1, 1]]

def raw10155step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -2, 1], ![0, 3, -3], ![1, -2, 1], ![-2, 1, 1]]

def raw10155step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -3, 3], ![1, 1, -2], ![1, 1, -2]]

theorem canonical10155 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw10155 = injectiveMoment H node223 := by
  calc
    injectiveMoment H raw10155 = injectiveMoment H raw10155step0 := by
      have heq : raw10155step0 = raw10155.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw10155).symm
    injectiveMoment H raw10155step0 = injectiveMoment H raw10155step1 := by
      have heq : raw10155step1 = (fun i j => raw10155step0 (permutation29 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw10155step0 permutation29 permutation4
    _ = injectiveMoment H node223 := by rfl

def raw10156 : Matrix (Fin 3) (Fin 4) ℤ := ![![1, 0, 1, -2], ![-2, 4, -3, 1], ![1, -4, 2, 1]]

def raw10156step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -2, 1], ![0, 4, -4], ![1, -3, 2], ![-2, 1, 1]]

def raw10156step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -4, 4], ![1, 1, -2], ![1, 2, -3]]

theorem canonical10156 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw10156 = injectiveMoment H node219 := by
  calc
    injectiveMoment H raw10156 = injectiveMoment H raw10156step0 := by
      have heq : raw10156step0 = raw10156.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw10156).symm
    injectiveMoment H raw10156step0 = injectiveMoment H raw10156step1 := by
      have heq : raw10156step1 = (fun i j => raw10156step0 (permutation29 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw10156step0 permutation29 permutation4
    _ = injectiveMoment H node219 := by rfl

def raw10157 : Matrix (Fin 3) (Fin 4) ℤ := ![![1, 0, 1, -2], ![-2, 4, -2, 0], ![1, -4, 1, 2]]

def raw10157step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -2, 1], ![0, 4, -4], ![1, -2, 1], ![-2, 0, 2]]

def raw10157step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 4, -4], ![1, -2, 1], ![1, -2, 1]]

theorem canonical10157 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw10157 = injectiveMoment H node218 := by
  calc
    injectiveMoment H raw10157 = injectiveMoment H raw10157step0 := by
      have heq : raw10157step0 = raw10157.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw10157).symm
    injectiveMoment H raw10157step0 = injectiveMoment H raw10157step1 := by
      have heq : raw10157step1 = (fun i j => raw10157step0 (permutation29 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw10157step0 permutation29 permutation3
    _ = injectiveMoment H node218 := by rfl

def raw10158 : Matrix (Fin 3) (Fin 4) ℤ := ![![1, 0, 1, -2], ![-1, -3, 1, 3], ![0, 3, -2, -1]]

def raw10158step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -1, 0], ![0, -3, 3], ![1, 1, -2], ![-2, 3, -1]]

def raw10158step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 3, -3], ![1, -2, 1], ![1, 0, -1]]

theorem canonical10158 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw10158 = injectiveMoment H node187 := by
  calc
    injectiveMoment H raw10158 = injectiveMoment H raw10158step0 := by
      have heq : raw10158step0 = raw10158.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw10158).symm
    injectiveMoment H raw10158step0 = injectiveMoment H raw10158step1 := by
      have heq : raw10158step1 = (fun i j => raw10158step0 (permutation30 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw10158step0 permutation30 permutation4
    _ = injectiveMoment H node187 := by rfl

def raw10159 : Matrix (Fin 3) (Fin 4) ℤ := ![![1, 0, 1, -2], ![-1, -3, 3, 1], ![0, 3, -4, 1]]

def raw10159step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -1, 0], ![0, -3, 3], ![1, 3, -4], ![-2, 1, 1]]

def raw10159step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -3, 3], ![1, -1, 0], ![1, 3, -4]]

theorem canonical10159 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw10159 = injectiveMoment H node221 := by
  calc
    injectiveMoment H raw10159 = injectiveMoment H raw10159step0 := by
      have heq : raw10159step0 = raw10159.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw10159).symm
    injectiveMoment H raw10159step0 = injectiveMoment H raw10159step1 := by
      have heq : raw10159step1 = (fun i j => raw10159step0 (permutation29 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw10159step0 permutation29 permutation3
    _ = injectiveMoment H node221 := by rfl

def raw10160 : Matrix (Fin 3) (Fin 4) ℤ := ![![1, 0, 1, -2], ![-1, -2, 1, 2], ![0, 2, -2, 0]]

def raw10160step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -1, 0], ![0, -2, 2], ![1, 1, -2], ![-2, 2, 0]]

def raw10160step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![0, 2, -2], ![-1, -1, 2], ![2, -2, 0]]

def raw10160step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]

theorem canonical10160 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw10160 = injectiveMoment H node203 := by
  calc
    injectiveMoment H raw10160 = injectiveMoment H raw10160step0 := by
      have heq : raw10160step0 = raw10160.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw10160).symm
    injectiveMoment H raw10160step0 = injectiveMoment H raw10160step1 := by
      have heq : raw10160step1 = -raw10160step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw10160step0).symm
    injectiveMoment H raw10160step1 = injectiveMoment H raw10160step2 := by
      have heq : raw10160step2 = (fun i j => raw10160step1 (permutation16 i) (permutation7 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw10160step1 permutation16 permutation7
    _ = injectiveMoment H node203 := by rfl

def raw10161 : Matrix (Fin 3) (Fin 4) ℤ := ![![1, 0, 1, -2], ![-1, -2, 2, 1], ![0, 2, -3, 1]]

def raw10161step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -1, 0], ![0, -2, 2], ![1, 2, -3], ![-2, 1, 1]]

def raw10161step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![1, -1, 0], ![1, 2, -3]]

theorem canonical10161 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw10161 = injectiveMoment H node226 := by
  calc
    injectiveMoment H raw10161 = injectiveMoment H raw10161step0 := by
      have heq : raw10161step0 = raw10161.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw10161).symm
    injectiveMoment H raw10161step0 = injectiveMoment H raw10161step1 := by
      have heq : raw10161step1 = (fun i j => raw10161step0 (permutation29 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw10161step0 permutation29 permutation3
    _ = injectiveMoment H node226 := by rfl

def raw10162 : Matrix (Fin 3) (Fin 4) ℤ := ![![1, 0, 1, -2], ![-1, -2, 3, 0], ![0, 2, -4, 2]]

def raw10162step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -1, 0], ![0, -2, 2], ![1, 3, -4], ![-2, 0, 2]]

def raw10162step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![1, -1, 0], ![1, 3, -4]]

theorem canonical10162 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw10162 = injectiveMoment H node201 := by
  calc
    injectiveMoment H raw10162 = injectiveMoment H raw10162step0 := by
      have heq : raw10162step0 = raw10162.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw10162).symm
    injectiveMoment H raw10162step0 = injectiveMoment H raw10162step1 := by
      have heq : raw10162step1 = (fun i j => raw10162step0 (permutation29 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw10162step0 permutation29 permutation3
    _ = injectiveMoment H node201 := by rfl

def raw10163 : Matrix (Fin 3) (Fin 4) ℤ := ![![1, 0, 1, -2], ![-1, 2, 1, -2], ![0, -2, -2, 4]]

def raw10163step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -1, 0], ![0, 2, -2], ![1, 1, -2], ![-2, -2, 4]]

def raw10163step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![1, -1, 0], ![1, 1, -2]]

theorem canonical10163 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw10163 = injectiveMoment H node153 := by
  calc
    injectiveMoment H raw10163 = injectiveMoment H raw10163step0 := by
      have heq : raw10163step0 = raw10163.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw10163).symm
    injectiveMoment H raw10163step0 = injectiveMoment H raw10163step1 := by
      have heq : raw10163step1 = (fun i j => raw10163step0 (permutation29 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw10163step0 permutation29 permutation3
    _ = injectiveMoment H node153 := by rfl

def raw10164 : Matrix (Fin 3) (Fin 4) ℤ := ![![1, 0, 1, -2], ![-1, 3, -2, 0], ![0, -3, 1, 2]]

def raw10164step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -1, 0], ![0, 3, -3], ![1, -2, 1], ![-2, 0, 2]]

def raw10164step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![1, -2, 1], ![1, -1, 0]]

theorem canonical10164 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw10164 = injectiveMoment H node215 := by
  calc
    injectiveMoment H raw10164 = injectiveMoment H raw10164step0 := by
      have heq : raw10164step0 = raw10164.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw10164).symm
    injectiveMoment H raw10164step0 = injectiveMoment H raw10164step1 := by
      have heq : raw10164step1 = (fun i j => raw10164step0 (permutation30 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw10164step0 permutation30 permutation3
    _ = injectiveMoment H node215 := by rfl

def raw10165 : Matrix (Fin 3) (Fin 4) ℤ := ![![1, 0, 1, -2], ![-1, 4, -3, 0], ![0, -4, 2, 2]]

def raw10165step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -1, 0], ![0, 4, -4], ![1, -3, 2], ![-2, 0, 2]]

def raw10165step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 4, -4], ![1, -3, 2], ![1, -1, 0]]

theorem canonical10165 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw10165 = injectiveMoment H node217 := by
  calc
    injectiveMoment H raw10165 = injectiveMoment H raw10165step0 := by
      have heq : raw10165step0 = raw10165.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw10165).symm
    injectiveMoment H raw10165step0 = injectiveMoment H raw10165step1 := by
      have heq : raw10165step1 = (fun i j => raw10165step0 (permutation30 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw10165step0 permutation30 permutation3
    _ = injectiveMoment H node217 := by rfl

def raw10166 : Matrix (Fin 3) (Fin 4) ℤ := ![![1, 0, 1, -2], ![0, -3, 2, 1], ![-1, 3, -3, 1]]

def raw10166step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![0, -3, 3], ![1, 2, -3], ![-2, 1, 1]]

def raw10166step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -3, 3], ![1, 0, -1], ![1, 2, -3]]

theorem canonical10166 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw10166 = injectiveMoment H node222 := by
  calc
    injectiveMoment H raw10166 = injectiveMoment H raw10166step0 := by
      have heq : raw10166step0 = raw10166.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw10166).symm
    injectiveMoment H raw10166step0 = injectiveMoment H raw10166step1 := by
      have heq : raw10166step1 = (fun i j => raw10166step0 (permutation29 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw10166step0 permutation29 permutation3
    _ = injectiveMoment H node222 := by rfl

def raw10167 : Matrix (Fin 3) (Fin 4) ℤ := ![![1, 0, 1, -2], ![0, -2, 2, 0], ![-1, 2, -3, 2]]

def raw10167step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![0, -2, 2], ![1, 2, -3], ![-2, 0, 2]]

def raw10167step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 2, -2], ![-1, -2, 3], ![2, 0, -2]]

def raw10167step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 2, -2], ![2, 0, -2]]

theorem canonical10167 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw10167 = injectiveMoment H node169 := by
  calc
    injectiveMoment H raw10167 = injectiveMoment H raw10167step0 := by
      have heq : raw10167step0 = raw10167.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw10167).symm
    injectiveMoment H raw10167step0 = injectiveMoment H raw10167step1 := by
      have heq : raw10167step1 = -raw10167step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw10167step0).symm
    injectiveMoment H raw10167step1 = injectiveMoment H raw10167step2 := by
      have heq : raw10167step2 = (fun i j => raw10167step1 (permutation22 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw10167step1 permutation22 permutation5
    _ = injectiveMoment H node169 := by rfl

def raw10168 : Matrix (Fin 3) (Fin 4) ℤ := ![![1, 0, 1, -2], ![1, -3, 1, 1], ![-2, 3, -2, 1]]

def raw10168step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![0, -3, 3], ![1, 1, -2], ![-2, 1, 1]]

def raw10168step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -3, 3], ![1, 1, -2], ![1, 1, -2]]

theorem canonical10168 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw10168 = injectiveMoment H node223 := by
  calc
    injectiveMoment H raw10168 = injectiveMoment H raw10168step0 := by
      have heq : raw10168step0 = raw10168.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw10168).symm
    injectiveMoment H raw10168step0 = injectiveMoment H raw10168step1 := by
      have heq : raw10168step1 = (fun i j => raw10168step0 (permutation29 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw10168step0 permutation29 permutation3
    _ = injectiveMoment H node223 := by rfl

def raw10169 : Matrix (Fin 3) (Fin 4) ℤ := ![![1, 0, 1, -2], ![1, -3, 2, 0], ![-2, 3, -3, 2]]

def raw10169step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![0, -3, 3], ![1, 2, -3], ![-2, 0, 2]]

def raw10169step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![1, 1, -2], ![1, 2, -3]]

theorem canonical10169 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw10169 = injectiveMoment H node196 := by
  calc
    injectiveMoment H raw10169 = injectiveMoment H raw10169step0 := by
      have heq : raw10169step0 = raw10169.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw10169).symm
    injectiveMoment H raw10169step0 = injectiveMoment H raw10169step1 := by
      have heq : raw10169step1 = (fun i j => raw10169step0 (permutation29 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw10169step0 permutation29 permutation3
    _ = injectiveMoment H node196 := by rfl

def raw10170 : Matrix (Fin 3) (Fin 4) ℤ := ![![1, 0, 1, -2], ![1, -2, 1, 0], ![-2, 2, -2, 2]]

def raw10170step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![0, -2, 2], ![1, 1, -2], ![-2, 0, 2]]

def raw10170step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![1, 1, -2], ![1, 1, -2]]

theorem canonical10170 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw10170 = injectiveMoment H node202 := by
  calc
    injectiveMoment H raw10170 = injectiveMoment H raw10170step0 := by
      have heq : raw10170step0 = raw10170.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw10170).symm
    injectiveMoment H raw10170step0 = injectiveMoment H raw10170step1 := by
      have heq : raw10170step1 = (fun i j => raw10170step0 (permutation29 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw10170step0 permutation29 permutation3
    _ = injectiveMoment H node202 := by rfl

def raw10171 : Matrix (Fin 3) (Fin 4) ℤ := ![![1, 0, 1, -2], ![1, -2, 2, -1], ![-2, 2, -3, 3]]

def raw10171step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![0, -2, 2], ![1, 2, -3], ![-2, -1, 3]]

def raw10171step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![1, 1, -2], ![1, 2, -3]]

theorem canonical10171 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw10171 = injectiveMoment H node167 := by
  calc
    injectiveMoment H raw10171 = injectiveMoment H raw10171step0 := by
      have heq : raw10171step0 = raw10171.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw10171).symm
    injectiveMoment H raw10171step0 = injectiveMoment H raw10171step1 := by
      have heq : raw10171step1 = (fun i j => raw10171step0 (permutation29 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw10171step0 permutation29 permutation3
    _ = injectiveMoment H node167 := by rfl

def raw10172 : Matrix (Fin 3) (Fin 4) ℤ := ![![1, 0, 1, -2], ![2, -3, 1, 0], ![-3, 3, -2, 2]]

def raw10172step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![0, -3, 3], ![1, 1, -2], ![-2, 0, 2]]

def raw10172step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![1, 1, -2], ![1, 2, -3]]

theorem canonical10172 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw10172 = injectiveMoment H node196 := by
  calc
    injectiveMoment H raw10172 = injectiveMoment H raw10172step0 := by
      have heq : raw10172step0 = raw10172.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw10172).symm
    injectiveMoment H raw10172step0 = injectiveMoment H raw10172step1 := by
      have heq : raw10172step1 = (fun i j => raw10172step0 (permutation30 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw10172step0 permutation30 permutation3
    _ = injectiveMoment H node196 := by rfl

def raw10173 : Matrix (Fin 3) (Fin 4) ℤ := ![![1, 0, 1, -2], ![2, -2, 1, -1], ![-3, 2, -2, 3]]

def raw10173step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![0, -2, 2], ![1, 1, -2], ![-2, -1, 3]]

def raw10173step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![1, 1, -2], ![1, 2, -3]]

theorem canonical10173 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw10173 = injectiveMoment H node167 := by
  calc
    injectiveMoment H raw10173 = injectiveMoment H raw10173step0 := by
      have heq : raw10173step0 = raw10173.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw10173).symm
    injectiveMoment H raw10173step0 = injectiveMoment H raw10173step1 := by
      have heq : raw10173step1 = (fun i j => raw10173step0 (permutation30 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw10173step0 permutation30 permutation3
    _ = injectiveMoment H node167 := by rfl

def raw10174 : Matrix (Fin 3) (Fin 4) ℤ := ![![1, 1, 1, -3], ![1, -2, 1, 0], ![-2, 1, -2, 3]]

def raw10174step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![1, -2, 1], ![1, 1, -2], ![-3, 0, 3]]

def raw10174step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -3, 3], ![1, 1, -2], ![1, 1, -2]]

theorem canonical10174 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw10174 = injectiveMoment H node223 := by
  calc
    injectiveMoment H raw10174 = injectiveMoment H raw10174step0 := by
      have heq : raw10174step0 = raw10174.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw10174).symm
    injectiveMoment H raw10174step0 = injectiveMoment H raw10174step1 := by
      have heq : raw10174step1 = (fun i j => raw10174step0 (permutation19 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw10174step0 permutation19 permutation5
    _ = injectiveMoment H node223 := by rfl

def raw10175 : Matrix (Fin 3) (Fin 4) ℤ := ![![1, 1, 1, -3], ![2, -2, 1, -1], ![-3, 1, -2, 4]]

def raw10175step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -2, 1], ![1, 1, -2], ![-3, -1, 4]]

def raw10175step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -2, 1], ![1, 1, -2], ![1, 2, -3]]

theorem canonical10175 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw10175 = injectiveMoment H node89 := by
  calc
    injectiveMoment H raw10175 = injectiveMoment H raw10175step0 := by
      have heq : raw10175step0 = raw10175.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw10175).symm
    injectiveMoment H raw10175step0 = injectiveMoment H raw10175step1 := by
      have heq : raw10175step1 = (fun i j => raw10175step0 (permutation30 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw10175step0 permutation30 permutation3
    _ = injectiveMoment H node89 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
