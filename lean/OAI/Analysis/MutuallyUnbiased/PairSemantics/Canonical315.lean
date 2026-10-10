import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes1
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes2
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes3
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes20
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes45
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes46
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes53
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes54

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw10080 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-1, -1, 2, 0], ![-1, 0, -2, 3]]

def raw10080step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, -1, -1, 0]]

theorem canonical10080 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw10080 = injectiveMoment H node2997 := by
  calc
    injectiveMoment H raw10080 = injectiveMoment H raw10080step0 := by
      have heq : raw10080step0 = (fun i j => raw10080 (permutation308 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw10080 permutation308 permutation21
    _ = injectiveMoment H node2997 := by rfl

def raw10081 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-1, -1, 3, -1], ![-1, 0, -3, 4]]

def raw10081step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, 3, -1], ![-1, 0, -3, 4], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1]]

theorem canonical10081 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw10081 = injectiveMoment H node3408 := by
  calc
    injectiveMoment H raw10081 = injectiveMoment H raw10081step0 := by
      have heq : raw10081step0 = (fun i j => raw10081 (permutation294 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw10081 permutation294 permutation9
    _ = injectiveMoment H node3408 := by rfl

def raw10082 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -2, 1], ![1, 0, 0, -1], ![-1, 0, 2, -1], ![-1, -2, 0, 3]]

def raw10082step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 0, 0, -1]]

theorem canonical10082 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw10082 = injectiveMoment H node2975 := by
  calc
    injectiveMoment H raw10082 = injectiveMoment H raw10082step0 := by
      have heq : raw10082step0 = (fun i j => raw10082 (permutation404 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw10082 permutation404 permutation15
    _ = injectiveMoment H node2975 := by rfl

def raw10083 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -2, 1], ![1, 0, 0, -1], ![0, -1, 2, -1], ![-2, -1, 0, 3]]

def raw10083step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -2, 1], ![1, 0, 0, -1]]

theorem canonical10083 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw10083 = injectiveMoment H node2978 := by
  calc
    injectiveMoment H raw10083 = injectiveMoment H raw10083step0 := by
      have heq : raw10083step0 = (fun i j => raw10083 (permutation395 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw10083 permutation395 permutation9
    _ = injectiveMoment H node2978 := by rfl

def raw10084 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, -1, 0], ![-1, 0, 2, -1], ![-1, -2, 0, 3]]

def raw10084step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 0, 0, -1]]

theorem canonical10084 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw10084 = injectiveMoment H node2976 := by
  calc
    injectiveMoment H raw10084 = injectiveMoment H raw10084step0 := by
      have heq : raw10084step0 = (fun i j => raw10084 (permutation404 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw10084 permutation404 permutation15
    _ = injectiveMoment H node2976 := by rfl

def raw10085 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, -1, 0], ![0, -1, 2, -1], ![-2, -1, 0, 3]]

def raw10085step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, -1, 0]]

theorem canonical10085 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw10085 = injectiveMoment H node2979 := by
  calc
    injectiveMoment H raw10085 = injectiveMoment H raw10085step0 := by
      have heq : raw10085step0 = (fun i j => raw10085 (permutation395 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw10085 permutation395 permutation9
    _ = injectiveMoment H node2979 := by rfl

def raw10086 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 0, -1], ![-1, 0, 1, 0], ![-1, -2, 0, 3]]

def raw10086step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -2, -1, 3], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -1, 0]]

theorem canonical10086 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw10086 = injectiveMoment H node3455 := by
  calc
    injectiveMoment H raw10086 = injectiveMoment H raw10086step0 := by
      have heq : raw10086step0 = (fun i j => raw10086 (permutation239 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw10086 permutation239 permutation23
    _ = injectiveMoment H node3455 := by rfl

def raw10087 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 0, -1], ![-1, 0, 2, -1], ![-1, -2, -1, 4]]

def raw10087step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, 0, 0, -1], ![1, 0, 0, -1]]

theorem canonical10087 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw10087 = injectiveMoment H node2918 := by
  calc
    injectiveMoment H raw10087 = injectiveMoment H raw10087step0 := by
      have heq : raw10087step0 = (fun i j => raw10087 (permutation366 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw10087 permutation366 permutation17
    _ = injectiveMoment H node2918 := by rfl

def raw10088 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 0, -1], ![0, -1, 1, 0], ![-2, -1, 0, 3]]

def raw10088step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -1, -2, 3], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, 0, 0]]

theorem canonical10088 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw10088 = injectiveMoment H node3457 := by
  calc
    injectiveMoment H raw10088 = injectiveMoment H raw10088step0 := by
      have heq : raw10088step0 = (fun i j => raw10088 (permutation239 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw10088 permutation239 permutation23
    _ = injectiveMoment H node3457 := by rfl

def raw10089 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 0, -1], ![0, -1, 2, -1], ![-2, -1, -1, 4]]

def raw10089step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 2, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 0, -1]]

theorem canonical10089 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw10089 = injectiveMoment H node2922 := by
  calc
    injectiveMoment H raw10089 = injectiveMoment H raw10089step0 := by
      have heq : raw10089step0 = (fun i j => raw10089 (permutation395 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw10089 permutation395 permutation9
    _ = injectiveMoment H node2922 := by rfl

def raw10090 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 1, 1, -2], ![-4, 1, 1, 2], ![4, -2, -2, 0]]

def raw10090step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -4, 4], ![1, 1, -2], ![1, 1, -2], ![-2, 2, 0]]

def raw10090step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 4, -4], ![1, -2, 1], ![1, -2, 1]]

theorem canonical10090 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw10090 = injectiveMoment H node218 := by
  calc
    injectiveMoment H raw10090 = injectiveMoment H raw10090step0 := by
      have heq : raw10090step0 = raw10090.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw10090).symm
    injectiveMoment H raw10090step0 = injectiveMoment H raw10090step1 := by
      have heq : raw10090step1 = (fun i j => raw10090step0 (permutation27 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw10090step0 permutation27 permutation4
    _ = injectiveMoment H node218 := by rfl

def raw10091 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 1, 1, -2], ![-4, 1, 2, 1], ![4, -2, -3, 1]]

def raw10091step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -4, 4], ![1, 1, -2], ![1, 2, -3], ![-2, 1, 1]]

def raw10091step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -4, 4], ![1, 1, -2], ![1, 2, -3]]

theorem canonical10091 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw10091 = injectiveMoment H node219 := by
  calc
    injectiveMoment H raw10091 = injectiveMoment H raw10091step0 := by
      have heq : raw10091step0 = raw10091.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw10091).symm
    injectiveMoment H raw10091step0 = injectiveMoment H raw10091step1 := by
      have heq : raw10091step1 = (fun i j => raw10091step0 (permutation27 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw10091step0 permutation27 permutation3
    _ = injectiveMoment H node219 := by rfl

def raw10092 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 1, 1, -2], ![-3, -2, 3, 2], ![3, 1, -4, 0]]

def raw10092step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![1, -2, 1], ![1, 3, -4], ![-2, 2, 0]]

def raw10092step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![1, -4, 3], ![1, 1, -2]]

theorem canonical10092 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw10092 = injectiveMoment H node213 := by
  calc
    injectiveMoment H raw10092 = injectiveMoment H raw10092step0 := by
      have heq : raw10092step0 = raw10092.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw10092).symm
    injectiveMoment H raw10092step0 = injectiveMoment H raw10092step1 := by
      have heq : raw10092step1 = (fun i j => raw10092step0 (permutation28 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw10092step0 permutation28 permutation4
    _ = injectiveMoment H node213 := by rfl

def raw10093 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 1, 1, -2], ![-3, 1, 1, 1], ![3, -2, -2, 1]]

def raw10093step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![1, 1, -2], ![1, 1, -2], ![-2, 1, 1]]

def raw10093step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -3, 3], ![1, 1, -2], ![1, 1, -2]]

theorem canonical10093 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw10093 = injectiveMoment H node223 := by
  calc
    injectiveMoment H raw10093 = injectiveMoment H raw10093step0 := by
      have heq : raw10093step0 = raw10093.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw10093).symm
    injectiveMoment H raw10093step0 = injectiveMoment H raw10093step1 := by
      have heq : raw10093step1 = (fun i j => raw10093step0 (permutation27 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw10093step0 permutation27 permutation3
    _ = injectiveMoment H node223 := by rfl

def raw10094 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 1, 1, -2], ![-3, 1, 2, 0], ![3, -2, -3, 2]]

def raw10094step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![1, 1, -2], ![1, 2, -3], ![-2, 0, 2]]

def raw10094step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![1, 1, -2], ![1, 2, -3]]

theorem canonical10094 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw10094 = injectiveMoment H node196 := by
  calc
    injectiveMoment H raw10094 = injectiveMoment H raw10094step0 := by
      have heq : raw10094step0 = raw10094.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw10094).symm
    injectiveMoment H raw10094step0 = injectiveMoment H raw10094step1 := by
      have heq : raw10094step1 = (fun i j => raw10094step0 (permutation27 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw10094step0 permutation27 permutation3
    _ = injectiveMoment H node196 := by rfl

def raw10095 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 1, 1, -2], ![-2, -3, 1, 4], ![2, 2, -2, -2]]

def raw10095step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![1, -3, 2], ![1, 1, -2], ![-2, 4, -2]]

def raw10095step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![1, -2, 1], ![1, 2, -3]]

theorem canonical10095 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw10095 = injectiveMoment H node152 := by
  calc
    injectiveMoment H raw10095 = injectiveMoment H raw10095step0 := by
      have heq : raw10095step0 = raw10095.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw10095).symm
    injectiveMoment H raw10095step0 = injectiveMoment H raw10095step1 := by
      have heq : raw10095step1 = (fun i j => raw10095step0 (permutation28 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw10095step0 permutation28 permutation4
    _ = injectiveMoment H node152 := by rfl

def raw10096 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 1, 1, -2], ![-2, -3, 3, 2], ![2, 2, -4, 0]]

def raw10096step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![1, -3, 2], ![1, 3, -4], ![-2, 2, 0]]

def raw10096step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![1, -4, 3], ![1, 2, -3]]

theorem canonical10096 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw10096 = injectiveMoment H node211 := by
  calc
    injectiveMoment H raw10096 = injectiveMoment H raw10096step0 := by
      have heq : raw10096step0 = raw10096.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw10096).symm
    injectiveMoment H raw10096step0 = injectiveMoment H raw10096step1 := by
      have heq : raw10096step1 = (fun i j => raw10096step0 (permutation28 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw10096step0 permutation28 permutation4
    _ = injectiveMoment H node211 := by rfl

def raw10097 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 1, 1, -2], ![-2, -2, 1, 3], ![2, 1, -2, -1]]

def raw10097step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![1, -2, 1], ![1, 1, -2], ![-2, 3, -1]]

def raw10097step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, -2, 1], ![1, 1, -2]]

theorem canonical10097 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw10097 = injectiveMoment H node184 := by
  calc
    injectiveMoment H raw10097 = injectiveMoment H raw10097step0 := by
      have heq : raw10097step0 = raw10097.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw10097).symm
    injectiveMoment H raw10097step0 = injectiveMoment H raw10097step1 := by
      have heq : raw10097step1 = (fun i j => raw10097step0 (permutation28 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw10097step0 permutation28 permutation4
    _ = injectiveMoment H node184 := by rfl

def raw10098 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 1, 1, -2], ![-2, -2, 2, 2], ![2, 1, -3, 0]]

def raw10098step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![1, -2, 1], ![1, 2, -3], ![-2, 2, 0]]

def raw10098step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![1, -3, 2], ![1, 1, -2]]

theorem canonical10098 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw10098 = injectiveMoment H node212 := by
  calc
    injectiveMoment H raw10098 = injectiveMoment H raw10098step0 := by
      have heq : raw10098step0 = raw10098.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw10098).symm
    injectiveMoment H raw10098step0 = injectiveMoment H raw10098step1 := by
      have heq : raw10098step1 = (fun i j => raw10098step0 (permutation28 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw10098step0 permutation28 permutation4
    _ = injectiveMoment H node212 := by rfl

def raw10099 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 1, 1, -2], ![-2, -2, 3, 1], ![2, 1, -4, 1]]

def raw10099step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![1, -2, 1], ![1, 3, -4], ![-2, 1, 1]]

def raw10099step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![1, -2, 1], ![1, 3, -4]]

theorem canonical10099 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw10099 = injectiveMoment H node225 := by
  calc
    injectiveMoment H raw10099 = injectiveMoment H raw10099step0 := by
      have heq : raw10099step0 = raw10099.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw10099).symm
    injectiveMoment H raw10099step0 = injectiveMoment H raw10099step1 := by
      have heq : raw10099step1 = (fun i j => raw10099step0 (permutation27 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw10099step0 permutation27 permutation3
    _ = injectiveMoment H node225 := by rfl

def raw10100 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 1, 1, -2], ![-2, 1, 2, -1], ![2, -2, -3, 3]]

def raw10100step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![1, 1, -2], ![1, 2, -3], ![-2, -1, 3]]

def raw10100step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![1, 1, -2], ![1, 2, -3]]

theorem canonical10100 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw10100 = injectiveMoment H node167 := by
  calc
    injectiveMoment H raw10100 = injectiveMoment H raw10100step0 := by
      have heq : raw10100step0 = raw10100.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw10100).symm
    injectiveMoment H raw10100step0 = injectiveMoment H raw10100step1 := by
      have heq : raw10100step1 = (fun i j => raw10100step0 (permutation27 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw10100step0 permutation27 permutation3
    _ = injectiveMoment H node167 := by rfl

def raw10101 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 1, 1, -2], ![-1, -3, 1, 3], ![1, 2, -2, -1]]

def raw10101step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![1, -3, 2], ![1, 1, -2], ![-2, 3, -1]]

def raw10101step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 2, -3]]

theorem canonical10101 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw10101 = injectiveMoment H node180 := by
  calc
    injectiveMoment H raw10101 = injectiveMoment H raw10101step0 := by
      have heq : raw10101step0 = raw10101.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw10101).symm
    injectiveMoment H raw10101step0 = injectiveMoment H raw10101step1 := by
      have heq : raw10101step1 = (fun i j => raw10101step0 (permutation28 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw10101step0 permutation28 permutation4
    _ = injectiveMoment H node180 := by rfl

def raw10102 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 1, 1, -2], ![-1, -3, 3, 1], ![1, 2, -4, 1]]

def raw10102step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![1, -3, 2], ![1, 3, -4], ![-2, 1, 1]]

def raw10102step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -3, 2], ![1, 3, -4]]

theorem canonical10102 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw10102 = injectiveMoment H node228 := by
  calc
    injectiveMoment H raw10102 = injectiveMoment H raw10102step0 := by
      have heq : raw10102step0 = raw10102.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw10102).symm
    injectiveMoment H raw10102step0 = injectiveMoment H raw10102step1 := by
      have heq : raw10102step1 = (fun i j => raw10102step0 (permutation27 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw10102step0 permutation27 permutation3
    _ = injectiveMoment H node228 := by rfl

def raw10103 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 1, 1, -2], ![-1, -2, 1, 2], ![1, 1, -2, 0]]

def raw10103step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![-2, 2, 0]]

def raw10103step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]

theorem canonical10103 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw10103 = injectiveMoment H node210 := by
  calc
    injectiveMoment H raw10103 = injectiveMoment H raw10103step0 := by
      have heq : raw10103step0 = raw10103.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw10103).symm
    injectiveMoment H raw10103step0 = injectiveMoment H raw10103step1 := by
      have heq : raw10103step1 = (fun i j => raw10103step0 (permutation28 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw10103step0 permutation28 permutation4
    _ = injectiveMoment H node210 := by rfl

def raw10104 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 1, 1, -2], ![-1, -2, 2, 1], ![1, 1, -3, 1]]

def raw10104step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![1, -2, 1], ![1, 2, -3], ![-2, 1, 1]]

def raw10104step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -2, 1], ![1, 2, -3]]

theorem canonical10104 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw10104 = injectiveMoment H node229 := by
  calc
    injectiveMoment H raw10104 = injectiveMoment H raw10104step0 := by
      have heq : raw10104step0 = raw10104.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw10104).symm
    injectiveMoment H raw10104step0 = injectiveMoment H raw10104step1 := by
      have heq : raw10104step1 = (fun i j => raw10104step0 (permutation27 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw10104step0 permutation27 permutation3
    _ = injectiveMoment H node229 := by rfl

def raw10105 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 1, 1, -2], ![-1, -2, 3, 0], ![1, 1, -4, 2]]

def raw10105step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![1, -2, 1], ![1, 3, -4], ![-2, 0, 2]]

def raw10105step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![1, -2, 1], ![1, 3, -4]]

theorem canonical10105 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw10105 = injectiveMoment H node206 := by
  calc
    injectiveMoment H raw10105 = injectiveMoment H raw10105step0 := by
      have heq : raw10105step0 = raw10105.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw10105).symm
    injectiveMoment H raw10105step0 = injectiveMoment H raw10105step1 := by
      have heq : raw10105step1 = (fun i j => raw10105step0 (permutation27 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw10105step0 permutation27 permutation3
    _ = injectiveMoment H node206 := by rfl

def raw10106 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 1, 1, -2], ![-1, 1, 2, -2], ![1, -2, -3, 4]]

def raw10106step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![1, 1, -2], ![1, 2, -3], ![-2, -2, 4]]

def raw10106step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, -1, 1], ![1, 1, -2], ![1, 2, -3]]

theorem canonical10106 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw10106 = injectiveMoment H node144 := by
  calc
    injectiveMoment H raw10106 = injectiveMoment H raw10106step0 := by
      have heq : raw10106step0 = raw10106.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw10106).symm
    injectiveMoment H raw10106step0 = injectiveMoment H raw10106step1 := by
      have heq : raw10106step1 = (fun i j => raw10106step0 (permutation27 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw10106step0 permutation27 permutation3
    _ = injectiveMoment H node144 := by rfl

def raw10107 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 1, 1, -2], ![2, -2, 1, -1], ![-2, 1, -2, 3]]

def raw10107step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![1, -2, 1], ![1, 1, -2], ![-2, -1, 3]]

def raw10107step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, -2, 1], ![1, 1, -2]]

theorem canonical10107 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw10107 = injectiveMoment H node184 := by
  calc
    injectiveMoment H raw10107 = injectiveMoment H raw10107step0 := by
      have heq : raw10107step0 = raw10107.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw10107).symm
    injectiveMoment H raw10107step0 = injectiveMoment H raw10107step1 := by
      have heq : raw10107step1 = (fun i j => raw10107step0 (permutation27 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw10107step0 permutation27 permutation3
    _ = injectiveMoment H node184 := by rfl

def raw10108 : Matrix (Fin 3) (Fin 4) ℤ := ![![1, -2, 2, -1], ![0, 1, 1, -2], ![-1, 1, -3, 3]]

def raw10108step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![-2, 1, 1], ![2, 1, -3], ![-1, -2, 3]]

def raw10108step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 2, -3]]

theorem canonical10108 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw10108 = injectiveMoment H node180 := by
  calc
    injectiveMoment H raw10108 = injectiveMoment H raw10108step0 := by
      have heq : raw10108step0 = raw10108.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw10108).symm
    injectiveMoment H raw10108step0 = injectiveMoment H raw10108step1 := by
      have heq : raw10108step1 = (fun i j => raw10108step0 (permutation27 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw10108step0 permutation27 permutation5
    _ = injectiveMoment H node180 := by rfl

def raw10109 : Matrix (Fin 3) (Fin 4) ℤ := ![![1, -2, 2, -1], ![1, 1, 1, -3], ![-2, 1, -3, 4]]

def raw10109step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![-2, 1, 1], ![2, 1, -3], ![-1, -3, 4]]

def raw10109step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -2, 1], ![1, 1, -2], ![1, 2, -3]]

theorem canonical10109 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw10109 = injectiveMoment H node89 := by
  calc
    injectiveMoment H raw10109 = injectiveMoment H raw10109step0 := by
      have heq : raw10109step0 = raw10109.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw10109).symm
    injectiveMoment H raw10109step0 = injectiveMoment H raw10109step1 := by
      have heq : raw10109step1 = (fun i j => raw10109step0 (permutation29 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw10109step0 permutation29 permutation5
    _ = injectiveMoment H node89 := by rfl

def raw10110 : Matrix (Fin 6) (Fin 2) ℤ := ![![1, -1], ![1, -1], ![-1, 1], ![-1, 1], ![-1, 1], ![1, -1]]

def raw10110step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]

theorem canonical10110 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw10110 = injectiveMoment H node1323 := by
  calc
    injectiveMoment H raw10110 = injectiveMoment H raw10110step0 := by
      have heq : raw10110step0 = (fun i j => raw10110 (permutation229 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw10110 permutation229 permutation1
    _ = injectiveMoment H node1323 := by rfl

def raw10111 : Matrix (Fin 5) (Fin 2) ℤ := ![![1, -1], ![1, -1], ![-1, 1], ![-1, 1], ![0, 0]]

def raw10111step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![1, -1], ![1, -1], ![-1, 1], ![-1, 1]]

def raw10111step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![1, -1]]

theorem canonical10111 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw10111 = injectiveMoment H node65 := by
  calc
    injectiveMoment H raw10111 = injectiveMoment H raw10111step0 := by
      have hz : ∀ j, raw10111 (permutation128 0) j = 0 := by decide +kernel
      have heq : raw10111step0 = (fun i j => raw10111 (permutation128 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw10111 permutation128 hz
    injectiveMoment H raw10111step0 = injectiveMoment H raw10111step1 := by
      have heq : raw10111step1 = (fun i j => raw10111step0 (permutation25 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw10111step0 permutation25 permutation1
    _ = injectiveMoment H node65 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
