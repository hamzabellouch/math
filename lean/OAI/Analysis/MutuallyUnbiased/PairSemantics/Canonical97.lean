import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes3
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes8
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes14
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes15
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes25
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes30
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes39
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes40
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes41
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes43
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes44

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw3104 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -1, 3, -2], ![1, 0, 0, -1], ![1, 1, -2, 0]]

def raw3104step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 1, -3], ![0, 1, -3, 2], ![-1, 0, 0, 1], ![-1, -1, 2, 0]]

def raw3104step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 1, 0], ![0, 2, -3, 1], ![1, 0, 2, -3]]

theorem canonical3104 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3104 = injectiveMoment H node1001 := by
  calc
    injectiveMoment H raw3104 = injectiveMoment H raw3104step0 := by
      have heq : raw3104step0 = -raw3104 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3104).symm
    injectiveMoment H raw3104step0 = injectiveMoment H raw3104step1 := by
      have heq : raw3104step1 = (fun i j => raw3104step0 (permutation31 i) (permutation16 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3104step0 permutation31 permutation16
    _ = injectiveMoment H node1001 := by rfl

def raw3105 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -1, 3, -2], ![1, 1, -2, 0], ![1, 0, 0, -1]]

def raw3105step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 1, -3], ![0, 1, -3, 2], ![-1, -1, 2, 0], ![-1, 0, 0, 1]]

def raw3105step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 1, 0], ![0, 2, -3, 1], ![1, 0, 2, -3]]

theorem canonical3105 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3105 = injectiveMoment H node1001 := by
  calc
    injectiveMoment H raw3105 = injectiveMoment H raw3105step0 := by
      have heq : raw3105step0 = -raw3105 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3105).symm
    injectiveMoment H raw3105step0 = injectiveMoment H raw3105step1 := by
      have heq : raw3105step1 = (fun i j => raw3105step0 (permutation25 i) (permutation16 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3105step0 permutation25 permutation16
    _ = injectiveMoment H node1001 := by rfl

def raw3106 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -1, 3, -2], ![1, 1, -1, -1], ![1, 0, -1, 0]]

def raw3106step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 1, 0], ![-1, 3, -1, -1], ![3, -2, -1, 0]]

def raw3106step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 3, -2], ![0, 1, 0, -1], ![1, 1, -2, 0]]

theorem canonical3106 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3106 = injectiveMoment H node950 := by
  calc
    injectiveMoment H raw3106 = injectiveMoment H raw3106step0 := by
      have heq : raw3106step0 = raw3106.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3106).symm
    injectiveMoment H raw3106step0 = injectiveMoment H raw3106step1 := by
      have heq : raw3106step1 = (fun i j => raw3106step0 (permutation26 i) (permutation31 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3106step0 permutation26 permutation31
    _ = injectiveMoment H node950 := by rfl

def raw3107 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -1, 3, -2], ![1, 2, -1, -2], ![1, -1, -1, 1]]

def raw3107step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 1, -3], ![0, 1, -3, 2], ![-1, -2, 1, 2], ![-1, 1, 1, -1]]

def raw3107step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 2, 1, -3], ![1, -1, 1, -1], ![1, 0, -3, 2]]

theorem canonical3107 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3107 = injectiveMoment H node519 := by
  calc
    injectiveMoment H raw3107 = injectiveMoment H raw3107step0 := by
      have heq : raw3107step0 = -raw3107 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3107).symm
    injectiveMoment H raw3107step0 = injectiveMoment H raw3107step1 := by
      have heq : raw3107step1 = (fun i j => raw3107step0 (permutation22 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3107step0 permutation22 permutation15
    _ = injectiveMoment H node519 := by rfl

def raw3108 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 1, 1, -3]]

def raw3108step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 1, -3], ![0, 0, 1, -1], ![0, 0, -1, 1], ![-1, 1, 0, 0], ![-1, -1, -1, 3]]

def raw3108step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 0, 1], ![0, 1, 0, -1], ![0, 1, 2, -3], ![1, 0, -1, 0]]

theorem canonical3108 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3108 = injectiveMoment H node2529 := by
  calc
    injectiveMoment H raw3108 = injectiveMoment H raw3108step0 := by
      have heq : raw3108step0 = -raw3108 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3108).symm
    injectiveMoment H raw3108step0 = injectiveMoment H raw3108step1 := by
      have heq : raw3108step1 = (fun i j => raw3108step0 (permutation141 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3108step0 permutation141 permutation17
    _ = injectiveMoment H node2529 := by rfl

def raw3109 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 1, -1], ![1, 1, 0, -2]]

def raw3109step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 1, -3], ![0, 0, 1, -1], ![0, 0, -1, 1], ![-1, 1, -1, 1], ![-1, -1, 0, 2]]

def raw3109step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 2, 1, -3], ![1, -1, -1, 1]]

theorem canonical3109 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3109 = injectiveMoment H node2597 := by
  calc
    injectiveMoment H raw3109 = injectiveMoment H raw3109step0 := by
      have heq : raw3109step0 = -raw3109 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3109).symm
    injectiveMoment H raw3109step0 = injectiveMoment H raw3109step1 := by
      have heq : raw3109step1 = (fun i j => raw3109step0 (permutation141 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3109step0 permutation141 permutation15
    _ = injectiveMoment H node2597 := by rfl

def raw3110 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, -1, 1], ![0, 0, 2, -2], ![1, -1, 0, 0], ![1, 1, 0, -2]]

def raw3110step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 1, -3], ![0, 0, 1, -1], ![0, 0, -2, 2], ![-1, 1, 0, 0], ![-1, -1, 0, 2]]

def raw3110step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 0, 1, -1], ![0, 2, 1, -3], ![1, -1, 0, 0]]

theorem canonical3110 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3110 = injectiveMoment H node2589 := by
  calc
    injectiveMoment H raw3110 = injectiveMoment H raw3110step0 := by
      have heq : raw3110step0 = -raw3110 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3110).symm
    injectiveMoment H raw3110step0 = injectiveMoment H raw3110step1 := by
      have heq : raw3110step1 = (fun i j => raw3110step0 (permutation141 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3110step0 permutation141 permutation15
    _ = injectiveMoment H node2589 := by rfl

def raw3111 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 3, -4], ![2, -2, 0, 0]]

theorem canonical3111 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3111 = injectiveMoment H node1952 := by
  rfl

def raw3112 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -2, 1, 0], ![1, 1, 2, -4]]

theorem canonical3112 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3112 = injectiveMoment H node1953 := by
  rfl

def raw3113 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 3, -3], ![1, 0, 0, -1]]

def raw3113step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 1, -3], ![0, 0, 1, -1], ![0, -1, 1, 0], ![-1, 1, -3, 3], ![-1, 0, 0, 1]]

def raw3113step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -1, 0, 1], ![0, 0, 1, -1], ![0, 2, 1, -3], ![1, -1, -3, 3]]

theorem canonical3113 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3113 = injectiveMoment H node2815 := by
  calc
    injectiveMoment H raw3113 = injectiveMoment H raw3113step0 := by
      have heq : raw3113step0 = -raw3113 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3113).symm
    injectiveMoment H raw3113step0 = injectiveMoment H raw3113step1 := by
      have heq : raw3113step1 = (fun i j => raw3113step0 (permutation100 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3113step0 permutation100 permutation15
    _ = injectiveMoment H node2815 := by rfl

def raw3114 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -1, 3, -3], ![1, 0, -1, 0]]

def raw3114step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 1, -3], ![0, 0, 1, -1], ![0, -1, 0, 1], ![-1, 1, -3, 3], ![-1, 0, 1, 0]]

def raw3114step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 2, 1, -3], ![1, -1, -3, 3]]

theorem canonical3114 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3114 = injectiveMoment H node2770 := by
  calc
    injectiveMoment H raw3114 = injectiveMoment H raw3114step0 := by
      have heq : raw3114step0 = -raw3114 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3114).symm
    injectiveMoment H raw3114step0 = injectiveMoment H raw3114step1 := by
      have heq : raw3114step1 = (fun i j => raw3114step0 (permutation100 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3114step0 permutation100 permutation15
    _ = injectiveMoment H node2770 := by rfl

def raw3115 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 0, 0], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, -2, 2, -2]]

def raw3115step0 : Matrix (Fin 4) (Fin 5) ℤ := ![![-2, 0, 0, 0, 2], ![0, 0, 1, 1, -2], ![-1, 0, -1, 0, 2], ![3, 0, 0, -1, -2]]

def raw3115step1 : Matrix (Fin 4) (Fin 5) ℤ := ![![2, 0, 0, 0, -2], ![0, 0, -1, -1, 2], ![1, 0, 1, 0, -2], ![-3, 0, 0, 1, 2]]

def raw3115step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, -1, -1, 2], ![1, 1, 0, -2], ![-3, 0, 1, 2]]

def raw3115step3 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 1, -3, 2], ![1, 0, 1, -2]]

theorem canonical3115 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3115 = injectiveMoment H node1052 := by
  calc
    injectiveMoment H raw3115 = injectiveMoment H raw3115step0 := by
      have heq : raw3115step0 = raw3115.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3115).symm
    injectiveMoment H raw3115step0 = injectiveMoment H raw3115step1 := by
      have heq : raw3115step1 = -raw3115step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3115step0).symm
    injectiveMoment H raw3115step1 = injectiveMoment H raw3115step2 := by
      have hz : ∀ i, raw3115step1 i (permutation57 0) = 0 := by decide +kernel
      have heq : raw3115step2 = (fun i j => raw3115step1 i (permutation57 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw3115step1 permutation57 hz
    injectiveMoment H raw3115step2 = injectiveMoment H raw3115step3 := by
      have heq : raw3115step3 = (fun i j => raw3115step2 (permutation16 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3115step2 permutation16 permutation17
    _ = injectiveMoment H node1052 := by rfl

def raw3116 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 0, 0], ![1, -1, -1, 1], ![1, 1, 2, -4]]

def raw3116step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, -1, 1], ![-1, 0, -1, 2], ![3, 0, 1, -4]]

def raw3116step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 0, 1, -1], ![1, 0, 1, -2], ![-3, 0, -1, 4]]

def raw3116step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![1, 1, -2], ![-3, -1, 4]]

def raw3116step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 2, -1], ![1, 0, -1], ![1, 1, -2]]

theorem canonical3116 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3116 = injectiveMoment H node246 := by
  calc
    injectiveMoment H raw3116 = injectiveMoment H raw3116step0 := by
      have heq : raw3116step0 = raw3116.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3116).symm
    injectiveMoment H raw3116step0 = injectiveMoment H raw3116step1 := by
      have heq : raw3116step1 = -raw3116step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3116step0).symm
    injectiveMoment H raw3116step1 = injectiveMoment H raw3116step2 := by
      have hz : ∀ i, raw3116step1 i (permutation15 0) = 0 := by decide +kernel
      have heq : raw3116step2 = (fun i j => raw3116step1 i (permutation15 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw3116step1 permutation15 hz
    injectiveMoment H raw3116step2 = injectiveMoment H raw3116step3 := by
      have heq : raw3116step3 = (fun i j => raw3116step2 (permutation27 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3116step2 permutation27 permutation5
    _ = injectiveMoment H node246 := by rfl

def raw3117 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![2, -1, 0, -1]]

def raw3117step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 1, -3], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, -1, 1, 0], ![-2, 1, 0, 1]]

def raw3117step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, -2, 0, 1]]

theorem canonical3117 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3117 = injectiveMoment H node2819 := by
  calc
    injectiveMoment H raw3117 = injectiveMoment H raw3117step0 := by
      have heq : raw3117step0 = -raw3117 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3117).symm
    injectiveMoment H raw3117step0 = injectiveMoment H raw3117step1 := by
      have heq : raw3117step1 = (fun i j => raw3117step0 (permutation112 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3117step0 permutation112 permutation15
    _ = injectiveMoment H node2819 := by rfl

def raw3118 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -1, -1], ![2, -2, 0, 0]]

def raw3118step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, -2, 0]]

theorem canonical3118 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3118 = injectiveMoment H node1650 := by
  calc
    injectiveMoment H raw3118 = injectiveMoment H raw3118step0 := by
      have heq : raw3118step0 = (fun i j => raw3118 (permutation45 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3118 permutation45 permutation11
    _ = injectiveMoment H node1650 := by rfl

def raw3119 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 1, -1, -1]]

def raw3119step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 1, -3], ![0, 0, -1, 1], ![0, 0, -1, 1], ![-1, 1, 0, 0], ![-1, -1, 1, 1]]

def raw3119step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, -1, 0, 0]]

theorem canonical3119 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3119 = injectiveMoment H node2640 := by
  calc
    injectiveMoment H raw3119 = injectiveMoment H raw3119step0 := by
      have heq : raw3119step0 = -raw3119 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3119).symm
    injectiveMoment H raw3119step0 = injectiveMoment H raw3119step1 := by
      have heq : raw3119step1 = (fun i j => raw3119step0 (permutation135 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3119step0 permutation135 permutation15
    _ = injectiveMoment H node2640 := by rfl

def raw3120 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 1, -1], ![0, 1, -2, 1], ![0, 1, 0, -1], ![2, -2, 2, -2]]

theorem canonical3120 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3120 = injectiveMoment H node1954 := by
  rfl

def raw3121 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 1, -1], ![0, 1, -2, 1], ![0, 1, 1, -2], ![2, -2, 1, -1]]

theorem canonical3121 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3121 = injectiveMoment H node1955 := by
  rfl

def raw3122 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, -2, 2, -2]]

theorem canonical3122 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3122 = injectiveMoment H node1956 := by
  rfl

def raw3123 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, -2, 1, -1]]

def raw3123step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, 1, -2, -1]]

theorem canonical3123 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3123 = injectiveMoment H node1631 := by
  calc
    injectiveMoment H raw3123 = injectiveMoment H raw3123step0 := by
      have heq : raw3123step0 = (fun i j => raw3123 (permutation41 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3123 permutation41 permutation11
    _ = injectiveMoment H node1631 := by rfl

def raw3124 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![2, -2, 0, 0]]

def raw3124step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 1, 0, -1], ![0, 1, 1, -2], ![2, 0, -2, 0]]

theorem canonical3124 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3124 = injectiveMoment H node1638 := by
  calc
    injectiveMoment H raw3124 = injectiveMoment H raw3124step0 := by
      have heq : raw3124step0 = (fun i j => raw3124 (permutation39 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3124 permutation39 permutation11
    _ = injectiveMoment H node1638 := by rfl

def raw3125 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 1, -2]]

def raw3125step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -1, -2, 3], ![0, 1, 0, -1], ![0, 1, 1, -2], ![1, -1, 0, 0]]

theorem canonical3125 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3125 = injectiveMoment H node2811 := by
  calc
    injectiveMoment H raw3125 = injectiveMoment H raw3125step0 := by
      have heq : raw3125step0 = (fun i j => raw3125 (permutation105 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3125 permutation105 permutation17
    _ = injectiveMoment H node2811 := by rfl

def raw3126 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 1, -1], ![1, 0, 0, -1]]

def raw3126step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 1, -3], ![0, 0, -1, 1], ![0, -1, 1, 0], ![-1, 1, -1, 1], ![-1, 0, 0, 1]]

def raw3126step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, -1, -1, 1]]

theorem canonical3126 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3126 = injectiveMoment H node2813 := by
  calc
    injectiveMoment H raw3126 = injectiveMoment H raw3126step0 := by
      have heq : raw3126step0 = -raw3126 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3126).symm
    injectiveMoment H raw3126step0 = injectiveMoment H raw3126step1 := by
      have heq : raw3126step1 = (fun i j => raw3126step0 (permutation100 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3126step0 permutation100 permutation15
    _ = injectiveMoment H node2813 := by rfl

def raw3127 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 2, -2], ![1, 0, -1, 0]]

def raw3127step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 1, -3], ![0, 0, -1, 1], ![0, -1, 1, 0], ![-1, 1, -2, 2], ![-1, 0, 1, 0]]

def raw3127step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, 0, 1, -1], ![0, 2, -3, 1], ![1, -1, 2, -2]]

theorem canonical3127 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3127 = injectiveMoment H node2757 := by
  calc
    injectiveMoment H raw3127 = injectiveMoment H raw3127step0 := by
      have heq : raw3127step0 = -raw3127 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3127).symm
    injectiveMoment H raw3127step0 = injectiveMoment H raw3127step1 := by
      have heq : raw3127step1 = (fun i j => raw3127step0 (permutation100 i) (permutation16 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3127step0 permutation100 permutation16
    _ = injectiveMoment H node2757 := by rfl

def raw3128 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, -1, 0], ![2, -2, 1, -1]]

def raw3128step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, 1, -2, -1]]

theorem canonical3128 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3128 = injectiveMoment H node1631 := by
  calc
    injectiveMoment H raw3128 = injectiveMoment H raw3128step0 := by
      have heq : raw3128step0 = (fun i j => raw3128 (permutation47 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3128 permutation47 permutation11
    _ = injectiveMoment H node1631 := by rfl

def raw3129 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 2, -2], ![1, 0, -2, 1]]

def raw3129step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 1, -3], ![0, 0, -1, 1], ![0, -1, 0, 1], ![-1, 1, -2, 2], ![-1, 0, 2, -1]]

def raw3129step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 2, -1], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, -1, -2, 2]]

theorem canonical3129 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3129 = injectiveMoment H node2775 := by
  calc
    injectiveMoment H raw3129 = injectiveMoment H raw3129step0 := by
      have heq : raw3129step0 = -raw3129 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3129).symm
    injectiveMoment H raw3129step0 = injectiveMoment H raw3129step1 := by
      have heq : raw3129step1 = (fun i j => raw3129step0 (permutation100 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3129step0 permutation100 permutation15
    _ = injectiveMoment H node2775 := by rfl

def raw3130 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, -1, 0, 0], ![1, -1, 2, -2]]

theorem canonical3130 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3130 = injectiveMoment H node1957 := by
  rfl

def raw3131 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, -1, 1, -1], ![1, -1, 1, -1]]

theorem canonical3131 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3131 = injectiveMoment H node1958 := by
  rfl

def raw3132 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, -1, 0, 0], ![1, -1, 1, -1]]

def raw3132step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 1, -1, -1]]

theorem canonical3132 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3132 = injectiveMoment H node1652 := by
  calc
    injectiveMoment H raw3132 = injectiveMoment H raw3132step0 := by
      have heq : raw3132step0 = (fun i j => raw3132 (permutation39 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3132 permutation39 permutation11
    _ = injectiveMoment H node1652 := by rfl

def raw3133 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 1, -1], ![0, 2, -1, -1], ![2, -2, 1, -1]]

def raw3133step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, 2, -2], ![-1, 1, -1, 1], ![3, -1, -1, -1]]

def raw3133step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 2, -2], ![0, 2, -2, 0], ![1, -1, 1, -1]]

theorem canonical3133 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3133 = injectiveMoment H node975 := by
  calc
    injectiveMoment H raw3133 = injectiveMoment H raw3133step0 := by
      have heq : raw3133step0 = raw3133.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3133).symm
    injectiveMoment H raw3133step0 = injectiveMoment H raw3133step1 := by
      have heq : raw3133step1 = (fun i j => raw3133step0 (permutation27 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3133step0 permutation27 permutation18
    _ = injectiveMoment H node975 := by rfl

def raw3134 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 1, -1], ![1, -1, 1, -1], ![1, 1, -1, -1]]

def raw3134step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, -1, 1], ![-1, 1, 1, -1], ![3, -1, -1, -1]]

def raw3134step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 1, 0], ![0, 1, 1, -2], ![1, 1, -1, -1]]

theorem canonical3134 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3134 = injectiveMoment H node936 := by
  calc
    injectiveMoment H raw3134 = injectiveMoment H raw3134step0 := by
      have heq : raw3134step0 = raw3134.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3134).symm
    injectiveMoment H raw3134step0 = injectiveMoment H raw3134step1 := by
      have heq : raw3134step1 = (fun i j => raw3134step0 (permutation29 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3134step0 permutation29 permutation18
    _ = injectiveMoment H node936 := by rfl

def raw3135 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 2, -2], ![0, 1, -2, 1], ![0, 1, 0, -1], ![2, -2, 1, -1]]

theorem canonical3135 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3135 = injectiveMoment H node1959 := by
  rfl

end MUB6.Certificate.PairSemantics

end OAI
