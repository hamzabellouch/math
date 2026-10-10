import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes0
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes2
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes4
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes10
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes13
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes17
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes18
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes19
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes20
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes40
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes41
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes42
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes43
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes48
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes49

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw8096 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, 0, 2], ![0, 0, 3, -3], ![0, 1, -1, 0], ![0, 1, -1, 0], ![0, 0, -1, 1]]

def raw8096step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1]]

def raw8096step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0]]

theorem canonical8096 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8096 = injectiveMoment H node663 := by
  calc
    injectiveMoment H raw8096 = injectiveMoment H raw8096step0 := by
      have hz : ∀ i, raw8096 i (permutation9 0) = 0 := by decide +kernel
      have heq : raw8096step0 = (fun i j => raw8096 i (permutation9 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8096 permutation9 hz
    injectiveMoment H raw8096step0 = injectiveMoment H raw8096step1 := by
      have heq : raw8096step1 = (fun i j => raw8096step0 (permutation51 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8096step0 permutation51 permutation3
    _ = injectiveMoment H node663 := by rfl

def raw8097 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -2, 0, 2], ![0, 0, 3, -3], ![0, 2, -3, 1]]

def raw8097step0 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 2, 0, -2], ![0, 0, -3, 3], ![0, -2, 3, -1]]

def raw8097step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 0, -2], ![0, -3, 3], ![-2, 3, -1]]

def raw8097step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 3, -3], ![2, -2, 0]]

theorem canonical8097 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8097 = injectiveMoment H node37 := by
  calc
    injectiveMoment H raw8097 = injectiveMoment H raw8097step0 := by
      have heq : raw8097step0 = -raw8097 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8097).symm
    injectiveMoment H raw8097step0 = injectiveMoment H raw8097step1 := by
      have hz : ∀ i, raw8097step0 i (permutation9 0) = 0 := by decide +kernel
      have heq : raw8097step1 = (fun i j => raw8097step0 i (permutation9 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8097step0 permutation9 hz
    injectiveMoment H raw8097step1 = injectiveMoment H raw8097step2 := by
      have heq : raw8097step2 = (fun i j => raw8097step1 (permutation8 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8097step1 permutation8 permutation4
    _ = injectiveMoment H node37 := by rfl

def raw8098 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -2, 0, 2], ![0, 1, -3, 2], ![0, 1, 3, -4]]

def raw8098step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 0, 0], ![-2, 1, 1], ![0, -3, 3], ![2, 2, -4]]

def raw8098step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 0, 0], ![2, -1, -1], ![0, 3, -3], ![-2, -2, 4]]

def raw8098step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, -1, -1], ![0, 3, -3], ![-2, -2, 4]]

def raw8098step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 3, -3], ![2, -1, -1]]

theorem canonical8098 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8098 = injectiveMoment H node32 := by
  calc
    injectiveMoment H raw8098 = injectiveMoment H raw8098step0 := by
      have heq : raw8098step0 = raw8098.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw8098).symm
    injectiveMoment H raw8098step0 = injectiveMoment H raw8098step1 := by
      have heq : raw8098step1 = -raw8098step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8098step0).symm
    injectiveMoment H raw8098step1 = injectiveMoment H raw8098step2 := by
      have hz : ∀ j, raw8098step1 (permutation9 0) j = 0 := by decide +kernel
      have heq : raw8098step2 = (fun i j => raw8098step1 (permutation9 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8098step1 permutation9 hz
    injectiveMoment H raw8098step2 = injectiveMoment H raw8098step3 := by
      have heq : raw8098step3 = (fun i j => raw8098step2 (permutation8 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8098step2 permutation8 permutation3
    _ = injectiveMoment H node32 := by rfl

def raw8099 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -2, 0, 2], ![0, 1, -2, 1], ![0, 1, 2, -3]]

def raw8099step0 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 2, 0, -2], ![0, -1, 2, -1], ![0, -1, -2, 3]]

def raw8099step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 0, -2], ![-1, 2, -1], ![-1, -2, 3]]

def raw8099step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![2, -1, -1]]

theorem canonical8099 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8099 = injectiveMoment H node36 := by
  calc
    injectiveMoment H raw8099 = injectiveMoment H raw8099step0 := by
      have heq : raw8099step0 = -raw8099 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8099).symm
    injectiveMoment H raw8099step0 = injectiveMoment H raw8099step1 := by
      have hz : ∀ i, raw8099step0 i (permutation9 0) = 0 := by decide +kernel
      have heq : raw8099step1 = (fun i j => raw8099step0 i (permutation9 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8099step0 permutation9 hz
    injectiveMoment H raw8099step1 = injectiveMoment H raw8099step2 := by
      have heq : raw8099step2 = (fun i j => raw8099step1 (permutation7 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8099step1 permutation7 permutation5
    _ = injectiveMoment H node36 := by rfl

def raw8100 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -2, 0, 2], ![0, 1, -1, 0], ![-1, 1, 2, -2], ![1, 0, -1, 0]]

def raw8100step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 1, 1, 0], ![0, -1, 2, -1], ![2, 0, -2, 0]]

def raw8100step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 1, -2, 1], ![1, 0, 0, -1]]

theorem canonical8100 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8100 = injectiveMoment H node1053 := by
  calc
    injectiveMoment H raw8100 = injectiveMoment H raw8100step0 := by
      have heq : raw8100step0 = raw8100.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw8100).symm
    injectiveMoment H raw8100step0 = injectiveMoment H raw8100step1 := by
      have heq : raw8100step1 = (fun i j => raw8100step0 (permutation26 i) (permutation29 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8100step0 permutation26 permutation29
    _ = injectiveMoment H node1053 := by rfl

def raw8101 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -2, 0, 2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, -1, 0], ![-2, 0, 0, 2], ![1, 0, 3, -4]]

def raw8101step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 0, 2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 0, 3, -4]]

theorem canonical8101 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8101 = injectiveMoment H node3150 := by
  calc
    injectiveMoment H raw8101 = injectiveMoment H raw8101step0 := by
      have heq : raw8101step0 = (fun i j => raw8101 (permutation258 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8101 permutation258 permutation9
    _ = injectiveMoment H node3150 := by rfl

def raw8102 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -2, 0, 2], ![0, 1, -1, 0], ![0, 1, 2, -3], ![0, 0, -1, 1]]

def raw8102step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 2, 0, -2], ![0, -1, 1, 0], ![0, -1, -2, 3], ![0, 0, 1, -1]]

def raw8102step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![-1, 1, 0], ![-1, -2, 3], ![0, 1, -1]]

def raw8102step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]

theorem canonical8102 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8102 = injectiveMoment H node185 := by
  calc
    injectiveMoment H raw8102 = injectiveMoment H raw8102step0 := by
      have heq : raw8102step0 = -raw8102 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8102).symm
    injectiveMoment H raw8102step0 = injectiveMoment H raw8102step1 := by
      have hz : ∀ i, raw8102step0 i (permutation9 0) = 0 := by decide +kernel
      have heq : raw8102step1 = (fun i j => raw8102step0 i (permutation9 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8102step0 permutation9 hz
    injectiveMoment H raw8102step1 = injectiveMoment H raw8102step2 := by
      have heq : raw8102step2 = (fun i j => raw8102step1 (permutation21 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8102step1 permutation21 permutation5
    _ = injectiveMoment H node185 := by rfl

def raw8103 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -2, 0, 2], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 0, -1, 0], ![-2, 0, 0, 2], ![0, 1, 3, -4]]

def raw8103step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 0, 2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 0, 3, -4]]

theorem canonical8103 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8103 = injectiveMoment H node3150 := by
  calc
    injectiveMoment H raw8103 = injectiveMoment H raw8103step0 := by
      have heq : raw8103step0 = (fun i j => raw8103 (permutation188 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8103 permutation188 permutation15
    _ = injectiveMoment H node3150 := by rfl

def raw8104 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -2, 0, 2], ![0, 1, 0, -1], ![-1, 1, 2, -2], ![1, 0, -2, 1]]

def raw8104step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 2, 0, -2], ![0, -1, 0, 1], ![1, -1, -2, 2], ![-1, 0, 2, -1]]

def raw8104step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -1, 0, 1], ![0, 2, 0, -2], ![1, -1, -2, 2]]

theorem canonical8104 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8104 = injectiveMoment H node1311 := by
  calc
    injectiveMoment H raw8104 = injectiveMoment H raw8104step0 := by
      have heq : raw8104step0 = -raw8104 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8104).symm
    injectiveMoment H raw8104step0 = injectiveMoment H raw8104step1 := by
      have heq : raw8104step1 = (fun i j => raw8104step0 (permutation29 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8104step0 permutation29 permutation9
    _ = injectiveMoment H node1311 := by rfl

def raw8105 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -2, 0, 2], ![0, 1, 0, -1], ![0, 1, 1, -2], ![0, 0, -1, 1]]

def raw8105step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 2, 0, -2], ![0, -1, 0, 1], ![0, -1, -1, 2], ![0, 0, 1, -1]]

def raw8105step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![-1, 0, 1], ![-1, -1, 2], ![0, 1, -1]]

def raw8105step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1]]

theorem canonical8105 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8105 = injectiveMoment H node284 := by
  calc
    injectiveMoment H raw8105 = injectiveMoment H raw8105step0 := by
      have heq : raw8105step0 = -raw8105 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8105).symm
    injectiveMoment H raw8105step0 = injectiveMoment H raw8105step1 := by
      have hz : ∀ i, raw8105step0 i (permutation9 0) = 0 := by decide +kernel
      have heq : raw8105step1 = (fun i j => raw8105step0 i (permutation9 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8105step0 permutation9 hz
    injectiveMoment H raw8105step1 = injectiveMoment H raw8105step2 := by
      have heq : raw8105step2 = (fun i j => raw8105step1 (permutation23 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8105step1 permutation23 permutation5
    _ = injectiveMoment H node284 := by rfl

def raw8106 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -2, 0, 2], ![0, 2, 1, -3], ![0, 0, -1, 1]]

def raw8106step0 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 2, 0, -2], ![0, -2, -1, 3], ![0, 0, 1, -1]]

def raw8106step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 0, -2], ![-2, -1, 3], ![0, 1, -1]]

def raw8106step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 2, -2], ![1, 0, -1]]

theorem canonical8106 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8106 = injectiveMoment H node57 := by
  calc
    injectiveMoment H raw8106 = injectiveMoment H raw8106step0 := by
      have heq : raw8106step0 = -raw8106 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8106).symm
    injectiveMoment H raw8106step0 = injectiveMoment H raw8106step1 := by
      have hz : ∀ i, raw8106step0 i (permutation9 0) = 0 := by decide +kernel
      have heq : raw8106step1 = (fun i j => raw8106step0 i (permutation9 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8106step0 permutation9 hz
    injectiveMoment H raw8106step1 = injectiveMoment H raw8106step2 := by
      have heq : raw8106step2 = (fun i j => raw8106step1 (permutation5 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8106step1 permutation5 permutation5
    _ = injectiveMoment H node57 := by rfl

def raw8107 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -2, 0, 2], ![0, 2, 2, -4], ![0, 0, -2, 2]]

def raw8107step0 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 2, 0, -2], ![0, -2, -2, 4], ![0, 0, 2, -2]]

def raw8107step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 0, -2], ![-2, -2, 4], ![0, 2, -2]]

def raw8107step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![2, 0, -2]]

theorem canonical8107 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8107 = injectiveMoment H node31 := by
  calc
    injectiveMoment H raw8107 = injectiveMoment H raw8107step0 := by
      have heq : raw8107step0 = -raw8107 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8107).symm
    injectiveMoment H raw8107step0 = injectiveMoment H raw8107step1 := by
      have hz : ∀ i, raw8107step0 i (permutation9 0) = 0 := by decide +kernel
      have heq : raw8107step1 = (fun i j => raw8107step0 i (permutation9 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8107step0 permutation9 hz
    injectiveMoment H raw8107step1 = injectiveMoment H raw8107step2 := by
      have heq : raw8107step2 = (fun i j => raw8107step1 (permutation6 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8107step1 permutation6 permutation3
    _ = injectiveMoment H node31 := by rfl

def raw8108 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -2, 1, 1], ![-1, 0, -2, 3], ![0, 2, 2, -4], ![1, 0, -1, 0]]

def raw8108step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -2, 1, 1], ![0, 2, 2, -4], ![1, 0, -1, 0]]

theorem canonical8108 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8108 = injectiveMoment H node1189 := by
  calc
    injectiveMoment H raw8108 = injectiveMoment H raw8108step0 := by
      have heq : raw8108step0 = (fun i j => raw8108 (permutation15 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8108 permutation15 permutation9
    _ = injectiveMoment H node1189 := by rfl

def raw8109 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, 1, 1], ![-1, 0, -1, 2], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, 0, -1, 0]]

def raw8109step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -2, 1, 1], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, 0, -1, 0]]

theorem canonical8109 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8109 = injectiveMoment H node2716 := by
  calc
    injectiveMoment H raw8109 = injectiveMoment H raw8109step0 := by
      have heq : raw8109step0 = (fun i j => raw8109 (permutation57 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8109 permutation57 permutation9
    _ = injectiveMoment H node2716 := by rfl

def raw8110 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, 1, 1], ![-1, 0, -1, 2], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, 0, 0, -1]]

def raw8110step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 1, 0], ![0, 1, -2, 1], ![0, 1, 1, -2], ![1, 0, 0, -1]]

theorem canonical8110 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8110 = injectiveMoment H node2585 := by
  calc
    injectiveMoment H raw8110 = injectiveMoment H raw8110step0 := by
      have heq : raw8110step0 = (fun i j => raw8110 (permutation63 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8110 permutation63 permutation11
    _ = injectiveMoment H node2585 := by rfl

def raw8111 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, 1, 1], ![-1, 0, -1, 2], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, 0, -1, 0]]

def raw8111step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -2, 1, 1], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, 0, -1, 0]]

theorem canonical8111 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8111 = injectiveMoment H node2717 := by
  calc
    injectiveMoment H raw8111 = injectiveMoment H raw8111step0 := by
      have heq : raw8111step0 = (fun i j => raw8111 (permutation57 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8111 permutation57 permutation9
    _ = injectiveMoment H node2717 := by rfl

def raw8112 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -2, 1, 1], ![-1, 0, -1, 2], ![0, 2, 1, -3], ![1, 0, -1, 0]]

def raw8112step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, -2, 1], ![0, 1, 2, -3], ![1, -1, 0, 0]]

theorem canonical8112 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8112 = injectiveMoment H node1079 := by
  calc
    injectiveMoment H raw8112 = injectiveMoment H raw8112step0 := by
      have heq : raw8112step0 = (fun i j => raw8112 (permutation15 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8112 permutation15 permutation11
    _ = injectiveMoment H node1079 := by rfl

def raw8113 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, 1, 1], ![-1, 0, 1, 0], ![0, 0, 1, -1], ![0, 2, -3, 1], ![1, 0, 0, -1]]

def raw8113step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 1, 1], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, 0, -1, 0]]

theorem canonical8113 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8113 = injectiveMoment H node2742 := by
  calc
    injectiveMoment H raw8113 = injectiveMoment H raw8113step0 := by
      have heq : raw8113step0 = (fun i j => raw8113 (permutation57 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8113 permutation57 permutation10
    _ = injectiveMoment H node2742 := by rfl

def raw8114 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, 1, 1], ![-1, 0, 1, 0], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, 0, 0, -1]]

def raw8114step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 1, 1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, 0, -1, 0]]

theorem canonical8114 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8114 = injectiveMoment H node2744 := by
  calc
    injectiveMoment H raw8114 = injectiveMoment H raw8114step0 := by
      have heq : raw8114step0 = (fun i j => raw8114 (permutation59 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8114 permutation59 permutation10
    _ = injectiveMoment H node2744 := by rfl

def raw8115 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, 1, 1], ![-1, 0, 1, 0], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1]]

def raw8115step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 2, -1, -1], ![1, 0, -1, 0], ![0, -1, 1, 0], ![0, -1, 1, 0], ![-1, 0, 0, 1]]

def raw8115step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 0, 0]]

theorem canonical8115 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8115 = injectiveMoment H node2734 := by
  calc
    injectiveMoment H raw8115 = injectiveMoment H raw8115step0 := by
      have heq : raw8115step0 = -raw8115 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8115).symm
    injectiveMoment H raw8115step0 = injectiveMoment H raw8115step1 := by
      have heq : raw8115step1 = (fun i j => raw8115step0 (permutation41 i) (permutation28 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8115step0 permutation41 permutation28
    _ = injectiveMoment H node2734 := by rfl

def raw8116 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, 1, 1], ![-1, 0, 1, 0], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0]]

def raw8116step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 2, -1, -1], ![1, 0, -1, 0], ![0, -1, 1, 0], ![0, -1, 0, 1], ![-1, 0, 1, 0]]

def raw8116step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 0, 0, -1]]

theorem canonical8116 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8116 = injectiveMoment H node2724 := by
  calc
    injectiveMoment H raw8116 = injectiveMoment H raw8116step0 := by
      have heq : raw8116step0 = -raw8116 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8116).symm
    injectiveMoment H raw8116step0 = injectiveMoment H raw8116step1 := by
      have heq : raw8116step1 = (fun i j => raw8116step0 (permutation53 i) (permutation28 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8116step0 permutation53 permutation28
    _ = injectiveMoment H node2724 := by rfl

def raw8117 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -2, 1, 1], ![-1, 0, 1, 0], ![0, 2, -2, 0], ![1, 0, 0, -1]]

def raw8117step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 2, -1, -1], ![1, 0, -1, 0], ![0, -2, 2, 0], ![-1, 0, 0, 1]]

def raw8117step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, -1, 0, 0]]

theorem canonical8117 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8117 = injectiveMoment H node1264 := by
  calc
    injectiveMoment H raw8117 = injectiveMoment H raw8117step0 := by
      have heq : raw8117step0 = -raw8117 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8117).symm
    injectiveMoment H raw8117step0 = injectiveMoment H raw8117step1 := by
      have heq : raw8117step1 = (fun i j => raw8117step0 (permutation11 i) (permutation28 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8117step0 permutation11 permutation28
    _ = injectiveMoment H node1264 := by rfl

def raw8118 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -2, 1, 1], ![-1, 1, -1, 1], ![0, 1, 1, -2], ![1, 0, -1, 0]]

def raw8118step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 1, -2, 1], ![0, 1, 1, -2], ![1, -1, 0, 0]]

theorem canonical8118 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8118 = injectiveMoment H node1126 := by
  calc
    injectiveMoment H raw8118 = injectiveMoment H raw8118step0 := by
      have heq : raw8118step0 = (fun i j => raw8118 (permutation15 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8118 permutation15 permutation11
    _ = injectiveMoment H node1126 := by rfl

def raw8119 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -2, 1, 1], ![0, 0, -2, 2], ![-1, 2, 2, -3], ![1, 0, -1, 0]]

def raw8119step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 0, 2, 0], ![1, -2, 2, -1], ![1, 2, -3, 0]]

def raw8119step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -2, 2], ![0, 2, 1, -3], ![1, 0, 0, -1]]

theorem canonical8119 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8119 = injectiveMoment H node832 := by
  calc
    injectiveMoment H raw8119 = injectiveMoment H raw8119step0 := by
      have heq : raw8119step0 = raw8119.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw8119).symm
    injectiveMoment H raw8119step0 = injectiveMoment H raw8119step1 := by
      have heq : raw8119step1 = (fun i j => raw8119step0 (permutation24 i) (permutation29 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8119step0 permutation24 permutation29
    _ = injectiveMoment H node832 := by rfl

def raw8120 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -2, 1, 1], ![0, 0, -2, 2], ![0, 2, 1, -3]]

def raw8120step0 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 2, -1, -1], ![0, 0, 2, -2], ![0, -2, -1, 3]]

def raw8120step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, -1, -1], ![0, 2, -2], ![-2, -1, 3]]

def raw8120step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![2, -1, -1]]

theorem canonical8120 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8120 = injectiveMoment H node36 := by
  calc
    injectiveMoment H raw8120 = injectiveMoment H raw8120step0 := by
      have heq : raw8120step0 = -raw8120 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8120).symm
    injectiveMoment H raw8120step0 = injectiveMoment H raw8120step1 := by
      have hz : ∀ i, raw8120step0 i (permutation9 0) = 0 := by decide +kernel
      have heq : raw8120step1 = (fun i j => raw8120step0 i (permutation9 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8120step0 permutation9 hz
    injectiveMoment H raw8120step1 = injectiveMoment H raw8120step2 := by
      have heq : raw8120step2 = (fun i j => raw8120step1 (permutation8 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8120step1 permutation8 permutation3
    _ = injectiveMoment H node36 := by rfl

def raw8121 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -2, 1, 1], ![0, 0, -2, 2], ![0, 2, 2, -4], ![0, 0, -1, 1]]

def raw8121step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 2, -1, -1], ![0, 0, 2, -2], ![0, -2, -2, 4], ![0, 0, 1, -1]]

def raw8121step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -1, -1], ![0, 2, -2], ![-2, -2, 4], ![0, 1, -1]]

def raw8121step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 2, -2], ![2, -1, -1]]

theorem canonical8121 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8121 = injectiveMoment H node146 := by
  calc
    injectiveMoment H raw8121 = injectiveMoment H raw8121step0 := by
      have heq : raw8121step0 = -raw8121 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8121).symm
    injectiveMoment H raw8121step0 = injectiveMoment H raw8121step1 := by
      have hz : ∀ i, raw8121step0 i (permutation9 0) = 0 := by decide +kernel
      have heq : raw8121step1 = (fun i j => raw8121step0 i (permutation9 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8121step0 permutation9 hz
    injectiveMoment H raw8121step1 = injectiveMoment H raw8121step2 := by
      have heq : raw8121step2 = (fun i j => raw8121step1 (permutation26 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8121step1 permutation26 permutation3
    _ = injectiveMoment H node146 := by rfl

def raw8122 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, 1, 1], ![0, 0, -1, 1], ![-1, 0, -1, 2], ![0, 2, 2, -4], ![1, 0, -1, 0]]

def raw8122step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -2, 1, 1], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, 0, -1, 0]]

theorem canonical8122 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8122 = injectiveMoment H node2716 := by
  calc
    injectiveMoment H raw8122 = injectiveMoment H raw8122step0 := by
      have heq : raw8122step0 = (fun i j => raw8122 (permutation80 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8122 permutation80 permutation9
    _ = injectiveMoment H node2716 := by rfl

def raw8123 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, 1, 1], ![0, 0, -1, 1], ![-1, 1, -1, 1], ![0, 1, 1, -2], ![1, 0, 0, -1]]

def raw8123step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, 0, 1], ![0, 1, -2, 1], ![0, 1, 1, -2], ![1, 0, 0, -1]]

theorem canonical8123 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8123 = injectiveMoment H node2631 := by
  calc
    injectiveMoment H raw8123 = injectiveMoment H raw8123step0 := by
      have heq : raw8123step0 = (fun i j => raw8123 (permutation86 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8123 permutation86 permutation11
    _ = injectiveMoment H node2631 := by rfl

def raw8124 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, 1, 1], ![0, 0, -1, 1], ![-1, 1, -1, 1], ![0, 1, 2, -3], ![1, 0, -1, 0]]

def raw8124step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 2, -1, -1], ![0, 0, 1, -1], ![1, -1, 1, -1], ![0, -1, -2, 3], ![-1, 0, 1, 0]]

def raw8124step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 3, -2], ![0, 0, -1, 1], ![0, 2, -1, -1], ![1, -1, -1, 1]]

theorem canonical8124 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8124 = injectiveMoment H node2779 := by
  calc
    injectiveMoment H raw8124 = injectiveMoment H raw8124step0 := by
      have heq : raw8124step0 = -raw8124 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8124).symm
    injectiveMoment H raw8124step0 = injectiveMoment H raw8124step1 := by
      have heq : raw8124step1 = (fun i j => raw8124step0 (permutation147 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8124step0 permutation147 permutation10
    _ = injectiveMoment H node2779 := by rfl

def raw8125 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -2, 1, 1], ![0, 0, -1, 1], ![-1, 2, 1, -2], ![1, 0, -1, 0]]

def raw8125step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 0, 2, 0], ![1, -1, 1, -1], ![1, 1, -2, 0]]

def raw8125step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, 0, 1, -2]]

theorem canonical8125 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8125 = injectiveMoment H node1110 := by
  calc
    injectiveMoment H raw8125 = injectiveMoment H raw8125step0 := by
      have heq : raw8125step0 = raw8125.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw8125).symm
    injectiveMoment H raw8125step0 = injectiveMoment H raw8125step1 := by
      have heq : raw8125step1 = (fun i j => raw8125step0 (permutation23 i) (permutation19 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8125step0 permutation23 permutation19
    _ = injectiveMoment H node1110 := by rfl

def raw8126 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, 1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![-1, 2, 2, -3], ![1, 0, -1, 0]]

def raw8126step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 2, -1, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -2, -2, 3], ![-1, 0, 1, 0]]

def raw8126step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 2, -1, -1], ![1, -2, 3, -2]]

theorem canonical8126 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8126 = injectiveMoment H node2782 := by
  calc
    injectiveMoment H raw8126 = injectiveMoment H raw8126step0 := by
      have heq : raw8126step0 = -raw8126 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8126).symm
    injectiveMoment H raw8126step0 = injectiveMoment H raw8126step1 := by
      have heq : raw8126step1 = (fun i j => raw8126step0 (permutation135 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8126step0 permutation135 permutation10
    _ = injectiveMoment H node2782 := by rfl

def raw8127 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -2, 1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![-2, 2, 0, 0], ![2, 0, 2, -4]]

def raw8127step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 2, -1, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![2, -2, 0, 0], ![-2, 0, -2, 4]]

def raw8127step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -1, -1], ![2, -2, 0, 0]]

theorem canonical8127 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8127 = injectiveMoment H node3117 := by
  calc
    injectiveMoment H raw8127 = injectiveMoment H raw8127step0 := by
      have heq : raw8127step0 = -raw8127 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8127).symm
    injectiveMoment H raw8127step0 = injectiveMoment H raw8127step1 := by
      have heq : raw8127step1 = (fun i j => raw8127step0 (permutation339 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8127step0 permutation339 permutation9
    _ = injectiveMoment H node3117 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
