import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes0
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes2
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes5
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes8
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes29

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw2720 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 3, -3], ![1, 0, -1], ![1, 0, -1]]

theorem canonical2720 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2720 = injectiveMoment H node549 := by
  rfl

def raw2721 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 3, -3], ![2, 0, -2]]

theorem canonical2721 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2721 = injectiveMoment H node163 := by
  rfl

def raw2722 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 4, -4], ![1, -1, 0], ![1, 0, -1]]

theorem canonical2722 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2722 = injectiveMoment H node550 := by
  rfl

def raw2723 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 4, -4], ![2, -1, -1]]

theorem canonical2723 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2723 = injectiveMoment H node164 := by
  rfl

def raw2724 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![1, -1, 0], ![1, 4, -5]]

theorem canonical2724 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2724 = injectiveMoment H node165 := by
  rfl

def raw2725 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![1, 0, -1], ![1, 3, -4]]

theorem canonical2725 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2725 = injectiveMoment H node166 := by
  rfl

def raw2726 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![1, 1, -2], ![1, 2, -3]]

theorem canonical2726 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2726 = injectiveMoment H node167 := by
  rfl

def raw2727 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![1, 2, -3], ![1, 1, -2]]

def raw2727step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![1, 1, -2], ![1, 2, -3]]

theorem canonical2727 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2727 = injectiveMoment H node167 := by
  calc
    injectiveMoment H raw2727 = injectiveMoment H raw2727step0 := by
      have heq : raw2727step0 = (fun i j => raw2727 (permutation10 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2727 permutation10 permutation3
    _ = injectiveMoment H node167 := by rfl

def raw2728 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![1, 3, -4], ![1, 0, -1]]

def raw2728step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![1, 0, -1], ![1, 3, -4]]

theorem canonical2728 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2728 = injectiveMoment H node166 := by
  calc
    injectiveMoment H raw2728 = injectiveMoment H raw2728step0 := by
      have heq : raw2728step0 = (fun i j => raw2728 (permutation10 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2728 permutation10 permutation3
    _ = injectiveMoment H node166 := by rfl

def raw2729 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![2, 3, -5]]

def raw2729step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 1, -3], ![0, 2, -2], ![-2, -3, 5]]

def raw2729step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 2, -2], ![2, 1, -3]]

theorem canonical2729 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2729 = injectiveMoment H node27 := by
  calc
    injectiveMoment H raw2729 = injectiveMoment H raw2729step0 := by
      have heq : raw2729step0 = -raw2729 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2729).symm
    injectiveMoment H raw2729step0 = injectiveMoment H raw2729step1 := by
      have heq : raw2729step1 = (fun i j => raw2729step0 (permutation8 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2729step0 permutation8 permutation3
    _ = injectiveMoment H node27 := by rfl

def raw2730 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![-1, 1, 0], ![1, 2, -3], ![2, -1, -1]]

def raw2730step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]

theorem canonical2730 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2730 = injectiveMoment H node531 := by
  calc
    injectiveMoment H raw2730 = injectiveMoment H raw2730step0 := by
      have heq : raw2730step0 = (fun i j => raw2730 (permutation39 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2730 permutation39 permutation3
    _ = injectiveMoment H node531 := by rfl

def raw2731 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![-1, 2, -1], ![1, -1, 0], ![2, 1, -3]]

def raw2731step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![1, -2, 1], ![-1, 1, 0], ![-2, -1, 3]]

def raw2731step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]

theorem canonical2731 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2731 = injectiveMoment H node532 := by
  calc
    injectiveMoment H raw2731 = injectiveMoment H raw2731step0 := by
      have heq : raw2731step0 = -raw2731 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2731).symm
    injectiveMoment H raw2731step0 = injectiveMoment H raw2731step1 := by
      have heq : raw2731step1 = (fun i j => raw2731step0 (permutation148 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2731step0 permutation148 permutation3
    _ = injectiveMoment H node532 := by rfl

def raw2732 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![-1, 2, -1], ![1, 1, -2], ![2, -1, -1]]

def raw2732step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]

theorem canonical2732 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2732 = injectiveMoment H node535 := by
  calc
    injectiveMoment H raw2732 = injectiveMoment H raw2732step0 := by
      have heq : raw2732step0 = (fun i j => raw2732 (permutation39 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2732 permutation39 permutation3
    _ = injectiveMoment H node535 := by rfl

def raw2733 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![-1, 3, -2], ![1, -1, 0], ![2, 0, -2]]

def raw2733step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![1, -3, 2], ![-1, 1, 0], ![-2, 0, 2]]

def raw2733step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]

theorem canonical2733 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2733 = injectiveMoment H node360 := by
  calc
    injectiveMoment H raw2733 = injectiveMoment H raw2733step0 := by
      have heq : raw2733step0 = -raw2733 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2733).symm
    injectiveMoment H raw2733step0 = injectiveMoment H raw2733step1 := by
      have heq : raw2733step1 = (fun i j => raw2733step0 (permutation103 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2733step0 permutation103 permutation5
    _ = injectiveMoment H node360 := by rfl

def raw2734 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![-1, 3, -2], ![1, 0, -1], ![2, -1, -1]]

def raw2734step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![1, -3, 2], ![-1, 0, 1], ![-2, 1, 1]]

def raw2734step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]

theorem canonical2734 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2734 = injectiveMoment H node371 := by
  calc
    injectiveMoment H raw2734 = injectiveMoment H raw2734step0 := by
      have heq : raw2734step0 = -raw2734 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2734).symm
    injectiveMoment H raw2734step0 = injectiveMoment H raw2734step1 := by
      have heq : raw2734step1 = (fun i j => raw2734step0 (permutation97 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2734step0 permutation97 permutation5
    _ = injectiveMoment H node371 := by rfl

def raw2735 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, 1, -3]]

theorem canonical2735 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2735 = injectiveMoment H node1873 := by
  rfl

def raw2736 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 4, -5]]

theorem canonical2736 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2736 = injectiveMoment H node552 := by
  rfl

def raw2737 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 3, -4]]

theorem canonical2737 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2737 = injectiveMoment H node553 := by
  rfl

def raw2738 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![2, 1, -3]]

def raw2738step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![2, 1, -3]]

theorem canonical2738 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2738 = injectiveMoment H node168 := by
  calc
    injectiveMoment H raw2738 = injectiveMoment H raw2738step0 := by
      have hz : ∀ j, raw2738 (permutation80 0) j = 0 := by decide +kernel
      have heq : raw2738step0 = (fun i j => raw2738 (permutation80 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw2738 permutation80 hz
    _ = injectiveMoment H node168 := by rfl

def raw2739 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 0, 0], ![0, 2, -2], ![2, 0, -2]]

def raw2739step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 2, -2], ![2, 0, -2]]

theorem canonical2739 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2739 = injectiveMoment H node169 := by
  calc
    injectiveMoment H raw2739 = injectiveMoment H raw2739step0 := by
      have hz : ∀ j, raw2739 (permutation80 0) j = 0 := by decide +kernel
      have heq : raw2739step0 = (fun i j => raw2739 (permutation80 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw2739 permutation80 hz
    _ = injectiveMoment H node169 := by rfl

def raw2740 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![1, 3, -4]]

def raw2740step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 3, -4]]

theorem canonical2740 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2740 = injectiveMoment H node173 := by
  calc
    injectiveMoment H raw2740 = injectiveMoment H raw2740step0 := by
      have hz : ∀ j, raw2740 (permutation80 0) j = 0 := by decide +kernel
      have heq : raw2740step0 = (fun i j => raw2740 (permutation80 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw2740 permutation80 hz
    _ = injectiveMoment H node173 := by rfl

def raw2741 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![1, 2, -3]]

def raw2741step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![1, 0, -1], ![1, 2, -3]]

theorem canonical2741 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2741 = injectiveMoment H node174 := by
  calc
    injectiveMoment H raw2741 = injectiveMoment H raw2741step0 := by
      have hz : ∀ j, raw2741 (permutation80 0) j = 0 := by decide +kernel
      have heq : raw2741step0 = (fun i j => raw2741 (permutation80 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw2741 permutation80 hz
    _ = injectiveMoment H node174 := by rfl

def raw2742 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 0, 0], ![2, 1, -3]]

def raw2742step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![2, 1, -3]]

theorem canonical2742 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2742 = injectiveMoment H node168 := by
  calc
    injectiveMoment H raw2742 = injectiveMoment H raw2742step0 := by
      have hz : ∀ j, raw2742 (permutation104 0) j = 0 := by decide +kernel
      have heq : raw2742step0 = (fun i j => raw2742 (permutation104 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw2742 permutation104 hz
    _ = injectiveMoment H node168 := by rfl

def raw2743 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]

theorem canonical2743 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2743 = injectiveMoment H node1880 := by
  rfl

def raw2744 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, 0, -2]]

theorem canonical2744 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2744 = injectiveMoment H node555 := by
  rfl

def raw2745 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![2, -1, -1]]

theorem canonical2745 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2745 = injectiveMoment H node556 := by
  rfl

def raw2746 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 3, -4]]

theorem canonical2746 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2746 = injectiveMoment H node558 := by
  rfl

def raw2747 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 2, -3]]

theorem canonical2747 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2747 = injectiveMoment H node559 := by
  rfl

def raw2748 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]

theorem canonical2748 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2748 = injectiveMoment H node560 := by
  rfl

def raw2749 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3], ![1, -1, 0]]

def raw2749step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 2, -3]]

theorem canonical2749 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2749 = injectiveMoment H node559 := by
  calc
    injectiveMoment H raw2749 = injectiveMoment H raw2749step0 := by
      have heq : raw2749step0 = (fun i j => raw2749 (permutation34 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2749 permutation34 permutation3
    _ = injectiveMoment H node559 := by rfl

def raw2750 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![2, 1, -3]]

theorem canonical2750 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2750 = injectiveMoment H node168 := by
  rfl

def raw2751 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 2, -2], ![0, 0, 0], ![2, 0, -2]]

def raw2751step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 2, -2], ![2, 0, -2]]

theorem canonical2751 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2751 = injectiveMoment H node169 := by
  calc
    injectiveMoment H raw2751 = injectiveMoment H raw2751step0 := by
      have hz : ∀ j, raw2751 (permutation104 0) j = 0 := by decide +kernel
      have heq : raw2751step0 = (fun i j => raw2751 (permutation104 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw2751 permutation104 hz
    _ = injectiveMoment H node169 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
