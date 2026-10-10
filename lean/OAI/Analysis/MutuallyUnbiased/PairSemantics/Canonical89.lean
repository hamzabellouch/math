import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes0
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes1
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes2
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes3
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes7
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes29

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw2848 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0]]

theorem canonical2848 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2848 = injectiveMoment H node188 := by
  rfl

def raw2849 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 3, -3], ![2, -2, 0]]

theorem canonical2849 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2849 = injectiveMoment H node37 := by
  rfl

def raw2850 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 4, -4], ![1, -3, 2], ![1, 0, -1]]

theorem canonical2850 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2850 = injectiveMoment H node189 := by
  rfl

def raw2851 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 4, -4], ![1, -2, 1], ![1, -1, 0]]

theorem canonical2851 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2851 = injectiveMoment H node190 := by
  rfl

def raw2852 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 4, -4], ![1, -1, 0], ![1, -2, 1]]

def raw2852step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 4, -4], ![1, -2, 1], ![1, -1, 0]]

theorem canonical2852 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2852 = injectiveMoment H node190 := by
  calc
    injectiveMoment H raw2852 = injectiveMoment H raw2852step0 := by
      have heq : raw2852step0 = (fun i j => raw2852 (permutation10 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2852 permutation10 permutation3
    _ = injectiveMoment H node190 := by rfl

def raw2853 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 4, -4], ![2, -3, 1]]

theorem canonical2853 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2853 = injectiveMoment H node38 := by
  rfl

def raw2854 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![1, -3, 2], ![0, 2, -2], ![1, 2, -3]]

def raw2854step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, -3, 2], ![1, 2, -3]]

theorem canonical2854 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2854 = injectiveMoment H node183 := by
  calc
    injectiveMoment H raw2854 = injectiveMoment H raw2854step0 := by
      have heq : raw2854step0 = (fun i j => raw2854 (permutation11 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2854 permutation11 permutation3
    _ = injectiveMoment H node183 := by rfl

def raw2855 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![1, -3, 2], ![0, 3, -3], ![1, 1, -2]]

def raw2855step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 3, -3], ![1, -3, 2], ![1, 1, -2]]

theorem canonical2855 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2855 = injectiveMoment H node186 := by
  calc
    injectiveMoment H raw2855 = injectiveMoment H raw2855step0 := by
      have heq : raw2855step0 = (fun i j => raw2855 (permutation11 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2855 permutation11 permutation3
    _ = injectiveMoment H node186 := by rfl

def raw2856 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![1, -3, 2], ![0, 4, -4], ![1, 0, -1]]

def raw2856step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 4, -4], ![1, -3, 2], ![1, 0, -1]]

theorem canonical2856 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2856 = injectiveMoment H node189 := by
  calc
    injectiveMoment H raw2856 = injectiveMoment H raw2856step0 := by
      have heq : raw2856step0 = (fun i j => raw2856 (permutation11 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2856 permutation11 permutation3
    _ = injectiveMoment H node189 := by rfl

def raw2857 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![1, -3, 2], ![1, 4, -5]]

theorem canonical2857 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2857 = injectiveMoment H node39 := by
  rfl

def raw2858 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![1, -2, 1], ![0, 2, -2], ![1, 1, -2]]

def raw2858step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, -2, 1], ![1, 1, -2]]

theorem canonical2858 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2858 = injectiveMoment H node184 := by
  calc
    injectiveMoment H raw2858 = injectiveMoment H raw2858step0 := by
      have heq : raw2858step0 = (fun i j => raw2858 (permutation11 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2858 permutation11 permutation3
    _ = injectiveMoment H node184 := by rfl

def raw2859 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![1, -2, 1], ![0, 3, -3], ![1, 0, -1]]

def raw2859step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 3, -3], ![1, -2, 1], ![1, 0, -1]]

theorem canonical2859 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2859 = injectiveMoment H node187 := by
  calc
    injectiveMoment H raw2859 = injectiveMoment H raw2859step0 := by
      have heq : raw2859step0 = (fun i j => raw2859 (permutation11 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2859 permutation11 permutation3
    _ = injectiveMoment H node187 := by rfl

def raw2860 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![1, -2, 1], ![1, 3, -4]]

theorem canonical2860 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2860 = injectiveMoment H node40 := by
  rfl

def raw2861 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![1, -1, 0], ![1, 2, -3]]

def raw2861step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![3, 0, -3]]

def raw2861step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 3, -3], ![1, -2, 1]]

theorem canonical2861 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2861 = injectiveMoment H node63 := by
  calc
    injectiveMoment H raw2861 = injectiveMoment H raw2861step0 := by
      have heq : raw2861step0 = raw2861.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2861).symm
    injectiveMoment H raw2861step0 = injectiveMoment H raw2861step1 := by
      have heq : raw2861step1 = (fun i j => raw2861step0 (permutation6 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2861step0 permutation6 permutation5
    _ = injectiveMoment H node63 := by rfl

def raw2862 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![1, 0, -1], ![1, 1, -2]]

def raw2862step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 1, -1], ![1, 1, -2]]

theorem canonical2862 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2862 = injectiveMoment H node56 := by
  calc
    injectiveMoment H raw2862 = injectiveMoment H raw2862step0 := by
      have heq : raw2862step0 = (fun i j => raw2862 (permutation3 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2862 permutation3 permutation5
    _ = injectiveMoment H node56 := by rfl

def raw2863 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![1, 1, -2], ![1, 0, -1]]

def raw2863step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 1, -1], ![1, 1, -2]]

theorem canonical2863 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2863 = injectiveMoment H node56 := by
  calc
    injectiveMoment H raw2863 = injectiveMoment H raw2863step0 := by
      have heq : raw2863step0 = (fun i j => raw2863 (permutation4 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2863 permutation4 permutation5
    _ = injectiveMoment H node56 := by rfl

def raw2864 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![1, 2, -3], ![1, -1, 0]]

def raw2864step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![3, -3, 0]]

def raw2864step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 3, -3], ![1, -2, 1]]

theorem canonical2864 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2864 = injectiveMoment H node63 := by
  calc
    injectiveMoment H raw2864 = injectiveMoment H raw2864step0 := by
      have heq : raw2864step0 = raw2864.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2864).symm
    injectiveMoment H raw2864step0 = injectiveMoment H raw2864step1 := by
      have heq : raw2864step1 = (fun i j => raw2864step0 (permutation6 i) (permutation7 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2864step0 permutation6 permutation7
    _ = injectiveMoment H node63 := by rfl

def raw2865 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![1, 3, -4], ![1, -2, 1]]

def raw2865step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![1, -2, 1], ![1, 3, -4]]

theorem canonical2865 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2865 = injectiveMoment H node40 := by
  calc
    injectiveMoment H raw2865 = injectiveMoment H raw2865step0 := by
      have heq : raw2865step0 = (fun i j => raw2865 (permutation4 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2865 permutation4 permutation3
    _ = injectiveMoment H node40 := by rfl

def raw2866 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![1, 4, -5], ![1, -3, 2]]

def raw2866step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![1, -3, 2], ![1, 4, -5]]

theorem canonical2866 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2866 = injectiveMoment H node39 := by
  calc
    injectiveMoment H raw2866 = injectiveMoment H raw2866step0 := by
      have heq : raw2866step0 = (fun i j => raw2866 (permutation4 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2866 permutation4 permutation3
    _ = injectiveMoment H node39 := by rfl

def raw2867 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, -1, 3, 0], ![-2, 2, -2, 2], ![4, -1, -1, -2]]

def raw2867step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![3, -2, -1], ![0, 2, -2]]

def raw2867step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -2, 1], ![-3, 2, 1], ![0, -2, 2]]

def raw2867step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, 1, -2], ![2, -4, 2]]

theorem canonical2867 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2867 = injectiveMoment H node112 := by
  calc
    injectiveMoment H raw2867 = injectiveMoment H raw2867step0 := by
      have heq : raw2867step0 = raw2867.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2867).symm
    injectiveMoment H raw2867step0 = injectiveMoment H raw2867step1 := by
      have heq : raw2867step1 = -raw2867step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2867step0).symm
    injectiveMoment H raw2867step1 = injectiveMoment H raw2867step2 := by
      have heq : raw2867step2 = (fun i j => raw2867step1 (permutation26 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2867step1 permutation26 permutation4
    _ = injectiveMoment H node112 := by rfl

def raw2868 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, -1, 3, 0], ![-1, 2, -2, 1], ![3, -1, -1, -1]]

def raw2868step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![3, -2, -1], ![0, 1, -1]]

def raw2868step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-3, 2, 1], ![0, -1, 1]]

def raw2868step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]

theorem canonical2868 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2868 = injectiveMoment H node109 := by
  calc
    injectiveMoment H raw2868 = injectiveMoment H raw2868step0 := by
      have heq : raw2868step0 = raw2868.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2868).symm
    injectiveMoment H raw2868step0 = injectiveMoment H raw2868step1 := by
      have heq : raw2868step1 = -raw2868step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2868step0).symm
    injectiveMoment H raw2868step1 = injectiveMoment H raw2868step2 := by
      have heq : raw2868step2 = (fun i j => raw2868step1 (permutation26 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2868step1 permutation26 permutation4
    _ = injectiveMoment H node109 := by rfl

def raw2869 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, -1, 3, 0], ![0, 2, -1, -1], ![2, -1, -2, 1]]

def raw2869step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![3, -1, -2], ![0, -1, 1]]

def raw2869step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-3, 1, 2], ![0, 1, -1]]

def raw2869step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![1, -1, 0], ![1, 2, -3]]

theorem canonical2869 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2869 = injectiveMoment H node226 := by
  calc
    injectiveMoment H raw2869 = injectiveMoment H raw2869step0 := by
      have heq : raw2869step0 = raw2869.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2869).symm
    injectiveMoment H raw2869step0 = injectiveMoment H raw2869step1 := by
      have heq : raw2869step1 = -raw2869step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2869step0).symm
    injectiveMoment H raw2869step1 = injectiveMoment H raw2869step2 := by
      have heq : raw2869step2 = (fun i j => raw2869step1 (permutation16 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2869step1 permutation16 permutation6
    _ = injectiveMoment H node226 := by rfl

def raw2870 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, -1, 3, 0], ![0, 3, -2, -1], ![2, -2, -1, 1]]

def raw2870step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![3, -2, -1], ![0, -1, 1]]

def raw2870step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -3, 2], ![-3, 2, 1], ![0, 1, -1]]

def raw2870step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]

theorem canonical2870 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2870 = injectiveMoment H node107 := by
  calc
    injectiveMoment H raw2870 = injectiveMoment H raw2870step0 := by
      have heq : raw2870step0 = raw2870.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2870).symm
    injectiveMoment H raw2870step0 = injectiveMoment H raw2870step1 := by
      have heq : raw2870step1 = -raw2870step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2870step0).symm
    injectiveMoment H raw2870step1 = injectiveMoment H raw2870step2 := by
      have heq : raw2870step2 = (fun i j => raw2870step1 (permutation26 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2870step1 permutation26 permutation4
    _ = injectiveMoment H node107 := by rfl

def raw2871 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, -1, 3, 0], ![1, 2, -1, -2], ![1, -1, -2, 2]]

def raw2871step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![3, -1, -2], ![0, -2, 2]]

def raw2871step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -1, -1], ![1, -2, 1], ![-3, 1, 2], ![0, 2, -2]]

def raw2871step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]

theorem canonical2871 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2871 = injectiveMoment H node111 := by
  calc
    injectiveMoment H raw2871 = injectiveMoment H raw2871step0 := by
      have heq : raw2871step0 = raw2871.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2871).symm
    injectiveMoment H raw2871step0 = injectiveMoment H raw2871step1 := by
      have heq : raw2871step1 = -raw2871step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2871step0).symm
    injectiveMoment H raw2871step1 = injectiveMoment H raw2871step2 := by
      have heq : raw2871step2 = (fun i j => raw2871step1 (permutation26 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2871step1 permutation26 permutation3
    _ = injectiveMoment H node111 := by rfl

def raw2872 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, -1, 3, 0], ![2, -2, 1, -1], ![0, 3, -4, 1]]

def raw2872step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![3, 1, -4], ![0, -1, 1]]

def raw2872step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -2, 0], ![1, 2, -3], ![-3, -1, 4], ![0, 1, -1]]

def raw2872step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 2, -3], ![2, -2, 0]]

theorem canonical2872 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2872 = injectiveMoment H node83 := by
  calc
    injectiveMoment H raw2872 = injectiveMoment H raw2872step0 := by
      have heq : raw2872step0 = raw2872.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2872).symm
    injectiveMoment H raw2872step0 = injectiveMoment H raw2872step1 := by
      have heq : raw2872step1 = -raw2872step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2872step0).symm
    injectiveMoment H raw2872step1 = injectiveMoment H raw2872step2 := by
      have heq : raw2872step2 = (fun i j => raw2872step1 (permutation26 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2872step1 permutation26 permutation3
    _ = injectiveMoment H node83 := by rfl

def raw2873 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -2, 2, 0], ![0, 0, 1, -1], ![0, 2, -1, -1], ![2, 0, 0, -2]]

theorem canonical2873 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2873 = injectiveMoment H node1892 := by
  rfl

def raw2874 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -2, 2, 0], ![0, 0, 1, -1], ![0, 2, 0, -2], ![2, 0, -1, -1]]

theorem canonical2874 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2874 = injectiveMoment H node1893 := by
  rfl

def raw2875 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -2, 2, 0], ![0, 0, 1, -1], ![1, 1, -1, -1], ![1, 1, 0, -2]]

theorem canonical2875 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2875 = injectiveMoment H node1894 := by
  rfl

def raw2876 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -2, 2, 0], ![0, 1, -1, 0], ![0, 1, 1, -2], ![2, 0, 0, -2]]

theorem canonical2876 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2876 = injectiveMoment H node1895 := by
  rfl

def raw2877 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -2, 2, 0], ![0, 1, 0, -1], ![0, 1, 1, -2], ![2, 0, -1, -1]]

theorem canonical2877 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2877 = injectiveMoment H node1896 := by
  rfl

def raw2878 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -2, 2, 0], ![0, 1, 0, -1], ![1, 0, 1, -2], ![1, 1, -1, -1]]

theorem canonical2878 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2878 = injectiveMoment H node1897 := by
  rfl

def raw2879 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -2, 2, 0], ![0, 1, 1, -2], ![2, 1, -1, -2]]

def raw2879step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 2, -4], ![0, 2, -2, 0], ![0, -1, -1, 2], ![-2, -1, 1, 2]]

def raw2879step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, -1, 2], ![0, 2, -2, 0], ![2, 0, 2, -4]]

theorem canonical2879 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2879 = injectiveMoment H node498 := by
  calc
    injectiveMoment H raw2879 = injectiveMoment H raw2879step0 := by
      have heq : raw2879step0 = -raw2879 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2879).symm
    injectiveMoment H raw2879step0 = injectiveMoment H raw2879step1 := by
      have heq : raw2879step1 = (fun i j => raw2879step0 (permutation32 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2879step0 permutation32 permutation9
    _ = injectiveMoment H node498 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
