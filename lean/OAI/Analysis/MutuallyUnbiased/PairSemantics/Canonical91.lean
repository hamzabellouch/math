import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes2
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes6
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes7
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes9
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes12
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes14
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes17
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes19
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes23
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes29
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes42

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw2912 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -1, 1, 0], ![0, 1, 1, -2], ![2, 0, 0, -2]]

def raw2912step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 2, -4], ![0, 1, -1, 0], ![0, -1, -1, 2], ![-2, 0, 0, 2]]

def raw2912step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 2, 2, -4], ![1, -1, 0, 0]]

theorem canonical2912 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2912 = injectiveMoment H node1037 := by
  calc
    injectiveMoment H raw2912 = injectiveMoment H raw2912step0 := by
      have heq : raw2912step0 = -raw2912 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2912).symm
    injectiveMoment H raw2912step0 = injectiveMoment H raw2912step1 := by
      have heq : raw2912step1 = (fun i j => raw2912step0 (permutation25 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2912step0 permutation25 permutation17
    _ = injectiveMoment H node1037 := by rfl

def raw2913 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -1, 1, 0], ![0, 2, -1, -1], ![1, -1, 1, -1], ![1, 0, 1, -2]]

theorem canonical2913 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2913 = injectiveMoment H node1906 := by
  rfl

def raw2914 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -1, 1, 0], ![0, 2, -1, -1], ![1, 0, 0, -1], ![1, -1, 2, -2]]

def raw2914step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -1, 1, 0], ![0, 2, -1, -1], ![1, -1, 2, -2], ![1, 0, 0, -1]]

theorem canonical2914 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2914 = injectiveMoment H node1907 := by
  calc
    injectiveMoment H raw2914 = injectiveMoment H raw2914step0 := by
      have heq : raw2914step0 = (fun i j => raw2914 (permutation34 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2914 permutation34 permutation9
    _ = injectiveMoment H node1907 := by rfl

def raw2915 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -1, 1, 0], ![0, 2, 0, -2], ![1, -1, 0, 0], ![1, 0, 1, -2]]

def raw2915step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 1, 0, -2]]

theorem canonical2915 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2915 = injectiveMoment H node1477 := by
  calc
    injectiveMoment H raw2915 = injectiveMoment H raw2915step0 := by
      have heq : raw2915step0 = (fun i j => raw2915 (permutation39 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2915 permutation39 permutation11
    _ = injectiveMoment H node1477 := by rfl

def raw2916 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -1, 1, 0], ![0, 2, 0, -2], ![1, 0, -1, 0], ![1, -1, 2, -2]]

def raw2916step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -1, 1, 0], ![0, 2, 0, -2], ![1, -1, 2, -2], ![1, 0, -1, 0]]

theorem canonical2916 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2916 = injectiveMoment H node1908 := by
  calc
    injectiveMoment H raw2916 = injectiveMoment H raw2916step0 := by
      have heq : raw2916step0 = (fun i j => raw2916 (permutation34 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2916 permutation34 permutation9
    _ = injectiveMoment H node1908 := by rfl

def raw2917 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -1, 2, -1], ![0, 0, 1, -1], ![0, 2, -1, -1], ![2, -1, 0, -1]]

theorem canonical2917 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2917 = injectiveMoment H node1909 := by
  rfl

def raw2918 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -1, 2, -1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![2, -1, 0, -1]]

theorem canonical2918 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2918 = injectiveMoment H node1910 := by
  rfl

def raw2919 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -1, 2, -1], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 1, -1, -1]]

theorem canonical2919 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2919 = injectiveMoment H node1911 := by
  rfl

def raw2920 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -1, 2, -1], ![0, 1, 0, -1], ![2, 0, 0, -2]]

def raw2920step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 1, 0], ![-2, 2, 0, 0], ![4, -1, -1, -2]]

def raw2920step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 2, -2], ![0, 2, 0, -2], ![1, 0, -1, 0]]

theorem canonical2920 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2920 = injectiveMoment H node775 := by
  calc
    injectiveMoment H raw2920 = injectiveMoment H raw2920step0 := by
      have heq : raw2920step0 = raw2920.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2920).symm
    injectiveMoment H raw2920step0 = injectiveMoment H raw2920step1 := by
      have heq : raw2920step1 = (fun i j => raw2920step0 (permutation31 i) (permutation26 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2920step0 permutation31 permutation26
    _ = injectiveMoment H node775 := by rfl

def raw2921 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -1, 2, -1], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, 1, -1, -1]]

theorem canonical2921 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2921 = injectiveMoment H node1912 := by
  rfl

def raw2922 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -1, 2, -1], ![0, 1, 1, -2], ![2, 0, -1, -1]]

def raw2922step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 2, -4], ![0, 1, -2, 1], ![0, -1, -1, 2], ![-2, 0, 1, 1]]

def raw2922step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -2, 1, 1], ![0, 2, 2, -4], ![1, 0, -2, 1]]

theorem canonical2922 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2922 = injectiveMoment H node1234 := by
  calc
    injectiveMoment H raw2922 = injectiveMoment H raw2922step0 := by
      have heq : raw2922step0 = -raw2922 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2922).symm
    injectiveMoment H raw2922step0 = injectiveMoment H raw2922step1 := by
      have heq : raw2922step1 = (fun i j => raw2922step0 (permutation25 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2922step0 permutation25 permutation15
    _ = injectiveMoment H node1234 := by rfl

def raw2923 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -1, 2, -1], ![0, 2, -1, -1], ![1, -1, 0, 0], ![1, 0, 1, -2]]

theorem canonical2923 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2923 = injectiveMoment H node1913 := by
  rfl

def raw2924 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -1, 2, -1], ![0, 2, -1, -1], ![1, -1, 1, -1], ![1, 0, 0, -1]]

theorem canonical2924 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2924 = injectiveMoment H node1914 := by
  rfl

def raw2925 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -1, 2, -1], ![0, 2, -1, -1], ![2, -1, 1, -2]]

theorem canonical2925 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2925 = injectiveMoment H node579 := by
  rfl

def raw2926 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -1, 2, -1], ![0, 2, 0, -2], ![1, -1, 1, -1], ![1, 0, -1, 0]]

theorem canonical2926 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2926 = injectiveMoment H node1915 := by
  rfl

def raw2927 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -1, 2, -1], ![0, 2, 0, -2], ![2, -1, 0, -1]]

def raw2927step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 2, -2], ![0, 2, -1, -1], ![2, 0, -1, -1]]

theorem canonical2927 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2927 = injectiveMoment H node396 := by
  calc
    injectiveMoment H raw2927 = injectiveMoment H raw2927step0 := by
      have heq : raw2927step0 = (fun i j => raw2927 (permutation11 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2927 permutation11 permutation11
    _ = injectiveMoment H node396 := by rfl

def raw2928 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -1, 2, -1], ![1, -1, 1, -1], ![1, 2, -1, -2]]

def raw2928step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, -1, 2], ![-2, 2, 1, -1], ![4, -1, -1, -2]]

def raw2928step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 1, 1, -2], ![2, -2, -1, 1], ![-4, 1, 1, 2]]

def raw2928step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, -1, 2], ![1, 1, -2, 0], ![1, 1, 2, -4]]

theorem canonical2928 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2928 = injectiveMoment H node501 := by
  calc
    injectiveMoment H raw2928 = injectiveMoment H raw2928step0 := by
      have heq : raw2928step0 = raw2928.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2928).symm
    injectiveMoment H raw2928step0 = injectiveMoment H raw2928step1 := by
      have heq : raw2928step1 = -raw2928step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2928step0).symm
    injectiveMoment H raw2928step1 = injectiveMoment H raw2928step2 := by
      have heq : raw2928step2 = (fun i j => raw2928step1 (permutation21 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2928step1 permutation21 permutation18
    _ = injectiveMoment H node501 := by rfl

def raw2929 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -1, 2, -1], ![1, 0, 0, -1], ![1, 1, 0, -2]]

def raw2929step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 0, 1], ![-2, 2, 0, 0], ![4, -1, -1, -2]]

def raw2929step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, 1, 0, -2]]

theorem canonical2929 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2929 = injectiveMoment H node771 := by
  calc
    injectiveMoment H raw2929 = injectiveMoment H raw2929step0 := by
      have heq : raw2929step0 = raw2929.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2929).symm
    injectiveMoment H raw2929step0 = injectiveMoment H raw2929step1 := by
      have heq : raw2929step1 = (fun i j => raw2929step0 (permutation32 i) (permutation26 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2929step0 permutation32 permutation26
    _ = injectiveMoment H node771 := by rfl

def raw2930 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -1, 2, -1], ![1, 0, 1, -2], ![1, 1, -1, -1]]

def raw2930step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 2, -4], ![0, 1, -2, 1], ![-1, 0, -1, 2], ![-1, -1, 1, 1]]

def raw2930step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, -1, 2], ![0, 2, 2, -4], ![1, 0, -2, 1]]

theorem canonical2930 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2930 = injectiveMoment H node1100 := by
  calc
    injectiveMoment H raw2930 = injectiveMoment H raw2930step0 := by
      have heq : raw2930step0 = -raw2930 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2930).symm
    injectiveMoment H raw2930step0 = injectiveMoment H raw2930step1 := by
      have heq : raw2930step1 = (fun i j => raw2930step0 (permutation31 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2930step0 permutation31 permutation15
    _ = injectiveMoment H node1100 := by rfl

def raw2931 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -1, 2, -1], ![1, 1, -1, -1], ![1, 0, 1, -2]]

def raw2931step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 2, -4], ![0, 1, -2, 1], ![-1, -1, 1, 1], ![-1, 0, -1, 2]]

def raw2931step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, -1, 2], ![0, 2, 2, -4], ![1, 0, -2, 1]]

theorem canonical2931 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2931 = injectiveMoment H node1100 := by
  calc
    injectiveMoment H raw2931 = injectiveMoment H raw2931step0 := by
      have heq : raw2931step0 = -raw2931 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2931).symm
    injectiveMoment H raw2931step0 = injectiveMoment H raw2931step1 := by
      have heq : raw2931step1 = (fun i j => raw2931step0 (permutation25 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2931step0 permutation25 permutation15
    _ = injectiveMoment H node1100 := by rfl

def raw2932 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -1, 2, -1], ![1, 2, -1, -2], ![1, -1, 1, -1]]

def raw2932step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 2, -1], ![-2, 2, -1, 1], ![4, -1, -2, -1]]

def raw2932step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 1, -2, 1], ![2, -2, 1, -1], ![-4, 1, 2, 1]]

def raw2932step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, -1, 2], ![1, 1, -2, 0], ![1, 1, 2, -4]]

theorem canonical2932 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2932 = injectiveMoment H node501 := by
  calc
    injectiveMoment H raw2932 = injectiveMoment H raw2932step0 := by
      have heq : raw2932step0 = raw2932.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2932).symm
    injectiveMoment H raw2932step0 = injectiveMoment H raw2932step1 := by
      have heq : raw2932step1 = -raw2932step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2932step0).symm
    injectiveMoment H raw2932step1 = injectiveMoment H raw2932step2 := by
      have heq : raw2932step2 = (fun i j => raw2932step1 (permutation21 i) (permutation20 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2932step1 permutation21 permutation20
    _ = injectiveMoment H node501 := by rfl

def raw2933 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -1, 3, -2], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 1, -1, -1]]

theorem canonical2933 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2933 = injectiveMoment H node1916 := by
  rfl

def raw2934 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -1, 3, -2], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 0, -1]]

def raw2934step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 2, -4], ![0, 1, -3, 2], ![0, -1, 0, 1], ![-1, 0, 1, 0], ![-1, 0, 0, 1]]

def raw2934step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, -1, 1, 0], ![0, 2, 2, -4], ![1, 0, -3, 2]]

theorem canonical2934 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2934 = injectiveMoment H node2751 := by
  calc
    injectiveMoment H raw2934 = injectiveMoment H raw2934step0 := by
      have heq : raw2934step0 = -raw2934 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2934).symm
    injectiveMoment H raw2934step0 = injectiveMoment H raw2934step1 := by
      have heq : raw2934step1 = (fun i j => raw2934step0 (permutation102 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2934step0 permutation102 permutation15
    _ = injectiveMoment H node2751 := by rfl

def raw2935 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -1, 3, -2], ![0, 2, -1, -1], ![1, -1, 0, 0], ![1, 0, 0, -1]]

theorem canonical2935 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2935 = injectiveMoment H node1917 := by
  rfl

def raw2936 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -1, 3, -2], ![0, 2, -1, -1], ![2, -1, 0, -1]]

theorem canonical2936 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2936 = injectiveMoment H node581 := by
  rfl

def raw2937 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -1, 3, -2], ![1, -1, 0, 0], ![1, 2, -1, -2]]

def raw2937step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, -1, 2], ![-2, 3, 0, -1], ![4, -2, 0, -2]]

def raw2937step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 1, 1, -2], ![2, -3, 0, 1], ![-4, 2, 0, 2]]

def raw2937step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, -3, 2], ![0, 2, 2, -4], ![1, -2, 1, 0]]

theorem canonical2937 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2937 = injectiveMoment H node1076 := by
  calc
    injectiveMoment H raw2937 = injectiveMoment H raw2937step0 := by
      have heq : raw2937step0 = raw2937.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2937).symm
    injectiveMoment H raw2937step0 = injectiveMoment H raw2937step1 := by
      have heq : raw2937step1 = -raw2937step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2937step0).symm
    injectiveMoment H raw2937step1 = injectiveMoment H raw2937step2 := by
      have heq : raw2937step2 = (fun i j => raw2937step1 (permutation12 i) (permutation26 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2937step1 permutation12 permutation26
    _ = injectiveMoment H node1076 := by rfl

def raw2938 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -1, 3, -2], ![1, 0, 0, -1], ![1, 1, -1, -1]]

def raw2938step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 0, 1], ![-2, 3, 0, -1], ![4, -2, -1, -1]]

def raw2938step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, -1, 3, -2], ![0, 1, -1, 0], ![1, 1, 0, -2]]

theorem canonical2938 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2938 = injectiveMoment H node898 := by
  calc
    injectiveMoment H raw2938 = injectiveMoment H raw2938step0 := by
      have heq : raw2938step0 = raw2938.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2938).symm
    injectiveMoment H raw2938step0 = injectiveMoment H raw2938step1 := by
      have heq : raw2938step1 = (fun i j => raw2938step0 (permutation32 i) (permutation26 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2938step0 permutation32 permutation26
    _ = injectiveMoment H node898 := by rfl

def raw2939 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -1, 3, -2], ![1, 1, -1, -1], ![1, 0, 0, -1]]

def raw2939step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 1, 0], ![-2, 3, -1, 0], ![4, -2, -1, -1]]

def raw2939step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, -1, 3, -2], ![0, 1, -1, 0], ![1, 1, 0, -2]]

theorem canonical2939 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2939 = injectiveMoment H node898 := by
  calc
    injectiveMoment H raw2939 = injectiveMoment H raw2939step0 := by
      have heq : raw2939step0 = raw2939.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2939).symm
    injectiveMoment H raw2939step0 = injectiveMoment H raw2939step1 := by
      have heq : raw2939step1 = (fun i j => raw2939step0 (permutation32 i) (permutation32 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2939step0 permutation32 permutation32
    _ = injectiveMoment H node898 := by rfl

def raw2940 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 0, 0, 0], ![0, 1, 1, -2], ![2, -1, 1, -2]]

def raw2940step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, 1, -1], ![-2, 0, 1, 1], ![4, 0, -2, -2]]

def raw2940step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![-2, 1, 1], ![4, -2, -2]]

def raw2940step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![1, -1, 0], ![1, 1, -2]]

theorem canonical2940 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2940 = injectiveMoment H node153 := by
  calc
    injectiveMoment H raw2940 = injectiveMoment H raw2940step0 := by
      have heq : raw2940step0 = raw2940.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2940).symm
    injectiveMoment H raw2940step0 = injectiveMoment H raw2940step1 := by
      have hz : ∀ i, raw2940step0 i (permutation15 0) = 0 := by decide +kernel
      have heq : raw2940step1 = (fun i j => raw2940step0 i (permutation15 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw2940step0 permutation15 hz
    injectiveMoment H raw2940step1 = injectiveMoment H raw2940step2 := by
      have heq : raw2940step2 = (fun i j => raw2940step1 (permutation27 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2940step1 permutation27 permutation6
    _ = injectiveMoment H node153 := by rfl

def raw2941 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 0, 1, -1], ![0, -1, 2, -1], ![0, 2, -1, -1], ![2, -1, 0, -1]]

def raw2941step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -1, 2, -1], ![0, 0, 1, -1], ![0, 2, -1, -1], ![2, -1, 0, -1]]

theorem canonical2941 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2941 = injectiveMoment H node1909 := by
  calc
    injectiveMoment H raw2941 = injectiveMoment H raw2941step0 := by
      have heq : raw2941step0 = (fun i j => raw2941 (permutation39 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2941 permutation39 permutation9
    _ = injectiveMoment H node1909 := by rfl

def raw2942 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 0, 1, -1], ![0, 0, 0, 0], ![0, 1, 1, -2], ![2, -1, 0, -1]]

def raw2942step0 : Matrix (Fin 4) (Fin 5) ℤ := ![![-2, 0, 0, 0, 2], ![0, 0, 0, 1, -1], ![-2, 1, 0, 1, 0], ![4, -1, 0, -2, -1]]

def raw2942step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, 1, -1], ![-2, 1, 1, 0], ![4, -1, -2, -1]]

def raw2942step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, 1, 0, -2]]

theorem canonical2942 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2942 = injectiveMoment H node771 := by
  calc
    injectiveMoment H raw2942 = injectiveMoment H raw2942step0 := by
      have heq : raw2942step0 = raw2942.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2942).symm
    injectiveMoment H raw2942step0 = injectiveMoment H raw2942step1 := by
      have hz : ∀ i, raw2942step0 i (permutation80 0) = 0 := by decide +kernel
      have heq : raw2942step1 = (fun i j => raw2942step0 i (permutation80 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw2942step0 permutation80 hz
    injectiveMoment H raw2942step1 = injectiveMoment H raw2942step2 := by
      have heq : raw2942step2 = (fun i j => raw2942step1 (permutation27 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2942step1 permutation27 permutation18
    _ = injectiveMoment H node771 := by rfl

def raw2943 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, -1, 0, -1]]

def raw2943step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 2, -4], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, -1, 0, 1], ![-2, 1, 0, 1]]

def raw2943step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, -1, 0, 1], ![0, 2, 2, -4], ![1, 0, -2, 1]]

theorem canonical2943 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2943 = injectiveMoment H node2749 := by
  calc
    injectiveMoment H raw2943 = injectiveMoment H raw2943step0 := by
      have heq : raw2943step0 = -raw2943 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2943).symm
    injectiveMoment H raw2943step0 = injectiveMoment H raw2943step1 := by
      have heq : raw2943step1 = (fun i j => raw2943step0 (permutation112 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2943step0 permutation112 permutation17
    _ = injectiveMoment H node2749 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
