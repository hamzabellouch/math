import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes12
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes14
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes22
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes23
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes29
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes30
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes40
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes41
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes42
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes43
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes44

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw2944 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -1, -1], ![2, -2, 1, -1]]

theorem canonical2944 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2944 = injectiveMoment H node1918 := by
  rfl

def raw2945 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, 0, -2], ![2, -2, 0, 0]]

def raw2945step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 2, -2], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, -2, 0]]

theorem canonical2945 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2945 = injectiveMoment H node1479 := by
  calc
    injectiveMoment H raw2945 = injectiveMoment H raw2945step0 := by
      have heq : raw2945step0 = (fun i j => raw2945 (permutation45 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2945 permutation45 permutation11
    _ = injectiveMoment H node1479 := by rfl

def raw2946 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, 1, -1], ![1, 1, -1, -1]]

def raw2946step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 2, -4], ![0, 0, -1, 1], ![0, 0, -1, 1], ![-1, 1, -1, 1], ![-1, -1, 1, 1]]

def raw2946step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, -1, -1, 1]]

theorem canonical2946 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2946 = injectiveMoment H node2641 := by
  calc
    injectiveMoment H raw2946 = injectiveMoment H raw2946step0 := by
      have heq : raw2946step0 = -raw2946 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2946).symm
    injectiveMoment H raw2946step0 = injectiveMoment H raw2946step1 := by
      have heq : raw2946step1 = (fun i j => raw2946step0 (permutation135 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2946step0 permutation135 permutation15
    _ = injectiveMoment H node2641 := by rfl

def raw2947 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 0, 1, -1], ![0, 0, 2, -2], ![0, 2, -1, -1], ![2, -2, 0, 0]]

theorem canonical2947 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2947 = injectiveMoment H node1919 := by
  rfl

def raw2948 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 0, 1, -1], ![0, 0, 2, -2], ![1, -1, 0, 0], ![1, 1, -1, -1]]

def raw2948step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 2, -4], ![0, 0, -1, 1], ![0, 0, -2, 2], ![-1, 1, 0, 0], ![-1, -1, 1, 1]]

def raw2948step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -2, 2], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, -1, 0, 0]]

theorem canonical2948 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2948 = injectiveMoment H node2634 := by
  calc
    injectiveMoment H raw2948 = injectiveMoment H raw2948step0 := by
      have heq : raw2948step0 = -raw2948 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2948).symm
    injectiveMoment H raw2948step0 = injectiveMoment H raw2948step1 := by
      have heq : raw2948step1 = (fun i j => raw2948step0 (permutation141 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2948step0 permutation141 permutation15
    _ = injectiveMoment H node2634 := by rfl

def raw2949 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 0, 2, -2], ![2, -1, 0, -1]]

def raw2949step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 2, -4], ![0, 0, -1, 1], ![0, -1, 1, 0], ![0, 0, -2, 2], ![-2, 1, 0, 1]]

def raw2949step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, 0, -2, 2], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, -2, 0, 1]]

theorem canonical2949 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2949 = injectiveMoment H node2818 := by
  calc
    injectiveMoment H raw2949 = injectiveMoment H raw2949step0 := by
      have heq : raw2949step0 = -raw2949 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2949).symm
    injectiveMoment H raw2949step0 = injectiveMoment H raw2949step1 := by
      have heq : raw2949step1 = (fun i j => raw2949step0 (permutation94 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2949step0 permutation94 permutation15
    _ = injectiveMoment H node2818 := by rfl

def raw2950 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, -2, 2, -2]]

theorem canonical2950 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2950 = injectiveMoment H node1920 := by
  rfl

def raw2951 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![2, -2, 1, -1]]

theorem canonical2951 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2951 = injectiveMoment H node1921 := by
  rfl

def raw2952 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 2, -3], ![2, -2, 0, 0]]

theorem canonical2952 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2952 = injectiveMoment H node1922 := by
  rfl

def raw2953 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, -2, 1, -1]]

def raw2953step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, 1, -2, -1]]

theorem canonical2953 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2953 = injectiveMoment H node1459 := by
  calc
    injectiveMoment H raw2953 = injectiveMoment H raw2953step0 := by
      have heq : raw2953step0 = (fun i j => raw2953 (permutation41 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2953 permutation41 permutation11
    _ = injectiveMoment H node1459 := by rfl

def raw2954 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 1, -2], ![2, -2, 0, 0]]

def raw2954step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 1, -2], ![2, 0, -2, 0]]

theorem canonical2954 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2954 = injectiveMoment H node1471 := by
  calc
    injectiveMoment H raw2954 = injectiveMoment H raw2954step0 := by
      have heq : raw2954step0 = (fun i j => raw2954 (permutation39 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2954 permutation39 permutation11
    _ = injectiveMoment H node1471 := by rfl

def raw2955 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -2, 2, -1], ![1, 1, -1, -1]]

theorem canonical2955 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2955 = injectiveMoment H node1923 := by
  rfl

def raw2956 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 1, -2]]

def raw2956step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 2, -4], ![0, 0, -1, 1], ![0, -1, 0, 1], ![-1, 1, 0, 0], ![-1, 0, -1, 2]]

def raw2956step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, -1, 2], ![0, -1, 0, 1], ![0, 2, 2, -4], ![1, 0, -1, 0]]

theorem canonical2956 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2956 = injectiveMoment H node2747 := by
  calc
    injectiveMoment H raw2956 = injectiveMoment H raw2956step0 := by
      have heq : raw2956step0 = -raw2956 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2956).symm
    injectiveMoment H raw2956step0 = injectiveMoment H raw2956step1 := by
      have heq : raw2956step1 = (fun i j => raw2956step0 (permutation100 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2956step0 permutation100 permutation17
    _ = injectiveMoment H node2747 := by rfl

def raw2957 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 0, 0, -1]]

def raw2957step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 2, -4], ![0, 0, -1, 1], ![0, -1, 0, 1], ![-1, 1, -1, 1], ![-1, 0, 0, 1]]

def raw2957step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, -1, -1, 1]]

theorem canonical2957 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2957 = injectiveMoment H node2755 := by
  calc
    injectiveMoment H raw2957 = injectiveMoment H raw2957step0 := by
      have heq : raw2957step0 = -raw2957 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2957).symm
    injectiveMoment H raw2957step0 = injectiveMoment H raw2957step1 := by
      have heq : raw2957step1 = (fun i j => raw2957step0 (permutation100 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2957step0 permutation100 permutation15
    _ = injectiveMoment H node2755 := by rfl

def raw2958 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 2, -2], ![1, 0, -1, 0]]

def raw2958step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 2, -4], ![0, 0, -1, 1], ![0, -1, 0, 1], ![-1, 1, -2, 2], ![-1, 0, 1, 0]]

def raw2958step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, -1, -2, 2]]

theorem canonical2958 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2958 = injectiveMoment H node2768 := by
  calc
    injectiveMoment H raw2958 = injectiveMoment H raw2958step0 := by
      have heq : raw2958step0 = -raw2958 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2958).symm
    injectiveMoment H raw2958step0 = injectiveMoment H raw2958step1 := by
      have heq : raw2958step1 = (fun i j => raw2958step0 (permutation100 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2958step0 permutation100 permutation15
    _ = injectiveMoment H node2768 := by rfl

def raw2959 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, -1, 1, -2]]

def raw2959step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, 1, -1], ![-2, 1, 0, 1], ![4, -1, -1, -2]]

def raw2959step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, 0, 1, -2]]

theorem canonical2959 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2959 = injectiveMoment H node914 := by
  calc
    injectiveMoment H raw2959 = injectiveMoment H raw2959step0 := by
      have heq : raw2959step0 = raw2959.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2959).symm
    injectiveMoment H raw2959step0 = injectiveMoment H raw2959step1 := by
      have heq : raw2959step1 = (fun i j => raw2959step0 (permutation27 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2959step0 permutation27 permutation18
    _ = injectiveMoment H node914 := by rfl

def raw2960 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, -2, 1, 0], ![1, 1, -1, -1]]

theorem canonical2960 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2960 = injectiveMoment H node1924 := by
  rfl

def raw2961 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw2961step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 2, -4], ![0, 0, -1, 1], ![0, -1, -1, 2], ![-1, 1, 0, 0], ![-1, 0, 0, 1]]

def raw2961step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, 0, -1, 0]]

theorem canonical2961 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2961 = injectiveMoment H node2578 := by
  calc
    injectiveMoment H raw2961 = injectiveMoment H raw2961step0 := by
      have heq : raw2961step0 = -raw2961 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2961).symm
    injectiveMoment H raw2961step0 = injectiveMoment H raw2961step1 := by
      have heq : raw2961step1 = (fun i j => raw2961step0 (permutation90 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2961step0 permutation90 permutation17
    _ = injectiveMoment H node2578 := by rfl

def raw2962 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, -1, 1, -1], ![1, 0, -1, 0]]

def raw2962step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 2, -4], ![0, 0, -1, 1], ![0, -1, -1, 2], ![-1, 1, -1, 1], ![-1, 0, 1, 0]]

def raw2962step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, -1, -1, 1]]

theorem canonical2962 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2962 = injectiveMoment H node2723 := by
  calc
    injectiveMoment H raw2962 = injectiveMoment H raw2962step0 := by
      have heq : raw2962step0 = -raw2962 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2962).symm
    injectiveMoment H raw2962step0 = injectiveMoment H raw2962step1 := by
      have heq : raw2962step1 = (fun i j => raw2962step0 (permutation100 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2962step0 permutation100 permutation15
    _ = injectiveMoment H node2723 := by rfl

def raw2963 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 0, 1, -1], ![0, 1, 1, -2], ![2, -1, 0, -1]]

def raw2963step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, 1, -1], ![-2, 1, 1, 0], ![4, -1, -2, -1]]

def raw2963step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, 1, 0, -2]]

theorem canonical2963 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2963 = injectiveMoment H node771 := by
  calc
    injectiveMoment H raw2963 = injectiveMoment H raw2963step0 := by
      have heq : raw2963step0 = raw2963.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2963).symm
    injectiveMoment H raw2963step0 = injectiveMoment H raw2963step1 := by
      have heq : raw2963step1 = (fun i j => raw2963step0 (permutation27 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2963step0 permutation27 permutation18
    _ = injectiveMoment H node771 := by rfl

def raw2964 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, -2, 1, 0], ![1, 0, 1, -2]]

theorem canonical2964 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2964 = injectiveMoment H node1925 := by
  rfl

def raw2965 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, -2, 2, -1], ![1, 0, 0, -1]]

theorem canonical2965 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2965 = injectiveMoment H node1926 := by
  rfl

def raw2966 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, -1, 0, 0], ![1, -1, 2, -2]]

theorem canonical2966 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2966 = injectiveMoment H node1927 := by
  rfl

def raw2967 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, -1, 1, -1], ![1, -1, 1, -1]]

theorem canonical2967 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2967 = injectiveMoment H node1928 := by
  rfl

def raw2968 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 0, 1, -1], ![0, 2, -1, -1], ![2, -2, 2, -2]]

def raw2968step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, 2, -2], ![-2, 1, -1, 2], ![4, -1, -1, -2]]

def raw2968step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 2, -2], ![0, 2, -2, 0], ![1, -1, 2, -2]]

theorem canonical2968 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2968 = injectiveMoment H node916 := by
  calc
    injectiveMoment H raw2968 = injectiveMoment H raw2968step0 := by
      have heq : raw2968step0 = raw2968.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2968).symm
    injectiveMoment H raw2968step0 = injectiveMoment H raw2968step1 := by
      have heq : raw2968step1 = (fun i j => raw2968step0 (permutation27 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2968step0 permutation27 permutation18
    _ = injectiveMoment H node916 := by rfl

def raw2969 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -2, 2, -1], ![1, 0, -1, 0]]

theorem canonical2969 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2969 = injectiveMoment H node1929 := by
  rfl

def raw2970 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -1, 0, 0], ![1, -1, 1, -1]]

def raw2970step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 1, -1, -1]]

theorem canonical2970 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2970 = injectiveMoment H node1478 := by
  calc
    injectiveMoment H raw2970 = injectiveMoment H raw2970step0 := by
      have heq : raw2970step0 = (fun i j => raw2970 (permutation41 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2970 permutation41 permutation21
    _ = injectiveMoment H node1478 := by rfl

def raw2971 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -1, 1, -1], ![1, -1, 0, 0]]

def raw2971step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 1, -1, -1]]

theorem canonical2971 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2971 = injectiveMoment H node1478 := by
  calc
    injectiveMoment H raw2971 = injectiveMoment H raw2971step0 := by
      have heq : raw2971step0 = (fun i j => raw2971 (permutation43 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2971 permutation43 permutation21
    _ = injectiveMoment H node1478 := by rfl

def raw2972 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 0, 1, -1], ![0, 2, 0, -2], ![2, -2, 1, -1]]

def raw2972step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, 2, -2], ![-2, 1, 0, 1], ![4, -1, -2, -1]]

def raw2972step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 2, -2], ![0, 2, -2, 0], ![1, 0, 1, -2]]

theorem canonical2972 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2972 = injectiveMoment H node773 := by
  calc
    injectiveMoment H raw2972 = injectiveMoment H raw2972step0 := by
      have heq : raw2972step0 = raw2972.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2972).symm
    injectiveMoment H raw2972step0 = injectiveMoment H raw2972step1 := by
      have heq : raw2972step1 = (fun i j => raw2972step0 (permutation27 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2972step0 permutation27 permutation18
    _ = injectiveMoment H node773 := by rfl

def raw2973 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 0, 1, -1], ![1, -1, 2, -2], ![1, 1, -1, -1]]

def raw2973step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, -1, 1], ![-2, 1, 2, -1], ![4, -1, -2, -1]]

def raw2973step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, -1, 2, -2]]

theorem canonical2973 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2973 = injectiveMoment H node921 := by
  calc
    injectiveMoment H raw2973 = injectiveMoment H raw2973step0 := by
      have heq : raw2973step0 = raw2973.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2973).symm
    injectiveMoment H raw2973step0 = injectiveMoment H raw2973step1 := by
      have heq : raw2973step1 = (fun i j => raw2973step0 (permutation29 i) (permutation20 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2973step0 permutation29 permutation20
    _ = injectiveMoment H node921 := by rfl

def raw2974 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 0, 2, -2], ![0, 0, 1, -1], ![0, 2, -1, -1], ![2, -2, 0, 0]]

def raw2974step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 0, 1, -1], ![0, 0, 2, -2], ![0, 2, -1, -1], ![2, -2, 0, 0]]

theorem canonical2974 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2974 = injectiveMoment H node1919 := by
  calc
    injectiveMoment H raw2974 = injectiveMoment H raw2974step0 := by
      have heq : raw2974step0 = (fun i j => raw2974 (permutation39 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2974 permutation39 permutation9
    _ = injectiveMoment H node1919 := by rfl

def raw2975 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, -2, 1, -1]]

theorem canonical2975 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2975 = injectiveMoment H node1930 := by
  rfl

end MUB6.Certificate.PairSemantics

end OAI
