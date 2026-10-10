import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes4
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes15
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes44
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes45
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes46
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes47
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes48
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes49
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes50
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes52
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes53

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw9888 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-2, -1, 1, 2]]

def raw9888step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -1, 0]]

theorem canonical9888 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9888 = injectiveMoment H node3083 := by
  calc
    injectiveMoment H raw9888 = injectiveMoment H raw9888step0 := by
      have heq : raw9888step0 = (fun i j => raw9888 (permutation308 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9888 permutation308 permutation9
    _ = injectiveMoment H node3083 := by rfl

def raw9889 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-2, -1, 0, 3]]

def raw9889step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, -1, 1, 0], ![0, -1, 0, 1], ![-1, 1, 0, 0], ![-1, 0, 0, 1], ![2, 1, 0, -3]]

def raw9889step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, 0, -1, 0]]

theorem canonical9889 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9889 = injectiveMoment H node3441 := by
  calc
    injectiveMoment H raw9889 = injectiveMoment H raw9889step0 := by
      have heq : raw9889step0 = -raw9889 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9889).symm
    injectiveMoment H raw9889step0 = injectiveMoment H raw9889step1 := by
      have heq : raw9889step1 = (fun i j => raw9889step0 (permutation193 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9889step0 permutation193 permutation21
    _ = injectiveMoment H node3441 := by rfl

def raw9890 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 1, -2], ![-2, -1, -1, 4]]

def raw9890step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 1, 0, -2]]

theorem canonical9890 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9890 = injectiveMoment H node2913 := by
  calc
    injectiveMoment H raw9890 = injectiveMoment H raw9890step0 := by
      have heq : raw9890step0 = (fun i j => raw9890 (permutation337 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9890 permutation337 permutation11
    _ = injectiveMoment H node2913 := by rfl

def raw9891 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0], ![-2, 0, 2, 0], ![1, -2, -1, 2]]

def raw9891step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, -1, 1, 0], ![0, -1, 0, 1], ![-1, 0, 1, 0], ![2, 0, -2, 0], ![-1, 2, 1, -2]]

def raw9891step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 2, 0, -2], ![1, 0, -1, 0], ![1, 0, 0, -1]]

theorem canonical9891 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9891 = injectiveMoment H node3095 := by
  calc
    injectiveMoment H raw9891 = injectiveMoment H raw9891step0 := by
      have heq : raw9891step0 = -raw9891 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9891).symm
    injectiveMoment H raw9891step0 = injectiveMoment H raw9891step1 := by
      have heq : raw9891step1 = (fun i j => raw9891step0 (permutation382 i) (permutation27 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9891step0 permutation382 permutation27
    _ = injectiveMoment H node3095 := by rfl

def raw9892 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, -1, 0, 0], ![-2, -1, 1, 2]]

def raw9892step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -1, 0]]

theorem canonical9892 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9892 = injectiveMoment H node3083 := by
  calc
    injectiveMoment H raw9892 = injectiveMoment H raw9892step0 := by
      have heq : raw9892step0 = (fun i j => raw9892 (permutation309 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9892 permutation309 permutation9
    _ = injectiveMoment H node3083 := by rfl

def raw9893 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 0, -1], ![-2, -2, 1, 3]]

def raw9893step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 0, -1]]

theorem canonical9893 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9893 = injectiveMoment H node2889 := by
  calc
    injectiveMoment H raw9893 = injectiveMoment H raw9893step0 := by
      have heq : raw9893step0 = (fun i j => raw9893 (permutation308 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9893 permutation308 permutation9
    _ = injectiveMoment H node2889 := by rfl

def raw9894 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 1, -2], ![-2, -2, 0, 4]]

def raw9894step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 1, -2]]

theorem canonical9894 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9894 = injectiveMoment H node2879 := by
  calc
    injectiveMoment H raw9894 = injectiveMoment H raw9894step0 := by
      have heq : raw9894step0 = (fun i j => raw9894 (permutation308 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9894 permutation308 permutation9
    _ = injectiveMoment H node2879 := by rfl

def raw9895 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, -1, 0, 0], ![-2, 0, -1, 3], ![0, 1, 2, -3]]

def raw9895step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, -1, -1, 1], ![1, -1, 0, 0]]

theorem canonical9895 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9895 = injectiveMoment H node3147 := by
  calc
    injectiveMoment H raw9895 = injectiveMoment H raw9895step0 := by
      have heq : raw9895step0 = (fun i j => raw9895 (permutation262 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9895 permutation262 permutation9
    _ = injectiveMoment H node3147 := by rfl

def raw9896 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, 0, -1, 0], ![-2, -1, 0, 3], ![0, 1, 2, -3]]

def raw9896step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, -1, -1, 1], ![1, 0, -1, 0]]

theorem canonical9896 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9896 = injectiveMoment H node3015 := by
  calc
    injectiveMoment H raw9896 = injectiveMoment H raw9896step0 := by
      have heq : raw9896step0 = (fun i j => raw9896 (permutation262 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9896 permutation262 permutation9
    _ = injectiveMoment H node3015 := by rfl

def raw9897 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, 0, 0, -1], ![-1, -1, -1, 3], ![-1, 1, 2, -2]]

def raw9897step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 1, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 2, -2], ![1, 0, -1, 0]]

theorem canonical9897 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9897 = injectiveMoment H node3365 := by
  calc
    injectiveMoment H raw9897 = injectiveMoment H raw9897step0 := by
      have heq : raw9897step0 = (fun i j => raw9897 (permutation285 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9897 permutation285 permutation15
    _ = injectiveMoment H node3365 := by rfl

def raw9898 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, -1, -1, 1], ![-2, 0, -1, 3], ![0, 1, 2, -3]]

def raw9898step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, -1, -1, 1], ![1, -1, 0, 0]]

theorem canonical9898 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9898 = injectiveMoment H node3147 := by
  calc
    injectiveMoment H raw9898 = injectiveMoment H raw9898step0 := by
      have heq : raw9898step0 = (fun i j => raw9898 (permutation263 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9898 permutation263 permutation9
    _ = injectiveMoment H node3147 := by rfl

def raw9899 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-2, 0, -2, 4], ![0, 1, 2, -3]]

def raw9899step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, -1, 0, 0], ![1, -1, 0, 0]]

theorem canonical9899 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9899 = injectiveMoment H node3123 := by
  calc
    injectiveMoment H raw9899 = injectiveMoment H raw9899step0 := by
      have heq : raw9899step0 = (fun i j => raw9899 (permutation262 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9899 permutation262 permutation9
    _ = injectiveMoment H node3123 := by rfl

def raw9900 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-2, 0, -1, 3], ![0, 1, 1, -2]]

def raw9900step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 1, 0, -1], ![0, 1, 1, -2], ![1, 0, -1, 0], ![1, 0, -1, 0]]

theorem canonical9900 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9900 = injectiveMoment H node2974 := by
  calc
    injectiveMoment H raw9900 = injectiveMoment H raw9900step0 := by
      have heq : raw9900step0 = (fun i j => raw9900 (permutation279 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9900 permutation279 permutation11
    _ = injectiveMoment H node2974 := by rfl

def raw9901 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, -2, 1], ![-2, -1, 0, 3], ![0, 1, 2, -3]]

def raw9901step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, -1, 0, 0], ![1, 0, -2, 1]]

theorem canonical9901 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9901 = injectiveMoment H node3016 := by
  calc
    injectiveMoment H raw9901 = injectiveMoment H raw9901step0 := by
      have heq : raw9901step0 = (fun i j => raw9901 (permutation262 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9901 permutation262 permutation9
    _ = injectiveMoment H node3016 := by rfl

def raw9902 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-2, -1, -1, 4], ![0, 1, 2, -3]]

def raw9902step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, -1, 0, 0], ![1, 0, -1, 0]]

theorem canonical9902 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9902 = injectiveMoment H node2937 := by
  calc
    injectiveMoment H raw9902 = injectiveMoment H raw9902step0 := by
      have heq : raw9902step0 = (fun i j => raw9902 (permutation262 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9902 permutation262 permutation9
    _ = injectiveMoment H node2937 := by rfl

def raw9903 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-2, -1, 0, 3], ![0, 1, 1, -2]]

def raw9903step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, 0, -1, 0]]

theorem canonical9903 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9903 = injectiveMoment H node3014 := by
  calc
    injectiveMoment H raw9903 = injectiveMoment H raw9903step0 := by
      have heq : raw9903step0 = (fun i j => raw9903 (permutation262 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9903 permutation262 permutation9
    _ = injectiveMoment H node3014 := by rfl

def raw9904 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-1, -1, -1, 3], ![-1, 1, 2, -2]]

def raw9904step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 1, 0, 0], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 2, -2], ![1, 0, -1, 0]]

theorem canonical9904 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9904 = injectiveMoment H node3368 := by
  calc
    injectiveMoment H raw9904 = injectiveMoment H raw9904step0 := by
      have heq : raw9904step0 = (fun i j => raw9904 (permutation285 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9904 permutation285 permutation15
    _ = injectiveMoment H node3368 := by rfl

def raw9905 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-1, -1, -2, 4], ![-1, 1, 2, -2]]

def raw9905step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![-1, 1, 0, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 2, -2], ![1, 0, -1, 0]]

theorem canonical9905 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9905 = injectiveMoment H node3346 := by
  calc
    injectiveMoment H raw9905 = injectiveMoment H raw9905step0 := by
      have heq : raw9905step0 = (fun i j => raw9905 (permutation285 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9905 permutation285 permutation15
    _ = injectiveMoment H node3346 := by rfl

def raw9906 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-1, -1, -1, 3], ![-1, 1, 1, -1]]

def raw9906step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 0, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 1, -1, -1]]

theorem canonical9906 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9906 = injectiveMoment H node3356 := by
  calc
    injectiveMoment H raw9906 = injectiveMoment H raw9906step0 := by
      have heq : raw9906step0 = (fun i j => raw9906 (permutation286 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9906 permutation286 permutation17
    _ = injectiveMoment H node3356 := by rfl

def raw9907 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-1, 1, 1, -1], ![-1, -1, -1, 3]]

def raw9907step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 0, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 1, -1, -1]]

theorem canonical9907 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9907 = injectiveMoment H node3356 := by
  calc
    injectiveMoment H raw9907 = injectiveMoment H raw9907step0 := by
      have heq : raw9907step0 = (fun i j => raw9907 (permutation363 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9907 permutation363 permutation17
    _ = injectiveMoment H node3356 := by rfl

def raw9908 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 0, -1], ![0, -1, 2, -1], ![-2, 1, -2, 3]]

def raw9908step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, -1, 2, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 0, -1]]

theorem canonical9908 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9908 = injectiveMoment H node3232 := by
  calc
    injectiveMoment H raw9908 = injectiveMoment H raw9908step0 := by
      have heq : raw9908step0 = (fun i j => raw9908 (permutation395 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9908 permutation395 permutation9
    _ = injectiveMoment H node3232 := by rfl

def raw9909 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 0, 0, -1], ![-1, 1, 1, -1], ![-1, -2, 0, 3]]

def raw9909step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 0, -1, 0]]

theorem canonical9909 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9909 = injectiveMoment H node3013 := by
  calc
    injectiveMoment H raw9909 = injectiveMoment H raw9909step0 := by
      have heq : raw9909step0 = (fun i j => raw9909 (permutation317 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9909 permutation317 permutation15
    _ = injectiveMoment H node3013 := by rfl

def raw9910 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 0, 0, -1], ![0, -2, 2, 0], ![-2, 1, -1, 2]]

def raw9910step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, -1, 1, 0], ![-1, 0, 1, 0], ![-1, 0, 0, 1], ![0, 2, -2, 0], ![2, -1, 1, -2]]

def raw9910step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 2, 0, -2], ![1, 0, -1, 0], ![1, 0, 0, -1]]

theorem canonical9910 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9910 = injectiveMoment H node3095 := by
  calc
    injectiveMoment H raw9910 = injectiveMoment H raw9910step0 := by
      have heq : raw9910step0 = -raw9910 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9910).symm
    injectiveMoment H raw9910step0 = injectiveMoment H raw9910step1 := by
      have heq : raw9910step1 = (fun i j => raw9910step0 (permutation342 i) (permutation29 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9910step0 permutation342 permutation29
    _ = injectiveMoment H node3095 := by rfl

def raw9911 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, 0, -1], ![-1, 1, 1, -1], ![1, -2, -2, 3]]

def raw9911step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 1, -2], ![1, 0, 1, -2], ![-1, -1, -1, 3]]

def raw9911step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, -1, 1], ![0, 1, 1, -2], ![1, 0, 1, -2]]

theorem canonical9911 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9911 = injectiveMoment H node964 := by
  calc
    injectiveMoment H raw9911 = injectiveMoment H raw9911step0 := by
      have heq : raw9911step0 = raw9911.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw9911).symm
    injectiveMoment H raw9911step0 = injectiveMoment H raw9911step1 := by
      have heq : raw9911step1 = (fun i j => raw9911step0 (permutation27 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9911step0 permutation27 permutation9
    _ = injectiveMoment H node964 := by rfl

def raw9912 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-2, -1, 1, 2]]

def raw9912step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -1, 0]]

theorem canonical9912 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9912 = injectiveMoment H node3083 := by
  calc
    injectiveMoment H raw9912 = injectiveMoment H raw9912step0 := by
      have heq : raw9912step0 = (fun i j => raw9912 (permutation314 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9912 permutation314 permutation9
    _ = injectiveMoment H node3083 := by rfl

def raw9913 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 1, -2], ![-2, -1, -1, 4]]

def raw9913step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 1, 0, -2]]

theorem canonical9913 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9913 = injectiveMoment H node2913 := by
  calc
    injectiveMoment H raw9913 = injectiveMoment H raw9913step0 := by
      have heq : raw9913step0 = (fun i j => raw9913 (permutation357 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9913 permutation357 permutation11
    _ = injectiveMoment H node2913 := by rfl

def raw9914 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, -1, 0], ![1, 0, -1, 0], ![-2, 0, 2, 0], ![1, -2, -1, 2]]

def raw9914step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, -1, 0, 1], ![0, -1, 1, 0], ![-1, 0, 1, 0], ![2, 0, -2, 0], ![-1, 2, 1, -2]]

def raw9914step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 2, 0, -2], ![1, 0, -1, 0], ![1, 0, 0, -1]]

theorem canonical9914 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9914 = injectiveMoment H node3095 := by
  calc
    injectiveMoment H raw9914 = injectiveMoment H raw9914step0 := by
      have heq : raw9914step0 = -raw9914 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9914).symm
    injectiveMoment H raw9914step0 = injectiveMoment H raw9914step1 := by
      have heq : raw9914step1 = (fun i j => raw9914step0 (permutation388 i) (permutation27 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9914step0 permutation388 permutation27
    _ = injectiveMoment H node3095 := by rfl

def raw9915 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 0, 0, -1], ![-2, -2, 1, 3]]

def raw9915step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 0, -1]]

theorem canonical9915 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9915 = injectiveMoment H node2889 := by
  calc
    injectiveMoment H raw9915 = injectiveMoment H raw9915step0 := by
      have heq : raw9915step0 = (fun i j => raw9915 (permutation314 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9915 permutation314 permutation9
    _ = injectiveMoment H node2889 := by rfl

def raw9916 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 0, 1, -2], ![-2, -2, 0, 4]]

def raw9916step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 1, -2]]

theorem canonical9916 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9916 = injectiveMoment H node2879 := by
  calc
    injectiveMoment H raw9916 = injectiveMoment H raw9916step0 := by
      have heq : raw9916step0 = (fun i j => raw9916 (permutation314 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9916 permutation314 permutation9
    _ = injectiveMoment H node2879 := by rfl

def raw9917 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![0, -2, -1, 3]]

def raw9917step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![-2, -1, 3]]

def raw9917step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1]]

theorem canonical9917 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9917 = injectiveMoment H node271 := by
  calc
    injectiveMoment H raw9917 = injectiveMoment H raw9917step0 := by
      have hz : ∀ i, raw9917 i (permutation9 0) = 0 := by decide +kernel
      have heq : raw9917step0 = (fun i j => raw9917 i (permutation9 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw9917 permutation9 hz
    injectiveMoment H raw9917step0 = injectiveMoment H raw9917step1 := by
      have heq : raw9917step1 = (fun i j => raw9917step0 (permutation30 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9917step0 permutation30 permutation5
    _ = injectiveMoment H node271 := by rfl

def raw9918 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 0, -1, 0], ![-2, -1, 1, 2]]

def raw9918step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 0, -1, 0]]

theorem canonical9918 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9918 = injectiveMoment H node3085 := by
  calc
    injectiveMoment H raw9918 = injectiveMoment H raw9918step0 := by
      have heq : raw9918step0 = (fun i j => raw9918 (permutation308 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9918 permutation308 permutation9
    _ = injectiveMoment H node3085 := by rfl

def raw9919 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 0, 1, -2], ![-2, -1, -1, 4]]

def raw9919step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 1, 0, -2]]

theorem canonical9919 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9919 = injectiveMoment H node2927 := by
  calc
    injectiveMoment H raw9919 = injectiveMoment H raw9919step0 := by
      have heq : raw9919step0 = (fun i j => raw9919 (permutation337 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9919 permutation337 permutation11
    _ = injectiveMoment H node2927 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
