import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes6
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes7
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes8
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes15
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes20
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes31
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes43
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes44

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw3296 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 0, 2], ![0, 1, 3, -4], ![2, 1, -3, 0]]

def raw3296step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 1, 1], ![0, 0, 3, -3], ![2, 2, -4, 0]]

def raw3296step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 2, -1, -1], ![0, 0, -3, 3], ![-2, -2, 4, 0]]

def raw3296step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 3, -3], ![0, 2, -2, 0], ![2, 0, -1, -1]]

theorem canonical3296 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3296 = injectiveMoment H node399 := by
  calc
    injectiveMoment H raw3296 = injectiveMoment H raw3296step0 := by
      have heq : raw3296step0 = raw3296.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3296).symm
    injectiveMoment H raw3296step0 = injectiveMoment H raw3296step1 := by
      have heq : raw3296step1 = -raw3296step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3296step0).symm
    injectiveMoment H raw3296step1 = injectiveMoment H raw3296step2 := by
      have heq : raw3296step2 = (fun i j => raw3296step1 (permutation31 i) (permutation16 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3296step1 permutation31 permutation16
    _ = injectiveMoment H node399 := by rfl

def raw3297 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 0, 2], ![0, 2, -2, 0], ![1, 0, -1, 0], ![1, 0, 3, -4]]

def raw3297step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 0, 2], ![0, 1, -1, 0], ![0, 1, 3, -4], ![2, 0, -2, 0]]

theorem canonical3297 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3297 = injectiveMoment H node1988 := by
  calc
    injectiveMoment H raw3297 = injectiveMoment H raw3297step0 := by
      have heq : raw3297step0 = (fun i j => raw3297 (permutation60 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3297 permutation60 permutation15
    _ = injectiveMoment H node1988 := by rfl

def raw3298 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 0, 2], ![0, 2, 2, -4], ![2, 0, -2, 0]]

def raw3298step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 2, 0, -2], ![0, -2, -2, 4], ![-2, 0, 2, 0]]

def raw3298step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 2, -2], ![0, 2, -2, 0], ![2, 0, 0, -2]]

theorem canonical3298 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3298 = injectiveMoment H node395 := by
  calc
    injectiveMoment H raw3298 = injectiveMoment H raw3298step0 := by
      have heq : raw3298step0 = -raw3298 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3298).symm
    injectiveMoment H raw3298step0 = injectiveMoment H raw3298step1 := by
      have heq : raw3298step1 = (fun i j => raw3298step0 (permutation22 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3298step0 permutation22 permutation17
    _ = injectiveMoment H node395 := by rfl

def raw3299 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 0, 2], ![1, 0, 3, -4], ![1, 2, -3, 0]]

def raw3299step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -2, 0, 2], ![0, 0, 3, -3], ![2, 2, -4, 0]]

def raw3299step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 2, 0, -2], ![0, 0, -3, 3], ![-2, -2, 4, 0]]

def raw3299step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 3, -3], ![0, 2, -2, 0], ![2, 0, -1, -1]]

theorem canonical3299 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3299 = injectiveMoment H node399 := by
  calc
    injectiveMoment H raw3299 = injectiveMoment H raw3299step0 := by
      have heq : raw3299step0 = raw3299.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3299).symm
    injectiveMoment H raw3299step0 = injectiveMoment H raw3299step1 := by
      have heq : raw3299step1 = -raw3299step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3299step0).symm
    injectiveMoment H raw3299step1 = injectiveMoment H raw3299step2 := by
      have heq : raw3299step2 = (fun i j => raw3299step1 (permutation32 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3299step1 permutation32 permutation10
    _ = injectiveMoment H node399 := by rfl

def raw3300 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 0, 2], ![1, 1, -1, -1], ![1, 1, 1, -3]]

def raw3300step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 2, 0, -2], ![-1, -1, 1, 1], ![-1, -1, -1, 3]]

def raw3300step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 2, -2], ![0, 2, 0, -2], ![1, -1, -1, 1]]

theorem canonical3300 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3300 = injectiveMoment H node976 := by
  calc
    injectiveMoment H raw3300 = injectiveMoment H raw3300step0 := by
      have heq : raw3300step0 = -raw3300 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3300).symm
    injectiveMoment H raw3300step0 = injectiveMoment H raw3300step1 := by
      have heq : raw3300step1 = (fun i j => raw3300step0 (permutation29 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3300step0 permutation29 permutation21
    _ = injectiveMoment H node976 := by rfl

def raw3301 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 0, 2], ![1, 1, 2, -4], ![1, 1, -2, 0]]

def raw3301step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -2, 1, 1], ![0, 0, 2, -2], ![2, 2, -4, 0]]

def raw3301step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 2, -1, -1], ![0, 0, -2, 2], ![-2, -2, 4, 0]]

def raw3301step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 2, -2], ![0, 2, -1, -1], ![2, 0, -1, -1]]

theorem canonical3301 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3301 = injectiveMoment H node396 := by
  calc
    injectiveMoment H raw3301 = injectiveMoment H raw3301step0 := by
      have heq : raw3301step0 = raw3301.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3301).symm
    injectiveMoment H raw3301step0 = injectiveMoment H raw3301step1 := by
      have heq : raw3301step1 = -raw3301step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3301step0).symm
    injectiveMoment H raw3301step1 = injectiveMoment H raw3301step2 := by
      have heq : raw3301step2 = (fun i j => raw3301step1 (permutation32 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3301step1 permutation32 permutation10
    _ = injectiveMoment H node396 := by rfl

def raw3302 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 1, 1], ![0, 1, -2, 1], ![1, 0, -1, 0], ![1, 1, 2, -4]]

theorem canonical3302 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3302 = injectiveMoment H node1991 := by
  rfl

def raw3303 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 1, 1], ![0, 1, -2, 1], ![2, 1, 1, -4]]

def raw3303step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 2, -1, -1], ![0, -1, 2, -1], ![-2, -1, -1, 4]]

def raw3303step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 2, -1], ![0, 2, -1, -1], ![2, 0, 0, -2]]

theorem canonical3303 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3303 = injectiveMoment H node449 := by
  calc
    injectiveMoment H raw3303 = injectiveMoment H raw3303step0 := by
      have heq : raw3303step0 = -raw3303 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3303).symm
    injectiveMoment H raw3303step0 = injectiveMoment H raw3303step1 := by
      have heq : raw3303step1 = (fun i j => raw3303step0 (permutation32 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3303step0 permutation32 permutation9
    _ = injectiveMoment H node449 := by rfl

def raw3304 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 1, 1], ![0, 1, -1, 0], ![1, 0, -2, 1], ![1, 1, 2, -4]]

theorem canonical3304 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3304 = injectiveMoment H node1992 := by
  rfl

def raw3305 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 1, 1], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 1, 1, -3]]

theorem canonical3305 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3305 = injectiveMoment H node1993 := by
  rfl

def raw3306 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 1, 1], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 1, 0, -2]]

def raw3306step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -2, 0, 2], ![0, 1, 0, -1], ![0, 1, 1, -2], ![1, 0, -2, 1]]

theorem canonical3306 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3306 = injectiveMoment H node2806 := by
  calc
    injectiveMoment H raw3306 = injectiveMoment H raw3306step0 := by
      have heq : raw3306step0 = (fun i j => raw3306 (permutation83 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3306 permutation83 permutation21
    _ = injectiveMoment H node2806 := by rfl

def raw3307 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 1, 1], ![0, 1, -1, 0], ![1, 0, 1, -2], ![1, 1, -1, -1]]

theorem canonical3307 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3307 = injectiveMoment H node1994 := by
  rfl

def raw3308 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 1, 1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 1, -1, -1]]

def raw3308step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 2, -1, -1], ![0, -1, 0, 1], ![-1, 0, 0, 1], ![-1, -1, 1, 1]]

def raw3308step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 2, 0, -2], ![1, -1, -1, 1]]

theorem canonical3308 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3308 = injectiveMoment H node2828 := by
  calc
    injectiveMoment H raw3308 = injectiveMoment H raw3308step0 := by
      have heq : raw3308step0 = -raw3308 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3308).symm
    injectiveMoment H raw3308step0 = injectiveMoment H raw3308step1 := by
      have heq : raw3308step1 = (fun i j => raw3308step0 (permutation70 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3308step0 permutation70 permutation21
    _ = injectiveMoment H node2828 := by rfl

def raw3309 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 1, 1], ![0, 1, 0, -1], ![1, 0, 1, -2], ![1, 1, -2, 0]]

theorem canonical3309 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3309 = injectiveMoment H node1995 := by
  rfl

def raw3310 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 1, 1], ![0, 1, 1, -2], ![1, 0, 0, -1], ![1, 1, -2, 0]]

theorem canonical3310 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3310 = injectiveMoment H node1996 := by
  rfl

def raw3311 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 1, 1], ![0, 1, 1, -2], ![2, 1, -2, -1]]

def raw3311step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 2, -1, -1], ![0, -1, -1, 2], ![-2, -1, 2, 1]]

def raw3311step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, -1, -1, 2], ![0, 2, -1, -1], ![2, 0, 0, -2]]

theorem canonical3311 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3311 = injectiveMoment H node520 := by
  calc
    injectiveMoment H raw3311 = injectiveMoment H raw3311step0 := by
      have heq : raw3311step0 = -raw3311 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3311).symm
    injectiveMoment H raw3311step0 = injectiveMoment H raw3311step1 := by
      have heq : raw3311step1 = (fun i j => raw3311step0 (permutation32 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3311step0 permutation32 permutation9
    _ = injectiveMoment H node520 := by rfl

def raw3312 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 1, 1], ![0, 2, -2, 0], ![1, 0, 0, -1], ![1, 0, 1, -2]]

theorem canonical3312 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3312 = injectiveMoment H node1997 := by
  rfl

def raw3313 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 1, 1], ![0, 2, -2, 0], ![1, 0, 1, -2], ![1, 0, 0, -1]]

def raw3313step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 1, 1], ![0, 2, -2, 0], ![1, 0, 0, -1], ![1, 0, 1, -2]]

theorem canonical3313 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3313 = injectiveMoment H node1997 := by
  calc
    injectiveMoment H raw3313 = injectiveMoment H raw3313step0 := by
      have heq : raw3313step0 = (fun i j => raw3313 (permutation34 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3313 permutation34 permutation9
    _ = injectiveMoment H node1997 := by rfl

def raw3314 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 1, 1], ![0, 2, -2, 0], ![2, 0, 1, -3]]

def raw3314step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 2, -1, -1], ![0, -2, 2, 0], ![-2, 0, -1, 3]]

def raw3314step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![0, 2, -2, 0], ![2, 0, 0, -2]]

theorem canonical3314 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3314 = injectiveMoment H node472 := by
  calc
    injectiveMoment H raw3314 = injectiveMoment H raw3314step0 := by
      have heq : raw3314step0 = -raw3314 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3314).symm
    injectiveMoment H raw3314step0 = injectiveMoment H raw3314step1 := by
      have heq : raw3314step1 = (fun i j => raw3314step0 (permutation30 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3314step0 permutation30 permutation11
    _ = injectiveMoment H node472 := by rfl

def raw3315 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 1, 1], ![0, 2, -1, -1], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def raw3315step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -2, 0, 2], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -2, 1]]

theorem canonical3315 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3315 = injectiveMoment H node2824 := by
  calc
    injectiveMoment H raw3315 = injectiveMoment H raw3315step0 := by
      have heq : raw3315step0 = (fun i j => raw3315 (permutation83 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3315 permutation83 permutation21
    _ = injectiveMoment H node2824 := by rfl

def raw3316 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 1, 1], ![1, 0, -2, 1], ![1, 2, 1, -4]]

def raw3316step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 2, -1, -1], ![-1, 0, 2, -1], ![-1, -2, -1, 4]]

def raw3316step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 2, -1], ![0, 2, 0, -2], ![2, 0, -1, -1]]

theorem canonical3316 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3316 = injectiveMoment H node450 := by
  calc
    injectiveMoment H raw3316 = injectiveMoment H raw3316step0 := by
      have heq : raw3316step0 = -raw3316 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3316).symm
    injectiveMoment H raw3316step0 = injectiveMoment H raw3316step1 := by
      have heq : raw3316step1 = (fun i j => raw3316step0 (permutation31 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3316step0 permutation31 permutation15
    _ = injectiveMoment H node450 := by rfl

def raw3317 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 1, 1], ![1, 0, -1, 0], ![1, 2, 0, -3]]

def raw3317step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, 0, -2, 2], ![0, 2, 1, -3], ![1, -2, 0, 1]]

theorem canonical3317 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3317 = injectiveMoment H node1301 := by
  calc
    injectiveMoment H raw3317 = injectiveMoment H raw3317step0 := by
      have heq : raw3317step0 = (fun i j => raw3317 (permutation22 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3317 permutation22 permutation23
    _ = injectiveMoment H node1301 := by rfl

def raw3318 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 1, 1], ![1, 0, 1, -2], ![1, 2, -2, -1]]

def raw3318step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 2, -1, -1], ![-1, 0, -1, 2], ![-1, -2, 2, 1]]

def raw3318step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, -1, -1, 2], ![0, 2, 0, -2], ![2, 0, -1, -1]]

theorem canonical3318 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3318 = injectiveMoment H node521 := by
  calc
    injectiveMoment H raw3318 = injectiveMoment H raw3318step0 := by
      have heq : raw3318step0 = -raw3318 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3318).symm
    injectiveMoment H raw3318step0 = injectiveMoment H raw3318step1 := by
      have heq : raw3318step1 = (fun i j => raw3318step0 (permutation31 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3318step0 permutation31 permutation15
    _ = injectiveMoment H node521 := by rfl

def raw3319 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 1, 1], ![1, 1, -3, 1], ![1, 1, 2, -4]]

def raw3319step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -2, 1, 1], ![0, 1, -3, 2], ![2, 1, 1, -4]]

def raw3319step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 2, -1, -1], ![0, -1, 3, -2], ![-2, -1, -1, 4]]

def raw3319step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 3, -2], ![0, 2, -1, -1], ![2, 0, -1, -1]]

theorem canonical3319 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3319 = injectiveMoment H node456 := by
  calc
    injectiveMoment H raw3319 = injectiveMoment H raw3319step0 := by
      have heq : raw3319step0 = raw3319.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3319).symm
    injectiveMoment H raw3319step0 = injectiveMoment H raw3319step1 := by
      have heq : raw3319step1 = -raw3319step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3319step0).symm
    injectiveMoment H raw3319step1 = injectiveMoment H raw3319step2 := by
      have heq : raw3319step2 = (fun i j => raw3319step1 (permutation32 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3319step1 permutation32 permutation9
    _ = injectiveMoment H node456 := by rfl

def raw3320 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 1, 1], ![1, 1, -2, 0], ![1, 1, 1, -3]]

def raw3320step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -2, 1, 1], ![0, 1, -2, 1], ![2, 1, 0, -3]]

def raw3320step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 2, -1, -1], ![0, -1, 2, -1], ![-2, -1, 0, 3]]

def raw3320step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![0, 2, -1, -1], ![2, 0, -1, -1]]

theorem canonical3320 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3320 = injectiveMoment H node473 := by
  calc
    injectiveMoment H raw3320 = injectiveMoment H raw3320step0 := by
      have heq : raw3320step0 = raw3320.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3320).symm
    injectiveMoment H raw3320step0 = injectiveMoment H raw3320step1 := by
      have heq : raw3320step1 = -raw3320step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3320step0).symm
    injectiveMoment H raw3320step1 = injectiveMoment H raw3320step2 := by
      have heq : raw3320step2 = (fun i j => raw3320step1 (permutation32 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3320step1 permutation32 permutation9
    _ = injectiveMoment H node473 := by rfl

def raw3321 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 1, 1], ![1, 1, -1, -1], ![1, 1, 0, -2]]

def raw3321step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 2, -1, -1], ![-1, -1, 1, 1], ![-1, -1, 0, 2]]

def raw3321step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -1, -1, 2], ![0, 2, 0, -2], ![1, -1, -1, 1]]

theorem canonical3321 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3321 = injectiveMoment H node1309 := by
  calc
    injectiveMoment H raw3321 = injectiveMoment H raw3321step0 := by
      have heq : raw3321step0 = -raw3321 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3321).symm
    injectiveMoment H raw3321step0 = injectiveMoment H raw3321step1 := by
      have heq : raw3321step1 = (fun i j => raw3321step0 (permutation19 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3321step0 permutation19 permutation21
    _ = injectiveMoment H node1309 := by rfl

def raw3322 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 1, 1], ![1, 1, 0, -2], ![1, 1, -1, -1]]

def raw3322step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 2, -1, -1], ![-1, -1, 0, 2], ![-1, -1, 1, 1]]

def raw3322step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -1, -1, 2], ![0, 2, 0, -2], ![1, -1, -1, 1]]

theorem canonical3322 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3322 = injectiveMoment H node1309 := by
  calc
    injectiveMoment H raw3322 = injectiveMoment H raw3322step0 := by
      have heq : raw3322step0 = -raw3322 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3322).symm
    injectiveMoment H raw3322step0 = injectiveMoment H raw3322step1 := by
      have heq : raw3322step1 = (fun i j => raw3322step0 (permutation17 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3322step0 permutation17 permutation21
    _ = injectiveMoment H node1309 := by rfl

def raw3323 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 1, 1], ![1, 1, 1, -3], ![1, 1, -2, 0]]

def raw3323step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -2, 1, 1], ![0, 1, 1, -2], ![2, 1, -3, 0]]

def raw3323step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 2, -1, -1], ![0, -1, -1, 2], ![-2, -1, 3, 0]]

def raw3323step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![0, 2, -1, -1], ![2, 0, -1, -1]]

theorem canonical3323 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3323 = injectiveMoment H node473 := by
  calc
    injectiveMoment H raw3323 = injectiveMoment H raw3323step0 := by
      have heq : raw3323step0 = raw3323.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3323).symm
    injectiveMoment H raw3323step0 = injectiveMoment H raw3323step1 := by
      have heq : raw3323step1 = -raw3323step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3323step0).symm
    injectiveMoment H raw3323step1 = injectiveMoment H raw3323step2 := by
      have heq : raw3323step2 = (fun i j => raw3323step1 (permutation32 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3323step1 permutation32 permutation10
    _ = injectiveMoment H node473 := by rfl

def raw3324 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 1, 1], ![1, 2, -2, -1], ![1, 0, 1, -2]]

def raw3324step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 2, -1, -1], ![-1, -2, 2, 1], ![-1, 0, -1, 2]]

def raw3324step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, -1, -1, 2], ![0, 2, 0, -2], ![2, 0, -1, -1]]

theorem canonical3324 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3324 = injectiveMoment H node521 := by
  calc
    injectiveMoment H raw3324 = injectiveMoment H raw3324step0 := by
      have heq : raw3324step0 = -raw3324 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3324).symm
    injectiveMoment H raw3324step0 = injectiveMoment H raw3324step1 := by
      have heq : raw3324step1 = (fun i j => raw3324step0 (permutation25 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3324step0 permutation25 permutation15
    _ = injectiveMoment H node521 := by rfl

def raw3325 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 2, 0], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, 0, 0, -2]]

theorem canonical3325 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3325 = injectiveMoment H node1998 := by
  rfl

def raw3326 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 2, 0], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, 0, -1, -1]]

theorem canonical3326 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3326 = injectiveMoment H node1999 := by
  rfl

def raw3327 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 2, 0], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 1, -1, -1]]

theorem canonical3327 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3327 = injectiveMoment H node2000 := by
  rfl

end MUB6.Certificate.PairSemantics

end OAI
