import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes0
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes12
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes19
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes42
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes45
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes46
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes47
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes48
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes49
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes50
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes51
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes52

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw9152 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -2, 2], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-2, 1, 0, 1], ![0, -1, 3, -2]]

def raw9152step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, 3, -2], ![0, 0, -2, 2], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 0, -1]]

theorem canonical9152 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9152 = injectiveMoment H node3278 := by
  calc
    injectiveMoment H raw9152 = injectiveMoment H raw9152step0 := by
      have heq : raw9152step0 = (fun i j => raw9152 (permutation294 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9152 permutation294 permutation9
    _ = injectiveMoment H node3278 := by rfl

def raw9153 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -2, 2], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-1, -1, 0, 2], ![-1, 1, 3, -3]]

def raw9153step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![-1, 1, 0, 0], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, -1, 3, -3], ![1, 0, -1, 0]]

theorem canonical9153 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9153 = injectiveMoment H node3383 := by
  calc
    injectiveMoment H raw9153 = injectiveMoment H raw9153step0 := by
      have heq : raw9153step0 = (fun i j => raw9153 (permutation285 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9153 permutation285 permutation15
    _ = injectiveMoment H node3383 := by rfl

def raw9154 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, -2, 2], ![0, 1, 0, -1], ![0, -1, 2, -1]]

def raw9154step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, -2, 2], ![1, 0, -1], ![-1, 2, -1]]

def raw9154step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 2, -2], ![1, -1, 0]]

theorem canonical9154 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9154 = injectiveMoment H node62 := by
  calc
    injectiveMoment H raw9154 = injectiveMoment H raw9154step0 := by
      have hz : ∀ i, raw9154 i (permutation9 0) = 0 := by decide +kernel
      have heq : raw9154step0 = (fun i j => raw9154 i (permutation9 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw9154 permutation9 hz
    injectiveMoment H raw9154step0 = injectiveMoment H raw9154step1 := by
      have heq : raw9154step1 = (fun i j => raw9154step0 (permutation7 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9154step0 permutation7 permutation4
    _ = injectiveMoment H node62 := by rfl

def raw9155 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -2, 2], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![-2, -1, 0, 3], ![1, 0, 2, -3]]

def raw9155step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 2, -2], ![0, -1, 0, 1], ![0, -1, 0, 1], ![-1, 1, 0, 0], ![2, 1, 0, -3], ![-1, 0, -2, 3]]

def raw9155step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 2, 1, -3], ![2, 0, 0, -2]]

theorem canonical9155 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9155 = injectiveMoment H node2958 := by
  calc
    injectiveMoment H raw9155 = injectiveMoment H raw9155step0 := by
      have heq : raw9155step0 = -raw9155 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9155).symm
    injectiveMoment H raw9155step0 = injectiveMoment H raw9155step1 := by
      have heq : raw9155step1 = (fun i j => raw9155step0 (permutation380 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9155step0 permutation380 permutation21
    _ = injectiveMoment H node2958 := by rfl

def raw9156 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -2, 2], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![-2, 0, 0, 2], ![1, -1, 2, -2]]

def raw9156step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 2, -2], ![0, -1, 0, 1], ![0, -1, 0, 1], ![-1, 1, 0, 0], ![2, 0, 0, -2], ![-1, 1, -2, 2]]

def raw9156step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 2, 0, -2], ![2, 0, 0, -2]]

theorem canonical9156 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9156 = injectiveMoment H node3038 := by
  calc
    injectiveMoment H raw9156 = injectiveMoment H raw9156step0 := by
      have heq : raw9156step0 = -raw9156 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9156).symm
    injectiveMoment H raw9156step0 = injectiveMoment H raw9156step1 := by
      have heq : raw9156step1 = (fun i j => raw9156step0 (permutation380 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9156step0 permutation380 permutation21
    _ = injectiveMoment H node3038 := by rfl

def raw9157 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -2, 2], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-2, 0, 2, 0]]

def raw9157step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 1, 0], ![0, -1, 1, 0], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, -2, 0]]

theorem canonical9157 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9157 = injectiveMoment H node3168 := by
  calc
    injectiveMoment H raw9157 = injectiveMoment H raw9157step0 := by
      have heq : raw9157step0 = (fun i j => raw9157 (permutation178 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9157 permutation178 permutation23
    _ = injectiveMoment H node3168 := by rfl

def raw9158 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -2, 2], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-2, -1, 2, 1]]

def raw9158step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, 0, -2, 2], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1]]

theorem canonical9158 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9158 = injectiveMoment H node3098 := by
  calc
    injectiveMoment H raw9158 = injectiveMoment H raw9158step0 := by
      have heq : raw9158step0 = (fun i j => raw9158 (permutation308 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9158 permutation308 permutation9
    _ = injectiveMoment H node3098 := by rfl

def raw9159 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -2, 2], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, -2, 0, 1], ![-2, 0, 3, -1]]

def raw9159step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -2, 1, 0], ![1, 0, 0, -1]]

theorem canonical9159 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9159 = injectiveMoment H node3148 := by
  calc
    injectiveMoment H raw9159 = injectiveMoment H raw9159step0 := by
      have heq : raw9159step0 = (fun i j => raw9159 (permutation309 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9159 permutation309 permutation10
    _ = injectiveMoment H node3148 := by rfl

def raw9160 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -2, 2], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, -1, 1, -1], ![-2, -1, 2, 1]]

def raw9160step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, 0, 0, -1]]

theorem canonical9160 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9160 = injectiveMoment H node3087 := by
  calc
    injectiveMoment H raw9160 = injectiveMoment H raw9160step0 := by
      have heq : raw9160step0 = (fun i j => raw9160 (permutation309 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9160 permutation309 permutation10
    _ = injectiveMoment H node3087 := by rfl

def raw9161 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -2, 2], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![-2, -1, 0, 3], ![1, -1, 2, -2]]

def raw9161step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, -2, 2], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, 2, -2], ![1, 0, 0, -1]]

theorem canonical9161 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9161 = injectiveMoment H node2982 := by
  calc
    injectiveMoment H raw9161 = injectiveMoment H raw9161step0 := by
      have heq : raw9161step0 = (fun i j => raw9161 (permutation259 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9161 permutation259 permutation9
    _ = injectiveMoment H node2982 := by rfl

def raw9162 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -2, 2], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![-2, 0, 3, -1], ![1, -2, -1, 2]]

def raw9162step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 3, -1], ![0, 0, -2, 2], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -2, -1, 2], ![1, 0, 0, -1]]

theorem canonical9162 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9162 = injectiveMoment H node3220 := by
  calc
    injectiveMoment H raw9162 = injectiveMoment H raw9162step0 := by
      have heq : raw9162step0 = (fun i j => raw9162 (permutation259 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9162 permutation259 permutation9
    _ = injectiveMoment H node3220 := by rfl

def raw9163 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -2, 2], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, -1, 1, -1], ![-2, -1, 1, 2]]

def raw9163step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -2, 2], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 0, 0, -1]]

theorem canonical9163 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9163 = injectiveMoment H node3051 := by
  calc
    injectiveMoment H raw9163 = injectiveMoment H raw9163step0 := by
      have heq : raw9163step0 = (fun i j => raw9163 (permutation309 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9163 permutation309 permutation9
    _ = injectiveMoment H node3051 := by rfl

def raw9164 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -2, 2], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 0, 0, -1], ![-2, -2, 2, 2]]

def raw9164step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 0, -2, 2], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 0, 0, -1]]

theorem canonical9164 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9164 = injectiveMoment H node2891 := by
  calc
    injectiveMoment H raw9164 = injectiveMoment H raw9164step0 := by
      have heq : raw9164step0 = (fun i j => raw9164 (permutation308 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9164 permutation308 permutation9
    _ = injectiveMoment H node2891 := by rfl

def raw9165 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -2, 2], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-2, 0, 0, 2], ![0, 1, 2, -3]]

def raw9165step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 2, -2], ![0, -1, 0, 1], ![-1, 1, 0, 0], ![-1, 1, 0, 0], ![2, 0, 0, -2], ![0, -1, -2, 3]]

def raw9165step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 0, 1], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, 0, 0, -2]]

theorem canonical9165 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9165 = injectiveMoment H node2947 := by
  calc
    injectiveMoment H raw9165 = injectiveMoment H raw9165step0 := by
      have heq : raw9165step0 = -raw9165 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9165).symm
    injectiveMoment H raw9165step0 = injectiveMoment H raw9165step1 := by
      have heq : raw9165step1 = (fun i j => raw9165step0 (permutation352 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9165step0 permutation352 permutation23
    _ = injectiveMoment H node2947 := by rfl

def raw9166 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -2, 2], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-2, 1, -1, 2], ![0, 0, 3, -3]]

def raw9166step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -2, 2], ![0, 0, 3, -3], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, -1, 0, 0]]

theorem canonical9166 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9166 = injectiveMoment H node3254 := by
  calc
    injectiveMoment H raw9166 = injectiveMoment H raw9166step0 := by
      have heq : raw9166step0 = (fun i j => raw9166 (permutation275 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9166 permutation275 permutation9
    _ = injectiveMoment H node3254 := by rfl

def raw9167 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -2, 2], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-2, 1, 0, 1], ![0, -1, 3, -2]]

def raw9167step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, 3, -2], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -1, 0]]

theorem canonical9167 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9167 = injectiveMoment H node3279 := by
  calc
    injectiveMoment H raw9167 = injectiveMoment H raw9167step0 := by
      have heq : raw9167step0 = (fun i j => raw9167 (permutation294 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9167 permutation294 permutation9
    _ = injectiveMoment H node3279 := by rfl

def raw9168 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -2, 2], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-1, -1, 0, 2], ![-1, 1, 3, -3]]

def raw9168step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![-1, 1, 0, 0], ![0, 0, -2, 2], ![0, 1, -1, 0], ![1, -1, 3, -3], ![1, 0, 0, -1]]

theorem canonical9168 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9168 = injectiveMoment H node3382 := by
  calc
    injectiveMoment H raw9168 = injectiveMoment H raw9168step0 := by
      have heq : raw9168step0 = (fun i j => raw9168 (permutation285 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9168 permutation285 permutation15
    _ = injectiveMoment H node3382 := by rfl

def raw9169 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -2, 2], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-2, -1, 0, 3], ![0, 1, 2, -3]]

def raw9169step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 2, -2], ![0, -1, 0, 1], ![-1, 1, 0, 0], ![-1, 0, 0, 1], ![2, 1, 0, -3], ![0, -1, -2, 3]]

def raw9169step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 2, -3], ![2, 0, 0, -2]]

theorem canonical9169 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9169 = injectiveMoment H node2941 := by
  calc
    injectiveMoment H raw9169 = injectiveMoment H raw9169step0 := by
      have heq : raw9169step0 = -raw9169 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9169).symm
    injectiveMoment H raw9169step0 = injectiveMoment H raw9169step1 := by
      have heq : raw9169step1 = (fun i j => raw9169step0 (permutation346 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9169step0 permutation346 permutation23
    _ = injectiveMoment H node2941 := by rfl

def raw9170 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -2, 2], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-1, -1, 0, 2], ![-1, 1, 2, -2]]

def raw9170step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 2, -2], ![0, -1, 0, 1], ![-1, 1, 0, 0], ![-1, 0, 0, 1], ![1, 1, 0, -2], ![1, -1, -2, 2]]

def raw9170step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![2, 0, 0, -2]]

theorem canonical9170 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9170 = injectiveMoment H node3020 := by
  calc
    injectiveMoment H raw9170 = injectiveMoment H raw9170step0 := by
      have heq : raw9170step0 = -raw9170 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9170).symm
    injectiveMoment H raw9170step0 = injectiveMoment H raw9170step1 := by
      have heq : raw9170step1 = (fun i j => raw9170step0 (permutation346 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9170step0 permutation346 permutation23
    _ = injectiveMoment H node3020 := by rfl

def raw9171 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -2, 2], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![0, -1, -1, 2], ![-2, 1, 3, -2]]

def raw9171step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, 3, -2], ![0, -1, -1, 2], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1]]

theorem canonical9171 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9171 = injectiveMoment H node3304 := by
  calc
    injectiveMoment H raw9171 = injectiveMoment H raw9171step0 := by
      have heq : raw9171step0 = (fun i j => raw9171 (permutation395 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9171 permutation395 permutation9
    _ = injectiveMoment H node3304 := by rfl

def raw9172 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -2, 2], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 0, -1], ![-2, 1, 0, 1], ![0, -2, 3, -1]]

def raw9172step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -2, 1, 0], ![1, 0, -1, 0]]

theorem canonical9172 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9172 = injectiveMoment H node3149 := by
  calc
    injectiveMoment H raw9172 = injectiveMoment H raw9172step0 := by
      have heq : raw9172step0 = (fun i j => raw9172 (permutation323 i) (permutation16 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9172 permutation323 permutation16
    _ = injectiveMoment H node3149 := by rfl

def raw9173 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -2, 2], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 0, -1], ![-1, 1, 1, -1], ![-1, -2, 2, 1]]

def raw9173step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 0, -1, 0]]

theorem canonical9173 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9173 = injectiveMoment H node3088 := by
  calc
    injectiveMoment H raw9173 = injectiveMoment H raw9173step0 := by
      have heq : raw9173step0 = (fun i j => raw9173 (permutation323 i) (permutation16 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9173 permutation323 permutation16
    _ = injectiveMoment H node3088 := by rfl

def raw9174 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -2, 2], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 0, -1], ![0, -2, 0, 2], ![-2, 1, 3, -2]]

def raw9174step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -2, 2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -2, 3, -2], ![1, 0, 0, -1]]

theorem canonical9174 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9174 = injectiveMoment H node3176 := by
  calc
    injectiveMoment H raw9174 = injectiveMoment H raw9174step0 := by
      have heq : raw9174step0 = (fun i j => raw9174 (permutation267 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9174 permutation267 permutation15
    _ = injectiveMoment H node3176 := by rfl

def raw9175 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -2, 2], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 0, -1], ![0, -2, 1, 1], ![-2, 1, 2, -1]]

def raw9175step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, -2, 2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -2, 2, -1], ![1, 0, 0, -1]]

theorem canonical9175 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9175 = injectiveMoment H node3212 := by
  calc
    injectiveMoment H raw9175 = injectiveMoment H raw9175step0 := by
      have heq : raw9175step0 = (fun i j => raw9175 (permutation267 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9175 permutation267 permutation15
    _ = injectiveMoment H node3212 := by rfl

def raw9176 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, -2, 2], ![0, 2, 1, -3], ![0, -2, 1, 1]]

def raw9176step0 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, 2, -2], ![0, -2, -1, 3], ![0, 2, -1, -1]]

def raw9176step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, 2, -2], ![-2, -1, 3], ![2, -1, -1]]

def raw9176step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![2, -1, -1]]

theorem canonical9176 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9176 = injectiveMoment H node36 := by
  calc
    injectiveMoment H raw9176 = injectiveMoment H raw9176step0 := by
      have heq : raw9176step0 = -raw9176 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9176).symm
    injectiveMoment H raw9176step0 = injectiveMoment H raw9176step1 := by
      have hz : ∀ i, raw9176step0 i (permutation9 0) = 0 := by decide +kernel
      have heq : raw9176step1 = (fun i j => raw9176step0 i (permutation9 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw9176step0 permutation9 hz
    injectiveMoment H raw9176step1 = injectiveMoment H raw9176step2 := by
      have heq : raw9176step2 = (fun i j => raw9176step1 (permutation5 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9176step1 permutation5 permutation3
    _ = injectiveMoment H node36 := by rfl

def raw9177 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, -2, 2], ![0, 2, 2, -4], ![0, -2, 0, 2]]

def raw9177step0 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, 2, -2], ![0, -2, -2, 4], ![0, 2, 0, -2]]

def raw9177step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, 2, -2], ![-2, -2, 4], ![2, 0, -2]]

def raw9177step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![2, 0, -2]]

theorem canonical9177 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9177 = injectiveMoment H node31 := by
  calc
    injectiveMoment H raw9177 = injectiveMoment H raw9177step0 := by
      have heq : raw9177step0 = -raw9177 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9177).symm
    injectiveMoment H raw9177step0 = injectiveMoment H raw9177step1 := by
      have hz : ∀ i, raw9177step0 i (permutation9 0) = 0 := by decide +kernel
      have heq : raw9177step1 = (fun i j => raw9177step0 i (permutation9 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw9177step0 permutation9 hz
    injectiveMoment H raw9177step1 = injectiveMoment H raw9177step2 := by
      have heq : raw9177step2 = (fun i j => raw9177step1 (permutation5 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9177step1 permutation5 permutation3
    _ = injectiveMoment H node31 := by rfl

def raw9178 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, 0, -1, 2], ![0, 0, -1, 1], ![1, -1, 0, 0], ![-1, -1, 2, 0], ![1, 2, 1, -4]]

def raw9178step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![1, 0, 1, -2], ![0, 0, 1, -1], ![-1, 1, 0, 0], ![1, 1, -2, 0], ![-1, -2, -1, 4]]

def raw9178step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, 1, -2, 0]]

theorem canonical9178 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9178 = injectiveMoment H node2930 := by
  calc
    injectiveMoment H raw9178 = injectiveMoment H raw9178step0 := by
      have heq : raw9178step0 = -raw9178 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9178).symm
    injectiveMoment H raw9178step0 = injectiveMoment H raw9178step1 := by
      have heq : raw9178step1 = (fun i j => raw9178step0 (permutation314 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9178step0 permutation314 permutation15
    _ = injectiveMoment H node2930 := by rfl

def raw9179 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, 0, -1, 2], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, -2, 1, 0]]

def raw9179step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, -2, 1, 0]]

theorem canonical9179 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9179 = injectiveMoment H node2732 := by
  calc
    injectiveMoment H raw9179 = injectiveMoment H raw9179step0 := by
      have heq : raw9179step0 = (fun i j => raw9179 (permutation57 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9179 permutation57 permutation9
    _ = injectiveMoment H node2732 := by rfl

def raw9180 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, 0, -1, 2], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, -2, 0, 1]]

def raw9180step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, -2, 0, 1]]

theorem canonical9180 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9180 = injectiveMoment H node2733 := by
  calc
    injectiveMoment H raw9180 = injectiveMoment H raw9180step0 := by
      have heq : raw9180step0 = (fun i j => raw9180 (permutation57 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9180 permutation57 permutation9
    _ = injectiveMoment H node2733 := by rfl

def raw9181 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, 0, -1, 2], ![0, 1, -1, 0], ![1, -1, 0, 0], ![-1, -1, 1, 1], ![1, 1, 2, -4]]

def raw9181step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![1, 0, 1, -2], ![0, -1, 1, 0], ![-1, 1, 0, 0], ![1, 1, -1, -1], ![-1, -1, -2, 4]]

def raw9181step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![-1, 0, 1, 0], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, 1, -1, -1]]

theorem canonical9181 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9181 = injectiveMoment H node3342 := by
  calc
    injectiveMoment H raw9181 = injectiveMoment H raw9181step0 := by
      have heq : raw9181step0 = -raw9181 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9181).symm
    injectiveMoment H raw9181step0 = injectiveMoment H raw9181step1 := by
      have heq : raw9181step1 = (fun i j => raw9181step0 (permutation355 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9181step0 permutation355 permutation15
    _ = injectiveMoment H node3342 := by rfl

def raw9182 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, 0, -1, 2], ![0, 1, 0, -1], ![1, -1, 2, -2]]

def raw9182step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -1, 2, -2]]

theorem canonical9182 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9182 = injectiveMoment H node1259 := by
  calc
    injectiveMoment H raw9182 = injectiveMoment H raw9182step0 := by
      have heq : raw9182step0 = (fun i j => raw9182 (permutation15 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9182 permutation15 permutation9
    _ = injectiveMoment H node1259 := by rfl

def raw9183 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, 0, -1, 2], ![0, 2, -1, -1], ![1, -2, 3, -2]]

def raw9183step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, 2, -2], ![-1, -1, -1, 3], ![1, 2, -1, -2]]

def raw9183step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 0, -2, 2], ![1, 1, 1, -3], ![-1, -2, 1, 2]]

def raw9183step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, 1, 1, -3]]

theorem canonical9183 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9183 = injectiveMoment H node827 := by
  calc
    injectiveMoment H raw9183 = injectiveMoment H raw9183step0 := by
      have heq : raw9183step0 = raw9183.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw9183).symm
    injectiveMoment H raw9183step0 = injectiveMoment H raw9183step1 := by
      have heq : raw9183step1 = -raw9183step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9183step0).symm
    injectiveMoment H raw9183step1 = injectiveMoment H raw9183step2 := by
      have heq : raw9183step2 = (fun i j => raw9183step1 (permutation29 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9183step1 permutation29 permutation9
    _ = injectiveMoment H node827 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
