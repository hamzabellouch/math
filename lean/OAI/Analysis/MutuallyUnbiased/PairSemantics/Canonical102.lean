import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes2
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes3
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes7
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes9
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes14
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes15
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes18
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes19
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes20
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes25
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes31

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw3264 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 2, -1, -1], ![1, -2, 1, 0], ![1, 0, 1, -2]]

def raw3264step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![1, 1, -2, 0], ![1, 1, 0, -2]]

theorem canonical3264 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3264 = injectiveMoment H node476 := by
  calc
    injectiveMoment H raw3264 = injectiveMoment H raw3264step0 := by
      have heq : raw3264step0 = (fun i j => raw3264 (permutation9 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3264 permutation9 permutation11
    _ = injectiveMoment H node476 := by rfl

def raw3265 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 2, -1, -1], ![1, -2, 2, -1], ![1, 0, 0, -1]]

def raw3265step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 2, -2, 0], ![-1, -1, 2, 0], ![3, -1, -1, -1]]

def raw3265step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 2, -1], ![0, 2, -2, 0], ![1, 0, 1, -2]]

theorem canonical3265 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3265 = injectiveMoment H node944 := by
  calc
    injectiveMoment H raw3265 = injectiveMoment H raw3265step0 := by
      have heq : raw3265step0 = raw3265.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3265).symm
    injectiveMoment H raw3265step0 = injectiveMoment H raw3265step1 := by
      have heq : raw3265step1 = (fun i j => raw3265step0 (permutation32 i) (permutation30 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3265step0 permutation32 permutation30
    _ = injectiveMoment H node944 := by rfl

def raw3266 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 2, -1, -1], ![1, -2, 3, -2], ![1, 0, -1, 0]]

def raw3266step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 2, -2, 0], ![-1, -1, 3, -1], ![3, -1, -2, 0]]

def raw3266step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 3, -2], ![0, 2, 0, -2], ![1, 0, -2, 1]]

theorem canonical3266 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3266 = injectiveMoment H node953 := by
  calc
    injectiveMoment H raw3266 = injectiveMoment H raw3266step0 := by
      have heq : raw3266step0 = raw3266.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3266).symm
    injectiveMoment H raw3266step0 = injectiveMoment H raw3266step1 := by
      have heq : raw3266step1 = (fun i j => raw3266step0 (permutation26 i) (permutation29 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3266step0 permutation26 permutation29
    _ = injectiveMoment H node953 := by rfl

def raw3267 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 2, -1, -1], ![1, -1, -1, 1], ![1, -1, 3, -3]]

theorem canonical3267 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3267 = injectiveMoment H node604 := by
  rfl

def raw3268 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 2, -1, -1], ![1, -1, 0, 0], ![1, -1, 2, -2]]

def raw3268step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 2, -1, -1], ![-1, -1, 0, 2], ![3, -1, 0, -2]]

def raw3268step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, -2, 1, 1], ![1, 1, 0, -2], ![-3, 1, 0, 2]]

def raw3268step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 1, -2, 1], ![0, 1, 2, -3], ![1, -2, 1, 0]]

theorem canonical3268 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3268 = injectiveMoment H node1277 := by
  calc
    injectiveMoment H raw3268 = injectiveMoment H raw3268step0 := by
      have heq : raw3268step0 = raw3268.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3268).symm
    injectiveMoment H raw3268step0 = injectiveMoment H raw3268step1 := by
      have heq : raw3268step1 = -raw3268step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3268step0).symm
    injectiveMoment H raw3268step1 = injectiveMoment H raw3268step2 := by
      have heq : raw3268step2 = (fun i j => raw3268step1 (permutation12 i) (permutation24 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3268step1 permutation12 permutation24
    _ = injectiveMoment H node1277 := by rfl

def raw3269 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 2, -1, -1], ![1, -1, 1, -1], ![1, -1, 1, -1]]

def raw3269step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![1, 1, -1, -1], ![1, 1, -1, -1]]

theorem canonical3269 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3269 = injectiveMoment H node477 := by
  calc
    injectiveMoment H raw3269 = injectiveMoment H raw3269step0 := by
      have heq : raw3269step0 = (fun i j => raw3269 (permutation9 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3269 permutation9 permutation11
    _ = injectiveMoment H node477 := by rfl

def raw3270 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 2, 0, -2], ![1, -2, 2, -1], ![1, 0, -1, 0]]

def raw3270step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 2, -2, 0], ![-1, 0, 2, -1], ![3, -2, -1, 0]]

def raw3270step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, -2, 2, 0], ![1, 0, -2, 1], ![-3, 2, 1, 0]]

def raw3270step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -2, 2, 0], ![0, 2, 1, -3], ![1, 0, -2, 1]]

theorem canonical3270 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3270 = injectiveMoment H node1235 := by
  calc
    injectiveMoment H raw3270 = injectiveMoment H raw3270step0 := by
      have heq : raw3270step0 = raw3270.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3270).symm
    injectiveMoment H raw3270step0 = injectiveMoment H raw3270step1 := by
      have heq : raw3270step1 = -raw3270step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3270step0).symm
    injectiveMoment H raw3270step1 = injectiveMoment H raw3270step2 := by
      have heq : raw3270step2 = (fun i j => raw3270step1 (permutation10 i) (permutation30 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3270step1 permutation10 permutation30
    _ = injectiveMoment H node1235 := by rfl

def raw3271 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 2, 0, -2], ![1, -1, -1, 1], ![1, -1, 2, -2]]

def raw3271step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 2, -2], ![1, -1, -1, 1], ![1, 2, -1, -2]]

theorem canonical3271 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3271 = injectiveMoment H node483 := by
  calc
    injectiveMoment H raw3271 = injectiveMoment H raw3271step0 := by
      have heq : raw3271step0 = (fun i j => raw3271 (permutation9 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3271 permutation9 permutation11
    _ = injectiveMoment H node483 := by rfl

def raw3272 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 2, 1, -3], ![1, -2, 1, 0], ![1, 0, -1, 0]]

def raw3272step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 2, -2, 0], ![-1, 1, 1, -1], ![3, -3, 0, 0]]

def raw3272step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, -2, 2, 0], ![1, -1, -1, 1], ![-3, 3, 0, 0]]

def raw3272step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 3, -3], ![0, 2, -2, 0], ![1, -1, -1, 1]]

theorem canonical3272 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3272 = injectiveMoment H node1066 := by
  calc
    injectiveMoment H raw3272 = injectiveMoment H raw3272step0 := by
      have heq : raw3272step0 = raw3272.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3272).symm
    injectiveMoment H raw3272step0 = injectiveMoment H raw3272step1 := by
      have heq : raw3272step1 = -raw3272step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3272step0).symm
    injectiveMoment H raw3272step1 = injectiveMoment H raw3272step2 := by
      have heq : raw3272step2 = (fun i j => raw3272step1 (permutation13 i) (permutation32 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3272step1 permutation13 permutation32
    _ = injectiveMoment H node1066 := by rfl

def raw3273 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 2, 1, -3], ![1, -1, -1, 1], ![1, -1, 1, -1]]

def raw3273step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, 2, -3], ![1, -1, -1, 1], ![1, 1, -1, -1]]

theorem canonical3273 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3273 = injectiveMoment H node491 := by
  calc
    injectiveMoment H raw3273 = injectiveMoment H raw3273step0 := by
      have heq : raw3273step0 = (fun i j => raw3273 (permutation9 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3273 permutation9 permutation11
    _ = injectiveMoment H node491 := by rfl

def raw3274 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 2, 2, -4], ![1, -2, 0, 1], ![1, 0, -1, 0]]

def raw3274step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 2, -2, 0], ![-1, 2, 0, -1], ![3, -4, 1, 0]]

def raw3274step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, -2, 2, 0], ![1, -2, 0, 1], ![-3, 4, -1, 0]]

def raw3274step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![0, -1, -3, 4], ![0, 2, 0, -2], ![1, 0, 1, -2]]

theorem canonical3274 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3274 = injectiveMoment H node1155 := by
  calc
    injectiveMoment H raw3274 = injectiveMoment H raw3274step0 := by
      have heq : raw3274step0 = raw3274.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3274).symm
    injectiveMoment H raw3274step0 = injectiveMoment H raw3274step1 := by
      have heq : raw3274step1 = -raw3274step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3274step0).symm
    injectiveMoment H raw3274step1 = injectiveMoment H raw3274step2 := by
      have heq : raw3274step2 = (fun i j => raw3274step1 (permutation13 i) (permutation31 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3274step1 permutation13 permutation31
    _ = injectiveMoment H node1155 := by rfl

def raw3275 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 2, 2, -4], ![1, -1, -1, 1], ![1, -1, 0, 0]]

def raw3275step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 2, -1, -1], ![-1, 2, -1, 0], ![3, -4, 1, 0]]

def raw3275step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, -1, 2], ![0, 1, 3, -4], ![1, 1, -2, 0]]

theorem canonical3275 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3275 = injectiveMoment H node996 := by
  calc
    injectiveMoment H raw3275 = injectiveMoment H raw3275step0 := by
      have heq : raw3275step0 = raw3275.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3275).symm
    injectiveMoment H raw3275step0 = injectiveMoment H raw3275step1 := by
      have heq : raw3275step1 = (fun i j => raw3275step0 (permutation18 i) (permutation31 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3275step0 permutation18 permutation31
    _ = injectiveMoment H node996 := by rfl

def raw3276 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![1, -2, 2, -1], ![0, 2, -2, 0], ![1, 0, 1, -2]]

def raw3276step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 2, -2, 0], ![1, -2, 2, -1], ![1, 0, 1, -2]]

theorem canonical3276 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3276 = injectiveMoment H node602 := by
  calc
    injectiveMoment H raw3276 = injectiveMoment H raw3276step0 := by
      have heq : raw3276step0 = (fun i j => raw3276 (permutation11 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3276 permutation11 permutation9
    _ = injectiveMoment H node602 := by rfl

def raw3277 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![1, -2, 3, -2], ![0, 1, -2, 1], ![1, 1, 0, -2]]

def raw3277step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -2, 1], ![1, -2, 3, -2], ![1, 1, 0, -2]]

theorem canonical3277 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3277 = injectiveMoment H node597 := by
  calc
    injectiveMoment H raw3277 = injectiveMoment H raw3277step0 := by
      have heq : raw3277step0 = (fun i j => raw3277 (permutation11 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3277 permutation11 permutation9
    _ = injectiveMoment H node597 := by rfl

def raw3278 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![1, -2, 3, -2], ![0, 2, -2, 0], ![1, 0, 0, -1]]

def raw3278step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -2, 2, 0], ![-1, 3, -2, 0], ![3, -2, 0, -1]]

def raw3278step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, -1, 0, -1], ![0, 2, -2, 0], ![1, -3, 2, 0], ![-3, 2, 0, 1]]

def raw3278step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -2, 0, 2], ![0, 2, 1, -3], ![1, 0, -3, 2]]

theorem canonical3278 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3278 = injectiveMoment H node1305 := by
  calc
    injectiveMoment H raw3278 = injectiveMoment H raw3278step0 := by
      have heq : raw3278step0 = raw3278.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3278).symm
    injectiveMoment H raw3278step0 = injectiveMoment H raw3278step1 := by
      have heq : raw3278step1 = -raw3278step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3278step0).symm
    injectiveMoment H raw3278step1 = injectiveMoment H raw3278step2 := by
      have heq : raw3278step2 = (fun i j => raw3278step1 (permutation9 i) (permutation31 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3278step1 permutation9 permutation31
    _ = injectiveMoment H node1305 := by rfl

def raw3279 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![1, -2, 3, -2], ![0, 2, -1, -1], ![1, 0, -1, 0]]

def raw3279step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -2, 2, 0], ![-1, 3, -1, -1], ![3, -2, -1, 0]]

def raw3279step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 3, -2], ![0, 2, 0, -2], ![1, 0, -2, 1]]

theorem canonical3279 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3279 = injectiveMoment H node953 := by
  calc
    injectiveMoment H raw3279 = injectiveMoment H raw3279step0 := by
      have heq : raw3279step0 = raw3279.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3279).symm
    injectiveMoment H raw3279step0 = injectiveMoment H raw3279step1 := by
      have heq : raw3279step1 = (fun i j => raw3279step0 (permutation26 i) (permutation31 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3279step0 permutation26 permutation31
    _ = injectiveMoment H node953 := by rfl

def raw3280 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![1, -1, 2, -2], ![0, 2, -2, 0], ![1, -1, 1, -1]]

def raw3280step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 2, -2, 0], ![1, -1, 1, -1], ![1, -1, 2, -2]]

theorem canonical3280 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3280 = injectiveMoment H node603 := by
  calc
    injectiveMoment H raw3280 = injectiveMoment H raw3280step0 := by
      have heq : raw3280step0 = (fun i j => raw3280 (permutation12 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3280 permutation12 permutation9
    _ = injectiveMoment H node603 := by rfl

def raw3281 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![1, -1, 3, -3], ![0, 2, -2, 0], ![1, -1, 0, 0]]

def raw3281step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, 2, -1], ![-1, 3, -2, 0], ![3, -3, 0, 0]]

def raw3281step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, -1, 0, -1], ![0, 1, -2, 1], ![1, -3, 2, 0], ![-3, 3, 0, 0]]

def raw3281step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, 0, -3, 3], ![0, 2, 1, -3], ![1, -2, 0, 1]]

theorem canonical3281 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3281 = injectiveMoment H node1313 := by
  calc
    injectiveMoment H raw3281 = injectiveMoment H raw3281step0 := by
      have heq : raw3281step0 = raw3281.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3281).symm
    injectiveMoment H raw3281step0 = injectiveMoment H raw3281step1 := by
      have heq : raw3281step1 = -raw3281step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3281step0).symm
    injectiveMoment H raw3281step1 = injectiveMoment H raw3281step2 := by
      have heq : raw3281step2 = (fun i j => raw3281step1 (permutation14 i) (permutation31 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3281step1 permutation14 permutation31
    _ = injectiveMoment H node1313 := by rfl

def raw3282 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![1, -1, 3, -3], ![0, 2, -1, -1], ![1, -1, -1, 1]]

def raw3282step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 2, -1, -1], ![1, -1, -1, 1], ![1, -1, 3, -3]]

theorem canonical3282 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3282 = injectiveMoment H node604 := by
  calc
    injectiveMoment H raw3282 = injectiveMoment H raw3282step0 := by
      have heq : raw3282step0 = (fun i j => raw3282 (permutation12 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3282 permutation12 permutation9
    _ = injectiveMoment H node604 := by rfl

def raw3283 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![1, 0, -2, 1], ![0, 1, 1, -2], ![1, -1, 2, -2]]

def raw3283step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 1, -3], ![-1, 0, 2, -1], ![0, -1, -1, 2], ![-1, 1, -2, 2]]

def raw3283step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 2, -1], ![0, 2, 1, -3], ![1, -1, -2, 2]]

theorem canonical3283 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3283 = injectiveMoment H node1248 := by
  calc
    injectiveMoment H raw3283 = injectiveMoment H raw3283step0 := by
      have heq : raw3283step0 = -raw3283 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3283).symm
    injectiveMoment H raw3283step0 = injectiveMoment H raw3283step1 := by
      have heq : raw3283step1 = (fun i j => raw3283step0 (permutation23 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3283step0 permutation23 permutation15
    _ = injectiveMoment H node1248 := by rfl

def raw3284 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![1, 0, -2, 1], ![0, 1, 2, -3], ![1, -1, 1, -1]]

def raw3284step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 1, -3], ![-1, 0, 2, -1], ![0, -1, -2, 3], ![-1, 1, -1, 1]]

def raw3284step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 2, -1], ![0, 2, 1, -3], ![1, -1, -1, 1]]

theorem canonical3284 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3284 = injectiveMoment H node1209 := by
  calc
    injectiveMoment H raw3284 = injectiveMoment H raw3284step0 := by
      have heq : raw3284step0 = -raw3284 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3284).symm
    injectiveMoment H raw3284step0 = injectiveMoment H raw3284step1 := by
      have heq : raw3284step1 = (fun i j => raw3284step0 (permutation23 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3284step0 permutation23 permutation15
    _ = injectiveMoment H node1209 := by rfl

def raw3285 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![1, 0, -2, 1], ![0, 1, 3, -4], ![1, -1, 0, 0]]

def raw3285step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, 1, -1], ![-1, -2, 3, 0], ![3, 1, -4, 0]]

def raw3285step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, -1, 0, -1], ![0, 0, -1, 1], ![1, 2, -3, 0], ![-3, -1, 4, 0]]

def raw3285step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![0, -1, -3, 4], ![0, 2, 1, -3], ![1, 0, 0, -1]]

theorem canonical3285 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3285 = injectiveMoment H node1156 := by
  calc
    injectiveMoment H raw3285 = injectiveMoment H raw3285step0 := by
      have heq : raw3285step0 = raw3285.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3285).symm
    injectiveMoment H raw3285step0 = injectiveMoment H raw3285step1 := by
      have heq : raw3285step1 = -raw3285step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3285step0).symm
    injectiveMoment H raw3285step1 = injectiveMoment H raw3285step2 := by
      have heq : raw3285step2 = (fun i j => raw3285step1 (permutation14 i) (permutation29 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3285step1 permutation14 permutation29
    _ = injectiveMoment H node1156 := by rfl

def raw3286 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![1, 0, 1, -2], ![0, 2, -1, -1], ![1, -2, 1, 0]]

def raw3286step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![1, 1, -2, 0], ![1, 1, 0, -2]]

theorem canonical3286 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3286 = injectiveMoment H node476 := by
  calc
    injectiveMoment H raw3286 = injectiveMoment H raw3286step0 := by
      have heq : raw3286step0 = (fun i j => raw3286 (permutation12 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3286 permutation12 permutation11
    _ = injectiveMoment H node476 := by rfl

def raw3287 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![1, 0, 2, -3], ![0, 2, -2, 0], ![1, -2, 1, 0]]

def raw3287step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 2, -2, 0], ![1, -2, 1, 0], ![1, 0, 2, -3]]

theorem canonical3287 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3287 = injectiveMoment H node601 := by
  calc
    injectiveMoment H raw3287 = injectiveMoment H raw3287step0 := by
      have heq : raw3287step0 = (fun i j => raw3287 (permutation12 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3287 permutation12 permutation9
    _ = injectiveMoment H node601 := by rfl

def raw3288 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-2, 2, 2, -2], ![4, -2, -2, 0]]

def raw3288step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![0, 2, -2], ![2, -2, 0]]

theorem canonical3288 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3288 = injectiveMoment H node151 := by
  calc
    injectiveMoment H raw3288 = injectiveMoment H raw3288step0 := by
      have heq : raw3288step0 = raw3288.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3288).symm
    _ = injectiveMoment H node151 := by rfl

def raw3289 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-1, -2, 2, 1], ![3, 2, -2, -3]]

def raw3289step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 2, -2], ![2, 1, -3]]

theorem canonical3289 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3289 = injectiveMoment H node162 := by
  calc
    injectiveMoment H raw3289 = injectiveMoment H raw3289step0 := by
      have heq : raw3289step0 = raw3289.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3289).symm
    _ = injectiveMoment H node162 := by rfl

def raw3290 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-1, -2, 3, 0], ![3, 2, -3, -2]]

def raw3290step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 3, -3], ![2, 0, -2]]

theorem canonical3290 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3290 = injectiveMoment H node163 := by
  calc
    injectiveMoment H raw3290 = injectiveMoment H raw3290step0 := by
      have heq : raw3290step0 = raw3290.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3290).symm
    _ = injectiveMoment H node163 := by rfl

def raw3291 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-1, -2, 4, -1], ![3, 2, -4, -1]]

def raw3291step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 4, -4], ![2, -1, -1]]

theorem canonical3291 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3291 = injectiveMoment H node164 := by
  calc
    injectiveMoment H raw3291 = injectiveMoment H raw3291step0 := by
      have heq : raw3291step0 = raw3291.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3291).symm
    _ = injectiveMoment H node164 := by rfl

def raw3292 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -3, 3, 0], ![2, 3, -3, -2]]

def raw3292step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![0, 3, -3], ![2, 0, -2]]

theorem canonical3292 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3292 = injectiveMoment H node192 := by
  calc
    injectiveMoment H raw3292 = injectiveMoment H raw3292step0 := by
      have heq : raw3292step0 = raw3292.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3292).symm
    _ = injectiveMoment H node192 := by rfl

def raw3293 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -3, 4, -1], ![2, 3, -4, -1]]

def raw3293step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![0, 4, -4], ![2, -1, -1]]

theorem canonical3293 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3293 = injectiveMoment H node193 := by
  calc
    injectiveMoment H raw3293 = injectiveMoment H raw3293step0 := by
      have heq : raw3293step0 = raw3293.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3293).symm
    _ = injectiveMoment H node193 := by rfl

def raw3294 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 0, 2], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 1, 2, -4]]

def raw3294step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 2, 0, -2], ![0, -1, 1, 0], ![-1, 0, 1, 0], ![-1, -1, -2, 4]]

def raw3294step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 2, -2], ![0, 2, 0, -2], ![1, -1, 0, 0], ![1, 0, -1, 0]]

theorem canonical3294 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3294 = injectiveMoment H node1613 := by
  calc
    injectiveMoment H raw3294 = injectiveMoment H raw3294step0 := by
      have heq : raw3294step0 = -raw3294 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3294).symm
    injectiveMoment H raw3294step0 = injectiveMoment H raw3294step1 := by
      have heq : raw3294step1 = (fun i j => raw3294step0 (permutation134 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3294step0 permutation134 permutation21
    _ = injectiveMoment H node1613 := by rfl

def raw3295 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 0, 2], ![0, 1, -1, 0], ![1, 1, -2, 0], ![1, 0, 3, -4]]

def raw3295step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 0, 2], ![0, 1, -1, 0], ![1, 0, 3, -4], ![1, 1, -2, 0]]

theorem canonical3295 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3295 = injectiveMoment H node1989 := by
  calc
    injectiveMoment H raw3295 = injectiveMoment H raw3295step0 := by
      have heq : raw3295step0 = (fun i j => raw3295 (permutation34 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3295 permutation34 permutation9
    _ = injectiveMoment H node1989 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
