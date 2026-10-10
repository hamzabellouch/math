import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes1
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes2
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes4
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes14
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes15
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes39
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes40

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw6272 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 0, 1, -1], ![1, 0, -1, 0]]

def raw6272step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 0, 0, -1]]

theorem canonical6272 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6272 = injectiveMoment H node2551 := by
  calc
    injectiveMoment H raw6272 = injectiveMoment H raw6272step0 := by
      have heq : raw6272step0 = (fun i j => raw6272 (permutation36 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6272 permutation36 permutation15
    _ = injectiveMoment H node2551 := by rfl

def raw6273 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 0, 2, -2], ![1, 0, -2, 1]]

def raw6273step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 1, -1], ![0, 0, 2, -2], ![0, 1, -2, 1], ![1, 0, 0, -1]]

theorem canonical6273 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6273 = injectiveMoment H node2554 := by
  calc
    injectiveMoment H raw6273 = injectiveMoment H raw6273step0 := by
      have heq : raw6273step0 = (fun i j => raw6273 (permutation36 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6273 permutation36 permutation15
    _ = injectiveMoment H node2554 := by rfl

def raw6274 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, 0, 0]]

def raw6274step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 0, 0, -1]]

theorem canonical6274 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6274 = injectiveMoment H node2551 := by
  calc
    injectiveMoment H raw6274 = injectiveMoment H raw6274step0 := by
      have heq : raw6274step0 = (fun i j => raw6274 (permutation42 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6274 permutation42 permutation21
    _ = injectiveMoment H node2551 := by rfl

def raw6275 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![0, 1, 0, -1]]

def raw6275step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 0, 0, -1]]

theorem canonical6275 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6275 = injectiveMoment H node2551 := by
  calc
    injectiveMoment H raw6275 = injectiveMoment H raw6275step0 := by
      have heq : raw6275step0 = (fun i j => raw6275 (permutation44 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6275 permutation44 permutation21
    _ = injectiveMoment H node2551 := by rfl

def raw6276 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 2, -2], ![0, 1, -2, 1]]

def raw6276step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 1, -1], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, -1, 2, -2]]

theorem canonical6276 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6276 = injectiveMoment H node2557 := by
  calc
    injectiveMoment H raw6276 = injectiveMoment H raw6276step0 := by
      have heq : raw6276step0 = (fun i j => raw6276 (permutation37 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6276 permutation37 permutation9
    _ = injectiveMoment H node2557 := by rfl

def raw6277 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, 0, -1]]

theorem canonical6277 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6277 = injectiveMoment H node970 := by
  rfl

def raw6278 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, 0, -1, 0]]

def raw6278step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 0, 1, -2]]

theorem canonical6278 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6278 = injectiveMoment H node969 := by
  calc
    injectiveMoment H raw6278 = injectiveMoment H raw6278step0 := by
      have heq : raw6278step0 = (fun i j => raw6278 (permutation10 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6278 permutation10 permutation15
    _ = injectiveMoment H node969 := by rfl

def raw6279 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, -1, 2, -2]]

theorem canonical6279 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6279 = injectiveMoment H node971 := by
  rfl

def raw6280 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, -1, 1, -1]]

def raw6280step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 2, -1], ![0, 1, 0, -1], ![1, 1, -1, -1]]

theorem canonical6280 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6280 = injectiveMoment H node942 := by
  calc
    injectiveMoment H raw6280 = injectiveMoment H raw6280step0 := by
      have heq : raw6280step0 = (fun i j => raw6280 (permutation11 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6280 permutation11 permutation11
    _ = injectiveMoment H node942 := by rfl

def raw6281 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -1, 0, 0]]

def raw6281step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, 0, 0, -1]]

theorem canonical6281 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6281 = injectiveMoment H node974 := by
  calc
    injectiveMoment H raw6281 = injectiveMoment H raw6281step0 := by
      have heq : raw6281step0 = (fun i j => raw6281 (permutation12 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6281 permutation12 permutation21
    _ = injectiveMoment H node974 := by rfl

def raw6282 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 1, -1], ![0, 2, 1, -3], ![1, -1, -1, 1]]

theorem canonical6282 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6282 = injectiveMoment H node972 := by
  rfl

def raw6283 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 1, -1], ![1, 1, 0, -2]]

def raw6283step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, 1, 0], ![3, -1, -2]]

def raw6283step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1]]

theorem canonical6283 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6283 = injectiveMoment H node271 := by
  calc
    injectiveMoment H raw6283 = injectiveMoment H raw6283step0 := by
      have heq : raw6283step0 = raw6283.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6283).symm
    injectiveMoment H raw6283step0 = injectiveMoment H raw6283step1 := by
      have heq : raw6283step1 = (fun i j => raw6283step0 (permutation27 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6283step0 permutation27 permutation6
    _ = injectiveMoment H node271 := by rfl

def raw6284 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 2, -2], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, -1, 0, 0]]

def raw6284step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 1, -1], ![0, 0, 2, -2], ![0, 2, -2, 0], ![1, -1, 0, 0]]

theorem canonical6284 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6284 = injectiveMoment H node2556 := by
  calc
    injectiveMoment H raw6284 = injectiveMoment H raw6284step0 := by
      have heq : raw6284step0 = (fun i j => raw6284 (permutation39 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6284 permutation39 permutation9
    _ = injectiveMoment H node2556 := by rfl

def raw6285 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 2, -2], ![0, 0, 1, -1], ![1, 1, -2, 0]]

def raw6285step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 1, -1], ![0, 0, 2, -2], ![1, 1, -2, 0]]

theorem canonical6285 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6285 = injectiveMoment H node967 := by
  calc
    injectiveMoment H raw6285 = injectiveMoment H raw6285step0 := by
      have heq : raw6285step0 = (fun i j => raw6285 (permutation11 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6285 permutation11 permutation9
    _ = injectiveMoment H node967 := by rfl

def raw6286 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 2, -2], ![0, 1, -2, 1], ![1, 0, 1, -2]]

theorem canonical6286 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6286 = injectiveMoment H node973 := by
  rfl

def raw6287 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, 0, 0, -1]]

theorem canonical6287 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6287 = injectiveMoment H node974 := by
  rfl

def raw6288 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, 0, -1, 0]]

def raw6288step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, 0, 0, -1]]

theorem canonical6288 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6288 = injectiveMoment H node974 := by
  calc
    injectiveMoment H raw6288 = injectiveMoment H raw6288step0 := by
      have heq : raw6288step0 = (fun i j => raw6288 (permutation10 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6288 permutation10 permutation15
    _ = injectiveMoment H node974 := by rfl

def raw6289 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 2, -2], ![0, 2, -2, 0], ![1, -1, 1, -1]]

theorem canonical6289 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6289 = injectiveMoment H node975 := by
  rfl

def raw6290 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 2, -2], ![0, 2, -1, -1], ![1, -1, 0, 0]]

def raw6290step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 2, -1], ![0, 2, 0, -2], ![1, 0, -1, 0]]

theorem canonical6290 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6290 = injectiveMoment H node946 := by
  calc
    injectiveMoment H raw6290 = injectiveMoment H raw6290step0 := by
      have heq : raw6290step0 = (fun i j => raw6290 (permutation11 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6290 permutation11 permutation11
    _ = injectiveMoment H node946 := by rfl

def raw6291 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 2, -2], ![0, 2, 0, -2], ![1, -1, -1, 1]]

theorem canonical6291 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6291 = injectiveMoment H node976 := by
  rfl

def raw6292 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 2, -2], ![1, 1, -1, -1]]

def raw6292step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, 2, -1], ![3, -2, -1]]

def raw6292step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]

theorem canonical6292 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6292 = injectiveMoment H node176 := by
  calc
    injectiveMoment H raw6292 = injectiveMoment H raw6292step0 := by
      have heq : raw6292step0 = raw6292.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6292).symm
    injectiveMoment H raw6292step0 = injectiveMoment H raw6292step1 := by
      have heq : raw6292step1 = (fun i j => raw6292step0 (permutation27 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6292step0 permutation27 permutation6
    _ = injectiveMoment H node176 := by rfl

def raw6293 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 3, -3], ![0, 1, -2, 1], ![1, 0, 0, -1]]

theorem canonical6293 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6293 = injectiveMoment H node977 := by
  rfl

def raw6294 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 3, -3], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 0, 0]]

theorem canonical6294 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6294 = injectiveMoment H node2560 := by
  rfl

def raw6295 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 3, -3], ![0, 1, -1, 0], ![1, 0, -1, 0]]

theorem canonical6295 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6295 = injectiveMoment H node978 := by
  rfl

def raw6296 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 3, -3], ![0, 1, 0, -1], ![1, 0, -2, 1]]

def raw6296step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 3, -3], ![0, 1, -2, 1], ![1, 0, 0, -1]]

theorem canonical6296 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6296 = injectiveMoment H node977 := by
  calc
    injectiveMoment H raw6296 = injectiveMoment H raw6296step0 := by
      have heq : raw6296step0 = (fun i j => raw6296 (permutation10 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6296 permutation10 permutation15
    _ = injectiveMoment H node977 := by rfl

def raw6297 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 3, -3], ![0, 2, -2, 0], ![1, -1, 0, 0]]

theorem canonical6297 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6297 = injectiveMoment H node979 := by
  rfl

def raw6298 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 3, -3], ![1, 1, -2, 0]]

def raw6298step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, 3, -2], ![3, -3, 0]]

def raw6298step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0]]

theorem canonical6298 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6298 = injectiveMoment H node188 := by
  calc
    injectiveMoment H raw6298 = injectiveMoment H raw6298step0 := by
      have heq : raw6298step0 = raw6298.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6298).symm
    injectiveMoment H raw6298step0 = injectiveMoment H raw6298step1 := by
      have heq : raw6298step1 = (fun i j => raw6298step0 (permutation25 i) (permutation7 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6298step0 permutation25 permutation7
    _ = injectiveMoment H node188 := by rfl

def raw6299 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 4, -4], ![1, 1, -3, 1]]

def raw6299step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, 4, -3], ![3, -4, 1]]

def raw6299step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -1, 0], ![1, -1, 0], ![1, 3, -4]]

theorem canonical6299 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6299 = injectiveMoment H node90 := by
  calc
    injectiveMoment H raw6299 = injectiveMoment H raw6299step0 := by
      have heq : raw6299step0 = raw6299.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6299).symm
    injectiveMoment H raw6299step0 = injectiveMoment H raw6299step1 := by
      have heq : raw6299step1 = (fun i j => raw6299step0 (permutation21 i) (permutation7 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6299step0 permutation21 permutation7
    _ = injectiveMoment H node90 := by rfl

def raw6300 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, -1, 3, -3]]

theorem canonical6300 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6300 = injectiveMoment H node982 := by
  rfl

def raw6301 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 1, -2, 1], ![0, 1, 1, -2], ![1, -1, 2, -2]]

theorem canonical6301 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6301 = injectiveMoment H node983 := by
  rfl

def raw6302 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 1, -2, 1], ![0, 1, 2, -3], ![1, -1, 1, -1]]

theorem canonical6302 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6302 = injectiveMoment H node984 := by
  rfl

def raw6303 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 1, -2, 1], ![0, 1, 3, -4], ![1, -1, 0, 0]]

theorem canonical6303 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6303 = injectiveMoment H node985 := by
  rfl

end MUB6.Certificate.PairSemantics

end OAI
