import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes1
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes2
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes7
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes10
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes12
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes15
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes17
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes18
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes20
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes40
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes42

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw6368 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![-1, 1, -1, 1], ![0, 1, 3, -4], ![1, -1, -1, 1], ![1, 0, -1, 0]]

def raw6368step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![-1, 1, -1, 1], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, 0, 3, -4]]

theorem canonical6368 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6368 = injectiveMoment H node2570 := by
  calc
    injectiveMoment H raw6368 = injectiveMoment H raw6368step0 := by
      have heq : raw6368step0 = (fun i j => raw6368 (permutation49 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6368 permutation49 permutation15
    _ = injectiveMoment H node2570 := by rfl

def raw6369 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![-1, 1, -1, 1], ![0, 1, 3, -4], ![1, -1, 0, 0], ![1, 0, -2, 1]]

theorem canonical6369 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6369 = injectiveMoment H node2573 := by
  rfl

def raw6370 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![-1, 1, -1, 1], ![0, 1, 3, -4], ![2, -1, -2, 1]]

def raw6370step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![-1, 1, 1, -1], ![0, -1, 3, -2], ![2, 1, -4, 1]]

def raw6370step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 1, 0, -2], ![1, -1, -1, 1], ![0, 1, -3, 2], ![-2, -1, 4, -1]]

def raw6370step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 1, 2, -3], ![1, -1, 1, -1], ![1, 1, -2, 0]]

theorem canonical6370 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6370 = injectiveMoment H node467 := by
  calc
    injectiveMoment H raw6370 = injectiveMoment H raw6370step0 := by
      have heq : raw6370step0 = raw6370.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6370).symm
    injectiveMoment H raw6370step0 = injectiveMoment H raw6370step1 := by
      have heq : raw6370step1 = -raw6370step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6370step0).symm
    injectiveMoment H raw6370step1 = injectiveMoment H raw6370step2 := by
      have heq : raw6370step2 = (fun i j => raw6370step1 (permutation32 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6370step1 permutation32 permutation10
    _ = injectiveMoment H node467 := by rfl

def raw6371 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![-1, 1, -1, 1], ![1, -1, -1, 1], ![1, 1, 2, -4]]

def raw6371step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 1, 0, -2], ![1, -1, 1, -1], ![-1, 1, 1, -1], ![-1, -1, -2, 4]]

def raw6371step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 1, 1, -2], ![1, -1, 1, -1], ![1, 1, -1, -1]]

theorem canonical6371 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6371 = injectiveMoment H node464 := by
  calc
    injectiveMoment H raw6371 = injectiveMoment H raw6371step0 := by
      have heq : raw6371step0 = -raw6371 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6371).symm
    injectiveMoment H raw6371step0 = injectiveMoment H raw6371step1 := by
      have heq : raw6371step1 = (fun i j => raw6371step0 (permutation28 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6371step0 permutation28 permutation21
    _ = injectiveMoment H node464 := by rfl

def raw6372 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![-1, 1, -1, 1], ![1, -1, 3, -3], ![1, 1, -2, 0]]

def raw6372step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![-1, 1, -1, 1], ![0, -1, 3, -2], ![2, 1, -3, 0]]

def raw6372step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, 2, -3], ![1, -1, -1, 1], ![1, 1, -1, -1]]

theorem canonical6372 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6372 = injectiveMoment H node491 := by
  calc
    injectiveMoment H raw6372 = injectiveMoment H raw6372step0 := by
      have heq : raw6372step0 = raw6372.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6372).symm
    injectiveMoment H raw6372step0 = injectiveMoment H raw6372step1 := by
      have heq : raw6372step1 = (fun i j => raw6372step0 (permutation25 i) (permutation29 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6372step0 permutation25 permutation29
    _ = injectiveMoment H node491 := by rfl

def raw6373 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![-1, 1, -1, 1], ![1, 0, -2, 1], ![1, 0, 3, -4]]

def raw6373step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, -2, 1], ![0, 1, 3, -4], ![1, -1, -1, 1]]

theorem canonical6373 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6373 = injectiveMoment H node1080 := by
  calc
    injectiveMoment H raw6373 = injectiveMoment H raw6373step0 := by
      have heq : raw6373step0 = (fun i j => raw6373 (permutation12 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6373 permutation12 permutation15
    _ = injectiveMoment H node1080 := by rfl

def raw6374 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![-1, 1, -1, 1], ![1, 0, 2, -3], ![1, 0, -1, 0]]

def raw6374step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, -1, -1, 1]]

theorem canonical6374 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6374 = injectiveMoment H node1081 := by
  calc
    injectiveMoment H raw6374 = injectiveMoment H raw6374step0 := by
      have heq : raw6374step0 = (fun i j => raw6374 (permutation14 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6374 permutation14 permutation15
    _ = injectiveMoment H node1081 := by rfl

def raw6375 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![-1, 1, -1, 1], ![1, 0, 3, -4], ![1, 0, -2, 1]]

def raw6375step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, -2, 1], ![0, 1, 3, -4], ![1, -1, -1, 1]]

theorem canonical6375 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6375 = injectiveMoment H node1080 := by
  calc
    injectiveMoment H raw6375 = injectiveMoment H raw6375step0 := by
      have heq : raw6375step0 = (fun i j => raw6375 (permutation14 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6375 permutation14 permutation15
    _ = injectiveMoment H node1080 := by rfl

def raw6376 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![-1, 1, -1, 1], ![1, 1, -2, 0], ![1, -1, 3, -3]]

def raw6376step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![-1, 1, 1, -1], ![0, -1, -2, 3], ![2, 1, 0, -3]]

def raw6376step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, 2, -3], ![1, -1, -1, 1], ![1, 1, -1, -1]]

theorem canonical6376 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6376 = injectiveMoment H node491 := by
  calc
    injectiveMoment H raw6376 = injectiveMoment H raw6376step0 := by
      have heq : raw6376step0 = raw6376.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6376).symm
    injectiveMoment H raw6376step0 = injectiveMoment H raw6376step1 := by
      have heq : raw6376step1 = (fun i j => raw6376step0 (permutation25 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6376step0 permutation25 permutation23
    _ = injectiveMoment H node491 := by rfl

def raw6377 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![-1, 1, 2, -2], ![1, -1, 1, -1], ![1, 1, -3, 1]]

def raw6377step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![-1, 1, -1, 1], ![0, 2, 1, -3], ![2, -2, -1, 1]]

def raw6377step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 1, -1, -1], ![1, -1, 1, -1], ![0, -2, -1, 3], ![-2, 2, 1, -1]]

def raw6377step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -1, 3, -2], ![1, -1, -1, 1], ![1, 1, -1, -1]]

theorem canonical6377 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6377 = injectiveMoment H node680 := by
  calc
    injectiveMoment H raw6377 = injectiveMoment H raw6377step0 := by
      have heq : raw6377step0 = raw6377.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6377).symm
    injectiveMoment H raw6377step0 = injectiveMoment H raw6377step1 := by
      have heq : raw6377step1 = -raw6377step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6377step0).symm
    injectiveMoment H raw6377step1 = injectiveMoment H raw6377step2 := by
      have heq : raw6377step2 = (fun i j => raw6377step1 (permutation31 i) (permutation12 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6377step1 permutation31 permutation12
    _ = injectiveMoment H node680 := by rfl

def raw6378 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![-1, 1, 3, -3], ![1, -1, 0, 0], ![1, 1, -3, 1]]

def raw6378step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![-1, 1, -1, 1], ![0, 3, 0, -3], ![2, -3, 0, 1]]

def raw6378step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -3, 3], ![0, 2, 1, -3], ![1, -1, 1, -1]]

theorem canonical6378 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6378 = injectiveMoment H node1105 := by
  calc
    injectiveMoment H raw6378 = injectiveMoment H raw6378step0 := by
      have heq : raw6378step0 = raw6378.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6378).symm
    injectiveMoment H raw6378step0 = injectiveMoment H raw6378step1 := by
      have heq : raw6378step1 = (fun i j => raw6378step0 (permutation18 i) (permutation22 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6378step0 permutation18 permutation22
    _ = injectiveMoment H node1105 := by rfl

def raw6379 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![-1, 2, -3, 2], ![1, -1, 0, 0], ![1, 0, 3, -4]]

def raw6379step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![-1, 2, -1, 0], ![0, -3, 0, 3], ![2, 2, 0, -4]]

def raw6379step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 3, -3], ![0, 2, -4, 2], ![1, -1, 1, -1]]

theorem canonical6379 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6379 = injectiveMoment H node1064 := by
  calc
    injectiveMoment H raw6379 = injectiveMoment H raw6379step0 := by
      have heq : raw6379step0 = raw6379.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6379).symm
    injectiveMoment H raw6379step0 = injectiveMoment H raw6379step1 := by
      have heq : raw6379step1 = (fun i j => raw6379step0 (permutation18 i) (permutation22 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6379step0 permutation18 permutation22
    _ = injectiveMoment H node1064 := by rfl

def raw6380 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![-1, 2, -3, 2], ![1, -1, 3, -3], ![1, 0, 0, -1]]

def raw6380step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![-1, 2, -1, 0], ![0, -3, 3, 0], ![2, 2, -3, -1]]

def raw6380step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 1, -1, -1], ![1, -2, 1, 0], ![0, 3, -3, 0], ![-2, -2, 3, 1]]

def raw6380step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, -3, 3], ![0, 1, 1, -2], ![1, -2, 3, -2]]

theorem canonical6380 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6380 = injectiveMoment H node1342 := by
  calc
    injectiveMoment H raw6380 = injectiveMoment H raw6380step0 := by
      have heq : raw6380step0 = raw6380.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6380).symm
    injectiveMoment H raw6380step0 = injectiveMoment H raw6380step1 := by
      have heq : raw6380step1 = -raw6380step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6380step0).symm
    injectiveMoment H raw6380step1 = injectiveMoment H raw6380step2 := by
      have heq : raw6380step2 = (fun i j => raw6380step1 (permutation11 i) (permutation28 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6380step1 permutation11 permutation28
    _ = injectiveMoment H node1342 := by rfl

def raw6381 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![-1, 2, -2, 1], ![1, -1, -1, 1], ![1, 0, 3, -4]]

def raw6381step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![-1, 2, -1, 0], ![0, -2, -1, 3], ![2, 1, 1, -4]]

def raw6381step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 1, -1, -1], ![1, -2, 1, 0], ![0, 2, 1, -3], ![-2, -1, -1, 4]]

def raw6381step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 1, 2, -3], ![1, -1, 1, -1], ![1, 1, -2, 0]]

theorem canonical6381 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6381 = injectiveMoment H node467 := by
  calc
    injectiveMoment H raw6381 = injectiveMoment H raw6381step0 := by
      have heq : raw6381step0 = raw6381.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6381).symm
    injectiveMoment H raw6381step0 = injectiveMoment H raw6381step1 := by
      have heq : raw6381step1 = -raw6381step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6381step0).symm
    injectiveMoment H raw6381step1 = injectiveMoment H raw6381step2 := by
      have heq : raw6381step2 = (fun i j => raw6381step1 (permutation31 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6381step1 permutation31 permutation11
    _ = injectiveMoment H node467 := by rfl

def raw6382 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![-1, 2, -2, 1], ![1, -1, 3, -3], ![1, 0, -1, 0]]

def raw6382step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![-1, 2, -1, 0], ![0, -2, 3, -1], ![2, 1, -3, 0]]

def raw6382step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 2, -1], ![0, 2, 1, -3], ![1, -1, -1, 1]]

theorem canonical6382 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6382 = injectiveMoment H node1209 := by
  calc
    injectiveMoment H raw6382 = injectiveMoment H raw6382step0 := by
      have heq : raw6382step0 = raw6382.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6382).symm
    injectiveMoment H raw6382step0 = injectiveMoment H raw6382step1 := by
      have heq : raw6382step1 = (fun i j => raw6382step0 (permutation24 i) (permutation27 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6382step0 permutation24 permutation27
    _ = injectiveMoment H node1209 := by rfl

def raw6383 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![-1, 2, -1, 0], ![1, -1, 3, -3], ![1, 0, -2, 1]]

def raw6383step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![-1, 2, -1, 0], ![0, -1, 3, -2], ![2, 0, -3, 1]]

def raw6383step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 2, -1, -1], ![1, -1, -1, 1], ![1, 0, 2, -3]]

theorem canonical6383 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6383 = injectiveMoment H node495 := by
  calc
    injectiveMoment H raw6383 = injectiveMoment H raw6383step0 := by
      have heq : raw6383step0 = raw6383.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6383).symm
    injectiveMoment H raw6383step0 = injectiveMoment H raw6383step1 := by
      have heq : raw6383step1 = (fun i j => raw6383step0 (permutation23 i) (permutation29 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6383step0 permutation23 permutation29
    _ = injectiveMoment H node495 := by rfl

def raw6384 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, -2, 3], ![0, 1, 2, -3], ![1, 1, 0, -2]]

theorem canonical6384 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6384 = injectiveMoment H node991 := by
  rfl

def raw6385 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, -2, 3], ![0, 2, 2, -4], ![1, 0, 0, -1]]

theorem canonical6385 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6385 = injectiveMoment H node994 := by
  rfl

def raw6386 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, -2, 3], ![1, 2, 2, -5]]

def raw6386step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, -2, 2], ![2, 3, -5]]

def raw6386step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![1, 1, -2], ![0, 2, -2], ![-2, -3, 5]]

def raw6386step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 2, -2], ![1, 0, -1], ![1, 1, -2]]

theorem canonical6386 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6386 = injectiveMoment H node127 := by
  calc
    injectiveMoment H raw6386 = injectiveMoment H raw6386step0 := by
      have heq : raw6386step0 = raw6386.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6386).symm
    injectiveMoment H raw6386step0 = injectiveMoment H raw6386step1 := by
      have heq : raw6386step1 = -raw6386step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6386step0).symm
    injectiveMoment H raw6386step1 = injectiveMoment H raw6386step2 := by
      have heq : raw6386step2 = (fun i j => raw6386step1 (permutation31 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6386step1 permutation31 permutation3
    _ = injectiveMoment H node127 := by rfl

def raw6387 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, -1, 2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 3, -4]]

theorem canonical6387 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6387 = injectiveMoment H node2575 := by
  rfl

def raw6388 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, -1, 2], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, 0, 0, -1]]

theorem canonical6388 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6388 = injectiveMoment H node2576 := by
  rfl

def raw6389 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, -1, 2], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, 0, -1, 0]]

theorem canonical6389 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6389 = injectiveMoment H node2577 := by
  rfl

def raw6390 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, -1, 2], ![0, 1, -1, 0], ![1, 1, 2, -4]]

def raw6390step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 1, 0, -2], ![0, 1, 1, -2], ![0, -1, 1, 0], ![-1, -1, -2, 4]]

def raw6390step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, 0, 1, -2]]

theorem canonical6390 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6390 = injectiveMoment H node786 := by
  calc
    injectiveMoment H raw6390 = injectiveMoment H raw6390step0 := by
      have heq : raw6390step0 = -raw6390 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6390).symm
    injectiveMoment H raw6390step0 = injectiveMoment H raw6390step1 := by
      have heq : raw6390step1 = (fun i j => raw6390step0 (permutation32 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6390step0 permutation32 permutation11
    _ = injectiveMoment H node786 := by rfl

def raw6391 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, -1, 2], ![0, 1, 2, -3], ![1, 1, -1, -1]]

theorem canonical6391 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6391 = injectiveMoment H node995 := by
  rfl

def raw6392 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, -1, 2], ![0, 1, 3, -4], ![1, 1, -2, 0]]

theorem canonical6392 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6392 = injectiveMoment H node996 := by
  rfl

def raw6393 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, -1, 2], ![0, 2, -2, 0], ![1, 0, 3, -4]]

theorem canonical6393 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6393 = injectiveMoment H node997 := by
  rfl

def raw6394 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, -1, 2], ![0, 2, 0, -2], ![1, 0, 1, -2]]

def raw6394step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 1, 0, -2], ![0, 1, 1, -2], ![0, -2, 0, 2], ![-1, 0, -1, 2]]

def raw6394step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 1, 1, -2], ![1, 0, 1, -2]]

theorem canonical6394 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6394 = injectiveMoment H node1033 := by
  calc
    injectiveMoment H raw6394 = injectiveMoment H raw6394step0 := by
      have heq : raw6394step0 = -raw6394 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6394).symm
    injectiveMoment H raw6394step0 = injectiveMoment H raw6394step1 := by
      have heq : raw6394step1 = (fun i j => raw6394step0 (permutation32 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6394step0 permutation32 permutation11
    _ = injectiveMoment H node1033 := by rfl

def raw6395 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, -1, 2], ![0, 2, 1, -3], ![1, 0, 0, -1]]

def raw6395step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 1, 0, -2], ![0, 1, 1, -2], ![0, -2, -1, 3], ![-1, 0, 0, 1]]

def raw6395step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 0, 1], ![0, 1, 1, -2], ![1, 0, 1, -2]]

theorem canonical6395 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6395 = injectiveMoment H node1198 := by
  calc
    injectiveMoment H raw6395 = injectiveMoment H raw6395step0 := by
      have heq : raw6395step0 = -raw6395 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6395).symm
    injectiveMoment H raw6395step0 = injectiveMoment H raw6395step1 := by
      have heq : raw6395step1 = (fun i j => raw6395step0 (permutation25 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6395step0 permutation25 permutation21
    _ = injectiveMoment H node1198 := by rfl

def raw6396 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, -1, 2], ![0, 2, 2, -4], ![1, 0, -1, 0]]

theorem canonical6396 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6396 = injectiveMoment H node998 := by
  rfl

def raw6397 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, -1, 2], ![1, 2, 1, -4]]

def raw6397step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, -1, 1], ![2, 2, -4]]

def raw6397step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![1, 1, -2], ![0, 1, -1], ![-2, -2, 4]]

def raw6397step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]

theorem canonical6397 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6397 = injectiveMoment H node150 := by
  calc
    injectiveMoment H raw6397 = injectiveMoment H raw6397step0 := by
      have heq : raw6397step0 = raw6397.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6397).symm
    injectiveMoment H raw6397step0 = injectiveMoment H raw6397step1 := by
      have heq : raw6397step1 = -raw6397step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6397step0).symm
    injectiveMoment H raw6397step1 = injectiveMoment H raw6397step2 := by
      have heq : raw6397step2 = (fun i j => raw6397step1 (permutation31 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6397step1 permutation31 permutation3
    _ = injectiveMoment H node150 := by rfl

def raw6398 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, 0, 0, -1]]

def raw6398step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 1, 0, -2], ![0, 1, 0, -1], ![0, 0, 1, -1], ![0, -2, -1, 3], ![-1, 0, 0, 1]]

def raw6398step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 0, 1], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, 0, 0, -1]]

theorem canonical6398 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6398 = injectiveMoment H node2700 := by
  calc
    injectiveMoment H raw6398 = injectiveMoment H raw6398step0 := by
      have heq : raw6398step0 = -raw6398 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6398).symm
    injectiveMoment H raw6398step0 = injectiveMoment H raw6398step1 := by
      have heq : raw6398step1 = (fun i j => raw6398step0 (permutation124 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6398step0 permutation124 permutation21
    _ = injectiveMoment H node2700 := by rfl

def raw6399 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, 0, -1, 0]]

theorem canonical6399 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6399 = injectiveMoment H node2578 := by
  rfl

end MUB6.Certificate.PairSemantics

end OAI
