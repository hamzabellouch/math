import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes0
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes1
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes2
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes3
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes4
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes8
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes9
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes10
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes11
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes17
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes21
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes33
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes37

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw64 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]

def raw64step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![0, 4, -4], ![1, -1, 0], ![1, -1, 0]]

theorem canonical64 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw64 = injectiveMoment H node1134 := by
  calc
    injectiveMoment H raw64 = injectiveMoment H raw64step0 := by
      have heq : raw64step0 = (fun i j => raw64 (permutation122 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw64 permutation122 permutation6
    _ = injectiveMoment H node1134 := by rfl

def raw65 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![4, -2, -2]]

def raw65step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 4, -4], ![1, -1, 0], ![1, -1, 0]]

theorem canonical65 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw65 = injectiveMoment H node157 := by
  calc
    injectiveMoment H raw65 = injectiveMoment H raw65step0 := by
      have heq : raw65step0 = (fun i j => raw65 (permutation27 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw65 permutation27 permutation6
    _ = injectiveMoment H node157 := by rfl

def raw66 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]

def raw66step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, 4, -4], ![1, -2, 1], ![1, -1, 0]]

theorem canonical66 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw66 = injectiveMoment H node1140 := by
  calc
    injectiveMoment H raw66 = injectiveMoment H raw66step0 := by
      have heq : raw66step0 = (fun i j => raw66 (permutation140 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw66 permutation140 permutation6
    _ = injectiveMoment H node1140 := by rfl

def raw67 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]

def raw67step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 4, -4], ![1, -2, 1], ![1, -1, 0]]

theorem canonical67 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw67 = injectiveMoment H node665 := by
  calc
    injectiveMoment H raw67 = injectiveMoment H raw67step0 := by
      have heq : raw67step0 = (fun i j => raw67 (permutation140 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw67 permutation140 permutation6
    _ = injectiveMoment H node665 := by rfl

def raw68 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]

def raw68step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 4, -4], ![1, -2, 1], ![1, -1, 0]]

theorem canonical68 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw68 = injectiveMoment H node190 := by
  calc
    injectiveMoment H raw68 = injectiveMoment H raw68step0 := by
      have heq : raw68step0 = (fun i j => raw68 (permutation28 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw68 permutation28 permutation6
    _ = injectiveMoment H node190 := by rfl

def raw69 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]

def raw69step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 4, -4], ![1, -3, 2], ![1, -1, 0]]

theorem canonical69 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw69 = injectiveMoment H node217 := by
  calc
    injectiveMoment H raw69 = injectiveMoment H raw69step0 := by
      have heq : raw69step0 = (fun i j => raw69 (permutation22 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw69 permutation22 permutation6
    _ = injectiveMoment H node217 := by rfl

def raw70 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]

def raw70step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 4, -4], ![2, -2, 0]]

theorem canonical70 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw70 = injectiveMoment H node171 := by
  calc
    injectiveMoment H raw70 = injectiveMoment H raw70step0 := by
      have heq : raw70step0 = (fun i j => raw70 (permutation31 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw70 permutation31 permutation6
    _ = injectiveMoment H node171 := by rfl

def raw71 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]

def raw71step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 4, -4], ![2, -2, 0]]

theorem canonical71 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw71 = injectiveMoment H node199 := by
  calc
    injectiveMoment H raw71 = injectiveMoment H raw71step0 := by
      have heq : raw71step0 = (fun i j => raw71 (permutation25 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw71 permutation25 permutation6
    _ = injectiveMoment H node199 := by rfl

def raw72 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]

def raw72step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![0, -2, 2], ![-2, 1, 1], ![-2, 1, 1]]

def raw72step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 4, -4], ![1, -2, 1], ![1, -2, 1]]

theorem canonical72 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw72 = injectiveMoment H node218 := by
  calc
    injectiveMoment H raw72 = injectiveMoment H raw72step0 := by
      have heq : raw72step0 = -raw72 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw72).symm
    injectiveMoment H raw72step0 = injectiveMoment H raw72step1 := by
      have heq : raw72step1 = (fun i j => raw72step0 (permutation15 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw72step0 permutation15 permutation5
    _ = injectiveMoment H node218 := by rfl

def raw73 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![4, -2, -2]]

def raw73step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 4, -4], ![2, -2, 0]]

theorem canonical73 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw73 = injectiveMoment H node33 := by
  calc
    injectiveMoment H raw73 = injectiveMoment H raw73step0 := by
      have heq : raw73step0 = (fun i j => raw73 (permutation7 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw73 permutation7 permutation6
    _ = injectiveMoment H node33 := by rfl

def raw74 : Matrix (Fin 3) (Fin 4) ℤ := ![![-4, 1, 1, 2], ![2, -2, 1, -1], ![2, 1, -2, -1]]

def raw74step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]

def raw74step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -2, -2], ![-1, 2, -1], ![-1, -1, 2], ![-2, 1, 1]]

def raw74step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![1, 1, -2], ![2, -1, -1]]

theorem canonical74 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw74 = injectiveMoment H node134 := by
  calc
    injectiveMoment H raw74 = injectiveMoment H raw74step0 := by
      have heq : raw74step0 = raw74.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw74).symm
    injectiveMoment H raw74step0 = injectiveMoment H raw74step1 := by
      have heq : raw74step1 = -raw74step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw74step0).symm
    injectiveMoment H raw74step1 = injectiveMoment H raw74step2 := by
      have heq : raw74step2 = (fun i j => raw74step1 (permutation12 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw74step1 permutation12 permutation6
    _ = injectiveMoment H node134 := by rfl

def raw75 : Matrix (Fin 3) (Fin 4) ℤ := ![![-4, 1, 2, 1], ![2, -2, -1, 1], ![2, 1, -1, -2]]

def raw75step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![2, -1, -1], ![1, 1, -2]]

def raw75step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -2, -2], ![-1, 2, -1], ![-2, 1, 1], ![-1, -1, 2]]

def raw75step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![1, 1, -2], ![2, -1, -1]]

theorem canonical75 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw75 = injectiveMoment H node134 := by
  calc
    injectiveMoment H raw75 = injectiveMoment H raw75step0 := by
      have heq : raw75step0 = raw75.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw75).symm
    injectiveMoment H raw75step0 = injectiveMoment H raw75step1 := by
      have heq : raw75step1 = -raw75step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw75step0).symm
    injectiveMoment H raw75step1 = injectiveMoment H raw75step2 := by
      have heq : raw75step2 = (fun i j => raw75step1 (permutation14 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw75step1 permutation14 permutation6
    _ = injectiveMoment H node134 := by rfl

def raw76 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]

def raw76step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-3, 3, 0]]

def raw76step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]

theorem canonical76 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw76 = injectiveMoment H node1385 := by
  calc
    injectiveMoment H raw76 = injectiveMoment H raw76step0 := by
      have heq : raw76step0 = -raw76 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw76).symm
    injectiveMoment H raw76step0 = injectiveMoment H raw76step1 := by
      have heq : raw76step1 = (fun i j => raw76step0 (permutation165 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw76step0 permutation165 permutation8
    _ = injectiveMoment H node1385 := by rfl

def raw77 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![4, -3, -1]]

def raw77step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 3, -4]]

theorem canonical77 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw77 = injectiveMoment H node311 := by
  calc
    injectiveMoment H raw77 = injectiveMoment H raw77step0 := by
      have heq : raw77step0 = (fun i j => raw77 (permutation150 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw77 permutation150 permutation6
    _ = injectiveMoment H node311 := by rfl

def raw78 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]

def raw78step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2], ![-3, 3, 0]]

def raw78step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![2, 0, -2]]

theorem canonical78 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw78 = injectiveMoment H node309 := by
  calc
    injectiveMoment H raw78 = injectiveMoment H raw78step0 := by
      have heq : raw78step0 = -raw78 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw78).symm
    injectiveMoment H raw78step0 = injectiveMoment H raw78step1 := by
      have heq : raw78step1 = (fun i j => raw78step0 (permutation37 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw78step0 permutation37 permutation8
    _ = injectiveMoment H node309 := by rfl

def raw79 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]

def raw79step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -1, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]

def raw79step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1]]

theorem canonical79 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw79 = injectiveMoment H node2378 := by
  calc
    injectiveMoment H raw79 = injectiveMoment H raw79step0 := by
      have heq : raw79step0 = -raw79 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw79).symm
    injectiveMoment H raw79step0 = injectiveMoment H raw79step1 := by
      have heq : raw79step1 = (fun i j => raw79step0 (permutation164 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw79step0 permutation164 permutation6
    _ = injectiveMoment H node2378 := by rfl

def raw80 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]

def raw80step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-3, 0, 3]]

def raw80step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 0, 1], ![0, 3, -3], ![1, 0, -1], ![1, 0, -1]]

theorem canonical80 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw80 = injectiveMoment H node734 := by
  calc
    injectiveMoment H raw80 = injectiveMoment H raw80step0 := by
      have heq : raw80step0 = -raw80 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw80).symm
    injectiveMoment H raw80step0 = injectiveMoment H raw80step1 := by
      have heq : raw80step1 = (fun i j => raw80step0 (permutation37 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw80step0 permutation37 permutation6
    _ = injectiveMoment H node734 := by rfl

def raw81 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]

def raw81step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -1, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]

def raw81step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]

theorem canonical81 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw81 = injectiveMoment H node2377 := by
  calc
    injectiveMoment H raw81 = injectiveMoment H raw81step0 := by
      have heq : raw81step0 = -raw81 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw81).symm
    injectiveMoment H raw81step0 = injectiveMoment H raw81step1 := by
      have heq : raw81step1 = (fun i j => raw81step0 (permutation158 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw81step0 permutation158 permutation6
    _ = injectiveMoment H node2377 := by rfl

def raw82 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]

def raw82step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]

def raw82step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 2, -3]]

theorem canonical82 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw82 = injectiveMoment H node732 := by
  calc
    injectiveMoment H raw82 = injectiveMoment H raw82step0 := by
      have heq : raw82step0 = -raw82 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw82).symm
    injectiveMoment H raw82step0 = injectiveMoment H raw82step1 := by
      have heq : raw82step1 = (fun i j => raw82step0 (permutation35 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw82step0 permutation35 permutation6
    _ = injectiveMoment H node732 := by rfl

def raw83 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]

def raw83step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 3, -4]]

theorem canonical83 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw83 = injectiveMoment H node2124 := by
  calc
    injectiveMoment H raw83 = injectiveMoment H raw83step0 := by
      have heq : raw83step0 = (fun i j => raw83 (permutation367 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw83 permutation367 permutation6
    _ = injectiveMoment H node2124 := by rfl

def raw84 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]

def raw84step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 3, -4]]

theorem canonical84 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw84 = injectiveMoment H node553 := by
  calc
    injectiveMoment H raw84 = injectiveMoment H raw84step0 := by
      have heq : raw84step0 = (fun i j => raw84 (permutation144 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw84 permutation144 permutation6
    _ = injectiveMoment H node553 := by rfl

def raw85 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]

def raw85step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-3, 3, 0]]

def raw85step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 3, -3], ![1, 0, -1], ![2, -1, -1]]

theorem canonical85 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw85 = injectiveMoment H node310 := by
  calc
    injectiveMoment H raw85 = injectiveMoment H raw85step0 := by
      have heq : raw85step0 = -raw85 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw85).symm
    injectiveMoment H raw85step0 = injectiveMoment H raw85step1 := by
      have heq : raw85step1 = (fun i j => raw85step0 (permutation37 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw85step0 permutation37 permutation8
    _ = injectiveMoment H node310 := by rfl

def raw86 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]

def raw86step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 3, -4]]

theorem canonical86 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw86 = injectiveMoment H node639 := by
  calc
    injectiveMoment H raw86 = injectiveMoment H raw86step0 := by
      have heq : raw86step0 = (fun i j => raw86 (permutation127 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw86 permutation127 permutation6
    _ = injectiveMoment H node639 := by rfl

def raw87 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]

def raw87step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1], ![-2, 1, 1]]

def raw87step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![1, 1, -2]]

theorem canonical87 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw87 = injectiveMoment H node733 := by
  calc
    injectiveMoment H raw87 = injectiveMoment H raw87step0 := by
      have heq : raw87step0 = -raw87 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw87).symm
    injectiveMoment H raw87step0 = injectiveMoment H raw87step1 := by
      have heq : raw87step1 = (fun i j => raw87step0 (permutation33 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw87step0 permutation33 permutation6
    _ = injectiveMoment H node733 := by rfl

def raw88 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![4, -2, -2]]

def raw88step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, -1, 1], ![1, 0, -1], ![1, 3, -4]]

theorem canonical88 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw88 = injectiveMoment H node143 := by
  calc
    injectiveMoment H raw88 = injectiveMoment H raw88step0 := by
      have heq : raw88step0 = (fun i j => raw88 (permutation32 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw88 permutation32 permutation6
    _ = injectiveMoment H node143 := by rfl

def raw89 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, -2, 0], ![3, 0, -3]]

def raw89step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![1, 0, -1], ![1, 3, -4]]

theorem canonical89 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw89 = injectiveMoment H node195 := by
  calc
    injectiveMoment H raw89 = injectiveMoment H raw89step0 := by
      have heq : raw89step0 = (fun i j => raw89 (permutation26 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw89 permutation26 permutation6
    _ = injectiveMoment H node195 := by rfl

def raw90 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]

def raw90step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![1, 0, -1], ![1, 3, -4]]

theorem canonical90 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw90 = injectiveMoment H node166 := by
  calc
    injectiveMoment H raw90 = injectiveMoment H raw90step0 := by
      have heq : raw90step0 = (fun i j => raw90 (permutation32 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw90 permutation32 permutation6
    _ = injectiveMoment H node166 := by rfl

def raw91 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, 1, -3], ![3, -3, 0]]

def raw91step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![1, -1, 0], ![-2, -1, 3], ![-3, 3, 0]]

def raw91step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 3, -3], ![3, -1, -2]]

theorem canonical91 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw91 = injectiveMoment H node79 := by
  calc
    injectiveMoment H raw91 = injectiveMoment H raw91step0 := by
      have heq : raw91step0 = -raw91 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw91).symm
    injectiveMoment H raw91step0 = injectiveMoment H raw91step1 := by
      have heq : raw91step1 = (fun i j => raw91step0 (permutation10 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw91step0 permutation10 permutation8
    _ = injectiveMoment H node79 := by rfl

def raw92 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]

def raw92step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, -2, 1], ![-1, 1, 0], ![-2, 2, 0], ![-2, 0, 2]]

def raw92step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]

theorem canonical92 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw92 = injectiveMoment H node315 := by
  calc
    injectiveMoment H raw92 = injectiveMoment H raw92step0 := by
      have heq : raw92step0 = -raw92 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw92).symm
    injectiveMoment H raw92step0 = injectiveMoment H raw92step1 := by
      have heq : raw92step1 = (fun i j => raw92step0 (permutation41 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw92step0 permutation41 permutation8
    _ = injectiveMoment H node315 := by rfl

def raw93 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![2, -2, 0], ![3, -1, -2]]

def raw93step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![1, -2, 1], ![-2, 2, 0], ![-3, 1, 2]]

def raw93step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -2, 1], ![2, 1, -3]]

theorem canonical93 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw93 = injectiveMoment H node84 := by
  calc
    injectiveMoment H raw93 = injectiveMoment H raw93step0 := by
      have heq : raw93step0 = -raw93 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw93).symm
    injectiveMoment H raw93step0 = injectiveMoment H raw93step1 := by
      have heq : raw93step1 = (fun i j => raw93step0 (permutation11 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw93step0 permutation11 permutation8
    _ = injectiveMoment H node84 := by rfl

def raw94 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![2, 0, -2], ![3, -3, 0]]

def raw94step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![1, -2, 1], ![-2, 0, 2], ![-3, 3, 0]]

def raw94step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, -2, 1], ![2, 0, -2]]

theorem canonical94 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw94 = injectiveMoment H node86 := by
  calc
    injectiveMoment H raw94 = injectiveMoment H raw94step0 := by
      have heq : raw94step0 = -raw94 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw94).symm
    injectiveMoment H raw94step0 = injectiveMoment H raw94step1 := by
      have heq : raw94step1 = (fun i j => raw94step0 (permutation13 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw94step0 permutation13 permutation8
    _ = injectiveMoment H node86 := by rfl

def raw95 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]

def raw95step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -1, -3], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]

def raw95step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 1, 0], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]

theorem canonical95 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw95 = injectiveMoment H node2381 := by
  calc
    injectiveMoment H raw95 = injectiveMoment H raw95step0 := by
      have heq : raw95step0 = -raw95 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw95).symm
    injectiveMoment H raw95step0 = injectiveMoment H raw95step1 := by
      have heq : raw95step1 = (fun i j => raw95step0 (permutation174 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw95step0 permutation174 permutation6
    _ = injectiveMoment H node2381 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
