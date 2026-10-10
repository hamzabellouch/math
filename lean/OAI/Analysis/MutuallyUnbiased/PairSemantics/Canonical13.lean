import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes2
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes3
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes5
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes8
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes10
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes13
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes17
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes20
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes21
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes22
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes33
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes38
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes41
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes43

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw416 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]

def raw416step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 3, -3], ![1, 0, -1], ![1, 0, -1]]

theorem canonical416 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw416 = injectiveMoment H node549 := by
  calc
    injectiveMoment H raw416 = injectiveMoment H raw416step0 := by
      have heq : raw416step0 = (fun i j => raw416 (permutation145 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw416 permutation145 permutation6
    _ = injectiveMoment H node549 := by rfl

def raw417 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]

def raw417step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 2, 1]]

def raw417step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]

theorem canonical417 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw417 = injectiveMoment H node1404 := by
  calc
    injectiveMoment H raw417 = injectiveMoment H raw417step0 := by
      have heq : raw417step0 = -raw417 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw417).symm
    injectiveMoment H raw417step0 = injectiveMoment H raw417step1 := by
      have heq : raw417step1 = (fun i j => raw417step0 (permutation156 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw417step0 permutation156 permutation8
    _ = injectiveMoment H node1404 := by rfl

def raw418 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]

def raw418step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![1, -2, 1], ![-1, 0, 1], ![-2, 2, 0], ![-2, 1, 1]]

def raw418step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]

theorem canonical418 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw418 = injectiveMoment H node1406 := by
  calc
    injectiveMoment H raw418 = injectiveMoment H raw418step0 := by
      have heq : raw418step0 = -raw418 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw418).symm
    injectiveMoment H raw418step0 = injectiveMoment H raw418step1 := by
      have heq : raw418step1 = (fun i j => raw418step0 (permutation162 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw418step0 permutation162 permutation8
    _ = injectiveMoment H node1406 := by rfl

def raw419 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![2, -2, 0], ![3, -1, -2]]

def raw419step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![1, -2, 1], ![-2, 2, 0], ![-3, 1, 2]]

def raw419step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![2, 1, -3]]

theorem canonical419 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw419 = injectiveMoment H node337 := by
  calc
    injectiveMoment H raw419 = injectiveMoment H raw419step0 := by
      have heq : raw419step0 = -raw419 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw419).symm
    injectiveMoment H raw419step0 = injectiveMoment H raw419step1 := by
      have heq : raw419step1 = (fun i j => raw419step0 (permutation35 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw419step0 permutation35 permutation8
    _ = injectiveMoment H node337 := by rfl

def raw420 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]

def raw420step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -3, 3], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1]]

theorem canonical420 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw420 = injectiveMoment H node2794 := by
  calc
    injectiveMoment H raw420 = injectiveMoment H raw420step0 := by
      have heq : raw420step0 = (fun i j => raw420 (permutation233 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw420 permutation233 permutation5
    _ = injectiveMoment H node2794 := by rfl

def raw421 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]

def raw421step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1]]

theorem canonical421 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw421 = injectiveMoment H node2468 := by
  calc
    injectiveMoment H raw421 = injectiveMoment H raw421step0 := by
      have heq : raw421step0 = (fun i j => raw421 (permutation369 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw421 permutation369 permutation6
    _ = injectiveMoment H node2468 := by rfl

def raw422 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]

def raw422step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1]]

theorem canonical422 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw422 = injectiveMoment H node2664 := by
  calc
    injectiveMoment H raw422 = injectiveMoment H raw422step0 := by
      have heq : raw422step0 = (fun i j => raw422 (permutation287 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw422 permutation287 permutation6
    _ = injectiveMoment H node2664 := by rfl

def raw423 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]

def raw423step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]

theorem canonical423 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw423 = injectiveMoment H node1407 := by
  calc
    injectiveMoment H raw423 = injectiveMoment H raw423step0 := by
      have heq : raw423step0 = (fun i j => raw423 (permutation397 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw423 permutation397 permutation6
    _ = injectiveMoment H node1407 := by rfl

def raw424 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![3, 0, -3]]

def raw424step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -3, 3], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1]]

theorem canonical424 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw424 = injectiveMoment H node700 := by
  calc
    injectiveMoment H raw424 = injectiveMoment H raw424step0 := by
      have heq : raw424step0 = (fun i j => raw424 (permutation108 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw424 permutation108 permutation5
    _ = injectiveMoment H node700 := by rfl

def raw425 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]

def raw425step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1]]

theorem canonical425 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw425 = injectiveMoment H node2788 := by
  calc
    injectiveMoment H raw425 = injectiveMoment H raw425step0 := by
      have heq : raw425step0 = (fun i j => raw425 (permutation253 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw425 permutation253 permutation6
    _ = injectiveMoment H node2788 := by rfl

def raw426 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]

def raw426step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1]]

theorem canonical426 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw426 = injectiveMoment H node2657 := by
  calc
    injectiveMoment H raw426 = injectiveMoment H raw426step0 := by
      have heq : raw426step0 = (fun i j => raw426 (permutation390 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw426 permutation390 permutation6
    _ = injectiveMoment H node2657 := by rfl

def raw427 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]

def raw427step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 0, 1], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1]]

theorem canonical427 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw427 = injectiveMoment H node864 := by
  calc
    injectiveMoment H raw427 = injectiveMoment H raw427step0 := by
      have heq : raw427step0 = (fun i j => raw427 (permutation146 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw427 permutation146 permutation6
    _ = injectiveMoment H node864 := by rfl

def raw428 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]

def raw428step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1]]

theorem canonical428 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw428 = injectiveMoment H node2132 := by
  calc
    injectiveMoment H raw428 = injectiveMoment H raw428step0 := by
      have heq : raw428step0 = (fun i j => raw428 (permutation390 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw428 permutation390 permutation6
    _ = injectiveMoment H node2132 := by rfl

def raw429 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]

def raw429step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1]]

theorem canonical429 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw429 = injectiveMoment H node563 := by
  calc
    injectiveMoment H raw429 = injectiveMoment H raw429step0 := by
      have heq : raw429step0 = (fun i j => raw429 (permutation146 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw429 permutation146 permutation6
    _ = injectiveMoment H node563 := by rfl

def raw430 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]

def raw430step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2], ![-3, 3, 0]]

def raw430step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![2, -1, -1]]

theorem canonical430 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw430 = injectiveMoment H node339 := by
  calc
    injectiveMoment H raw430 = injectiveMoment H raw430step0 := by
      have heq : raw430step0 = -raw430 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw430).symm
    injectiveMoment H raw430step0 = injectiveMoment H raw430step1 := by
      have heq : raw430step1 = (fun i j => raw430step0 (permutation37 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw430step0 permutation37 permutation8
    _ = injectiveMoment H node339 := by rfl

def raw431 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]

def raw431step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1]]

theorem canonical431 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw431 = injectiveMoment H node648 := by
  calc
    injectiveMoment H raw431 = injectiveMoment H raw431step0 := by
      have heq : raw431step0 = (fun i j => raw431 (permutation123 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw431 permutation123 permutation6
    _ = injectiveMoment H node648 := by rfl

def raw432 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]

def raw432step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1]]

theorem canonical432 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw432 = injectiveMoment H node1132 := by
  calc
    injectiveMoment H raw432 = injectiveMoment H raw432step0 := by
      have heq : raw432step0 = (fun i j => raw432 (permutation123 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw432 permutation123 permutation6
    _ = injectiveMoment H node1132 := by rfl

def raw433 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]

def raw433step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 3, -3], ![1, 0, -1], ![2, -2, 0]]

theorem canonical433 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw433 = injectiveMoment H node340 := by
  calc
    injectiveMoment H raw433 = injectiveMoment H raw433step0 := by
      have heq : raw433step0 = (fun i j => raw433 (permutation145 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw433 permutation145 permutation6
    _ = injectiveMoment H node340 := by rfl

def raw434 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]

def raw434step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -2, 2], ![-2, 2, 0], ![-2, 1, 1]]

def raw434step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]

theorem canonical434 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw434 = injectiveMoment H node338 := by
  calc
    injectiveMoment H raw434 = injectiveMoment H raw434step0 := by
      have heq : raw434step0 = -raw434 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw434).symm
    injectiveMoment H raw434step0 = injectiveMoment H raw434step1 := by
      have heq : raw434step1 = (fun i j => raw434step0 (permutation36 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw434step0 permutation36 permutation8
    _ = injectiveMoment H node338 := by rfl

def raw435 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]

def raw435step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -3, 3], ![0, 1, -1], ![1, -1, 0], ![1, 2, -3]]

theorem canonical435 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw435 = injectiveMoment H node696 := by
  calc
    injectiveMoment H raw435 = injectiveMoment H raw435step0 := by
      have heq : raw435step0 = (fun i j => raw435 (permutation82 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw435 permutation82 permutation5
    _ = injectiveMoment H node696 := by rfl

def raw436 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]

def raw436step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -3, 3], ![0, 2, -2], ![1, -1, 0], ![1, 1, -2]]

theorem canonical436 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw436 = injectiveMoment H node698 := by
  calc
    injectiveMoment H raw436 = injectiveMoment H raw436step0 := by
      have heq : raw436step0 = (fun i j => raw436 (permutation84 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw436 permutation84 permutation5
    _ = injectiveMoment H node698 := by rfl

def raw437 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]

def raw437step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 3, -3], ![1, -2, 1], ![1, 0, -1]]

theorem canonical437 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw437 = injectiveMoment H node2790 := by
  calc
    injectiveMoment H raw437 = injectiveMoment H raw437step0 := by
      have heq : raw437step0 = (fun i j => raw437 (permutation230 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw437 permutation230 permutation6
    _ = injectiveMoment H node2790 := by rfl

def raw438 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]

def raw438step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 3, -3], ![1, -3, 2], ![1, 0, -1]]

theorem canonical438 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw438 = injectiveMoment H node1287 := by
  calc
    injectiveMoment H raw438 = injectiveMoment H raw438step0 := by
      have heq : raw438step0 = (fun i j => raw438 (permutation93 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw438 permutation93 permutation6
    _ = injectiveMoment H node1287 := by rfl

def raw439 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]

def raw439step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, 3, -3], ![1, -2, 1], ![1, 0, -1]]

theorem canonical439 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw439 = injectiveMoment H node1138 := by
  calc
    injectiveMoment H raw439 = injectiveMoment H raw439step0 := by
      have heq : raw439step0 = (fun i j => raw439 (permutation140 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw439 permutation140 permutation6
    _ = injectiveMoment H node1138 := by rfl

def raw440 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]

def raw440step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 3, -3], ![1, -2, 1], ![1, 0, -1]]

theorem canonical440 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw440 = injectiveMoment H node662 := by
  calc
    injectiveMoment H raw440 = injectiveMoment H raw440step0 := by
      have heq : raw440step0 = (fun i j => raw440 (permutation140 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw440 permutation140 permutation6
    _ = injectiveMoment H node662 := by rfl

def raw441 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![3, -2, -1]]

def raw441step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 3, -3], ![1, -2, 1], ![1, 0, -1]]

theorem canonical441 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw441 = injectiveMoment H node187 := by
  calc
    injectiveMoment H raw441 = injectiveMoment H raw441step0 := by
      have heq : raw441step0 = (fun i j => raw441 (permutation28 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw441 permutation28 permutation6
    _ = injectiveMoment H node187 := by rfl

def raw442 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, -2, 0], ![2, 1, -3]]

def raw442step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![1, -3, 2], ![1, 0, -1]]

theorem canonical442 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw442 = injectiveMoment H node214 := by
  calc
    injectiveMoment H raw442 = injectiveMoment H raw442step0 := by
      have heq : raw442step0 = (fun i j => raw442 (permutation22 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw442 permutation22 permutation6
    _ = injectiveMoment H node214 := by rfl

def raw443 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]

def raw443step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 2, 0]]

def raw443step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]

theorem canonical443 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw443 = injectiveMoment H node1413 := by
  calc
    injectiveMoment H raw443 = injectiveMoment H raw443step0 := by
      have heq : raw443step0 = -raw443 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw443).symm
    injectiveMoment H raw443step0 = injectiveMoment H raw443step1 := by
      have heq : raw443step1 = (fun i j => raw443step0 (permutation181 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw443step0 permutation181 permutation8
    _ = injectiveMoment H node1413 := by rfl

def raw444 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]

def raw444step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-3, 2, 1]]

def raw444step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]

theorem canonical444 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw444 = injectiveMoment H node349 := by
  calc
    injectiveMoment H raw444 = injectiveMoment H raw444step0 := by
      have heq : raw444step0 = -raw444 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw444).symm
    injectiveMoment H raw444step0 = injectiveMoment H raw444step1 := by
      have heq : raw444step1 = (fun i j => raw444step0 (permutation45 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw444step0 permutation45 permutation8
    _ = injectiveMoment H node349 := by rfl

def raw445 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]

def raw445step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, -1, 1], ![-2, 2, 0], ![-2, 1, 1]]

def raw445step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]

theorem canonical445 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw445 = injectiveMoment H node351 := by
  calc
    injectiveMoment H raw445 = injectiveMoment H raw445step0 := by
      have heq : raw445step0 = -raw445 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw445).symm
    injectiveMoment H raw445step0 = injectiveMoment H raw445step1 := by
      have heq : raw445step1 = (fun i j => raw445step0 (permutation45 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw445step0 permutation45 permutation8
    _ = injectiveMoment H node351 := by rfl

def raw446 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -2, 1], ![3, 0, -3]]

def raw446step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -3, 3], ![0, 3, -3], ![2, -1, -1]]

theorem canonical446 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw446 = injectiveMoment H node220 := by
  calc
    injectiveMoment H raw446 = injectiveMoment H raw446step0 := by
      have heq : raw446step0 = (fun i j => raw446 (permutation22 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw446 permutation22 permutation5
    _ = injectiveMoment H node220 := by rfl

def raw447 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]

def raw447step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]

def raw447step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]

theorem canonical447 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw447 = injectiveMoment H node1409 := by
  calc
    injectiveMoment H raw447 = injectiveMoment H raw447step0 := by
      have heq : raw447step0 = -raw447 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw447).symm
    injectiveMoment H raw447step0 = injectiveMoment H raw447step1 := by
      have heq : raw447step1 = (fun i j => raw447step0 (permutation171 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw447step0 permutation171 permutation8
    _ = injectiveMoment H node1409 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
