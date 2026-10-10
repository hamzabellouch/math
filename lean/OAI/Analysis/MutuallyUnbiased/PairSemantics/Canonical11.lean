import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes1
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes2
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes3
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes5
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes9
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes21
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes32

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw352 : Matrix (Fin 3) (Fin 4) ℤ := ![![-3, 0, 1, 2], ![1, 2, -3, 0], ![2, -2, 2, -2]]

def raw352step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -3, 2], ![2, 0, -2]]

theorem canonical352 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw352 = injectiveMoment H node110 := by
  calc
    injectiveMoment H raw352 = injectiveMoment H raw352step0 := by
      have heq : raw352step0 = raw352.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw352).symm
    _ = injectiveMoment H node110 := by rfl

def raw353 : Matrix (Fin 3) (Fin 4) ℤ := ![![-3, 0, 1, 2], ![1, 2, -2, -1], ![2, -2, 1, -1]]

def raw353step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]

theorem canonical353 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw353 = injectiveMoment H node111 := by
  calc
    injectiveMoment H raw353 = injectiveMoment H raw353step0 := by
      have heq : raw353step0 = raw353.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw353).symm
    _ = injectiveMoment H node111 := by rfl

def raw354 : Matrix (Fin 3) (Fin 4) ℤ := ![![-3, 0, 1, 2], ![2, -2, 1, -1], ![1, 2, -2, -1]]

def raw354step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]

def raw354step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]

theorem canonical354 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw354 = injectiveMoment H node111 := by
  calc
    injectiveMoment H raw354 = injectiveMoment H raw354step0 := by
      have heq : raw354step0 = raw354.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw354).symm
    injectiveMoment H raw354step0 = injectiveMoment H raw354step1 := by
      have heq : raw354step1 = (fun i j => raw354step0 (permutation9 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw354step0 permutation9 permutation4
    _ = injectiveMoment H node111 := by rfl

def raw355 : Matrix (Fin 3) (Fin 4) ℤ := ![![-3, 0, 2, 1], ![-2, 2, -1, 1], ![5, -2, -1, -2]]

def raw355step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![2, -1, -1], ![1, 1, -2]]

def raw355step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]

theorem canonical355 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw355 = injectiveMoment H node74 := by
  calc
    injectiveMoment H raw355 = injectiveMoment H raw355step0 := by
      have heq : raw355step0 = raw355.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw355).symm
    injectiveMoment H raw355step0 = injectiveMoment H raw355step1 := by
      have heq : raw355step1 = (fun i j => raw355step0 (permutation10 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw355step0 permutation10 permutation3
    _ = injectiveMoment H node74 := by rfl

def raw356 : Matrix (Fin 3) (Fin 4) ℤ := ![![-3, 0, 2, 1], ![-1, 2, -2, 1], ![4, -2, 0, -2]]

def raw356step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![2, -2, 0], ![1, 1, -2]]

def raw356step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]

theorem canonical356 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw356 = injectiveMoment H node85 := by
  calc
    injectiveMoment H raw356 = injectiveMoment H raw356step0 := by
      have heq : raw356step0 = raw356.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw356).symm
    injectiveMoment H raw356step0 = injectiveMoment H raw356step1 := by
      have heq : raw356step1 = (fun i j => raw356step0 (permutation10 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw356step0 permutation10 permutation3
    _ = injectiveMoment H node85 := by rfl

def raw357 : Matrix (Fin 3) (Fin 4) ℤ := ![![-3, 0, 2, 1], ![-1, 2, 1, -2], ![4, -2, -3, 1]]

def raw357step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![2, 1, -3], ![1, -2, 1]]

def raw357step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -2, 1], ![2, 1, -3]]

theorem canonical357 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw357 = injectiveMoment H node84 := by
  calc
    injectiveMoment H raw357 = injectiveMoment H raw357step0 := by
      have heq : raw357step0 = raw357.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw357).symm
    injectiveMoment H raw357step0 = injectiveMoment H raw357step1 := by
      have heq : raw357step1 = (fun i j => raw357step0 (permutation10 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw357step0 permutation10 permutation3
    _ = injectiveMoment H node84 := by rfl

def raw358 : Matrix (Fin 3) (Fin 4) ℤ := ![![-3, 0, 2, 1], ![-1, 3, 0, -2], ![4, -3, -2, 1]]

def raw358step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![2, 0, -2], ![1, -2, 1]]

def raw358step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, -2, 1], ![2, 0, -2]]

theorem canonical358 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw358 = injectiveMoment H node86 := by
  calc
    injectiveMoment H raw358 = injectiveMoment H raw358step0 := by
      have heq : raw358step0 = raw358.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw358).symm
    injectiveMoment H raw358step0 = injectiveMoment H raw358step1 := by
      have heq : raw358step1 = (fun i j => raw358step0 (permutation10 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw358step0 permutation10 permutation3
    _ = injectiveMoment H node86 := by rfl

def raw359 : Matrix (Fin 3) (Fin 4) ℤ := ![![-3, 0, 2, 1], ![0, -2, 0, 2], ![3, 2, -2, -3]]

def raw359step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![2, 0, -2], ![1, 2, -3]]

def raw359step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![-2, 0, 2], ![-1, -2, 3]]

def raw359step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 3, -3], ![2, 0, -2]]

theorem canonical359 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw359 = injectiveMoment H node163 := by
  calc
    injectiveMoment H raw359 = injectiveMoment H raw359step0 := by
      have heq : raw359step0 = raw359.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw359).symm
    injectiveMoment H raw359step0 = injectiveMoment H raw359step1 := by
      have heq : raw359step1 = -raw359step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw359step0).symm
    injectiveMoment H raw359step1 = injectiveMoment H raw359step2 := by
      have heq : raw359step2 = (fun i j => raw359step1 (permutation31 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw359step1 permutation31 permutation5
    _ = injectiveMoment H node163 := by rfl

def raw360 : Matrix (Fin 3) (Fin 4) ℤ := ![![-3, 0, 2, 1], ![0, -2, 1, 1], ![3, 2, -3, -2]]

def raw360step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![2, 1, -3], ![1, 1, -2]]

def raw360step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![1, 1, -2], ![1, 2, -3]]

theorem canonical360 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw360 = injectiveMoment H node196 := by
  calc
    injectiveMoment H raw360 = injectiveMoment H raw360step0 := by
      have heq : raw360step0 = raw360.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw360).symm
    injectiveMoment H raw360step0 = injectiveMoment H raw360step1 := by
      have heq : raw360step1 = (fun i j => raw360step0 (permutation16 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw360step0 permutation16 permutation5
    _ = injectiveMoment H node196 := by rfl

def raw361 : Matrix (Fin 3) (Fin 4) ℤ := ![![-3, 0, 2, 1], ![0, 2, -2, 0], ![3, -2, 0, -1]]

def raw361step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![2, -2, 0], ![1, 0, -1]]

def raw361step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 3, -3], ![2, -2, 0]]

theorem canonical361 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw361 = injectiveMoment H node204 := by
  calc
    injectiveMoment H raw361 = injectiveMoment H raw361step0 := by
      have heq : raw361step0 = raw361.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw361).symm
    injectiveMoment H raw361step0 = injectiveMoment H raw361step1 := by
      have heq : raw361step1 = (fun i j => raw361step0 (permutation25 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw361step0 permutation25 permutation6
    _ = injectiveMoment H node204 := by rfl

def raw362 : Matrix (Fin 3) (Fin 4) ℤ := ![![-3, 0, 2, 1], ![0, 2, 0, -2], ![3, -2, -2, 1]]

def raw362step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![2, 0, -2], ![1, -2, 1]]

def raw362step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-2, 0, 2], ![-1, 2, -1]]

def raw362step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 3, -3], ![2, -1, -1]]

theorem canonical362 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw362 = injectiveMoment H node198 := by
  calc
    injectiveMoment H raw362 = injectiveMoment H raw362step0 := by
      have heq : raw362step0 = raw362.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw362).symm
    injectiveMoment H raw362step0 = injectiveMoment H raw362step1 := by
      have heq : raw362step1 = -raw362step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw362step0).symm
    injectiveMoment H raw362step1 = injectiveMoment H raw362step2 := by
      have heq : raw362step2 = (fun i j => raw362step1 (permutation17 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw362step1 permutation17 permutation5
    _ = injectiveMoment H node198 := by rfl

def raw363 : Matrix (Fin 3) (Fin 4) ℤ := ![![-3, 0, 2, 1], ![0, 3, -1, -2], ![3, -3, -1, 1]]

def raw363step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![2, -1, -1], ![1, -2, 1]]

def raw363step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![1, -2, 1], ![2, -1, -1]]

theorem canonical363 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw363 = injectiveMoment H node98 := by
  calc
    injectiveMoment H raw363 = injectiveMoment H raw363step0 := by
      have heq : raw363step0 = raw363.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw363).symm
    injectiveMoment H raw363step0 = injectiveMoment H raw363step1 := by
      have heq : raw363step1 = (fun i j => raw363step0 (permutation10 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw363step0 permutation10 permutation3
    _ = injectiveMoment H node98 := by rfl

def raw364 : Matrix (Fin 3) (Fin 4) ℤ := ![![-3, 0, 2, 1], ![0, 4, -2, -2], ![3, -4, 0, 1]]

def raw364step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 4, -4], ![2, -2, 0], ![1, -2, 1]]

def raw364step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 4, -4], ![1, -2, 1], ![2, -2, 0]]

theorem canonical364 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw364 = injectiveMoment H node99 := by
  calc
    injectiveMoment H raw364 = injectiveMoment H raw364step0 := by
      have heq : raw364step0 = raw364.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw364).symm
    injectiveMoment H raw364step0 = injectiveMoment H raw364step1 := by
      have heq : raw364step1 = (fun i j => raw364step0 (permutation10 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw364step0 permutation10 permutation3
    _ = injectiveMoment H node99 := by rfl

def raw365 : Matrix (Fin 3) (Fin 4) ℤ := ![![-3, 0, 2, 1], ![1, -2, 0, 1], ![2, 2, -2, -2]]

def raw365step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![2, 0, -2], ![1, 1, -2]]

def raw365step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![1, -3, 2], ![1, 1, -2]]

theorem canonical365 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw365 = injectiveMoment H node212 := by
  calc
    injectiveMoment H raw365 = injectiveMoment H raw365step0 := by
      have heq : raw365step0 = raw365.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw365).symm
    injectiveMoment H raw365step0 = injectiveMoment H raw365step1 := by
      have heq : raw365step1 = (fun i j => raw365step0 (permutation17 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw365step0 permutation17 permutation5
    _ = injectiveMoment H node212 := by rfl

def raw366 : Matrix (Fin 3) (Fin 4) ℤ := ![![-3, 0, 2, 1], ![1, 2, -2, -1], ![2, -2, 0, 0]]

def raw366step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![2, -2, 0], ![1, -1, 0]]

def raw366step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -2, 2], ![-2, 2, 0], ![-1, 1, 0]]

def raw366step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]

theorem canonical366 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw366 = injectiveMoment H node177 := by
  calc
    injectiveMoment H raw366 = injectiveMoment H raw366step0 := by
      have heq : raw366step0 = raw366.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw366).symm
    injectiveMoment H raw366step0 = injectiveMoment H raw366step1 := by
      have heq : raw366step1 = -raw366step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw366step0).symm
    injectiveMoment H raw366step1 = injectiveMoment H raw366step2 := by
      have heq : raw366step2 = (fun i j => raw366step1 (permutation14 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw366step1 permutation14 permutation8
    _ = injectiveMoment H node177 := by rfl

def raw367 : Matrix (Fin 3) (Fin 4) ℤ := ![![-3, 0, 2, 1], ![1, 2, -1, -2], ![2, -2, -1, 1]]

def raw367step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![2, -1, -1], ![1, -2, 1]]

def raw367step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]

theorem canonical367 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw367 = injectiveMoment H node111 := by
  calc
    injectiveMoment H raw367 = injectiveMoment H raw367step0 := by
      have heq : raw367step0 = raw367.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw367).symm
    injectiveMoment H raw367step0 = injectiveMoment H raw367step1 := by
      have heq : raw367step1 = (fun i j => raw367step0 (permutation10 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw367step0 permutation10 permutation3
    _ = injectiveMoment H node111 := by rfl

def raw368 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]

def raw368step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-3, 1, 2]]

def raw368step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]

theorem canonical368 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw368 = injectiveMoment H node1392 := by
  calc
    injectiveMoment H raw368 = injectiveMoment H raw368step0 := by
      have heq : raw368step0 = -raw368 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw368).symm
    injectiveMoment H raw368step0 = injectiveMoment H raw368step1 := by
      have heq : raw368step1 = (fun i j => raw368step0 (permutation158 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw368step0 permutation158 permutation8
    _ = injectiveMoment H node1392 := by rfl

def raw369 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]

def raw369step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 2, 1]]

def raw369step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]

theorem canonical369 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw369 = injectiveMoment H node1395 := by
  calc
    injectiveMoment H raw369 = injectiveMoment H raw369step0 := by
      have heq : raw369step0 = -raw369 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw369).symm
    injectiveMoment H raw369step0 = injectiveMoment H raw369step1 := by
      have heq : raw369step1 = (fun i j => raw369step0 (permutation156 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw369step0 permutation156 permutation8
    _ = injectiveMoment H node1395 := by rfl

def raw370 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]

def raw370step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, 2, 0], ![-2, 0, 2]]

def raw370step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]

theorem canonical370 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw370 = injectiveMoment H node1394 := by
  calc
    injectiveMoment H raw370 = injectiveMoment H raw370step0 := by
      have heq : raw370step0 = -raw370 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw370).symm
    injectiveMoment H raw370step0 = injectiveMoment H raw370step1 := by
      have heq : raw370step1 = (fun i j => raw370step0 (permutation158 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw370step0 permutation158 permutation8
    _ = injectiveMoment H node1394 := by rfl

def raw371 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]

def raw371step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-3, 3, 0]]

def raw371step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]

theorem canonical371 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw371 = injectiveMoment H node1397 := by
  calc
    injectiveMoment H raw371 = injectiveMoment H raw371step0 := by
      have heq : raw371step0 = -raw371 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw371).symm
    injectiveMoment H raw371step0 = injectiveMoment H raw371step1 := by
      have heq : raw371step1 = (fun i j => raw371step0 (permutation165 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw371step0 permutation165 permutation8
    _ = injectiveMoment H node1397 := by rfl

def raw372 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]

def raw372step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0], ![-2, 1, 1]]

def raw372step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]

theorem canonical372 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw372 = injectiveMoment H node1396 := by
  calc
    injectiveMoment H raw372 = injectiveMoment H raw372step0 := by
      have heq : raw372step0 = -raw372 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw372).symm
    injectiveMoment H raw372step0 = injectiveMoment H raw372step1 := by
      have heq : raw372step1 = (fun i j => raw372step0 (permutation162 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw372step0 permutation162 permutation8
    _ = injectiveMoment H node1396 := by rfl

def raw373 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]

def raw373step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![0, -1, 1], ![-2, 2, 0], ![-3, 1, 2]]

def raw373step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]

theorem canonical373 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw373 = injectiveMoment H node328 := by
  calc
    injectiveMoment H raw373 = injectiveMoment H raw373step0 := by
      have heq : raw373step0 = -raw373 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw373).symm
    injectiveMoment H raw373step0 = injectiveMoment H raw373step1 := by
      have heq : raw373step1 = (fun i j => raw373step0 (permutation35 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw373step0 permutation35 permutation8
    _ = injectiveMoment H node328 := by rfl

def raw374 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]

def raw374step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![0, -1, 1], ![-2, 1, 1], ![-3, 2, 1]]

def raw374step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]

theorem canonical374 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw374 = injectiveMoment H node332 := by
  calc
    injectiveMoment H raw374 = injectiveMoment H raw374step0 := by
      have heq : raw374step0 = -raw374 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw374).symm
    injectiveMoment H raw374step0 = injectiveMoment H raw374step1 := by
      have heq : raw374step1 = (fun i j => raw374step0 (permutation33 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw374step0 permutation33 permutation8
    _ = injectiveMoment H node332 := by rfl

def raw375 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]

def raw375step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 3, -3], ![1, -1, 0], ![2, 0, -2]]

theorem canonical375 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw375 = injectiveMoment H node330 := by
  calc
    injectiveMoment H raw375 = injectiveMoment H raw375step0 := by
      have heq : raw375step0 = (fun i j => raw375 (permutation146 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw375 permutation146 permutation6
    _ = injectiveMoment H node330 := by rfl

def raw376 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]

def raw376step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]

def raw376step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1]]

theorem canonical376 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw376 = injectiveMoment H node2111 := by
  calc
    injectiveMoment H raw376 = injectiveMoment H raw376step0 := by
      have heq : raw376step0 = -raw376 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw376).symm
    injectiveMoment H raw376step0 = injectiveMoment H raw376step1 := by
      have heq : raw376step1 = (fun i j => raw376step0 (permutation206 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw376step0 permutation206 permutation6
    _ = injectiveMoment H node2111 := by rfl

def raw377 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]

def raw377step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]

def raw377step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]

theorem canonical377 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw377 = injectiveMoment H node1393 := by
  calc
    injectiveMoment H raw377 = injectiveMoment H raw377step0 := by
      have heq : raw377step0 = -raw377 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw377).symm
    injectiveMoment H raw377step0 = injectiveMoment H raw377step1 := by
      have heq : raw377step1 = (fun i j => raw377step0 (permutation152 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw377step0 permutation152 permutation8
    _ = injectiveMoment H node1393 := by rfl

def raw378 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]

def raw378step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-1, 1, 0], ![-1, 1, 0], ![-3, 0, 3]]

def raw378step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![0, 3, -3], ![1, 0, -1], ![1, 0, -1]]

theorem canonical378 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw378 = injectiveMoment H node636 := by
  calc
    injectiveMoment H raw378 = injectiveMoment H raw378step0 := by
      have heq : raw378step0 = -raw378 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw378).symm
    injectiveMoment H raw378step0 = injectiveMoment H raw378step1 := by
      have heq : raw378step1 = (fun i j => raw378step0 (permutation61 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw378step0 permutation61 permutation6
    _ = injectiveMoment H node636 := by rfl

def raw379 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]

def raw379step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]

def raw379step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]

theorem canonical379 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw379 = injectiveMoment H node2110 := by
  calc
    injectiveMoment H raw379 = injectiveMoment H raw379step0 := by
      have heq : raw379step0 = -raw379 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw379).symm
    injectiveMoment H raw379step0 = injectiveMoment H raw379step1 := by
      have heq : raw379step1 = (fun i j => raw379step0 (permutation204 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw379step0 permutation204 permutation6
    _ = injectiveMoment H node2110 := by rfl

def raw380 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]

def raw380step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]

def raw380step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![0, 1, -1], ![1, 0, -1], ![1, 2, -3]]

theorem canonical380 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw380 = injectiveMoment H node633 := by
  calc
    injectiveMoment H raw380 = injectiveMoment H raw380step0 := by
      have heq : raw380step0 = -raw380 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw380).symm
    injectiveMoment H raw380step0 = injectiveMoment H raw380step1 := by
      have heq : raw380step1 = (fun i j => raw380step0 (permutation59 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw380step0 permutation59 permutation6
    _ = injectiveMoment H node633 := by rfl

def raw381 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]

def raw381step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-1, 1, 0], ![-1, -1, 2], ![-3, 2, 1]]

def raw381step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]

theorem canonical381 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw381 = injectiveMoment H node327 := by
  calc
    injectiveMoment H raw381 = injectiveMoment H raw381step0 := by
      have heq : raw381step0 = -raw381 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw381).symm
    injectiveMoment H raw381step0 = injectiveMoment H raw381step1 := by
      have heq : raw381step1 = (fun i j => raw381step0 (permutation34 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw381step0 permutation34 permutation8
    _ = injectiveMoment H node327 := by rfl

def raw382 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]

def raw382step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-1, 1, 0], ![-2, 2, 0], ![-2, -1, 3]]

def raw382step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![3, -1, -2]]

theorem canonical382 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw382 = injectiveMoment H node325 := by
  calc
    injectiveMoment H raw382 = injectiveMoment H raw382step0 := by
      have heq : raw382step0 = -raw382 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw382).symm
    injectiveMoment H raw382step0 = injectiveMoment H raw382step1 := by
      have heq : raw382step1 = (fun i j => raw382step0 (permutation33 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw382step0 permutation33 permutation8
    _ = injectiveMoment H node325 := by rfl

def raw383 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]

def raw383step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-1, 1, 0], ![-2, 1, 1], ![-2, 0, 2]]

def raw383step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![0, 2, -2], ![1, 0, -1], ![1, 1, -2]]

theorem canonical383 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw383 = injectiveMoment H node635 := by
  calc
    injectiveMoment H raw383 = injectiveMoment H raw383step0 := by
      have heq : raw383step0 = -raw383 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw383).symm
    injectiveMoment H raw383step0 = injectiveMoment H raw383step1 := by
      have heq : raw383step1 = (fun i j => raw383step0 (permutation61 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw383step0 permutation61 permutation6
    _ = injectiveMoment H node635 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
