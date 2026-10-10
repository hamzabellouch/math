import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes0
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes2
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes6

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw1376 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, -1, 1], ![1, -1, 0], ![1, 4, -5]]

theorem canonical1376 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1376 = injectiveMoment H node142 := by
  rfl

def raw1377 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, -1, 1], ![1, 0, -1], ![1, 3, -4]]

theorem canonical1377 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1377 = injectiveMoment H node143 := by
  rfl

def raw1378 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, -1, 1], ![1, 1, -2], ![1, 2, -3]]

theorem canonical1378 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1378 = injectiveMoment H node144 := by
  rfl

def raw1379 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![2, 0, -2]]

def raw1379step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 1, -1], ![2, 0, -2]]

theorem canonical1379 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1379 = injectiveMoment H node145 := by
  calc
    injectiveMoment H raw1379 = injectiveMoment H raw1379step0 := by
      have hz : ∀ j, raw1379 (permutation57 0) j = 0 := by decide +kernel
      have heq : raw1379step0 = (fun i j => raw1379 (permutation57 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw1379 permutation57 hz
    _ = injectiveMoment H node145 := by rfl

def raw1380 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![1, 2, -3]]

def raw1380step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![1, -1, 0], ![1, 2, -3]]

theorem canonical1380 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1380 = injectiveMoment H node149 := by
  calc
    injectiveMoment H raw1380 = injectiveMoment H raw1380step0 := by
      have hz : ∀ j, raw1380 (permutation57 0) j = 0 := by decide +kernel
      have heq : raw1380step0 = (fun i j => raw1380 (permutation57 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw1380 permutation57 hz
    _ = injectiveMoment H node149 := by rfl

def raw1381 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]

def raw1381step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]

theorem canonical1381 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1381 = injectiveMoment H node150 := by
  calc
    injectiveMoment H raw1381 = injectiveMoment H raw1381step0 := by
      have hz : ∀ j, raw1381 (permutation57 0) j = 0 := by decide +kernel
      have heq : raw1381step0 = (fun i j => raw1381 (permutation57 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw1381 permutation57 hz
    _ = injectiveMoment H node150 := by rfl

def raw1382 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 0, 0], ![0, 1, -1], ![2, 1, -3]]

def raw1382step0 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-2, 0, 1, 1], ![4, 0, -1, -3]]

def raw1382step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![4, -1, -3]]

def raw1382step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 2, -2], ![1, 1, -2]]

theorem canonical1382 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1382 = injectiveMoment H node52 := by
  calc
    injectiveMoment H raw1382 = injectiveMoment H raw1382step0 := by
      have heq : raw1382step0 = raw1382.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1382).symm
    injectiveMoment H raw1382step0 = injectiveMoment H raw1382step1 := by
      have hz : ∀ i, raw1382step0 i (permutation15 0) = 0 := by decide +kernel
      have heq : raw1382step1 = (fun i j => raw1382step0 i (permutation15 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw1382step0 permutation15 hz
    injectiveMoment H raw1382step1 = injectiveMoment H raw1382step2 := by
      have heq : raw1382step2 = (fun i j => raw1382step1 (permutation7 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1382step1 permutation7 permutation6
    _ = injectiveMoment H node52 := by rfl

def raw1383 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 0, 0], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1]]

def raw1383step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1]]

def raw1383step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 1, -1], ![2, 0, -2]]

theorem canonical1383 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1383 = injectiveMoment H node145 := by
  calc
    injectiveMoment H raw1383 = injectiveMoment H raw1383step0 := by
      have hz : ∀ j, raw1383 (permutation57 0) j = 0 := by decide +kernel
      have heq : raw1383step0 = (fun i j => raw1383 (permutation57 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw1383 permutation57 hz
    injectiveMoment H raw1383step0 = injectiveMoment H raw1383step1 := by
      have heq : raw1383step1 = (fun i j => raw1383step0 (permutation12 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1383step0 permutation12 permutation5
    _ = injectiveMoment H node145 := by rfl

def raw1384 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 0, 0], ![0, 2, -2], ![2, 0, -2]]

def raw1384step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![2, 0, -2]]

theorem canonical1384 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1384 = injectiveMoment H node31 := by
  calc
    injectiveMoment H raw1384 = injectiveMoment H raw1384step0 := by
      have hz : ∀ j, raw1384 (permutation15 0) j = 0 := by decide +kernel
      have heq : raw1384step0 = (fun i j => raw1384 (permutation15 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw1384 permutation15 hz
    _ = injectiveMoment H node31 := by rfl

def raw1385 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 0, 0], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1]]

def raw1385step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1]]

theorem canonical1385 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1385 = injectiveMoment H node155 := by
  calc
    injectiveMoment H raw1385 = injectiveMoment H raw1385step0 := by
      have hz : ∀ j, raw1385 (permutation57 0) j = 0 := by decide +kernel
      have heq : raw1385step0 = (fun i j => raw1385 (permutation57 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw1385 permutation57 hz
    _ = injectiveMoment H node155 := by rfl

def raw1386 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 0, 0], ![1, -1, 0], ![1, 3, -4]]

def raw1386step0 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-2, 0, -1, 3], ![4, 0, 0, -4]]

def raw1386step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, -1, 3], ![4, 0, -4]]

def raw1386step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 4, -4], ![1, -2, 1]]

theorem canonical1386 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1386 = injectiveMoment H node59 := by
  calc
    injectiveMoment H raw1386 = injectiveMoment H raw1386step0 := by
      have heq : raw1386step0 = raw1386.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1386).symm
    injectiveMoment H raw1386step0 = injectiveMoment H raw1386step1 := by
      have hz : ∀ i, raw1386step0 i (permutation15 0) = 0 := by decide +kernel
      have heq : raw1386step1 = (fun i j => raw1386step0 i (permutation15 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw1386step0 permutation15 hz
    injectiveMoment H raw1386step1 = injectiveMoment H raw1386step2 := by
      have heq : raw1386step2 = (fun i j => raw1386step1 (permutation6 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1386step1 permutation6 permutation5
    _ = injectiveMoment H node59 := by rfl

def raw1387 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 0, 0], ![1, 0, -1], ![1, 2, -3]]

def raw1387step0 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-2, 0, 0, 2], ![4, 0, -1, -3]]

def raw1387step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![4, -1, -3]]

def raw1387step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 2, -2], ![1, 1, -2]]

theorem canonical1387 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1387 = injectiveMoment H node52 := by
  calc
    injectiveMoment H raw1387 = injectiveMoment H raw1387step0 := by
      have heq : raw1387step0 = raw1387.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1387).symm
    injectiveMoment H raw1387step0 = injectiveMoment H raw1387step1 := by
      have hz : ∀ i, raw1387step0 i (permutation15 0) = 0 := by decide +kernel
      have heq : raw1387step1 = (fun i j => raw1387step0 i (permutation15 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw1387step0 permutation15 hz
    injectiveMoment H raw1387step1 = injectiveMoment H raw1387step2 := by
      have heq : raw1387step2 = (fun i j => raw1387step1 (permutation8 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1387step1 permutation8 permutation6
    _ = injectiveMoment H node52 := by rfl

def raw1388 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 0, 0], ![1, 1, -2], ![1, 1, -2]]

def raw1388step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -2, 4], ![1, 1, -2], ![1, 1, -2]]

theorem canonical1388 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1388 = injectiveMoment H node35 := by
  calc
    injectiveMoment H raw1388 = injectiveMoment H raw1388step0 := by
      have hz : ∀ j, raw1388 (permutation15 0) j = 0 := by decide +kernel
      have heq : raw1388step0 = (fun i j => raw1388 (permutation15 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw1388 permutation15 hz
    _ = injectiveMoment H node35 := by rfl

def raw1389 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 0, 0], ![2, 2, -4]]

def raw1389step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![4, 0, -4]]

def raw1389step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![4, -4]]

def raw1389step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-4, 4], ![2, -2], ![2, -2]]

theorem canonical1389 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1389 = injectiveMoment H node9 := by
  calc
    injectiveMoment H raw1389 = injectiveMoment H raw1389step0 := by
      have heq : raw1389step0 = raw1389.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1389).symm
    injectiveMoment H raw1389step0 = injectiveMoment H raw1389step1 := by
      have hz : ∀ i, raw1389step0 i (permutation5 0) = 0 := by decide +kernel
      have heq : raw1389step1 = (fun i j => raw1389step0 i (permutation5 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw1389step0 permutation5 hz
    injectiveMoment H raw1389step1 = injectiveMoment H raw1389step2 := by
      have heq : raw1389step2 = (fun i j => raw1389step1 (permutation7 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1389step1 permutation7 permutation2
    _ = injectiveMoment H node9 := by rfl

def raw1390 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![-1, 2, -1], ![1, -1, 0], ![2, 0, -2]]

def raw1390step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]

theorem canonical1390 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1390 = injectiveMoment H node421 := by
  calc
    injectiveMoment H raw1390 = injectiveMoment H raw1390step0 := by
      have heq : raw1390step0 = (fun i j => raw1390 (permutation49 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1390 permutation49 permutation5
    _ = injectiveMoment H node421 := by rfl

def raw1391 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1]]

def raw1391step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]

theorem canonical1391 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1391 = injectiveMoment H node422 := by
  calc
    injectiveMoment H raw1391 = injectiveMoment H raw1391step0 := by
      have heq : raw1391step0 = (fun i j => raw1391 (permutation39 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1391 permutation39 permutation3
    _ = injectiveMoment H node422 := by rfl

def raw1392 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, -1, 1], ![2, 2, -4]]

def raw1392step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, -1, 1], ![0, 1, -1], ![2, 2, -4]]

theorem canonical1392 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1392 = injectiveMoment H node139 := by
  calc
    injectiveMoment H raw1392 = injectiveMoment H raw1392step0 := by
      have heq : raw1392step0 = (fun i j => raw1392 (permutation11 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1392 permutation11 permutation3
    _ = injectiveMoment H node139 := by rfl

def raw1393 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 0, 0], ![0, 1, -1], ![2, 0, -2]]

def raw1393step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 1, -1], ![2, 0, -2]]

theorem canonical1393 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1393 = injectiveMoment H node145 := by
  calc
    injectiveMoment H raw1393 = injectiveMoment H raw1393step0 := by
      have hz : ∀ j, raw1393 (permutation80 0) j = 0 := by decide +kernel
      have heq : raw1393step0 = (fun i j => raw1393 (permutation80 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw1393 permutation80 hz
    _ = injectiveMoment H node145 := by rfl

def raw1394 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, 2, -3]]

def raw1394step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![1, -1, 0], ![1, 2, -3]]

theorem canonical1394 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1394 = injectiveMoment H node149 := by
  calc
    injectiveMoment H raw1394 = injectiveMoment H raw1394step0 := by
      have hz : ∀ j, raw1394 (permutation80 0) j = 0 := by decide +kernel
      have heq : raw1394step0 = (fun i j => raw1394 (permutation80 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw1394 permutation80 hz
    _ = injectiveMoment H node149 := by rfl

def raw1395 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![1, 1, -2]]

def raw1395step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]

theorem canonical1395 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1395 = injectiveMoment H node150 := by
  calc
    injectiveMoment H raw1395 = injectiveMoment H raw1395step0 := by
      have hz : ∀ j, raw1395 (permutation80 0) j = 0 := by decide +kernel
      have heq : raw1395step0 = (fun i j => raw1395 (permutation80 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw1395 permutation80 hz
    _ = injectiveMoment H node150 := by rfl

def raw1396 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 0, 0], ![2, 1, -3]]

def raw1396step0 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-2, 1, 0, 1], ![4, -1, 0, -3]]

def raw1396step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![4, -1, -3]]

def raw1396step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 2, -2], ![1, 1, -2]]

theorem canonical1396 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1396 = injectiveMoment H node52 := by
  calc
    injectiveMoment H raw1396 = injectiveMoment H raw1396step0 := by
      have heq : raw1396step0 = raw1396.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1396).symm
    injectiveMoment H raw1396step0 = injectiveMoment H raw1396step1 := by
      have hz : ∀ i, raw1396step0 i (permutation21 0) = 0 := by decide +kernel
      have heq : raw1396step1 = (fun i j => raw1396step0 i (permutation21 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw1396step0 permutation21 hz
    injectiveMoment H raw1396step1 = injectiveMoment H raw1396step2 := by
      have heq : raw1396step2 = (fun i j => raw1396step1 (permutation7 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1396step1 permutation7 permutation6
    _ = injectiveMoment H node52 := by rfl

def raw1397 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2]]

def raw1397step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 1, -1], ![2, 0, -2]]

theorem canonical1397 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1397 = injectiveMoment H node145 := by
  calc
    injectiveMoment H raw1397 = injectiveMoment H raw1397step0 := by
      have hz : ∀ j, raw1397 (permutation104 0) j = 0 := by decide +kernel
      have heq : raw1397step0 = (fun i j => raw1397 (permutation104 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw1397 permutation104 hz
    _ = injectiveMoment H node145 := by rfl

def raw1398 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]

theorem canonical1398 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1398 = injectiveMoment H node437 := by
  rfl

def raw1399 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]

theorem canonical1399 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1399 = injectiveMoment H node438 := by
  rfl

def raw1400 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 2, -3]]

theorem canonical1400 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1400 = injectiveMoment H node439 := by
  rfl

def raw1401 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

theorem canonical1401 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1401 = injectiveMoment H node440 := by
  rfl

def raw1402 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]

theorem canonical1402 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1402 = injectiveMoment H node441 := by
  rfl

def raw1403 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 1, -1], ![2, 0, -2]]

theorem canonical1403 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1403 = injectiveMoment H node145 := by
  rfl

def raw1404 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 2, -2], ![0, -1, 1], ![2, 0, -2]]

def raw1404step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![2, 0, -2]]

theorem canonical1404 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1404 = injectiveMoment H node430 := by
  calc
    injectiveMoment H raw1404 = injectiveMoment H raw1404step0 := by
      have heq : raw1404step0 = (fun i j => raw1404 (permutation45 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1404 permutation45 permutation3
    _ = injectiveMoment H node430 := by rfl

def raw1405 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 2, -2], ![0, 0, 0], ![2, -1, -1]]

def raw1405step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 2, -2], ![2, -1, -1]]

theorem canonical1405 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1405 = injectiveMoment H node146 := by
  calc
    injectiveMoment H raw1405 = injectiveMoment H raw1405step0 := by
      have hz : ∀ j, raw1405 (permutation104 0) j = 0 := by decide +kernel
      have heq : raw1405step0 = (fun i j => raw1405 (permutation104 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw1405 permutation104 hz
    _ = injectiveMoment H node146 := by rfl

def raw1406 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, 1, -2]]

theorem canonical1406 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1406 = injectiveMoment H node442 := by
  rfl

def raw1407 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]

theorem canonical1407 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1407 = injectiveMoment H node443 := by
  rfl

end MUB6.Certificate.PairSemantics

end OAI
