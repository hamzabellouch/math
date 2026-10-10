import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes0
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes2
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes6

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw1408 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![1, -1, 0]]

def raw1408step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]

theorem canonical1408 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1408 = injectiveMoment H node443 := by
  calc
    injectiveMoment H raw1408 = injectiveMoment H raw1408step0 := by
      have heq : raw1408step0 = (fun i j => raw1408 (permutation34 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1408 permutation34 permutation3
    _ = injectiveMoment H node443 := by rfl

def raw1409 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 2, -2], ![2, -1, -1]]

theorem canonical1409 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1409 = injectiveMoment H node146 := by
  rfl

def raw1410 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 3, -3], ![1, -2, 1], ![1, 0, -1]]

theorem canonical1410 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1410 = injectiveMoment H node444 := by
  rfl

def raw1411 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0]]

theorem canonical1411 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1411 = injectiveMoment H node445 := by
  rfl

def raw1412 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 3, -3], ![2, -2, 0]]

theorem canonical1412 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1412 = injectiveMoment H node147 := by
  rfl

def raw1413 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![1, -2, 1], ![1, 3, -4]]

theorem canonical1413 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1413 = injectiveMoment H node148 := by
  rfl

def raw1414 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![1, -1, 0], ![0, 1, -1], ![1, 1, -2]]

def raw1414step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

theorem canonical1414 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1414 = injectiveMoment H node440 := by
  calc
    injectiveMoment H raw1414 = injectiveMoment H raw1414step0 := by
      have heq : raw1414step0 = (fun i j => raw1414 (permutation35 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1414 permutation35 permutation3
    _ = injectiveMoment H node440 := by rfl

def raw1415 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![0, 2, -2]]

def raw1415step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]

theorem canonical1415 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1415 = injectiveMoment H node443 := by
  calc
    injectiveMoment H raw1415 = injectiveMoment H raw1415step0 := by
      have heq : raw1415step0 = (fun i j => raw1415 (permutation37 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1415 permutation37 permutation3
    _ = injectiveMoment H node443 := by rfl

def raw1416 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![1, -1, 0], ![1, 2, -3]]

theorem canonical1416 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1416 = injectiveMoment H node149 := by
  rfl

def raw1417 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]

theorem canonical1417 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1417 = injectiveMoment H node150 := by
  rfl

def raw1418 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![1, 1, -2], ![1, 0, -1]]

def raw1418step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]

theorem canonical1418 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1418 = injectiveMoment H node150 := by
  calc
    injectiveMoment H raw1418 = injectiveMoment H raw1418step0 := by
      have heq : raw1418step0 = (fun i j => raw1418 (permutation10 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1418 permutation10 permutation3
    _ = injectiveMoment H node150 := by rfl

def raw1419 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![1, 2, -3], ![1, -1, 0]]

def raw1419step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![1, -1, 0], ![1, 2, -3]]

theorem canonical1419 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1419 = injectiveMoment H node149 := by
  calc
    injectiveMoment H raw1419 = injectiveMoment H raw1419step0 := by
      have heq : raw1419step0 = (fun i j => raw1419 (permutation10 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1419 permutation10 permutation3
    _ = injectiveMoment H node149 := by rfl

def raw1420 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![2, 1, -3]]

def raw1420step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![4, -1, -3]]

def raw1420step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 2, -2], ![1, 1, -2]]

theorem canonical1420 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1420 = injectiveMoment H node52 := by
  calc
    injectiveMoment H raw1420 = injectiveMoment H raw1420step0 := by
      have heq : raw1420step0 = raw1420.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1420).symm
    injectiveMoment H raw1420step0 = injectiveMoment H raw1420step1 := by
      have heq : raw1420step1 = (fun i j => raw1420step0 (permutation7 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1420step0 permutation7 permutation6
    _ = injectiveMoment H node52 := by rfl

def raw1421 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2]]

def raw1421step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![1, 1, -2]]

theorem canonical1421 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1421 = injectiveMoment H node434 := by
  calc
    injectiveMoment H raw1421 = injectiveMoment H raw1421step0 := by
      have heq : raw1421step0 = (fun i j => raw1421 (permutation39 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1421 permutation39 permutation3
    _ = injectiveMoment H node434 := by rfl

def raw1422 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![0, -1, 1], ![2, 1, -3]]

def raw1422step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, -1, 1], ![0, 2, -2], ![2, 1, -3]]

theorem canonical1422 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1422 = injectiveMoment H node140 := by
  calc
    injectiveMoment H raw1422 = injectiveMoment H raw1422step0 := by
      have heq : raw1422step0 = (fun i j => raw1422 (permutation11 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1422 permutation11 permutation3
    _ = injectiveMoment H node140 := by rfl

def raw1423 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![0, 0, 0], ![2, 0, -2]]

def raw1423step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![2, 0, -2]]

theorem canonical1423 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1423 = injectiveMoment H node31 := by
  calc
    injectiveMoment H raw1423 = injectiveMoment H raw1423step0 := by
      have hz : ∀ j, raw1423 (permutation21 0) j = 0 := by decide +kernel
      have heq : raw1423step0 = (fun i j => raw1423 (permutation21 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw1423 permutation21 hz
    _ = injectiveMoment H node31 := by rfl

def raw1424 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]

def raw1424step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, 1, -2]]

theorem canonical1424 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1424 = injectiveMoment H node442 := by
  calc
    injectiveMoment H raw1424 = injectiveMoment H raw1424step0 := by
      have heq : raw1424step0 = (fun i j => raw1424 (permutation39 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1424 permutation39 permutation3
    _ = injectiveMoment H node442 := by rfl

def raw1425 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

def raw1425step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]

theorem canonical1425 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1425 = injectiveMoment H node443 := by
  calc
    injectiveMoment H raw1425 = injectiveMoment H raw1425step0 := by
      have heq : raw1425step0 = (fun i j => raw1425 (permutation39 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1425 permutation39 permutation3
    _ = injectiveMoment H node443 := by rfl

def raw1426 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![0, 1, -1], ![2, -1, -1]]

def raw1426step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 2, -2], ![2, -1, -1]]

theorem canonical1426 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1426 = injectiveMoment H node146 := by
  calc
    injectiveMoment H raw1426 = injectiveMoment H raw1426step0 := by
      have heq : raw1426step0 = (fun i j => raw1426 (permutation11 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1426 permutation11 permutation3
    _ = injectiveMoment H node146 := by rfl

def raw1427 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]

theorem canonical1427 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1427 = injectiveMoment H node446 := by
  rfl

def raw1428 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![0, 2, -2], ![2, -2, 0]]

theorem canonical1428 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1428 = injectiveMoment H node151 := by
  rfl

def raw1429 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![1, -2, 1], ![1, 2, -3]]

theorem canonical1429 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1429 = injectiveMoment H node152 := by
  rfl

def raw1430 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2]]

def raw1430step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![1, -1, 0], ![1, 1, -2]]

theorem canonical1430 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1430 = injectiveMoment H node153 := by
  calc
    injectiveMoment H raw1430 = injectiveMoment H raw1430step0 := by
      have hz : ∀ j, raw1430 (permutation104 0) j = 0 := by decide +kernel
      have heq : raw1430step0 = (fun i j => raw1430 (permutation104 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw1430 permutation104 hz
    _ = injectiveMoment H node153 := by rfl

def raw1431 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1]]

def raw1431step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]

theorem canonical1431 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1431 = injectiveMoment H node443 := by
  calc
    injectiveMoment H raw1431 = injectiveMoment H raw1431step0 := by
      have heq : raw1431step0 = (fun i j => raw1431 (permutation51 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1431 permutation51 permutation3
    _ = injectiveMoment H node443 := by rfl

def raw1432 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![1, -1, 0], ![1, 1, -2]]

theorem canonical1432 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1432 = injectiveMoment H node153 := by
  rfl

def raw1433 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1]]

def raw1433step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 1, -1], ![2, 0, -2]]

theorem canonical1433 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1433 = injectiveMoment H node145 := by
  calc
    injectiveMoment H raw1433 = injectiveMoment H raw1433step0 := by
      have heq : raw1433step0 = (fun i j => raw1433 (permutation12 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1433 permutation12 permutation5
    _ = injectiveMoment H node145 := by rfl

def raw1434 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![1, 1, -2], ![1, -1, 0]]

def raw1434step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![1, -1, 0], ![1, 1, -2]]

theorem canonical1434 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1434 = injectiveMoment H node153 := by
  calc
    injectiveMoment H raw1434 = injectiveMoment H raw1434step0 := by
      have heq : raw1434step0 = (fun i j => raw1434 (permutation10 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1434 permutation10 permutation3
    _ = injectiveMoment H node153 := by rfl

def raw1435 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![2, 0, -2]]

theorem canonical1435 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1435 = injectiveMoment H node31 := by
  rfl

def raw1436 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 3, -3], ![1, -2, 1], ![1, 1, -2]]

theorem canonical1436 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1436 = injectiveMoment H node154 := by
  rfl

def raw1437 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1]]

theorem canonical1437 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1437 = injectiveMoment H node155 := by
  rfl

def raw1438 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 3, -3], ![1, 0, -1], ![1, -1, 0]]

def raw1438step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1]]

theorem canonical1438 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1438 = injectiveMoment H node155 := by
  calc
    injectiveMoment H raw1438 = injectiveMoment H raw1438step0 := by
      have heq : raw1438step0 = (fun i j => raw1438 (permutation10 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1438 permutation10 permutation3
    _ = injectiveMoment H node155 := by rfl

def raw1439 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 3, -3], ![2, -1, -1]]

theorem canonical1439 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1439 = injectiveMoment H node32 := by
  rfl

end MUB6.Certificate.PairSemantics

end OAI
