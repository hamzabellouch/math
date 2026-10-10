import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes0
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes1
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes2
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes5
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes6

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw1344 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]

theorem canonical1344 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1344 = injectiveMoment H node423 := by
  rfl

def raw1345 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![0, 2, -2], ![2, -2, 0], ![1, 0, -1]]

def raw1345step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]

theorem canonical1345 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1345 = injectiveMoment H node424 := by
  calc
    injectiveMoment H raw1345 = injectiveMoment H raw1345step0 := by
      have heq : raw1345step0 = (fun i j => raw1345 (permutation34 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1345 permutation34 permutation3
    _ = injectiveMoment H node424 := by rfl

def raw1346 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![0, 2, -2], ![3, -2, -1]]

def raw1346step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -2, 1], ![0, -2, 2], ![-3, 2, 1]]

def raw1346step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, 1, -2], ![2, -4, 2]]

theorem canonical1346 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw1346 = injectiveMoment H node112 := by
  calc
    injectiveMoment H raw1346 = injectiveMoment H raw1346step0 := by
      have heq : raw1346step0 = -raw1346 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw1346).symm
    injectiveMoment H raw1346step0 = injectiveMoment H raw1346step1 := by
      have heq : raw1346step1 = (fun i j => raw1346step0 (permutation32 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1346step0 permutation32 permutation4
    _ = injectiveMoment H node112 := by rfl

def raw1347 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]

theorem canonical1347 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1347 = injectiveMoment H node425 := by
  rfl

def raw1348 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]

def raw1348step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]

theorem canonical1348 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1348 = injectiveMoment H node419 := by
  calc
    injectiveMoment H raw1348 = injectiveMoment H raw1348step0 := by
      have heq : raw1348step0 = (fun i j => raw1348 (permutation42 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1348 permutation42 permutation5
    _ = injectiveMoment H node419 := by rfl

def raw1349 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![1, -1, 0], ![2, 1, -3]]

def raw1349step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 2, -3], ![2, -1, -1]]

theorem canonical1349 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1349 = injectiveMoment H node132 := by
  calc
    injectiveMoment H raw1349 = injectiveMoment H raw1349step0 := by
      have heq : raw1349step0 = (fun i j => raw1349 (permutation12 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1349 permutation12 permutation5
    _ = injectiveMoment H node132 := by rfl

def raw1350 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![1, 0, -1], ![1, -1, 0], ![1, 1, -2]]

def raw1350step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]

theorem canonical1350 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1350 = injectiveMoment H node419 := by
  calc
    injectiveMoment H raw1350 = injectiveMoment H raw1350step0 := by
      have heq : raw1350step0 = (fun i j => raw1350 (permutation48 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1350 permutation48 permutation5
    _ = injectiveMoment H node419 := by rfl

def raw1351 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![1, 0, -1], ![2, 0, -2]]

def raw1351step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 2, -2], ![2, -1, -1]]

theorem canonical1351 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1351 = injectiveMoment H node146 := by
  calc
    injectiveMoment H raw1351 = injectiveMoment H raw1351step0 := by
      have heq : raw1351step0 = (fun i j => raw1351 (permutation12 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1351 permutation12 permutation5
    _ = injectiveMoment H node146 := by rfl

def raw1352 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![1, 1, -2], ![1, -1, 0], ![1, 0, -1]]

def raw1352step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]

theorem canonical1352 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1352 = injectiveMoment H node419 := by
  calc
    injectiveMoment H raw1352 = injectiveMoment H raw1352step0 := by
      have heq : raw1352step0 = (fun i j => raw1352 (permutation50 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1352 permutation50 permutation5
    _ = injectiveMoment H node419 := by rfl

def raw1353 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![1, 1, -2], ![2, -1, -1]]

theorem canonical1353 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1353 = injectiveMoment H node134 := by
  rfl

def raw1354 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![1, 2, -3], ![2, -2, 0]]

theorem canonical1354 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1354 = injectiveMoment H node135 := by
  rfl

def raw1355 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![2, -2, 0], ![1, 2, -3]]

def raw1355step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![1, 2, -3], ![2, -2, 0]]

theorem canonical1355 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1355 = injectiveMoment H node135 := by
  calc
    injectiveMoment H raw1355 = injectiveMoment H raw1355step0 := by
      have heq : raw1355step0 = (fun i j => raw1355 (permutation10 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1355 permutation10 permutation3
    _ = injectiveMoment H node135 := by rfl

def raw1356 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 3, -2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]

theorem canonical1356 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1356 = injectiveMoment H node426 := by
  rfl

def raw1357 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 3, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]

theorem canonical1357 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1357 = injectiveMoment H node427 := by
  rfl

def raw1358 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 3, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]

def raw1358step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -3, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]

def raw1358step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]

theorem canonical1358 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw1358 = injectiveMoment H node362 := by
  calc
    injectiveMoment H raw1358 = injectiveMoment H raw1358step0 := by
      have heq : raw1358step0 = -raw1358 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw1358).symm
    injectiveMoment H raw1358step0 = injectiveMoment H raw1358step1 := by
      have heq : raw1358step1 = (fun i j => raw1358step0 (permutation73 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1358step0 permutation73 permutation5
    _ = injectiveMoment H node362 := by rfl

def raw1359 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 3, -2], ![1, -1, 0], ![2, 0, -2]]

def raw1359step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -3, 2], ![-1, 1, 0], ![-2, 0, 2]]

def raw1359step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![2, 2, -4]]

theorem canonical1359 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw1359 = injectiveMoment H node102 := by
  calc
    injectiveMoment H raw1359 = injectiveMoment H raw1359step0 := by
      have heq : raw1359step0 = -raw1359 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw1359).symm
    injectiveMoment H raw1359step0 = injectiveMoment H raw1359step1 := by
      have heq : raw1359step1 = (fun i j => raw1359step0 (permutation20 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1359step0 permutation20 permutation5
    _ = injectiveMoment H node102 := by rfl

def raw1360 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 3, -2], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]

def raw1360step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -3, 2], ![-1, 0, 1], ![-1, 1, 0], ![-1, 0, 1]]

def raw1360step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]

theorem canonical1360 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw1360 = injectiveMoment H node362 := by
  calc
    injectiveMoment H raw1360 = injectiveMoment H raw1360step0 := by
      have heq : raw1360step0 = -raw1360 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw1360).symm
    injectiveMoment H raw1360step0 = injectiveMoment H raw1360step1 := by
      have heq : raw1360step1 = (fun i j => raw1360step0 (permutation67 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1360step0 permutation67 permutation5
    _ = injectiveMoment H node362 := by rfl

def raw1361 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 3, -2], ![1, 0, -1], ![2, -1, -1]]

def raw1361step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -3, 2], ![-1, 0, 1], ![-2, 1, 1]]

def raw1361step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![2, 2, -4]]

theorem canonical1361 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw1361 = injectiveMoment H node106 := by
  calc
    injectiveMoment H raw1361 = injectiveMoment H raw1361step0 := by
      have heq : raw1361step0 = -raw1361 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw1361).symm
    injectiveMoment H raw1361step0 = injectiveMoment H raw1361step1 := by
      have heq : raw1361step1 = (fun i j => raw1361step0 (permutation18 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1361step0 permutation18 permutation5
    _ = injectiveMoment H node106 := by rfl

def raw1362 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 3, -2], ![2, -2, 0], ![1, 1, -2]]

def raw1362step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 3, -2], ![1, 1, -2], ![2, -2, 0]]

theorem canonical1362 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1362 = injectiveMoment H node136 := by
  calc
    injectiveMoment H raw1362 = injectiveMoment H raw1362step0 := by
      have heq : raw1362step0 = (fun i j => raw1362 (permutation10 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1362 permutation10 permutation3
    _ = injectiveMoment H node136 := by rfl

def raw1363 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 4, -3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]

theorem canonical1363 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1363 = injectiveMoment H node428 := by
  rfl

def raw1364 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 4, -3], ![1, -1, 0], ![2, -1, -1]]

theorem canonical1364 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1364 = injectiveMoment H node137 := by
  rfl

def raw1365 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 4, -3], ![2, -2, 0], ![1, 0, -1]]

def raw1365step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 4, -3], ![1, 0, -1], ![2, -2, 0]]

theorem canonical1365 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1365 = injectiveMoment H node138 := by
  calc
    injectiveMoment H raw1365 = injectiveMoment H raw1365step0 := by
      have heq : raw1365step0 = (fun i j => raw1365 (permutation10 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1365 permutation10 permutation3
    _ = injectiveMoment H node138 := by rfl

def raw1366 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 4, -3], ![3, -2, -1]]

def raw1366step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 2, -4], ![1, -4, 3], ![-3, 2, 1]]

def raw1366step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 3, -4], ![2, -4, 2]]

theorem canonical1366 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw1366 = injectiveMoment H node22 := by
  calc
    injectiveMoment H raw1366 = injectiveMoment H raw1366step0 := by
      have heq : raw1366step0 = -raw1366 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw1366).symm
    injectiveMoment H raw1366step0 = injectiveMoment H raw1366step1 := by
      have heq : raw1366step1 = (fun i j => raw1366step0 (permutation8 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1366step0 permutation8 permutation4
    _ = injectiveMoment H node22 := by rfl

def raw1367 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, 1, -3]]

theorem canonical1367 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1367 = injectiveMoment H node429 := by
  rfl

def raw1368 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![2, 0, -2]]

theorem canonical1368 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1368 = injectiveMoment H node430 := by
  rfl

def raw1369 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 3, -4]]

theorem canonical1369 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1369 = injectiveMoment H node431 := by
  rfl

def raw1370 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 2, -3]]

theorem canonical1370 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1370 = injectiveMoment H node432 := by
  rfl

def raw1371 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![1, 1, -2]]

theorem canonical1371 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1371 = injectiveMoment H node433 := by
  rfl

def raw1372 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![1, 1, -2]]

theorem canonical1372 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1372 = injectiveMoment H node434 := by
  rfl

def raw1373 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, -1, 1], ![0, 3, -3], ![1, 0, -1], ![1, 0, -1]]

theorem canonical1373 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1373 = injectiveMoment H node435 := by
  rfl

def raw1374 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, -1, 1], ![0, 3, -3], ![2, 0, -2]]

theorem canonical1374 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1374 = injectiveMoment H node141 := by
  rfl

def raw1375 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, -1, 1], ![0, 4, -4], ![1, -1, 0], ![1, 0, -1]]

theorem canonical1375 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1375 = injectiveMoment H node436 := by
  rfl

end MUB6.Certificate.PairSemantics

end OAI
