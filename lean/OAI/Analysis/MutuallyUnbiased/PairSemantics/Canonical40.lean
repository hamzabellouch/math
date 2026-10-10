import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes6
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes8
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes12
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes19
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes23

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw1280 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 0, -2, 2], ![0, 1, 1, -2], ![2, 1, -1, -2]]

theorem canonical1280 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1280 = injectiveMoment H node410 := by
  rfl

def raw1281 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 0, -2, 2], ![0, 2, 0, -2], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def raw1281step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 0, -2, 2], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, 0, -2]]

theorem canonical1281 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1281 = injectiveMoment H node1514 := by
  calc
    injectiveMoment H raw1281 = injectiveMoment H raw1281step0 := by
      have heq : raw1281step0 = (fun i j => raw1281 (permutation36 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1281 permutation36 permutation15
    _ = injectiveMoment H node1514 := by rfl

def raw1282 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 0, -2, 2], ![0, 2, 0, -2], ![2, 0, 0, -2]]

theorem canonical1282 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1282 = injectiveMoment H node412 := by
  rfl

def raw1283 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 0, -2, 2], ![0, 2, 1, -3], ![2, 0, -1, -1]]

def raw1283step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 0, -2, 2], ![0, 2, -1, -1], ![2, 0, 1, -3]]

theorem canonical1283 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1283 = injectiveMoment H node411 := by
  calc
    injectiveMoment H raw1283 = injectiveMoment H raw1283step0 := by
      have heq : raw1283step0 = (fun i j => raw1283 (permutation10 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1283 permutation10 permutation15
    _ = injectiveMoment H node411 := by rfl

def raw1284 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 0, -2, 2], ![1, 0, 0, -1], ![1, 2, 0, -3]]

def raw1284step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-2, 0, 0, 2], ![2, -2, 0, 0], ![2, 2, -1, -3]]

def raw1284step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![2, 0, 0, -2], ![-2, 2, 0, 0], ![-2, -2, 1, 3]]

def raw1284step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, -2, 2], ![0, 2, 0, -2], ![1, -2, 3, -2]]

theorem canonical1284 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw1284 = injectiveMoment H node1255 := by
  calc
    injectiveMoment H raw1284 = injectiveMoment H raw1284step0 := by
      have heq : raw1284step0 = raw1284.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1284).symm
    injectiveMoment H raw1284step0 = injectiveMoment H raw1284step1 := by
      have heq : raw1284step1 = -raw1284step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw1284step0).symm
    injectiveMoment H raw1284step1 = injectiveMoment H raw1284step2 := by
      have heq : raw1284step2 = (fun i j => raw1284step1 (permutation9 i) (permutation24 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1284step1 permutation9 permutation24
    _ = injectiveMoment H node1255 := by rfl

def raw1285 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 0, -2, 2], ![1, 1, 0, -2], ![1, 1, 0, -2]]

theorem canonical1285 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1285 = injectiveMoment H node413 := by
  rfl

def raw1286 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 2, 0, -2], ![2, 0, 0, -2]]

theorem canonical1286 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1286 = injectiveMoment H node1517 := by
  rfl

def raw1287 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, 0, 0, -2]]

theorem canonical1287 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1287 = injectiveMoment H node1518 := by
  rfl

def raw1288 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 1, 0, -2]]

theorem canonical1288 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1288 = injectiveMoment H node1520 := by
  rfl

def raw1289 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, -1, -1]]

theorem canonical1289 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1289 = injectiveMoment H node1521 := by
  rfl

def raw1290 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 1, 0, -2]]

def raw1290step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 1, 0, -2]]

theorem canonical1290 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1290 = injectiveMoment H node1520 := by
  calc
    injectiveMoment H raw1290 = injectiveMoment H raw1290step0 := by
      have heq : raw1290step0 = (fun i j => raw1290 (permutation35 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1290 permutation35 permutation15
    _ = injectiveMoment H node1520 := by rfl

def raw1291 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 0, -1, 1], ![0, 2, -1, -1], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def raw1291step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, -1, -1]]

theorem canonical1291 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1291 = injectiveMoment H node1521 := by
  calc
    injectiveMoment H raw1291 = injectiveMoment H raw1291step0 := by
      have heq : raw1291step0 = (fun i j => raw1291 (permutation36 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1291 permutation36 permutation15
    _ = injectiveMoment H node1521 := by rfl

def raw1292 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 0, -1, 1], ![0, 2, -1, -1], ![2, 0, 0, -2]]

def raw1292step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-2, 0, 2, 0], ![2, -1, -1, 0], ![2, 1, -1, -2]]

def raw1292step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 2, 0, -2], ![1, -1, -2, 2]]

theorem canonical1292 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1292 = injectiveMoment H node1059 := by
  calc
    injectiveMoment H raw1292 = injectiveMoment H raw1292step0 := by
      have heq : raw1292step0 = raw1292.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1292).symm
    injectiveMoment H raw1292step0 = injectiveMoment H raw1292step1 := by
      have heq : raw1292step1 = (fun i j => raw1292step0 (permutation21 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1292step0 permutation21 permutation18
    _ = injectiveMoment H node1059 := by rfl

def raw1293 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 0, -1, 1], ![0, 2, 0, -2], ![1, 0, -1, 0], ![1, 0, 0, -1]]

def raw1293step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, 0, 0, -2]]

theorem canonical1293 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1293 = injectiveMoment H node1518 := by
  calc
    injectiveMoment H raw1293 = injectiveMoment H raw1293step0 := by
      have heq : raw1293step0 = (fun i j => raw1293 (permutation36 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1293 permutation36 permutation15
    _ = injectiveMoment H node1518 := by rfl

def raw1294 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 0, -1, 1], ![0, 2, 0, -2], ![2, 0, -1, -1]]

def raw1294step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-2, 0, 2, 0], ![2, -1, 0, -1], ![2, 1, -2, -1]]

def raw1294step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 2, 0, -2], ![1, -1, -2, 2]]

theorem canonical1294 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1294 = injectiveMoment H node1059 := by
  calc
    injectiveMoment H raw1294 = injectiveMoment H raw1294step0 := by
      have heq : raw1294step0 = raw1294.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1294).symm
    injectiveMoment H raw1294step0 = injectiveMoment H raw1294step1 := by
      have heq : raw1294step1 = (fun i j => raw1294step0 (permutation23 i) (permutation20 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1294step0 permutation23 permutation20
    _ = injectiveMoment H node1059 := by rfl

def raw1295 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 0, -1, 1], ![1, 1, -1, -1], ![1, 1, 0, -2]]

def raw1295step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-2, 0, 1, 1], ![2, -1, -1, 0], ![2, 1, -1, -2]]

def raw1295step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, 1, -2], ![0, 1, 1, -2], ![1, -1, -2, 2]]

theorem canonical1295 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1295 = injectiveMoment H node1084 := by
  calc
    injectiveMoment H raw1295 = injectiveMoment H raw1295step0 := by
      have heq : raw1295step0 = raw1295.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1295).symm
    injectiveMoment H raw1295step0 = injectiveMoment H raw1295step1 := by
      have heq : raw1295step1 = (fun i j => raw1295step0 (permutation21 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1295step0 permutation21 permutation18
    _ = injectiveMoment H node1084 := by rfl

def raw1296 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 0, 0, 0], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, 0, 0, -2]]

def raw1296step0 : Matrix (Fin 4) (Fin 5) ℤ := ![![-2, 0, 0, 0, 2], ![-2, 0, 1, 1, 0], ![2, 0, -1, -1, 0], ![2, 0, 0, 0, -2]]

def raw1296step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-2, 1, 1, 0], ![2, -1, -1, 0], ![2, 0, 0, -2]]

def raw1296step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 0, 2, -2], ![1, 1, 0, -2]]

theorem canonical1296 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1296 = injectiveMoment H node1027 := by
  calc
    injectiveMoment H raw1296 = injectiveMoment H raw1296step0 := by
      have heq : raw1296step0 = raw1296.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1296).symm
    injectiveMoment H raw1296step0 = injectiveMoment H raw1296step1 := by
      have hz : ∀ i, raw1296step0 i (permutation57 0) = 0 := by decide +kernel
      have heq : raw1296step1 = (fun i j => raw1296step0 i (permutation57 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw1296step0 permutation57 hz
    injectiveMoment H raw1296step1 = injectiveMoment H raw1296step2 := by
      have heq : raw1296step2 = (fun i j => raw1296step1 (permutation25 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1296step1 permutation25 permutation18
    _ = injectiveMoment H node1027 := by rfl

def raw1297 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 0, 0, 0], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, 0, -1, -1]]

def raw1297step0 : Matrix (Fin 4) (Fin 5) ℤ := ![![-2, 0, 0, 0, 2], ![-2, 0, 1, 1, 0], ![2, 0, -1, 0, -1], ![2, 0, 0, -1, -1]]

def raw1297step1 : Matrix (Fin 4) (Fin 5) ℤ := ![![2, 0, 0, 0, -2], ![2, 0, -1, -1, 0], ![-2, 0, 1, 0, 1], ![-2, 0, 0, 1, 1]]

def raw1297step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![2, -1, -1, 0], ![-2, 1, 0, 1], ![-2, 0, 1, 1]]

def raw1297step3 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 1, 1, -2], ![1, 0, 1, -2]]

theorem canonical1297 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw1297 = injectiveMoment H node1033 := by
  calc
    injectiveMoment H raw1297 = injectiveMoment H raw1297step0 := by
      have heq : raw1297step0 = raw1297.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1297).symm
    injectiveMoment H raw1297step0 = injectiveMoment H raw1297step1 := by
      have heq : raw1297step1 = -raw1297step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw1297step0).symm
    injectiveMoment H raw1297step1 = injectiveMoment H raw1297step2 := by
      have hz : ∀ i, raw1297step1 i (permutation57 0) = 0 := by decide +kernel
      have heq : raw1297step2 = (fun i j => raw1297step1 i (permutation57 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw1297step1 permutation57 hz
    injectiveMoment H raw1297step2 = injectiveMoment H raw1297step3 := by
      have heq : raw1297step3 = (fun i j => raw1297step2 (permutation16 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1297step2 permutation16 permutation18
    _ = injectiveMoment H node1033 := by rfl

def raw1298 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 0, 1, -1], ![0, 1, -2, 1], ![0, 1, -1, 0], ![2, 0, 0, -2]]

def raw1298step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 1, -2], ![2, 0, -2, 0]]

theorem canonical1298 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1298 = injectiveMoment H node1522 := by
  calc
    injectiveMoment H raw1298 = injectiveMoment H raw1298step0 := by
      have heq : raw1298step0 = (fun i j => raw1298 (permutation35 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1298 permutation35 permutation10
    _ = injectiveMoment H node1522 := by rfl

def raw1299 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 0, 1, -1], ![0, 1, -2, 1], ![0, 1, 0, -1], ![2, 0, -1, -1]]

def raw1299step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![2, 0, -1, -1]]

theorem canonical1299 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1299 = injectiveMoment H node1519 := by
  calc
    injectiveMoment H raw1299 = injectiveMoment H raw1299step0 := by
      have heq : raw1299step0 = (fun i j => raw1299 (permutation35 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1299 permutation35 permutation10
    _ = injectiveMoment H node1519 := by rfl

def raw1300 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -2, 1], ![2, 0, 0, -2]]

def raw1300step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 1, -2], ![2, 0, -2, 0]]

theorem canonical1300 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1300 = injectiveMoment H node1522 := by
  calc
    injectiveMoment H raw1300 = injectiveMoment H raw1300step0 := by
      have heq : raw1300step0 = (fun i j => raw1300 (permutation33 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1300 permutation33 permutation10
    _ = injectiveMoment H node1522 := by rfl

def raw1301 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, 0, -1, -1]]

def raw1301step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, -1, -1]]

theorem canonical1301 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1301 = injectiveMoment H node1521 := by
  calc
    injectiveMoment H raw1301 = injectiveMoment H raw1301step0 := by
      have heq : raw1301step0 = (fun i j => raw1301 (permutation33 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1301 permutation33 permutation10
    _ = injectiveMoment H node1521 := by rfl

def raw1302 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, 0, -2, 0]]

def raw1302step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, 0, 0, -2]]

theorem canonical1302 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1302 = injectiveMoment H node1518 := by
  calc
    injectiveMoment H raw1302 = injectiveMoment H raw1302step0 := by
      have heq : raw1302step0 = (fun i j => raw1302 (permutation35 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1302 permutation35 permutation10
    _ = injectiveMoment H node1518 := by rfl

def raw1303 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 0, 0, -1]]

theorem canonical1303 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1303 = injectiveMoment H node1523 := by
  rfl

def raw1304 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 1, -2, 1], ![0, 1, 0, -1], ![2, 0, 0, -2]]

def raw1304step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-2, 1, 1, 0], ![2, -2, 0, 0], ![2, 1, -1, -2]]

def raw1304step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -2, 2], ![0, 2, 0, -2], ![1, 0, 1, -2]]

theorem canonical1304 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1304 = injectiveMoment H node831 := by
  calc
    injectiveMoment H raw1304 = injectiveMoment H raw1304step0 := by
      have heq : raw1304step0 = raw1304.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1304).symm
    injectiveMoment H raw1304step0 = injectiveMoment H raw1304step1 := by
      have heq : raw1304step1 = (fun i j => raw1304step0 (permutation31 i) (permutation26 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1304step0 permutation31 permutation26
    _ = injectiveMoment H node831 := by rfl

def raw1305 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 1, -2, 1], ![0, 1, 1, -2], ![2, 0, -1, -1]]

def raw1305step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-2, 1, 1, 0], ![2, -2, 1, -1], ![2, 1, -2, -1]]

def raw1305step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 2, 0, -2], ![1, -1, -2, 2], ![1, 0, 1, -2]]

theorem canonical1305 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1305 = injectiveMoment H node518 := by
  calc
    injectiveMoment H raw1305 = injectiveMoment H raw1305step0 := by
      have heq : raw1305step0 = raw1305.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1305).symm
    injectiveMoment H raw1305step0 = injectiveMoment H raw1305step1 := by
      have heq : raw1305step1 = (fun i j => raw1305step0 (permutation22 i) (permutation20 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1305step0 permutation22 permutation20
    _ = injectiveMoment H node518 := by rfl

def raw1306 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 1, -2, 1], ![1, 0, 0, -1], ![1, 1, 0, -2]]

def raw1306step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-2, 1, 0, 1], ![2, -2, 0, 0], ![2, 1, -1, -2]]

def raw1306step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -2, 2], ![0, 1, 1, -2], ![1, 1, 0, -2]]

theorem canonical1306 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1306 = injectiveMoment H node828 := by
  calc
    injectiveMoment H raw1306 = injectiveMoment H raw1306step0 := by
      have heq : raw1306step0 = raw1306.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1306).symm
    injectiveMoment H raw1306step0 = injectiveMoment H raw1306step1 := by
      have heq : raw1306step1 = (fun i j => raw1306step0 (permutation32 i) (permutation26 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1306step0 permutation32 permutation26
    _ = injectiveMoment H node828 := by rfl

def raw1307 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 1, -2, 1], ![1, 1, 0, -2], ![1, 0, 0, -1]]

def raw1307step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-2, 1, 1, 0], ![2, -2, 0, 0], ![2, 1, -2, -1]]

def raw1307step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -2, 2], ![0, 1, 1, -2], ![1, 1, 0, -2]]

theorem canonical1307 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1307 = injectiveMoment H node828 := by
  calc
    injectiveMoment H raw1307 = injectiveMoment H raw1307step0 := by
      have heq : raw1307step0 = raw1307.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1307).symm
    injectiveMoment H raw1307step0 = injectiveMoment H raw1307step1 := by
      have heq : raw1307step1 = (fun i j => raw1307step0 (permutation32 i) (permutation32 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1307step0 permutation32 permutation32
    _ = injectiveMoment H node828 := by rfl

def raw1308 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 0, 0, -1]]

theorem canonical1308 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1308 = injectiveMoment H node1524 := by
  rfl

def raw1309 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, 0, 0, -2]]

def raw1309step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-2, 1, 1, 0], ![2, -1, -1, 0], ![2, 0, 0, -2]]

def raw1309step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 0, 2, -2], ![1, 1, 0, -2]]

theorem canonical1309 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1309 = injectiveMoment H node1027 := by
  calc
    injectiveMoment H raw1309 = injectiveMoment H raw1309step0 := by
      have heq : raw1309step0 = raw1309.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1309).symm
    injectiveMoment H raw1309step0 = injectiveMoment H raw1309step1 := by
      have heq : raw1309step1 = (fun i j => raw1309step0 (permutation25 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1309step0 permutation25 permutation18
    _ = injectiveMoment H node1027 := by rfl

def raw1310 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 0, -1]]

theorem canonical1310 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1310 = injectiveMoment H node1525 := by
  rfl

def raw1311 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 0, -1, 0]]

def raw1311step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 0, -1]]

theorem canonical1311 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1311 = injectiveMoment H node1525 := by
  calc
    injectiveMoment H raw1311 = injectiveMoment H raw1311step0 := by
      have heq : raw1311step0 = (fun i j => raw1311 (permutation34 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1311 permutation34 permutation9
    _ = injectiveMoment H node1525 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
