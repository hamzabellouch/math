import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes0
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes1
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes2
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes6
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes12
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes13
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes19
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes23

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw1312 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, 0, -1, -1]]

def raw1312step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-2, 1, 1, 0], ![2, -1, 0, -1], ![2, 0, -1, -1]]

def raw1312step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![2, -1, -1, 0], ![-2, 1, 0, 1], ![-2, 0, 1, 1]]

def raw1312step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 1, 1, -2], ![1, 0, 1, -2]]

theorem canonical1312 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw1312 = injectiveMoment H node1033 := by
  calc
    injectiveMoment H raw1312 = injectiveMoment H raw1312step0 := by
      have heq : raw1312step0 = raw1312.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1312).symm
    injectiveMoment H raw1312step0 = injectiveMoment H raw1312step1 := by
      have heq : raw1312step1 = -raw1312step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw1312step0).symm
    injectiveMoment H raw1312step1 = injectiveMoment H raw1312step2 := by
      have heq : raw1312step2 = (fun i j => raw1312step1 (permutation16 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1312step1 permutation16 permutation18
    _ = injectiveMoment H node1033 := by rfl

def raw1313 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 1, -1, 0], ![0, 1, 1, -2], ![2, 0, -2, 0]]

def raw1313step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-2, 1, 1, 0], ![2, -1, 1, -2], ![2, 0, -2, 0]]

def raw1313step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -2, 2], ![0, 2, 0, -2], ![1, 0, 1, -2]]

theorem canonical1313 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1313 = injectiveMoment H node831 := by
  calc
    injectiveMoment H raw1313 = injectiveMoment H raw1313step0 := by
      have heq : raw1313step0 = raw1313.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1313).symm
    injectiveMoment H raw1313step0 = injectiveMoment H raw1313step1 := by
      have heq : raw1313step1 = (fun i j => raw1313step0 (permutation25 i) (permutation20 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1313step0 permutation25 permutation20
    _ = injectiveMoment H node831 := by rfl

def raw1314 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 1, 0, -2]]

def raw1314step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-2, 1, 0, 1], ![2, -1, -1, 0], ![2, 0, 0, -2]]

def raw1314step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 1, 1, -2], ![1, 0, 1, -2]]

theorem canonical1314 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1314 = injectiveMoment H node1033 := by
  calc
    injectiveMoment H raw1314 = injectiveMoment H raw1314step0 := by
      have heq : raw1314step0 = raw1314.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1314).symm
    injectiveMoment H raw1314step0 = injectiveMoment H raw1314step1 := by
      have heq : raw1314step1 = (fun i j => raw1314step0 (permutation25 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1314step0 permutation25 permutation18
    _ = injectiveMoment H node1033 := by rfl

def raw1315 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 1, -1, -1]]

def raw1315step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-2, 1, 0, 1], ![2, -1, 0, -1], ![2, 0, -1, -1]]

def raw1315step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, -1, 2], ![0, 1, 1, -2], ![1, 0, 1, -2]]

theorem canonical1315 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1315 = injectiveMoment H node1237 := by
  calc
    injectiveMoment H raw1315 = injectiveMoment H raw1315step0 := by
      have heq : raw1315step0 = raw1315.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1315).symm
    injectiveMoment H raw1315step0 = injectiveMoment H raw1315step1 := by
      have heq : raw1315step1 = (fun i j => raw1315step0 (permutation25 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1315step0 permutation25 permutation18
    _ = injectiveMoment H node1237 := by rfl

def raw1316 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 1, -1, 0], ![1, 1, -1, -1], ![1, 0, 0, -1]]

def raw1316step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-2, 1, 1, 0], ![2, -1, -1, 0], ![2, 0, -1, -1]]

def raw1316step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, -1, 2], ![0, 1, 1, -2], ![1, 0, 1, -2]]

theorem canonical1316 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1316 = injectiveMoment H node1237 := by
  calc
    injectiveMoment H raw1316 = injectiveMoment H raw1316step0 := by
      have heq : raw1316step0 = raw1316.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1316).symm
    injectiveMoment H raw1316step0 = injectiveMoment H raw1316step1 := by
      have heq : raw1316step1 = (fun i j => raw1316step0 (permutation25 i) (permutation20 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1316step0 permutation25 permutation20
    _ = injectiveMoment H node1237 := by rfl

def raw1317 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 1, 0, -1], ![0, 1, -1, 0], ![2, 0, -1, -1]]

def raw1317step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-2, 1, 1, 0], ![2, 0, -1, -1], ![2, -1, 0, -1]]

def raw1317step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![2, -1, -1, 0], ![-2, 0, 1, 1], ![-2, 1, 0, 1]]

def raw1317step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 1, 1, -2], ![1, 0, 1, -2]]

theorem canonical1317 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw1317 = injectiveMoment H node1033 := by
  calc
    injectiveMoment H raw1317 = injectiveMoment H raw1317step0 := by
      have heq : raw1317step0 = raw1317.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1317).symm
    injectiveMoment H raw1317step0 = injectiveMoment H raw1317step1 := by
      have heq : raw1317step1 = -raw1317step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw1317step0).symm
    injectiveMoment H raw1317step1 = injectiveMoment H raw1317step2 := by
      have heq : raw1317step2 = (fun i j => raw1317step1 (permutation15 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1317step1 permutation15 permutation18
    _ = injectiveMoment H node1033 := by rfl

def raw1318 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -2, 1], ![1, 0, 0, -1]]

def raw1318step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 0, 0, -1]]

theorem canonical1318 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1318 = injectiveMoment H node1523 := by
  calc
    injectiveMoment H raw1318 = injectiveMoment H raw1318step0 := by
      have heq : raw1318step0 = (fun i j => raw1318 (permutation49 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1318 permutation49 permutation15
    _ = injectiveMoment H node1523 := by rfl

def raw1319 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, -1, 0]]

def raw1319step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 0, 0, -1]]

theorem canonical1319 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1319 = injectiveMoment H node1524 := by
  calc
    injectiveMoment H raw1319 = injectiveMoment H raw1319step0 := by
      have heq : raw1319step0 = (fun i j => raw1319 (permutation33 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1319 permutation33 permutation10
    _ = injectiveMoment H node1524 := by rfl

def raw1320 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, -2, 0]]

def raw1320step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-2, 1, 1, 0], ![2, 0, 0, -2], ![2, -1, -1, 0]]

def raw1320step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 0, 2, -2], ![1, 1, 0, -2]]

theorem canonical1320 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1320 = injectiveMoment H node1027 := by
  calc
    injectiveMoment H raw1320 = injectiveMoment H raw1320step0 := by
      have heq : raw1320step0 = raw1320.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1320).symm
    injectiveMoment H raw1320step0 = injectiveMoment H raw1320step1 := by
      have heq : raw1320step1 = (fun i j => raw1320step0 (permutation31 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1320step0 permutation31 permutation18
    _ = injectiveMoment H node1027 := by rfl

def raw1321 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 1, 0, -1], ![0, 1, 1, -2], ![2, 0, -3, 1]]

def raw1321step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-2, 1, 1, 0], ![2, 0, 1, -3], ![2, -1, -2, 1]]

def raw1321step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, 2, -2], ![0, 1, -3, 2], ![1, 1, 0, -2]]

theorem canonical1321 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1321 = injectiveMoment H node841 := by
  calc
    injectiveMoment H raw1321 = injectiveMoment H raw1321step0 := by
      have heq : raw1321step0 = raw1321.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1321).symm
    injectiveMoment H raw1321step0 = injectiveMoment H raw1321step1 := by
      have heq : raw1321step1 = (fun i j => raw1321step0 (permutation28 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1321step0 permutation28 permutation18
    _ = injectiveMoment H node841 := by rfl

def raw1322 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 1, -1, -1]]

def raw1322step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-2, 1, 0, 1], ![2, 0, -1, -1], ![2, -1, 0, -1]]

def raw1322step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, -1, 2], ![0, 1, 1, -2], ![1, 0, 1, -2]]

theorem canonical1322 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1322 = injectiveMoment H node1237 := by
  calc
    injectiveMoment H raw1322 = injectiveMoment H raw1322step0 := by
      have heq : raw1322step0 = raw1322.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1322).symm
    injectiveMoment H raw1322step0 = injectiveMoment H raw1322step1 := by
      have heq : raw1322step1 = (fun i j => raw1322step0 (permutation31 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1322step0 permutation31 permutation18
    _ = injectiveMoment H node1237 := by rfl

def raw1323 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 1, -2, 0]]

def raw1323step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-2, 1, 0, 1], ![2, 0, 0, -2], ![2, -1, -1, 0]]

def raw1323step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 1, 1, -2], ![1, 0, 1, -2]]

theorem canonical1323 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1323 = injectiveMoment H node1033 := by
  calc
    injectiveMoment H raw1323 = injectiveMoment H raw1323step0 := by
      have heq : raw1323step0 = raw1323.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1323).symm
    injectiveMoment H raw1323step0 = injectiveMoment H raw1323step1 := by
      have heq : raw1323step1 = (fun i j => raw1323step0 (permutation31 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1323step0 permutation31 permutation18
    _ = injectiveMoment H node1033 := by rfl

def raw1324 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 1, 0, -1], ![1, 1, -2, 0], ![1, 0, 0, -1]]

def raw1324step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-2, 1, 1, 0], ![2, 0, -2, 0], ![2, -1, 0, -1]]

def raw1324step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 1, 1, -2], ![1, 0, 1, -2]]

theorem canonical1324 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1324 = injectiveMoment H node1033 := by
  calc
    injectiveMoment H raw1324 = injectiveMoment H raw1324step0 := by
      have heq : raw1324step0 = raw1324.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1324).symm
    injectiveMoment H raw1324step0 = injectiveMoment H raw1324step1 := by
      have heq : raw1324step1 = (fun i j => raw1324step0 (permutation31 i) (permutation20 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1324step0 permutation31 permutation20
    _ = injectiveMoment H node1033 := by rfl

def raw1325 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 1, 2, -3], ![2, 1, -4, 1]]

def raw1325step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![2, 2, -4], ![2, -3, 1]]

def raw1325step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, 1, -2], ![2, -4, 2]]

theorem canonical1325 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1325 = injectiveMoment H node112 := by
  calc
    injectiveMoment H raw1325 = injectiveMoment H raw1325step0 := by
      have heq : raw1325step0 = raw1325.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1325).symm
    injectiveMoment H raw1325step0 = injectiveMoment H raw1325step1 := by
      have heq : raw1325step1 = (fun i j => raw1325step0 (permutation27 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1325step0 permutation27 permutation6
    _ = injectiveMoment H node112 := by rfl

def raw1326 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 2, -2, 0], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def raw1326step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-2, 2, 0, 0], ![2, -2, 0, 0], ![2, 0, -1, -1]]

def raw1326step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 0, 2, -2], ![1, 1, 0, -2]]

theorem canonical1326 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1326 = injectiveMoment H node1027 := by
  calc
    injectiveMoment H raw1326 = injectiveMoment H raw1326step0 := by
      have heq : raw1326step0 = raw1326.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1326).symm
    injectiveMoment H raw1326step0 = injectiveMoment H raw1326step1 := by
      have heq : raw1326step1 = (fun i j => raw1326step0 (permutation32 i) (permutation26 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1326step0 permutation32 permutation26
    _ = injectiveMoment H node1027 := by rfl

def raw1327 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 2, -1, -1], ![1, 0, -1, 0], ![1, 0, 0, -1]]

def raw1327step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-2, 2, 0, 0], ![2, -1, -1, 0], ![2, -1, 0, -1]]

def raw1327step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![2, -2, 0, 0], ![-2, 1, 1, 0], ![-2, 1, 0, 1]]

def raw1327step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 1, 1, -2], ![1, 0, 1, -2]]

theorem canonical1327 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw1327 = injectiveMoment H node1033 := by
  calc
    injectiveMoment H raw1327 = injectiveMoment H raw1327step0 := by
      have heq : raw1327step0 = raw1327.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1327).symm
    injectiveMoment H raw1327step0 = injectiveMoment H raw1327step1 := by
      have heq : raw1327step1 = -raw1327step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw1327step0).symm
    injectiveMoment H raw1327step1 = injectiveMoment H raw1327step2 := by
      have heq : raw1327step2 = (fun i j => raw1327step1 (permutation10 i) (permutation26 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1327step1 permutation10 permutation26
    _ = injectiveMoment H node1033 := by rfl

def raw1328 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 2, 0, -2], ![1, 0, -2, 1], ![1, 0, 0, -1]]

def raw1328step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-2, 2, 0, 0], ![2, 0, -2, 0], ![2, -2, 1, -1]]

def raw1328step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -2, 2], ![0, 2, 0, -2], ![1, 0, 1, -2]]

theorem canonical1328 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1328 = injectiveMoment H node831 := by
  calc
    injectiveMoment H raw1328 = injectiveMoment H raw1328step0 := by
      have heq : raw1328step0 = raw1328.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1328).symm
    injectiveMoment H raw1328step0 = injectiveMoment H raw1328step1 := by
      have heq : raw1328step1 = (fun i j => raw1328step0 (permutation32 i) (permutation30 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1328step0 permutation32 permutation30
    _ = injectiveMoment H node831 := by rfl

def raw1329 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 3, -3, 0], ![2, -1, 1, -2]]

def raw1329step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![2, -3, 1], ![2, 0, -2]]

def raw1329step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![3, -1, -2]]

theorem canonical1329 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1329 = injectiveMoment H node101 := by
  calc
    injectiveMoment H raw1329 = injectiveMoment H raw1329step0 := by
      have heq : raw1329step0 = raw1329.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1329).symm
    injectiveMoment H raw1329step0 = injectiveMoment H raw1329step1 := by
      have heq : raw1329step1 = (fun i j => raw1329step0 (permutation25 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1329step0 permutation25 permutation6
    _ = injectiveMoment H node101 := by rfl

def raw1330 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![1, -1, 2, -2], ![1, 3, -4, 0]]

def raw1330step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, -1, 3], ![2, 2, -4], ![2, -2, 0]]

def raw1330step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -1, -1], ![2, 1, -3], ![-2, -2, 4], ![-2, 2, 0]]

def raw1330step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![1, 2, -3], ![2, -2, 0]]

theorem canonical1330 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw1330 = injectiveMoment H node135 := by
  calc
    injectiveMoment H raw1330 = injectiveMoment H raw1330step0 := by
      have heq : raw1330step0 = raw1330.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1330).symm
    injectiveMoment H raw1330step0 = injectiveMoment H raw1330step1 := by
      have heq : raw1330step1 = -raw1330step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw1330step0).symm
    injectiveMoment H raw1330step1 = injectiveMoment H raw1330step2 := by
      have heq : raw1330step2 = (fun i j => raw1330step1 (permutation21 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1330step1 permutation21 permutation5
    _ = injectiveMoment H node135 := by rfl

def raw1331 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![1, 0, 2, -3], ![1, 2, -4, 1]]

def raw1331step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![2, 2, -4], ![2, -3, 1]]

def raw1331step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, 1, -2], ![2, -4, 2]]

theorem canonical1331 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1331 = injectiveMoment H node112 := by
  calc
    injectiveMoment H raw1331 = injectiveMoment H raw1331step0 := by
      have heq : raw1331step0 = raw1331.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1331).symm
    injectiveMoment H raw1331step0 = injectiveMoment H raw1331step1 := by
      have heq : raw1331step1 = (fun i j => raw1331step0 (permutation29 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1331step0 permutation29 permutation6
    _ = injectiveMoment H node112 := by rfl

def raw1332 : Matrix (Fin 2) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![2, 2, -2, -2]]

def raw1332step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![2, -2], ![2, -2]]

theorem canonical1332 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1332 = injectiveMoment H node45 := by
  calc
    injectiveMoment H raw1332 = injectiveMoment H raw1332step0 := by
      have heq : raw1332step0 = raw1332.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1332).symm
    _ = injectiveMoment H node45 := by rfl

def raw1333 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, -2, 3, 1], ![-1, 2, 1, -2], ![3, 0, -4, 1]]

def raw1333step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![3, 1, -4], ![1, -2, 1]]

def raw1333step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![-3, -1, 4], ![-1, 2, -1]]

def raw1333step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 4, -3], ![1, -3, 2], ![2, -1, -1]]

theorem canonical1333 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw1333 = injectiveMoment H node191 := by
  calc
    injectiveMoment H raw1333 = injectiveMoment H raw1333step0 := by
      have heq : raw1333step0 = raw1333.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1333).symm
    injectiveMoment H raw1333step0 = injectiveMoment H raw1333step1 := by
      have heq : raw1333step1 = -raw1333step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw1333step0).symm
    injectiveMoment H raw1333step1 = injectiveMoment H raw1333step2 := by
      have heq : raw1333step2 = (fun i j => raw1333step1 (permutation17 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1333step1 permutation17 permutation6
    _ = injectiveMoment H node191 := by rfl

def raw1334 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 3, 1], ![0, 0, -2, 2], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, -1, -1]]

def raw1334step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, 0, -1, -1]]

theorem canonical1334 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1334 = injectiveMoment H node1509 := by
  calc
    injectiveMoment H raw1334 = injectiveMoment H raw1334step0 := by
      have heq : raw1334step0 = (fun i j => raw1334 (permutation33 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1334 permutation33 permutation10
    _ = injectiveMoment H node1509 := by rfl

def raw1335 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, -2, 3, 1], ![0, 3, -1, -2], ![2, -1, -2, 1]]

def raw1335step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![3, -1, -2], ![1, -2, 1]]

def raw1335step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![2, -3, 1], ![-3, 1, 2], ![-1, 2, -1]]

def raw1335step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 2, -3], ![2, -1, -1]]

theorem canonical1335 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw1335 = injectiveMoment H node103 := by
  calc
    injectiveMoment H raw1335 = injectiveMoment H raw1335step0 := by
      have heq : raw1335step0 = raw1335.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1335).symm
    injectiveMoment H raw1335step0 = injectiveMoment H raw1335step1 := by
      have heq : raw1335step1 = -raw1335step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw1335step0).symm
    injectiveMoment H raw1335step1 = injectiveMoment H raw1335step2 := by
      have heq : raw1335step2 = (fun i j => raw1335step1 (permutation15 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1335step1 permutation15 permutation6
    _ = injectiveMoment H node103 := by rfl

def raw1336 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, -2, 3, 1], ![2, -1, 1, -2], ![0, 3, -4, 1]]

def raw1336step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![3, 1, -4], ![1, -2, 1]]

def raw1336step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -2, 0], ![2, 1, -3], ![-3, -1, 4], ![-1, 2, -1]]

def raw1336step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 4, -3], ![1, -3, 2], ![2, -1, -1]]

theorem canonical1336 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw1336 = injectiveMoment H node191 := by
  calc
    injectiveMoment H raw1336 = injectiveMoment H raw1336step0 := by
      have heq : raw1336step0 = raw1336.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1336).symm
    injectiveMoment H raw1336step0 = injectiveMoment H raw1336step1 := by
      have heq : raw1336step1 = -raw1336step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw1336step0).symm
    injectiveMoment H raw1336step1 = injectiveMoment H raw1336step2 := by
      have heq : raw1336step2 = (fun i j => raw1336step1 (permutation11 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1336step1 permutation11 permutation6
    _ = injectiveMoment H node191 := by rfl

def raw1337 : Matrix (Fin 2) (Fin 4) ℤ := ![![-2, -2, 3, 1], ![2, 2, -3, -1]]

def raw1337step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![3, -3], ![1, -1]]

def raw1337step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![2, -2], ![2, -2]]

theorem canonical1337 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1337 = injectiveMoment H node25 := by
  calc
    injectiveMoment H raw1337 = injectiveMoment H raw1337step0 := by
      have heq : raw1337step0 = raw1337.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1337).symm
    injectiveMoment H raw1337step0 = injectiveMoment H raw1337step1 := by
      have heq : raw1337step1 = (fun i j => raw1337step0 (permutation25 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1337step0 permutation25 permutation2
    _ = injectiveMoment H node25 := by rfl

def raw1338 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]

theorem canonical1338 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1338 = injectiveMoment H node420 := by
  rfl

def raw1339 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]

theorem canonical1339 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1339 = injectiveMoment H node421 := by
  rfl

def raw1340 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, -1, 0], ![2, 2, -4]]

theorem canonical1340 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1340 = injectiveMoment H node131 := by
  rfl

def raw1341 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 2, -3], ![2, -1, -1]]

theorem canonical1341 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1341 = injectiveMoment H node132 := by
  rfl

def raw1342 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]

def raw1342step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]

theorem canonical1342 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1342 = injectiveMoment H node421 := by
  calc
    injectiveMoment H raw1342 = injectiveMoment H raw1342step0 := by
      have heq : raw1342step0 = (fun i j => raw1342 (permutation50 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1342 permutation50 permutation5
    _ = injectiveMoment H node421 := by rfl

def raw1343 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]

theorem canonical1343 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1343 = injectiveMoment H node422 := by
  rfl

end MUB6.Certificate.PairSemantics

end OAI
