import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes4
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes14
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes17
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes19
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes20
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes21
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes23
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes43

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw1184 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 1, 1, -3]]

theorem canonical1184 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1184 = injectiveMoment H node1498 := by
  rfl

def raw1185 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, 0, -2]]

def raw1185step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -2, -2, 3]]

theorem canonical1185 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1185 = injectiveMoment H node2786 := by
  calc
    injectiveMoment H raw1185 = injectiveMoment H raw1185step0 := by
      have heq : raw1185step0 = (fun i j => raw1185 (permutation65 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1185 permutation65 permutation21
    _ = injectiveMoment H node2786 := by rfl

def raw1186 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 1, -2], ![2, 0, -1, -1]]

theorem canonical1186 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1186 = injectiveMoment H node1499 := by
  rfl

def raw1187 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 1, 1, -3]]

def raw1187step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 1, 1, -3]]

theorem canonical1187 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1187 = injectiveMoment H node1498 := by
  calc
    injectiveMoment H raw1187 = injectiveMoment H raw1187step0 := by
      have heq : raw1187step0 = (fun i j => raw1187 (permutation35 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1187 permutation35 permutation15
    _ = injectiveMoment H node1498 := by rfl

def raw1188 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, 0, 1, -2], ![1, 1, -1, -1]]

theorem canonical1188 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1188 = injectiveMoment H node1500 := by
  rfl

def raw1189 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, -1, 1], ![0, 1, 0, -1], ![2, 1, 0, -3]]

def raw1189step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-2, 0, 1, 1], ![1, -1, 0, 0], ![3, 1, -1, -3]]

def raw1189step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![2, 0, -1, -1], ![-1, 1, 0, 0], ![-3, -1, 1, 3]]

def raw1189step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, -1, 3, -3]]

theorem canonical1189 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw1189 = injectiveMoment H node1252 := by
  calc
    injectiveMoment H raw1189 = injectiveMoment H raw1189step0 := by
      have heq : raw1189step0 = raw1189.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1189).symm
    injectiveMoment H raw1189step0 = injectiveMoment H raw1189step1 := by
      have heq : raw1189step1 = -raw1189step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw1189step0).symm
    injectiveMoment H raw1189step1 = injectiveMoment H raw1189step2 := by
      have heq : raw1189step2 = (fun i j => raw1189step1 (permutation15 i) (permutation24 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1189step1 permutation15 permutation24
    _ = injectiveMoment H node1252 := by rfl

def raw1190 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, -1, 1], ![0, 1, 1, -2], ![1, 0, 0, -1], ![1, 1, -1, -1]]

def raw1190step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, 0, 1, -2], ![1, 1, -1, -1]]

theorem canonical1190 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1190 = injectiveMoment H node1500 := by
  calc
    injectiveMoment H raw1190 = injectiveMoment H raw1190step0 := by
      have heq : raw1190step0 = (fun i j => raw1190 (permutation35 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1190 permutation35 permutation15
    _ = injectiveMoment H node1500 := by rfl

def raw1191 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, -1, 1], ![0, 1, 1, -2], ![2, 1, -1, -2]]

def raw1191step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-2, 0, 1, 1], ![1, -1, 1, -1], ![3, 1, -2, -2]]

def raw1191step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, 2, -2], ![0, 1, 1, -2], ![1, -2, -2, 3]]

theorem canonical1191 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1191 = injectiveMoment H node1351 := by
  calc
    injectiveMoment H raw1191 = injectiveMoment H raw1191step0 := by
      have heq : raw1191step0 = raw1191.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1191).symm
    injectiveMoment H raw1191step0 = injectiveMoment H raw1191step1 := by
      have heq : raw1191step1 = (fun i j => raw1191step0 (permutation21 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1191step0 permutation21 permutation18
    _ = injectiveMoment H node1351 := by rfl

def raw1192 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, -1, 1], ![0, 2, -1, -1], ![1, 0, 0, -1], ![1, 0, 1, -2]]

def raw1192step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 1, -2], ![2, 0, -1, -1]]

theorem canonical1192 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1192 = injectiveMoment H node1499 := by
  calc
    injectiveMoment H raw1192 = injectiveMoment H raw1192step0 := by
      have heq : raw1192step0 = (fun i j => raw1192 (permutation36 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1192 permutation36 permutation15
    _ = injectiveMoment H node1499 := by rfl

def raw1193 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, -1, 1], ![0, 2, -1, -1], ![2, 0, 1, -3]]

def raw1193step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-2, 0, 2, 0], ![1, -1, -1, 1], ![3, 1, -1, -3]]

def raw1193step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, 2, -2], ![0, 2, 0, -2], ![1, -1, -3, 3]]

theorem canonical1193 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1193 = injectiveMoment H node1120 := by
  calc
    injectiveMoment H raw1193 = injectiveMoment H raw1193step0 := by
      have heq : raw1193step0 = raw1193.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1193).symm
    injectiveMoment H raw1193step0 = injectiveMoment H raw1193step1 := by
      have heq : raw1193step1 = (fun i j => raw1193step0 (permutation21 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1193step0 permutation21 permutation18
    _ = injectiveMoment H node1120 := by rfl

def raw1194 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, -1, 1], ![0, 2, 0, -2], ![1, 0, -1, 0], ![1, 0, 1, -2]]

def raw1194step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![2, 0, 0, -2]]

theorem canonical1194 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1194 = injectiveMoment H node1496 := by
  calc
    injectiveMoment H raw1194 = injectiveMoment H raw1194step0 := by
      have heq : raw1194step0 = (fun i j => raw1194 (permutation36 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1194 permutation36 permutation15
    _ = injectiveMoment H node1496 := by rfl

def raw1195 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, -1, 1], ![0, 2, 0, -2], ![2, 0, 0, -2]]

def raw1195step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, 2, -2], ![0, 2, 0, -2], ![1, -2, -2, 3]]

theorem canonical1195 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1195 = injectiveMoment H node1285 := by
  calc
    injectiveMoment H raw1195 = injectiveMoment H raw1195step0 := by
      have heq : raw1195step0 = (fun i j => raw1195 (permutation18 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1195 permutation18 permutation21
    _ = injectiveMoment H node1285 := by rfl

def raw1196 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, 0, -1, 0], ![1, 0, 0, -1]]

def raw1196step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, 0, 1, -3]]

theorem canonical1196 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1196 = injectiveMoment H node1495 := by
  calc
    injectiveMoment H raw1196 = injectiveMoment H raw1196step0 := by
      have heq : raw1196step0 = (fun i j => raw1196 (permutation36 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1196 permutation36 permutation15
    _ = injectiveMoment H node1495 := by rfl

def raw1197 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, -1, 1], ![0, 2, 1, -3], ![2, 0, -1, -1]]

def raw1197step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-2, 0, 2, 0], ![1, -1, 1, -1], ![3, 1, -3, -1]]

def raw1197step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, 2, -2], ![0, 2, 0, -2], ![1, -1, -3, 3]]

theorem canonical1197 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1197 = injectiveMoment H node1120 := by
  calc
    injectiveMoment H raw1197 = injectiveMoment H raw1197step0 := by
      have heq : raw1197step0 = raw1197.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1197).symm
    injectiveMoment H raw1197step0 = injectiveMoment H raw1197step1 := by
      have heq : raw1197step1 = (fun i j => raw1197step0 (permutation23 i) (permutation20 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1197step0 permutation23 permutation20
    _ = injectiveMoment H node1120 := by rfl

def raw1198 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, 0, -1, 0], ![1, 0, -1, 0]]

def raw1198step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, 0, 2, -4]]

theorem canonical1198 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1198 = injectiveMoment H node1494 := by
  calc
    injectiveMoment H raw1198 = injectiveMoment H raw1198step0 := by
      have heq : raw1198step0 = (fun i j => raw1198 (permutation36 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1198 permutation36 permutation15
    _ = injectiveMoment H node1494 := by rfl

def raw1199 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, -1, 1], ![1, 1, -1, -1], ![1, 1, 1, -3]]

def raw1199step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-2, 0, 1, 1], ![1, -1, -1, 1], ![3, 1, -1, -3]]

def raw1199step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 1, 1, -2], ![0, 1, 1, -2], ![1, -1, -3, 3]]

theorem canonical1199 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1199 = injectiveMoment H node1129 := by
  calc
    injectiveMoment H raw1199 = injectiveMoment H raw1199step0 := by
      have heq : raw1199step0 = raw1199.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1199).symm
    injectiveMoment H raw1199step0 = injectiveMoment H raw1199step1 := by
      have heq : raw1199step1 = (fun i j => raw1199step0 (permutation21 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1199step0 permutation21 permutation18
    _ = injectiveMoment H node1129 := by rfl

def raw1200 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, 0, 0], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, 0, 0, -2]]

def raw1200step0 : Matrix (Fin 4) (Fin 5) ℤ := ![![-2, 0, 0, 0, 2], ![-2, 0, 1, 1, 0], ![1, 0, -1, 0, 0], ![3, 0, 0, -1, -2]]

def raw1200step1 : Matrix (Fin 4) (Fin 5) ℤ := ![![2, 0, 0, 0, -2], ![2, 0, -1, -1, 0], ![-1, 0, 1, 0, 0], ![-3, 0, 0, 1, 2]]

def raw1200step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![2, -1, -1, 0], ![-1, 1, 0, 0], ![-3, 0, 1, 2]]

def raw1200step3 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, 0, 2, -3]]

theorem canonical1200 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw1200 = injectiveMoment H node1032 := by
  calc
    injectiveMoment H raw1200 = injectiveMoment H raw1200step0 := by
      have heq : raw1200step0 = raw1200.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1200).symm
    injectiveMoment H raw1200step0 = injectiveMoment H raw1200step1 := by
      have heq : raw1200step1 = -raw1200step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw1200step0).symm
    injectiveMoment H raw1200step1 = injectiveMoment H raw1200step2 := by
      have hz : ∀ i, raw1200step1 i (permutation57 0) = 0 := by decide +kernel
      have heq : raw1200step2 = (fun i j => raw1200step1 i (permutation57 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw1200step1 permutation57 hz
    injectiveMoment H raw1200step2 = injectiveMoment H raw1200step3 := by
      have heq : raw1200step3 = (fun i j => raw1200step2 (permutation15 i) (permutation24 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1200step2 permutation15 permutation24
    _ = injectiveMoment H node1032 := by rfl

def raw1201 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, 0, 0], ![0, 1, -1, 0], ![2, 1, 0, -3]]

def raw1201step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-2, 0, 1, 1], ![1, 0, -1, 0], ![3, 0, 0, -3]]

def raw1201step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![2, 0, -1, -1], ![-1, 0, 1, 0], ![-3, 0, 0, 3]]

def raw1201step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![-1, 1, 0], ![-3, 0, 3]]

def raw1201step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -2, 2], ![0, 3, -3], ![1, 0, -1]]

theorem canonical1201 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw1201 = injectiveMoment H node280 := by
  calc
    injectiveMoment H raw1201 = injectiveMoment H raw1201step0 := by
      have heq : raw1201step0 = raw1201.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1201).symm
    injectiveMoment H raw1201step0 = injectiveMoment H raw1201step1 := by
      have heq : raw1201step1 = -raw1201step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw1201step0).symm
    injectiveMoment H raw1201step1 = injectiveMoment H raw1201step2 := by
      have hz : ∀ i, raw1201step1 i (permutation15 0) = 0 := by decide +kernel
      have heq : raw1201step2 = (fun i j => raw1201step1 i (permutation15 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw1201step1 permutation15 hz
    injectiveMoment H raw1201step2 = injectiveMoment H raw1201step3 := by
      have heq : raw1201step3 = (fun i j => raw1201step2 (permutation16 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1201step2 permutation16 permutation6
    _ = injectiveMoment H node280 := by rfl

def raw1202 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, 0, 0], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, -1, -1]]

def raw1202step0 : Matrix (Fin 4) (Fin 5) ℤ := ![![-2, 0, 0, 0, 2], ![-2, 0, 1, 1, 0], ![1, 0, 0, 0, -1], ![3, 0, -1, -1, -1]]

def raw1202step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-2, 1, 1, 0], ![1, 0, 0, -1], ![3, -1, -1, -1]]

def raw1202step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, -1, 1], ![0, 0, 2, -2], ![1, 1, 0, -2]]

theorem canonical1202 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1202 = injectiveMoment H node959 := by
  calc
    injectiveMoment H raw1202 = injectiveMoment H raw1202step0 := by
      have heq : raw1202step0 = raw1202.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1202).symm
    injectiveMoment H raw1202step0 = injectiveMoment H raw1202step1 := by
      have hz : ∀ i, raw1202step0 i (permutation57 0) = 0 := by decide +kernel
      have heq : raw1202step1 = (fun i j => raw1202step0 i (permutation57 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw1202step0 permutation57 hz
    injectiveMoment H raw1202step1 = injectiveMoment H raw1202step2 := by
      have heq : raw1202step2 = (fun i j => raw1202step1 (permutation31 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1202step1 permutation31 permutation18
    _ = injectiveMoment H node959 := by rfl

def raw1203 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, 0, 0], ![0, 1, 0, -1], ![2, 1, -1, -2]]

def raw1203step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-2, 0, 1, 1], ![1, 0, 0, -1], ![3, 0, -1, -2]]

def raw1203step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, 0, -1], ![3, -1, -2]]

def raw1203step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2]]

theorem canonical1203 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1203 = injectiveMoment H node268 := by
  calc
    injectiveMoment H raw1203 = injectiveMoment H raw1203step0 := by
      have heq : raw1203step0 = raw1203.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1203).symm
    injectiveMoment H raw1203step0 = injectiveMoment H raw1203step1 := by
      have hz : ∀ i, raw1203step0 i (permutation15 0) = 0 := by decide +kernel
      have heq : raw1203step1 = (fun i j => raw1203step0 i (permutation15 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw1203step0 permutation15 hz
    injectiveMoment H raw1203step1 = injectiveMoment H raw1203step2 := by
      have heq : raw1203step2 = (fun i j => raw1203step1 (permutation31 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1203step1 permutation31 permutation6
    _ = injectiveMoment H node268 := by rfl

def raw1204 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, 1, -1], ![0, 1, -2, 1], ![0, 1, 0, -1], ![2, 0, 0, -2]]

theorem canonical1204 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1204 = injectiveMoment H node1501 := by
  rfl

def raw1205 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, 1, -1], ![0, 1, -2, 1], ![1, 0, 0, -1], ![1, 1, 0, -2]]

theorem canonical1205 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1205 = injectiveMoment H node1502 := by
  rfl

def raw1206 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, 1, -1], ![0, 1, -2, 1], ![2, 1, 0, -3]]

def raw1206step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-2, 0, 1, 1], ![1, 1, -2, 0], ![3, -1, 1, -3]]

def raw1206step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -3, 3], ![0, 0, 2, -2], ![0, 1, 1, -2], ![1, -2, 0, 1]]

theorem canonical1206 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1206 = injectiveMoment H node1329 := by
  calc
    injectiveMoment H raw1206 = injectiveMoment H raw1206step0 := by
      have heq : raw1206step0 = raw1206.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1206).symm
    injectiveMoment H raw1206step0 = injectiveMoment H raw1206step1 := by
      have heq : raw1206step1 = (fun i j => raw1206step0 (permutation27 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1206step0 permutation27 permutation18
    _ = injectiveMoment H node1329 := by rfl

def raw1207 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, 0, 0, -2]]

theorem canonical1207 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1207 = injectiveMoment H node1503 := by
  rfl

def raw1208 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, 0, -1, -1]]

theorem canonical1208 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1208 = injectiveMoment H node1504 := by
  rfl

def raw1209 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 1, 0, -2]]

theorem canonical1209 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1209 = injectiveMoment H node1505 := by
  rfl

def raw1210 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 1, -1, -1]]

theorem canonical1210 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1210 = injectiveMoment H node1506 := by
  rfl

def raw1211 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![2, 1, -1, -2]]

def raw1211step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-2, 0, 1, 1], ![1, 1, -1, -1], ![3, -1, 0, -2]]

def raw1211step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 0, 2, -2], ![0, 1, 1, -2], ![1, -1, -1, 1]]

theorem canonical1211 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1211 = injectiveMoment H node1222 := by
  calc
    injectiveMoment H raw1211 = injectiveMoment H raw1211step0 := by
      have heq : raw1211step0 = raw1211.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1211).symm
    injectiveMoment H raw1211step0 = injectiveMoment H raw1211step1 := by
      have heq : raw1211step1 = (fun i j => raw1211step0 (permutation27 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1211step0 permutation27 permutation18
    _ = injectiveMoment H node1222 := by rfl

def raw1212 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, -1, 0], ![2, 0, -1, -1]]

def raw1212step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, 0, -1, -1]]

theorem canonical1212 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1212 = injectiveMoment H node1504 := by
  calc
    injectiveMoment H raw1212 = injectiveMoment H raw1212step0 := by
      have heq : raw1212step0 = (fun i j => raw1212 (permutation35 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1212 permutation35 permutation9
    _ = injectiveMoment H node1504 := by rfl

def raw1213 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, -2, 0]]

theorem canonical1213 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1213 = injectiveMoment H node1507 := by
  rfl

def raw1214 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 1, -1, -1]]

def raw1214step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 1, -1, -1]]

theorem canonical1214 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1214 = injectiveMoment H node1506 := by
  calc
    injectiveMoment H raw1214 = injectiveMoment H raw1214step0 := by
      have heq : raw1214step0 = (fun i j => raw1214 (permutation35 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1214 permutation35 permutation15
    _ = injectiveMoment H node1506 := by rfl

def raw1215 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 1, -2, 0]]

theorem canonical1215 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1215 = injectiveMoment H node1508 := by
  rfl

end MUB6.Certificate.PairSemantics

end OAI
