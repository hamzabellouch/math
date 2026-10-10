import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes1
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes2
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes12
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes13
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes14
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes15
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes17
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes18
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes19
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes23
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes44

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw1248 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 1, -1, 0], ![0, 1, 1, -2], ![2, 0, -1, -1]]

def raw1248step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-2, 1, 1, 0], ![1, -1, 1, -1], ![3, 0, -2, -1]]

def raw1248step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![2, -1, -1, 0], ![-1, 1, -1, 1], ![-3, 0, 2, 1]]

def raw1248step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 2, 1, -3], ![1, -1, 1, -1]]

theorem canonical1248 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw1248 = injectiveMoment H node1036 := by
  calc
    injectiveMoment H raw1248 = injectiveMoment H raw1248step0 := by
      have heq : raw1248step0 = raw1248.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1248).symm
    injectiveMoment H raw1248step0 = injectiveMoment H raw1248step1 := by
      have heq : raw1248step1 = -raw1248step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw1248step0).symm
    injectiveMoment H raw1248step1 = injectiveMoment H raw1248step2 := by
      have heq : raw1248step2 = (fun i j => raw1248step1 (permutation16 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1248step1 permutation16 permutation18
    _ = injectiveMoment H node1036 := by rfl

def raw1249 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 1, -1, 0], ![1, 0, -2, 1], ![1, 1, 2, -4]]

def raw1249step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-2, 1, 0, 1], ![1, -1, -2, 2], ![3, 0, 1, -4]]

def raw1249step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 1, -2, 1], ![0, 1, 3, -4], ![1, 0, -2, 1]]

theorem canonical1249 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1249 = injectiveMoment H node848 := by
  calc
    injectiveMoment H raw1249 = injectiveMoment H raw1249step0 := by
      have heq : raw1249step0 = raw1249.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1249).symm
    injectiveMoment H raw1249step0 = injectiveMoment H raw1249step1 := by
      have heq : raw1249step1 = (fun i j => raw1249step0 (permutation22 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1249step0 permutation22 permutation17
    _ = injectiveMoment H node848 := by rfl

def raw1250 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 1, 1, -3]]

def raw1250step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-2, 1, 0, 1], ![1, -1, -1, 1], ![3, 0, 0, -3]]

def raw1250step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -3, 3], ![0, 1, 1, -2], ![1, 0, 1, -2]]

theorem canonical1250 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1250 = injectiveMoment H node1104 := by
  calc
    injectiveMoment H raw1250 = injectiveMoment H raw1250step0 := by
      have heq : raw1250step0 = raw1250.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1250).symm
    injectiveMoment H raw1250step0 = injectiveMoment H raw1250step1 := by
      have heq : raw1250step1 = (fun i j => raw1250step0 (permutation25 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1250step0 permutation25 permutation18
    _ = injectiveMoment H node1104 := by rfl

def raw1251 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 1, 0, -2]]

def raw1251step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-2, 1, 0, 1], ![1, -1, 0, 0], ![3, 0, -1, -2]]

def raw1251step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 0, 1], ![0, 1, 1, -2], ![1, 0, 1, -2]]

theorem canonical1251 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1251 = injectiveMoment H node1198 := by
  calc
    injectiveMoment H raw1251 = injectiveMoment H raw1251step0 := by
      have heq : raw1251step0 = raw1251.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1251).symm
    injectiveMoment H raw1251step0 = injectiveMoment H raw1251step1 := by
      have heq : raw1251step1 = (fun i j => raw1251step0 (permutation32 i) (permutation24 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1251step0 permutation32 permutation24
    _ = injectiveMoment H node1198 := by rfl

def raw1252 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 1, -1, 0], ![1, 0, 1, -2], ![1, 1, -1, -1]]

def raw1252step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-2, 1, 0, 1], ![1, -1, 1, -1], ![3, 0, -2, -1]]

def raw1252step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![2, -1, 0, -1], ![-1, 1, -1, 1], ![-3, 0, 2, 1]]

def raw1252step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, -1, 2], ![0, 1, 2, -3], ![1, 1, -1, -1]]

theorem canonical1252 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw1252 = injectiveMoment H node995 := by
  calc
    injectiveMoment H raw1252 = injectiveMoment H raw1252step0 := by
      have heq : raw1252step0 = raw1252.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1252).symm
    injectiveMoment H raw1252step0 = injectiveMoment H raw1252step1 := by
      have heq : raw1252step1 = -raw1252step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw1252step0).symm
    injectiveMoment H raw1252step1 = injectiveMoment H raw1252step2 := by
      have heq : raw1252step2 = (fun i j => raw1252step1 (permutation16 i) (permutation20 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1252step1 permutation16 permutation20
    _ = injectiveMoment H node995 := by rfl

def raw1253 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 1, -1, 0], ![1, 1, -1, -1], ![1, 0, 1, -2]]

def raw1253step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-2, 1, 1, 0], ![1, -1, -1, 1], ![3, 0, -1, -2]]

def raw1253step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![2, -1, -1, 0], ![-1, 1, 1, -1], ![-3, 0, 1, 2]]

def raw1253step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, -1, 2], ![0, 1, 2, -3], ![1, 1, -1, -1]]

theorem canonical1253 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw1253 = injectiveMoment H node995 := by
  calc
    injectiveMoment H raw1253 = injectiveMoment H raw1253step0 := by
      have heq : raw1253step0 = raw1253.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1253).symm
    injectiveMoment H raw1253step0 = injectiveMoment H raw1253step1 := by
      have heq : raw1253step1 = -raw1253step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw1253step0).symm
    injectiveMoment H raw1253step1 = injectiveMoment H raw1253step2 := by
      have heq : raw1253step2 = (fun i j => raw1253step1 (permutation16 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1253step1 permutation16 permutation18
    _ = injectiveMoment H node995 := by rfl

def raw1254 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 1, 0, -1], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def raw1254step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -2, -2, 3]]

theorem canonical1254 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1254 = injectiveMoment H node2823 := by
  calc
    injectiveMoment H raw1254 = injectiveMoment H raw1254step0 := by
      have heq : raw1254step0 = (fun i j => raw1254 (permutation89 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1254 permutation89 permutation21
    _ = injectiveMoment H node2823 := by rfl

def raw1255 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 1, 0, -1], ![0, 1, -1, 0], ![2, 0, 0, -2]]

def raw1255step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-2, 1, 1, 0], ![1, 0, -1, 0], ![3, -1, 0, -2]]

def raw1255step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![2, -1, -1, 0], ![-1, 0, 1, 0], ![-3, 1, 0, 2]]

def raw1255step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, 0, 2, -3]]

theorem canonical1255 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw1255 = injectiveMoment H node1032 := by
  calc
    injectiveMoment H raw1255 = injectiveMoment H raw1255step0 := by
      have heq : raw1255step0 = raw1255.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1255).symm
    injectiveMoment H raw1255step0 = injectiveMoment H raw1255step1 := by
      have heq : raw1255step1 = -raw1255step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw1255step0).symm
    injectiveMoment H raw1255step1 = injectiveMoment H raw1255step2 := by
      have heq : raw1255step2 = (fun i j => raw1255step1 (permutation15 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1255step1 permutation15 permutation18
    _ = injectiveMoment H node1032 := by rfl

def raw1256 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 0, -1]]

def raw1256step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -2, -2, 3]]

theorem canonical1256 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1256 = injectiveMoment H node2823 := by
  calc
    injectiveMoment H raw1256 = injectiveMoment H raw1256step0 := by
      have heq : raw1256step0 = (fun i j => raw1256 (permutation125 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1256 permutation125 permutation23
    _ = injectiveMoment H node2823 := by rfl

def raw1257 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, -1, -1]]

def raw1257step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-2, 1, 1, 0], ![1, 0, 0, -1], ![3, -1, -1, -1]]

def raw1257step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, -1, 1], ![0, 0, 2, -2], ![1, 1, 0, -2]]

theorem canonical1257 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1257 = injectiveMoment H node959 := by
  calc
    injectiveMoment H raw1257 = injectiveMoment H raw1257step0 := by
      have heq : raw1257step0 = raw1257.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1257).symm
    injectiveMoment H raw1257step0 = injectiveMoment H raw1257step1 := by
      have heq : raw1257step1 = (fun i j => raw1257step0 (permutation31 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1257step0 permutation31 permutation18
    _ = injectiveMoment H node959 := by rfl

def raw1258 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 1, 0, -1], ![0, 1, 1, -2], ![1, 0, -1, 0], ![1, 0, -1, 0]]

def raw1258step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 0, 1, -2]]

theorem canonical1258 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1258 = injectiveMoment H node1512 := by
  calc
    injectiveMoment H raw1258 = injectiveMoment H raw1258step0 := by
      have heq : raw1258step0 = (fun i j => raw1258 (permutation49 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1258 permutation49 permutation15
    _ = injectiveMoment H node1512 := by rfl

def raw1259 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 1, 0, -1], ![0, 1, 1, -2], ![2, 0, -2, 0]]

def raw1259step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-2, 1, 1, 0], ![1, 0, 1, -2], ![3, -1, -2, 0]]

def raw1259step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 2, -2], ![0, 1, -2, 1], ![1, 1, 0, -2]]

theorem canonical1259 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1259 = injectiveMoment H node804 := by
  calc
    injectiveMoment H raw1259 = injectiveMoment H raw1259step0 := by
      have heq : raw1259step0 = raw1259.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1259).symm
    injectiveMoment H raw1259step0 = injectiveMoment H raw1259step1 := by
      have heq : raw1259step1 = (fun i j => raw1259step0 (permutation28 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1259step0 permutation28 permutation18
    _ = injectiveMoment H node804 := by rfl

def raw1260 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 1, 0, -2]]

def raw1260step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-2, 1, 0, 1], ![1, 0, -1, 0], ![3, -1, 0, -2]]

def raw1260step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 0, 1], ![0, 1, 1, -2], ![1, 0, 1, -2]]

theorem canonical1260 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1260 = injectiveMoment H node1198 := by
  calc
    injectiveMoment H raw1260 = injectiveMoment H raw1260step0 := by
      have heq : raw1260step0 = raw1260.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1260).symm
    injectiveMoment H raw1260step0 = injectiveMoment H raw1260step1 := by
      have heq : raw1260step1 = (fun i j => raw1260step0 (permutation31 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1260step0 permutation31 permutation18
    _ = injectiveMoment H node1198 := by rfl

def raw1261 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 1, -1, -1]]

def raw1261step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-2, 1, 0, 1], ![1, 0, 0, -1], ![3, -1, -1, -1]]

def raw1261step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, -1, 1], ![0, 1, 1, -2], ![1, 0, 1, -2]]

theorem canonical1261 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1261 = injectiveMoment H node964 := by
  calc
    injectiveMoment H raw1261 = injectiveMoment H raw1261step0 := by
      have heq : raw1261step0 = raw1261.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1261).symm
    injectiveMoment H raw1261step0 = injectiveMoment H raw1261step1 := by
      have heq : raw1261step1 = (fun i j => raw1261step0 (permutation31 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1261step0 permutation31 permutation18
    _ = injectiveMoment H node964 := by rfl

def raw1262 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 1, 0, -1], ![1, 0, 1, -2], ![1, 1, -2, 0]]

def raw1262step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-2, 1, 0, 1], ![1, 0, 1, -2], ![3, -1, -2, 0]]

def raw1262step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 1, -2, 1], ![0, 1, 1, -2], ![1, 0, 1, -2]]

theorem canonical1262 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1262 = injectiveMoment H node815 := by
  calc
    injectiveMoment H raw1262 = injectiveMoment H raw1262step0 := by
      have heq : raw1262step0 = raw1262.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1262).symm
    injectiveMoment H raw1262step0 = injectiveMoment H raw1262step1 := by
      have heq : raw1262step1 = (fun i j => raw1262step0 (permutation31 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1262step0 permutation31 permutation18
    _ = injectiveMoment H node815 := by rfl

def raw1263 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 1, 0, -1], ![1, 1, -2, 0], ![1, 0, 1, -2]]

def raw1263step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-2, 1, 1, 0], ![1, 0, -2, 1], ![3, -1, 0, -2]]

def raw1263step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 1, -2, 1], ![0, 1, 1, -2], ![1, 0, 1, -2]]

theorem canonical1263 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1263 = injectiveMoment H node815 := by
  calc
    injectiveMoment H raw1263 = injectiveMoment H raw1263step0 := by
      have heq : raw1263step0 = raw1263.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1263).symm
    injectiveMoment H raw1263step0 = injectiveMoment H raw1263step1 := by
      have heq : raw1263step1 = (fun i j => raw1263step0 (permutation31 i) (permutation20 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1263step0 permutation31 permutation20
    _ = injectiveMoment H node815 := by rfl

def raw1264 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 1, 1, -2], ![0, 1, -1, 0], ![2, 0, -1, -1]]

def raw1264step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-2, 1, 1, 0], ![1, 1, -1, -1], ![3, -2, 0, -1]]

def raw1264step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![2, -1, -1, 0], ![-1, -1, 1, 1], ![-3, 2, 0, 1]]

def raw1264step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 2, 1, -3], ![1, -1, 1, -1]]

theorem canonical1264 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw1264 = injectiveMoment H node1036 := by
  calc
    injectiveMoment H raw1264 = injectiveMoment H raw1264step0 := by
      have heq : raw1264step0 = raw1264.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1264).symm
    injectiveMoment H raw1264step0 = injectiveMoment H raw1264step1 := by
      have heq : raw1264step1 = -raw1264step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw1264step0).symm
    injectiveMoment H raw1264step1 = injectiveMoment H raw1264step2 := by
      have heq : raw1264step2 = (fun i j => raw1264step1 (permutation16 i) (permutation24 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1264step1 permutation16 permutation24
    _ = injectiveMoment H node1036 := by rfl

def raw1265 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 1, 1, -2], ![0, 1, 0, -1], ![2, 0, -2, 0]]

def raw1265step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-2, 1, 1, 0], ![1, 1, 0, -2], ![3, -2, -1, 0]]

def raw1265step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 2, -2], ![0, 1, -2, 1], ![1, 1, 0, -2]]

theorem canonical1265 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1265 = injectiveMoment H node804 := by
  calc
    injectiveMoment H raw1265 = injectiveMoment H raw1265step0 := by
      have heq : raw1265step0 = raw1265.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1265).symm
    injectiveMoment H raw1265step0 = injectiveMoment H raw1265step1 := by
      have heq : raw1265step1 = (fun i j => raw1265step0 (permutation28 i) (permutation24 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1265step0 permutation28 permutation24
    _ = injectiveMoment H node804 := by rfl

def raw1266 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 1, 1, -2], ![1, 0, -1, 0], ![1, 1, -1, -1]]

def raw1266step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-2, 1, 0, 1], ![1, 1, -1, -1], ![3, -2, 0, -1]]

def raw1266step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![2, -1, 0, -1], ![-1, -1, 1, 1], ![-3, 2, 0, 1]]

def raw1266step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, -1, 2], ![0, 1, 2, -3], ![1, 1, -1, -1]]

theorem canonical1266 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw1266 = injectiveMoment H node995 := by
  calc
    injectiveMoment H raw1266 = injectiveMoment H raw1266step0 := by
      have heq : raw1266step0 = raw1266.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1266).symm
    injectiveMoment H raw1266step0 = injectiveMoment H raw1266step1 := by
      have heq : raw1266step1 = -raw1266step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw1266step0).symm
    injectiveMoment H raw1266step1 = injectiveMoment H raw1266step2 := by
      have heq : raw1266step2 = (fun i j => raw1266step1 (permutation10 i) (permutation26 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1266step1 permutation10 permutation26
    _ = injectiveMoment H node995 := by rfl

def raw1267 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 1, 1, -2], ![1, 0, 0, -1], ![1, 1, -2, 0]]

def raw1267step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-2, 1, 0, 1], ![1, 1, 0, -2], ![3, -2, -1, 0]]

def raw1267step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 1, -2, 1], ![0, 1, 1, -2], ![1, 0, 1, -2]]

theorem canonical1267 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1267 = injectiveMoment H node815 := by
  calc
    injectiveMoment H raw1267 = injectiveMoment H raw1267step0 := by
      have heq : raw1267step0 = raw1267.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1267).symm
    injectiveMoment H raw1267step0 = injectiveMoment H raw1267step1 := by
      have heq : raw1267step1 = (fun i j => raw1267step0 (permutation32 i) (permutation24 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1267step0 permutation32 permutation24
    _ = injectiveMoment H node815 := by rfl

def raw1268 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 2, -2, 0], ![1, 0, 0, -1], ![1, 0, 1, -2]]

def raw1268step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-2, 2, 0, 0], ![1, -2, 0, 1], ![3, 0, -1, -2]]

def raw1268step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 2, -2], ![0, 1, -2, 1], ![1, 1, 0, -2]]

theorem canonical1268 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1268 = injectiveMoment H node804 := by
  calc
    injectiveMoment H raw1268 = injectiveMoment H raw1268step0 := by
      have heq : raw1268step0 = raw1268.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1268).symm
    injectiveMoment H raw1268step0 = injectiveMoment H raw1268step1 := by
      have heq : raw1268step1 = (fun i j => raw1268step0 (permutation30 i) (permutation26 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1268step0 permutation30 permutation26
    _ = injectiveMoment H node804 := by rfl

def raw1269 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 2, -1, -1], ![1, 0, -1, 0], ![1, 0, 1, -2]]

def raw1269step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-2, 2, 0, 0], ![1, -1, -1, 1], ![3, -1, 0, -2]]

def raw1269step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![2, -2, 0, 0], ![-1, 1, 1, -1], ![-3, 1, 0, 2]]

def raw1269step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 2, 1, -3], ![1, -1, 1, -1]]

theorem canonical1269 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw1269 = injectiveMoment H node1036 := by
  calc
    injectiveMoment H raw1269 = injectiveMoment H raw1269step0 := by
      have heq : raw1269step0 = raw1269.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1269).symm
    injectiveMoment H raw1269step0 = injectiveMoment H raw1269step1 := by
      have heq : raw1269step1 = -raw1269step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw1269step0).symm
    injectiveMoment H raw1269step1 = injectiveMoment H raw1269step2 := by
      have heq : raw1269step2 = (fun i j => raw1269step1 (permutation10 i) (permutation26 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1269step1 permutation10 permutation26
    _ = injectiveMoment H node1036 := by rfl

def raw1270 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 2, 1, -3], ![1, 0, -1, 0], ![1, 0, -1, 0]]

def raw1270step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-2, 2, 0, 0], ![1, 1, -1, -1], ![3, -3, 0, 0]]

def raw1270step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![2, -2, 0, 0], ![-1, -1, 1, 1], ![-3, 3, 0, 0]]

def raw1270step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 0, 3, -3], ![1, 1, -1, -1]]

theorem canonical1270 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw1270 = injectiveMoment H node1028 := by
  calc
    injectiveMoment H raw1270 = injectiveMoment H raw1270step0 := by
      have heq : raw1270step0 = raw1270.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1270).symm
    injectiveMoment H raw1270step0 = injectiveMoment H raw1270step1 := by
      have heq : raw1270step1 = -raw1270step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw1270step0).symm
    injectiveMoment H raw1270step1 = injectiveMoment H raw1270step2 := by
      have heq : raw1270step2 = (fun i j => raw1270step1 (permutation10 i) (permutation26 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1270step1 permutation10 permutation26
    _ = injectiveMoment H node1028 := by rfl

def raw1271 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![1, 1, -2, 0], ![0, 1, 1, -2], ![1, 0, 0, -1]]

def raw1271step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![-2, 1, 1, 0], ![1, -2, 1, 0], ![3, 0, -2, -1]]

def raw1271step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 1, -2, 1], ![0, 1, 1, -2], ![1, 0, 1, -2]]

theorem canonical1271 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1271 = injectiveMoment H node815 := by
  calc
    injectiveMoment H raw1271 = injectiveMoment H raw1271step0 := by
      have heq : raw1271step0 = raw1271.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1271).symm
    injectiveMoment H raw1271step0 = injectiveMoment H raw1271step1 := by
      have heq : raw1271step1 = (fun i j => raw1271step0 (permutation32 i) (permutation32 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1271step0 permutation32 permutation32
    _ = injectiveMoment H node815 := by rfl

def raw1272 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![-1, 1, 2, -2], ![3, 1, -4, 0]]

def raw1272step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![2, 2, -4], ![2, -2, 0]]

def raw1272step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![2, -1, -1], ![-2, -2, 4], ![-2, 2, 0]]

def raw1272step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![1, 2, -3], ![2, -2, 0]]

theorem canonical1272 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw1272 = injectiveMoment H node135 := by
  calc
    injectiveMoment H raw1272 = injectiveMoment H raw1272step0 := by
      have heq : raw1272step0 = raw1272.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1272).symm
    injectiveMoment H raw1272step0 = injectiveMoment H raw1272step1 := by
      have heq : raw1272step1 = -raw1272step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw1272step0).symm
    injectiveMoment H raw1272step1 = injectiveMoment H raw1272step2 := by
      have heq : raw1272step2 = (fun i j => raw1272step1 (permutation23 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1272step1 permutation23 permutation5
    _ = injectiveMoment H node135 := by rfl

def raw1273 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![-1, 2, 1, -2], ![3, 0, -3, 0]]

def raw1273step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![2, 1, -3], ![2, -2, 0]]

def raw1273step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![3, -1, -2]]

theorem canonical1273 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1273 = injectiveMoment H node101 := by
  calc
    injectiveMoment H raw1273 = injectiveMoment H raw1273step0 := by
      have heq : raw1273step0 = raw1273.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1273).symm
    injectiveMoment H raw1273step0 = injectiveMoment H raw1273step1 := by
      have heq : raw1273step1 = (fun i j => raw1273step0 (permutation26 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1273step0 permutation26 permutation8
    _ = injectiveMoment H node101 := by rfl

def raw1274 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 0, -2, 2], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, 0, -2]]

theorem canonical1274 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1274 = injectiveMoment H node1514 := by
  rfl

def raw1275 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 0, -2, 2], ![0, 1, 0, -1], ![0, 1, 1, -2], ![2, 0, -1, -1]]

theorem canonical1275 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1275 = injectiveMoment H node1515 := by
  rfl

def raw1276 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 1, 0, -2]]

theorem canonical1276 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1276 = injectiveMoment H node1516 := by
  rfl

def raw1277 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, 1, 0, -2], ![1, 0, 0, -1]]

def raw1277step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 1, 0, -2]]

theorem canonical1277 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1277 = injectiveMoment H node1516 := by
  calc
    injectiveMoment H raw1277 = injectiveMoment H raw1277step0 := by
      have heq : raw1277step0 = (fun i j => raw1277 (permutation34 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1277 permutation34 permutation9
    _ = injectiveMoment H node1516 := by rfl

def raw1278 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 0, -2, 2], ![0, 1, 0, -1], ![2, 1, 0, -3]]

def raw1278step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-2, 0, 1, 1], ![2, -2, 0, 0], ![2, 2, -1, -3]]

def raw1278step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![2, 0, -1, -1], ![-2, 2, 0, 0], ![-2, -2, 1, 3]]

def raw1278step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, -2, 2], ![0, 2, 0, -2], ![1, -2, 3, -2]]

theorem canonical1278 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw1278 = injectiveMoment H node1255 := by
  calc
    injectiveMoment H raw1278 = injectiveMoment H raw1278step0 := by
      have heq : raw1278step0 = raw1278.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1278).symm
    injectiveMoment H raw1278step0 = injectiveMoment H raw1278step1 := by
      have heq : raw1278step1 = -raw1278step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw1278step0).symm
    injectiveMoment H raw1278step1 = injectiveMoment H raw1278step2 := by
      have heq : raw1278step2 = (fun i j => raw1278step1 (permutation15 i) (permutation24 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1278step1 permutation15 permutation24
    _ = injectiveMoment H node1255 := by rfl

def raw1279 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 0, -2, 2], ![0, 1, 1, -2], ![0, 1, 0, -1], ![2, 0, -1, -1]]

def raw1279step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 0, -2, 2], ![0, 1, 0, -1], ![0, 1, 1, -2], ![2, 0, -1, -1]]

theorem canonical1279 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1279 = injectiveMoment H node1515 := by
  calc
    injectiveMoment H raw1279 = injectiveMoment H raw1279step0 := by
      have heq : raw1279step0 = (fun i j => raw1279 (permutation35 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1279 permutation35 permutation9
    _ = injectiveMoment H node1515 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
