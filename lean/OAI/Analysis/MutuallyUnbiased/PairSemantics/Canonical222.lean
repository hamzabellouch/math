import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes0
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes2
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes3
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes4
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes12
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes15
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes17
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes19
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes42
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes43

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw7104 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 0, 2, -2], ![0, 1, 1, -2], ![1, -1, -1, 1]]

theorem canonical7104 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7104 = injectiveMoment H node1222 := by
  rfl

def raw7105 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 0, 2, -2], ![0, 2, -1, -1], ![1, -2, 1, 0]]

theorem canonical7105 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7105 = injectiveMoment H node1223 := by
  rfl

def raw7106 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 0, 2, -2], ![1, 0, 0, -1]]

def raw7106step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 2, -2], ![1, 0, -1]]

theorem canonical7106 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7106 = injectiveMoment H node57 := by
  calc
    injectiveMoment H raw7106 = injectiveMoment H raw7106step0 := by
      have hz : ∀ i, raw7106 i (permutation15 0) = 0 := by decide +kernel
      have heq : raw7106step0 = (fun i j => raw7106 i (permutation15 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw7106 permutation15 hz
    _ = injectiveMoment H node57 := by rfl

def raw7107 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 0, 3, -3], ![0, 1, -1, 0], ![1, -1, 0, 0]]

theorem canonical7107 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7107 = injectiveMoment H node1225 := by
  rfl

def raw7108 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 0, 3, -3], ![1, 0, -1, 0]]

def raw7108step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 3, -3], ![1, -1, 0]]

theorem canonical7108 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7108 = injectiveMoment H node58 := by
  calc
    injectiveMoment H raw7108 = injectiveMoment H raw7108step0 := by
      have hz : ∀ i, raw7108 i (permutation15 0) = 0 := by decide +kernel
      have heq : raw7108step0 = (fun i j => raw7108 i (permutation15 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw7108 permutation15 hz
    _ = injectiveMoment H node58 := by rfl

def raw7109 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 0, 4, -4], ![1, 0, -2, 1]]

def raw7109step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 4, -4], ![1, -2, 1]]

theorem canonical7109 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7109 = injectiveMoment H node59 := by
  calc
    injectiveMoment H raw7109 = injectiveMoment H raw7109step0 := by
      have hz : ∀ i, raw7109 i (permutation15 0) = 0 := by decide +kernel
      have heq : raw7109step0 = (fun i j => raw7109 i (permutation15 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw7109 permutation15 hz
    _ = injectiveMoment H node59 := by rfl

def raw7110 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 1, -2, 1], ![1, -1, 4, -4]]

def raw7110step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 1, -1], ![-2, -2, 4], ![3, 1, -4]]

def raw7110step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, -1, 1], ![1, 0, -1], ![1, 3, -4]]

theorem canonical7110 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7110 = injectiveMoment H node143 := by
  calc
    injectiveMoment H raw7110 = injectiveMoment H raw7110step0 := by
      have heq : raw7110step0 = raw7110.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7110).symm
    injectiveMoment H raw7110step0 = injectiveMoment H raw7110step1 := by
      have heq : raw7110step1 = (fun i j => raw7110step0 (permutation21 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7110step0 permutation21 permutation5
    _ = injectiveMoment H node143 := by rfl

def raw7111 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -2, 3, -2]]

def raw7111step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 1, 1, -2], ![-2, -1, 0, 3], ![3, 0, -1, -2]]

def raw7111step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 0, -1], ![0, -1, -1, 2], ![2, 1, 0, -3], ![-3, 0, 1, 2]]

def raw7111step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 1, -1], ![0, 1, -3, 2], ![1, 0, 2, -3]]

theorem canonical7111 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7111 = injectiveMoment H node1046 := by
  calc
    injectiveMoment H raw7111 = injectiveMoment H raw7111step0 := by
      have heq : raw7111step0 = raw7111.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7111).symm
    injectiveMoment H raw7111step0 = injectiveMoment H raw7111step1 := by
      have heq : raw7111step1 = -raw7111step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7111step0).symm
    injectiveMoment H raw7111step1 = injectiveMoment H raw7111step2 := by
      have heq : raw7111step2 = (fun i j => raw7111step1 (permutation16 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7111step1 permutation16 permutation17
    _ = injectiveMoment H node1046 := by rfl

def raw7112 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, -2, 1, 0]]

theorem canonical7112 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7112 = injectiveMoment H node1231 := by
  rfl

def raw7113 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, -2, 0, 1]]

theorem canonical7113 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7113 = injectiveMoment H node1232 := by
  rfl

def raw7114 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 1, -1, 0], ![1, -1, 3, -3]]

def raw7114step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 1, -1], ![-2, -1, 3], ![3, 0, -3]]

def raw7114step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -1, 1], ![0, 3, -3], ![1, 0, -1]]

theorem canonical7114 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7114 = injectiveMoment H node269 := by
  calc
    injectiveMoment H raw7114 = injectiveMoment H raw7114step0 := by
      have heq : raw7114step0 = raw7114.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7114).symm
    injectiveMoment H raw7114step0 = injectiveMoment H raw7114step1 := by
      have heq : raw7114step1 = (fun i j => raw7114step0 (permutation22 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7114step0 permutation22 permutation5
    _ = injectiveMoment H node269 := by rfl

def raw7115 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -2, 2, -1]]

def raw7115step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 1, 1, -2], ![-2, 0, 0, 2], ![3, -1, -1, -1]]

def raw7115step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 1, -1], ![0, 0, 2, -2], ![1, 1, -2, 0]]

theorem canonical7115 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7115 = injectiveMoment H node967 := by
  calc
    injectiveMoment H raw7115 = injectiveMoment H raw7115step0 := by
      have heq : raw7115step0 = raw7115.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7115).symm
    injectiveMoment H raw7115step0 = injectiveMoment H raw7115step1 := by
      have heq : raw7115step1 = (fun i j => raw7115step0 (permutation28 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7115step0 permutation28 permutation18
    _ = injectiveMoment H node967 := by rfl

def raw7116 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 1, 0, -1], ![0, 1, 1, -2], ![1, -2, 1, 0]]

def raw7116step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, 1, -2, 0]]

theorem canonical7116 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7116 = injectiveMoment H node801 := by
  calc
    injectiveMoment H raw7116 = injectiveMoment H raw7116step0 := by
      have heq : raw7116step0 = (fun i j => raw7116 (permutation9 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7116 permutation9 permutation11
    _ = injectiveMoment H node801 := by rfl

def raw7117 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 1, 0, -1], ![1, -1, 2, -2]]

def raw7117step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 1, -1], ![-2, 0, 2], ![3, -1, -2]]

def raw7117step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0]]

theorem canonical7117 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7117 = injectiveMoment H node272 := by
  calc
    injectiveMoment H raw7117 = injectiveMoment H raw7117step0 := by
      have heq : raw7117step0 = raw7117.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7117).symm
    injectiveMoment H raw7117step0 = injectiveMoment H raw7117step1 := by
      have heq : raw7117step1 = (fun i j => raw7117step0 (permutation28 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7117step0 permutation28 permutation6
    _ = injectiveMoment H node272 := by rfl

def raw7118 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 1, 1, -2], ![0, 1, 0, -1], ![1, -2, 1, 0]]

def raw7118step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, 1, -2, 0]]

theorem canonical7118 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7118 = injectiveMoment H node801 := by
  calc
    injectiveMoment H raw7118 = injectiveMoment H raw7118step0 := by
      have heq : raw7118step0 = (fun i j => raw7118 (permutation11 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7118 permutation11 permutation11
    _ = injectiveMoment H node801 := by rfl

def raw7119 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 1, 1, -2], ![1, -1, 1, -1]]

def raw7119step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 1, -1], ![-2, 1, 1], ![3, -2, -1]]

def raw7119step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

theorem canonical7119 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7119 = injectiveMoment H node181 := by
  calc
    injectiveMoment H raw7119 = injectiveMoment H raw7119step0 := by
      have heq : raw7119step0 = raw7119.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7119).symm
    injectiveMoment H raw7119step0 = injectiveMoment H raw7119step1 := by
      have heq : raw7119step1 = (fun i j => raw7119step0 (permutation27 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7119step0 permutation27 permutation6
    _ = injectiveMoment H node181 := by rfl

def raw7120 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 1, 2, -3], ![1, -1, 0, 0]]

def raw7120step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 1, -1], ![-2, 2, 0], ![3, -3, 0]]

def raw7120step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -2, 2], ![0, 3, -3], ![1, -1, 0]]

theorem canonical7120 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7120 = injectiveMoment H node292 := by
  calc
    injectiveMoment H raw7120 = injectiveMoment H raw7120step0 := by
      have heq : raw7120step0 = raw7120.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7120).symm
    injectiveMoment H raw7120step0 = injectiveMoment H raw7120step1 := by
      have heq : raw7120step1 = (fun i j => raw7120step0 (permutation18 i) (permutation7 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7120step0 permutation18 permutation7
    _ = injectiveMoment H node292 := by rfl

def raw7121 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 1, 3, -4], ![1, -1, -1, 1]]

def raw7121step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 1, -1], ![-2, 3, -1], ![3, -4, 1]]

def raw7121step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![0, -1, 1], ![2, -3, 1], ![-3, 4, -1]]

def raw7121step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 1, 0], ![1, 0, -1], ![1, 2, -3]]

theorem canonical7121 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7121 = injectiveMoment H node243 := by
  calc
    injectiveMoment H raw7121 = injectiveMoment H raw7121step0 := by
      have heq : raw7121step0 = raw7121.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7121).symm
    injectiveMoment H raw7121step0 = injectiveMoment H raw7121step1 := by
      have heq : raw7121step1 = -raw7121step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7121step0).symm
    injectiveMoment H raw7121step1 = injectiveMoment H raw7121step2 := by
      have heq : raw7121step2 = (fun i j => raw7121step1 (permutation27 i) (permutation7 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7121step1 permutation27 permutation7
    _ = injectiveMoment H node243 := by rfl

def raw7122 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 2, -1, -1], ![1, -2, 3, -2]]

def raw7122step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 2, -2], ![-2, -1, 3], ![3, -1, -2]]

def raw7122step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![0, -2, 2], ![2, 1, -3], ![-3, 1, 2]]

def raw7122step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -3, 2], ![1, 2, -3]]

theorem canonical7122 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7122 = injectiveMoment H node209 := by
  calc
    injectiveMoment H raw7122 = injectiveMoment H raw7122step0 := by
      have heq : raw7122step0 = raw7122.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7122).symm
    injectiveMoment H raw7122step0 = injectiveMoment H raw7122step1 := by
      have heq : raw7122step1 = -raw7122step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7122step0).symm
    injectiveMoment H raw7122step1 = injectiveMoment H raw7122step2 := by
      have heq : raw7122step2 = (fun i j => raw7122step1 (permutation16 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7122step1 permutation16 permutation5
    _ = injectiveMoment H node209 := by rfl

def raw7123 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 2, 1, -3], ![1, -2, 1, 0]]

def raw7123step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 2, -2], ![-2, 1, 1], ![3, -3, 0]]

def raw7123step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![1, -2, 1], ![1, -1, 0]]

theorem canonical7123 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7123 = injectiveMoment H node215 := by
  calc
    injectiveMoment H raw7123 = injectiveMoment H raw7123step0 := by
      have heq : raw7123step0 = raw7123.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7123).symm
    injectiveMoment H raw7123step0 = injectiveMoment H raw7123step1 := by
      have heq : raw7123step1 = (fun i j => raw7123step0 (permutation20 i) (permutation7 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7123step0 permutation20 permutation7
    _ = injectiveMoment H node215 := by rfl

def raw7124 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 2, 2, -4], ![1, -2, 0, 1]]

def raw7124step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 2, -2], ![-2, 2, 0], ![3, -4, 1]]

def raw7124step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![1, -1, 0], ![1, 3, -4]]

theorem canonical7124 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7124 = injectiveMoment H node201 := by
  calc
    injectiveMoment H raw7124 = injectiveMoment H raw7124step0 := by
      have heq : raw7124step0 = raw7124.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7124).symm
    injectiveMoment H raw7124step0 = injectiveMoment H raw7124step1 := by
      have heq : raw7124step1 = (fun i j => raw7124step0 (permutation17 i) (permutation7 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7124step0 permutation17 permutation7
    _ = injectiveMoment H node201 := by rfl

def raw7125 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![1, -2, 0, 1], ![0, 2, 2, -4]]

def raw7125step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![0, -2, 2], ![-2, 0, 2], ![3, 1, -4]]

def raw7125step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![1, -1, 0], ![1, 3, -4]]

theorem canonical7125 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7125 = injectiveMoment H node201 := by
  calc
    injectiveMoment H raw7125 = injectiveMoment H raw7125step0 := by
      have heq : raw7125step0 = raw7125.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7125).symm
    injectiveMoment H raw7125step0 = injectiveMoment H raw7125step1 := by
      have heq : raw7125step1 = (fun i j => raw7125step0 (permutation17 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7125step0 permutation17 permutation5
    _ = injectiveMoment H node201 := by rfl

def raw7126 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![1, -2, 1, 0], ![0, 2, 1, -3]]

def raw7126step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![0, -2, 2], ![-2, 1, 1], ![3, 0, -3]]

def raw7126step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![1, -2, 1], ![1, -1, 0]]

theorem canonical7126 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7126 = injectiveMoment H node215 := by
  calc
    injectiveMoment H raw7126 = injectiveMoment H raw7126step0 := by
      have heq : raw7126step0 = raw7126.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7126).symm
    injectiveMoment H raw7126step0 = injectiveMoment H raw7126step1 := by
      have heq : raw7126step1 = (fun i j => raw7126step0 (permutation20 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7126step0 permutation20 permutation5
    _ = injectiveMoment H node215 := by rfl

def raw7127 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![1, -2, 2, -1], ![0, 2, 0, -2]]

def raw7127step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![0, -2, 2], ![-2, 2, 0], ![3, -1, -2]]

def raw7127step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]

theorem canonical7127 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7127 = injectiveMoment H node177 := by
  calc
    injectiveMoment H raw7127 = injectiveMoment H raw7127step0 := by
      have heq : raw7127step0 = raw7127.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7127).symm
    injectiveMoment H raw7127step0 = injectiveMoment H raw7127step1 := by
      have heq : raw7127step1 = (fun i j => raw7127step0 (permutation28 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7127step0 permutation28 permutation8
    _ = injectiveMoment H node177 := by rfl

def raw7128 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![1, -2, 3, -2], ![0, 2, -1, -1]]

def raw7128step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![0, -2, 2], ![-2, 3, -1], ![3, -2, -1]]

def raw7128step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -1, 0], ![0, 2, -2], ![2, -3, 1], ![-3, 2, 1]]

def raw7128step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -3, 2], ![1, 2, -3]]

theorem canonical7128 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7128 = injectiveMoment H node209 := by
  calc
    injectiveMoment H raw7128 = injectiveMoment H raw7128step0 := by
      have heq : raw7128step0 = raw7128.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7128).symm
    injectiveMoment H raw7128step0 = injectiveMoment H raw7128step1 := by
      have heq : raw7128step1 = -raw7128step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7128step0).symm
    injectiveMoment H raw7128step1 = injectiveMoment H raw7128step2 := by
      have heq : raw7128step2 = (fun i j => raw7128step1 (permutation16 i) (permutation7 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7128step1 permutation16 permutation7
    _ = injectiveMoment H node209 := by rfl

def raw7129 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![1, -1, 1, -1], ![0, 1, 1, -2]]

def raw7129step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![0, -1, 1], ![-2, 1, 1], ![3, -1, -2]]

def raw7129step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

theorem canonical7129 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7129 = injectiveMoment H node181 := by
  calc
    injectiveMoment H raw7129 = injectiveMoment H raw7129step0 := by
      have heq : raw7129step0 = raw7129.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7129).symm
    injectiveMoment H raw7129step0 = injectiveMoment H raw7129step1 := by
      have heq : raw7129step1 = (fun i j => raw7129step0 (permutation27 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7129step0 permutation27 permutation8
    _ = injectiveMoment H node181 := by rfl

def raw7130 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![1, -1, 4, -4], ![0, 1, -2, 1]]

def raw7130step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![0, -1, 1], ![-2, 4, -2], ![3, -4, 1]]

def raw7130step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, -1, 1], ![1, 0, -1], ![1, 3, -4]]

theorem canonical7130 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7130 = injectiveMoment H node143 := by
  calc
    injectiveMoment H raw7130 = injectiveMoment H raw7130step0 := by
      have heq : raw7130step0 = raw7130.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7130).symm
    injectiveMoment H raw7130step0 = injectiveMoment H raw7130step1 := by
      have heq : raw7130step1 = (fun i j => raw7130step0 (permutation21 i) (permutation7 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7130step0 permutation21 permutation7
    _ = injectiveMoment H node143 := by rfl

def raw7131 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![-1, -1, 1, 1], ![1, 0, 1, -2], ![1, 1, -1, -1]]

def raw7131step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, -1, 2], ![0, 1, 1, -2], ![1, 1, -1, -1]]

theorem canonical7131 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7131 = injectiveMoment H node1096 := by
  calc
    injectiveMoment H raw7131 = injectiveMoment H raw7131step0 := by
      have heq : raw7131step0 = (fun i j => raw7131 (permutation15 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7131 permutation15 permutation15
    _ = injectiveMoment H node1096 := by rfl

def raw7132 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![-1, 0, -1, 2], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 3, -4]]

def raw7132step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 0, 1, -2], ![1, 0, 1, -2], ![0, -1, 1, 0], ![-1, 1, 0, 0], ![-1, 0, -3, 4]]

def raw7132step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -1, -3, 4], ![0, 1, 1, -2], ![0, 1, 1, -2], ![1, -1, 0, 0]]

theorem canonical7132 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7132 = injectiveMoment H node2809 := by
  calc
    injectiveMoment H raw7132 = injectiveMoment H raw7132step0 := by
      have heq : raw7132step0 = -raw7132 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7132).symm
    injectiveMoment H raw7132step0 = injectiveMoment H raw7132step1 := by
      have heq : raw7132step1 = (fun i j => raw7132step0 (permutation98 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7132step0 permutation98 permutation15
    _ = injectiveMoment H node2809 := by rfl

def raw7133 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![-1, 0, -1, 2], ![0, 1, 3, -4], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def raw7133step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 0, 1, -2], ![1, 0, 1, -2], ![0, -1, -3, 4], ![-1, 1, 0, 0], ![-1, 0, 1, 0]]

def raw7133step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, -1, 1, 0], ![0, 1, 1, -2], ![0, 1, 1, -2], ![1, -1, 0, 0]]

theorem canonical7133 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7133 = injectiveMoment H node2688 := by
  calc
    injectiveMoment H raw7133 = injectiveMoment H raw7133step0 := by
      have heq : raw7133step0 = -raw7133 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7133).symm
    injectiveMoment H raw7133step0 = injectiveMoment H raw7133step1 := by
      have heq : raw7133step1 = (fun i j => raw7133step0 (permutation98 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7133step0 permutation98 permutation15
    _ = injectiveMoment H node2688 := by rfl

def raw7134 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![-1, 0, 2, -1], ![1, -1, 1, -1], ![1, 1, -2, 0]]

def raw7134step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 1, -2], ![1, 0, -2, 1], ![-1, 1, -1, 1], ![-1, -1, 2, 0]]

def raw7134step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, -2, 1], ![0, 1, 1, -2], ![1, -1, 1, -1]]

theorem canonical7134 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7134 = injectiveMoment H node1078 := by
  calc
    injectiveMoment H raw7134 = injectiveMoment H raw7134step0 := by
      have heq : raw7134step0 = -raw7134 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7134).symm
    injectiveMoment H raw7134step0 = injectiveMoment H raw7134step1 := by
      have heq : raw7134step1 = (fun i j => raw7134step0 (permutation27 i) (permutation16 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7134step0 permutation27 permutation16
    _ = injectiveMoment H node1078 := by rfl

def raw7135 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![-1, 0, 3, -2], ![0, 1, -2, 1], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw7135step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 0, 1, -2], ![1, 0, -3, 2], ![0, -1, 2, -1], ![-1, 1, 0, 0], ![-1, 0, 0, 1]]

def raw7135step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 1, 0], ![0, 1, -2, 1], ![0, 1, 2, -3], ![1, -1, 0, 0]]

theorem canonical7135 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7135 = injectiveMoment H node2726 := by
  calc
    injectiveMoment H raw7135 = injectiveMoment H raw7135step0 := by
      have heq : raw7135step0 = -raw7135 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7135).symm
    injectiveMoment H raw7135step0 = injectiveMoment H raw7135step1 := by
      have heq : raw7135step1 = (fun i j => raw7135step0 (permutation98 i) (permutation16 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7135step0 permutation98 permutation16
    _ = injectiveMoment H node2726 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
