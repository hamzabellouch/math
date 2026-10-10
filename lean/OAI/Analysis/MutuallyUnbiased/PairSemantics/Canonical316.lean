import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes1
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes2
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes3
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes4
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes20

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw10112 : Matrix (Fin 5) (Fin 2) ℤ := ![![1, -1], ![1, -1], ![0, 0], ![-1, 1], ![-1, 1]]

def raw10112step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![1, -1], ![1, -1], ![-1, 1], ![-1, 1]]

def raw10112step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![1, -1]]

theorem canonical10112 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw10112 = injectiveMoment H node65 := by
  calc
    injectiveMoment H raw10112 = injectiveMoment H raw10112step0 := by
      have hz : ∀ j, raw10112 (permutation80 0) j = 0 := by decide +kernel
      have heq : raw10112step0 = (fun i j => raw10112 (permutation80 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw10112 permutation80 hz
    injectiveMoment H raw10112step0 = injectiveMoment H raw10112step1 := by
      have heq : raw10112step1 = (fun i j => raw10112step0 (permutation25 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw10112step0 permutation25 permutation1
    _ = injectiveMoment H node65 := by rfl

def raw10113 : Matrix (Fin 6) (Fin 2) ℤ := ![![1, -1], ![1, -1], ![1, -1], ![-1, 1], ![-1, 1], ![-1, 1]]

def raw10113step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]

theorem canonical10113 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw10113 = injectiveMoment H node1323 := by
  calc
    injectiveMoment H raw10113 = injectiveMoment H raw10113step0 := by
      have heq : raw10113step0 = (fun i j => raw10113 (permutation252 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw10113 permutation252 permutation1
    _ = injectiveMoment H node1323 := by rfl

def raw10114 : Matrix (Fin 5) (Fin 2) ℤ := ![![1, -1], ![2, -2], ![-1, 1], ![-1, 1], ![-1, 1]]

def raw10114step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]

theorem canonical10114 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw10114 = injectiveMoment H node232 := by
  calc
    injectiveMoment H raw10114 = injectiveMoment H raw10114step0 := by
      have heq : raw10114step0 = (fun i j => raw10114 (permutation57 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw10114 permutation57 permutation2
    _ = injectiveMoment H node232 := by rfl

def raw10115 : Matrix (Fin 3) (Fin 4) ℤ := ![![1, -1, 1, -1], ![-5, 2, 1, 2], ![4, -1, -2, -1]]

def raw10115step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -5, 4], ![-1, 2, -1], ![1, 1, -2], ![-1, 2, -1]]

def raw10115step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 5, -4], ![1, -2, 1], ![-1, -1, 2], ![1, -2, 1]]

def raw10115step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -4, 5], ![-1, 2, -1], ![1, 1, -2], ![1, 1, -2]]

theorem canonical10115 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw10115 = injectiveMoment H node234 := by
  calc
    injectiveMoment H raw10115 = injectiveMoment H raw10115step0 := by
      have heq : raw10115step0 = raw10115.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw10115).symm
    injectiveMoment H raw10115step0 = injectiveMoment H raw10115step1 := by
      have heq : raw10115step1 = -raw10115step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw10115step0).symm
    injectiveMoment H raw10115step1 = injectiveMoment H raw10115step2 := by
      have heq : raw10115step2 = (fun i j => raw10115step1 (permutation11 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw10115step1 permutation11 permutation4
    _ = injectiveMoment H node234 := by rfl

def raw10116 : Matrix (Fin 3) (Fin 4) ℤ := ![![1, -1, 1, -1], ![-4, 2, 1, 1], ![3, -1, -2, 0]]

def raw10116step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -4, 3], ![-1, 2, -1], ![1, 1, -2], ![-1, 1, 0]]

def raw10116step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 4, -3], ![1, -2, 1], ![-1, -1, 2], ![1, -1, 0]]

def raw10116step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 2, -1], ![1, 0, -1], ![1, 1, -2]]

theorem canonical10116 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw10116 = injectiveMoment H node246 := by
  calc
    injectiveMoment H raw10116 = injectiveMoment H raw10116step0 := by
      have heq : raw10116step0 = raw10116.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw10116).symm
    injectiveMoment H raw10116step0 = injectiveMoment H raw10116step1 := by
      have heq : raw10116step1 = -raw10116step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw10116step0).symm
    injectiveMoment H raw10116step1 = injectiveMoment H raw10116step2 := by
      have heq : raw10116step2 = (fun i j => raw10116step1 (permutation12 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw10116step1 permutation12 permutation4
    _ = injectiveMoment H node246 := by rfl

def raw10117 : Matrix (Fin 3) (Fin 4) ℤ := ![![1, -1, 1, -1], ![-4, 3, 1, 0], ![3, -2, -2, 1]]

def raw10117step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -4, 3], ![-1, 3, -2], ![1, 1, -2], ![-1, 0, 1]]

def raw10117step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 4, -3], ![1, -3, 2], ![-1, -1, 2], ![1, 0, -1]]

def raw10117step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 2, -1], ![1, -1, 0], ![1, 2, -3]]

theorem canonical10117 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw10117 = injectiveMoment H node245 := by
  calc
    injectiveMoment H raw10117 = injectiveMoment H raw10117step0 := by
      have heq : raw10117step0 = raw10117.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw10117).symm
    injectiveMoment H raw10117step0 = injectiveMoment H raw10117step1 := by
      have heq : raw10117step1 = -raw10117step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw10117step0).symm
    injectiveMoment H raw10117step1 = injectiveMoment H raw10117step2 := by
      have heq : raw10117step2 = (fun i j => raw10117step1 (permutation12 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw10117step1 permutation12 permutation4
    _ = injectiveMoment H node245 := by rfl

def raw10118 : Matrix (Fin 3) (Fin 4) ℤ := ![![1, -1, 1, -1], ![-3, -1, 1, 3], ![2, 2, -2, -2]]

def raw10118step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![-1, -1, 2], ![1, 1, -2], ![-1, 3, -2]]

def raw10118step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 2, -3]]

theorem canonical10118 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw10118 = injectiveMoment H node260 := by
  calc
    injectiveMoment H raw10118 = injectiveMoment H raw10118step0 := by
      have heq : raw10118step0 = raw10118.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw10118).symm
    injectiveMoment H raw10118step0 = injectiveMoment H raw10118step1 := by
      have heq : raw10118step1 = (fun i j => raw10118step0 (permutation30 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw10118step0 permutation30 permutation4
    _ = injectiveMoment H node260 := by rfl

def raw10119 : Matrix (Fin 3) (Fin 4) ℤ := ![![1, -1, 1, -1], ![-3, -1, 2, 2], ![2, 2, -3, -1]]

def raw10119step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![-1, -1, 2], ![1, 2, -3], ![-1, 2, -1]]

def raw10119step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 3, -2], ![1, 1, -2], ![-1, -2, 3], ![1, -2, 1]]

def raw10119step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 3, -2], ![1, -2, 1], ![1, 1, -2]]

theorem canonical10119 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw10119 = injectiveMoment H node262 := by
  calc
    injectiveMoment H raw10119 = injectiveMoment H raw10119step0 := by
      have heq : raw10119step0 = raw10119.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw10119).symm
    injectiveMoment H raw10119step0 = injectiveMoment H raw10119step1 := by
      have heq : raw10119step1 = -raw10119step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw10119step0).symm
    injectiveMoment H raw10119step1 = injectiveMoment H raw10119step2 := by
      have heq : raw10119step2 = (fun i j => raw10119step1 (permutation22 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw10119step1 permutation22 permutation3
    _ = injectiveMoment H node262 := by rfl

def raw10120 : Matrix (Fin 3) (Fin 4) ℤ := ![![1, -1, 1, -1], ![-3, 2, 1, 0], ![2, -1, -2, 1]]

def raw10120step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![-1, 2, -1], ![1, 1, -2], ![-1, 0, 1]]

def raw10120step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 3, -2], ![1, -2, 1], ![-1, -1, 2], ![1, 0, -1]]

def raw10120step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2]]

theorem canonical10120 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw10120 = injectiveMoment H node261 := by
  calc
    injectiveMoment H raw10120 = injectiveMoment H raw10120step0 := by
      have heq : raw10120step0 = raw10120.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw10120).symm
    injectiveMoment H raw10120step0 = injectiveMoment H raw10120step1 := by
      have heq : raw10120step1 = -raw10120step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw10120step0).symm
    injectiveMoment H raw10120step1 = injectiveMoment H raw10120step2 := by
      have heq : raw10120step2 = (fun i j => raw10120step1 (permutation12 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw10120step1 permutation12 permutation4
    _ = injectiveMoment H node261 := by rfl

def raw10121 : Matrix (Fin 3) (Fin 4) ℤ := ![![1, -1, 1, -1], ![-3, 3, 1, -1], ![2, -2, -2, 2]]

def raw10121step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![-1, 3, -2], ![1, 1, -2], ![-1, -1, 2]]

def raw10121step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 2, -3]]

theorem canonical10121 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw10121 = injectiveMoment H node260 := by
  calc
    injectiveMoment H raw10121 = injectiveMoment H raw10121step0 := by
      have heq : raw10121step0 = raw10121.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw10121).symm
    injectiveMoment H raw10121step0 = injectiveMoment H raw10121step1 := by
      have heq : raw10121step1 = (fun i j => raw10121step0 (permutation20 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw10121step0 permutation20 permutation4
    _ = injectiveMoment H node260 := by rfl

def raw10122 : Matrix (Fin 3) (Fin 4) ℤ := ![![1, -1, 1, -1], ![-2, -2, 2, 2], ![1, 3, -3, -1]]

def raw10122step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -2, 1], ![-1, -2, 3], ![1, 2, -3], ![-1, 2, -1]]

def raw10122step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 2, -3]]

theorem canonical10122 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw10122 = injectiveMoment H node260 := by
  calc
    injectiveMoment H raw10122 = injectiveMoment H raw10122step0 := by
      have heq : raw10122step0 = raw10122.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw10122).symm
    injectiveMoment H raw10122step0 = injectiveMoment H raw10122step1 := by
      have heq : raw10122step1 = (fun i j => raw10122step0 (permutation19 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw10122step0 permutation19 permutation3
    _ = injectiveMoment H node260 := by rfl

def raw10123 : Matrix (Fin 3) (Fin 4) ℤ := ![![1, -1, 1, -1], ![-2, -1, 1, 2], ![1, 2, -2, -1]]

def raw10123step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -2, 1], ![-1, -1, 2], ![1, 1, -2], ![-1, 2, -1]]

def raw10123step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 1, -2]]

theorem canonical10123 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw10123 = injectiveMoment H node276 := by
  calc
    injectiveMoment H raw10123 = injectiveMoment H raw10123step0 := by
      have heq : raw10123step0 = raw10123.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw10123).symm
    injectiveMoment H raw10123step0 = injectiveMoment H raw10123step1 := by
      have heq : raw10123step1 = (fun i j => raw10123step0 (permutation19 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw10123step0 permutation19 permutation3
    _ = injectiveMoment H node276 := by rfl

def raw10124 : Matrix (Fin 3) (Fin 4) ℤ := ![![1, -1, 1, -1], ![-2, -1, 2, 1], ![1, 2, -3, 0]]

def raw10124step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -2, 1], ![-1, -1, 2], ![1, 2, -3], ![-1, 1, 0]]

def raw10124step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 2, -1], ![1, 1, -2], ![-1, -2, 3], ![1, -1, 0]]

def raw10124step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2]]

theorem canonical10124 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw10124 = injectiveMoment H node261 := by
  calc
    injectiveMoment H raw10124 = injectiveMoment H raw10124step0 := by
      have heq : raw10124step0 = raw10124.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw10124).symm
    injectiveMoment H raw10124step0 = injectiveMoment H raw10124step1 := by
      have heq : raw10124step1 = -raw10124step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw10124step0).symm
    injectiveMoment H raw10124step1 = injectiveMoment H raw10124step2 := by
      have heq : raw10124step2 = (fun i j => raw10124step1 (permutation22 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw10124step1 permutation22 permutation3
    _ = injectiveMoment H node261 := by rfl

def raw10125 : Matrix (Fin 3) (Fin 4) ℤ := ![![1, -1, 1, -1], ![-2, -1, 3, 0], ![1, 2, -4, 1]]

def raw10125step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -2, 1], ![-1, -1, 2], ![1, 3, -4], ![-1, 0, 1]]

def raw10125step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 2, -1], ![1, 1, -2], ![-1, -3, 4], ![1, 0, -1]]

def raw10125step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 2, -1], ![1, 0, -1], ![1, 1, -2]]

theorem canonical10125 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw10125 = injectiveMoment H node246 := by
  calc
    injectiveMoment H raw10125 = injectiveMoment H raw10125step0 := by
      have heq : raw10125step0 = raw10125.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw10125).symm
    injectiveMoment H raw10125step0 = injectiveMoment H raw10125step1 := by
      have heq : raw10125step1 = -raw10125step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw10125step0).symm
    injectiveMoment H raw10125step1 = injectiveMoment H raw10125step2 := by
      have heq : raw10125step2 = (fun i j => raw10125step1 (permutation22 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw10125step1 permutation22 permutation3
    _ = injectiveMoment H node246 := by rfl

def raw10126 : Matrix (Fin 3) (Fin 4) ℤ := ![![1, -1, 1, -1], ![-2, 2, 1, -1], ![1, -1, -2, 2]]

def raw10126step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -2, 1], ![-1, 2, -1], ![1, 1, -2], ![-1, -1, 2]]

def raw10126step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 1, -2]]

theorem canonical10126 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw10126 = injectiveMoment H node276 := by
  calc
    injectiveMoment H raw10126 = injectiveMoment H raw10126step0 := by
      have heq : raw10126step0 = raw10126.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw10126).symm
    injectiveMoment H raw10126step0 = injectiveMoment H raw10126step1 := by
      have heq : raw10126step1 = (fun i j => raw10126step0 (permutation29 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw10126step0 permutation29 permutation3
    _ = injectiveMoment H node276 := by rfl

def raw10127 : Matrix (Fin 3) (Fin 4) ℤ := ![![1, -1, 1, -1], ![-1, -2, 2, 1], ![0, 3, -3, 0]]

def raw10127step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -1, 0], ![-1, -2, 3], ![1, 2, -3], ![-1, 1, 0]]

def raw10127step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 2, -3]]

theorem canonical10127 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw10127 = injectiveMoment H node259 := by
  calc
    injectiveMoment H raw10127 = injectiveMoment H raw10127step0 := by
      have heq : raw10127step0 = raw10127.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw10127).symm
    injectiveMoment H raw10127step0 = injectiveMoment H raw10127step1 := by
      have heq : raw10127step1 = (fun i j => raw10127step0 (permutation19 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw10127step0 permutation19 permutation3
    _ = injectiveMoment H node259 := by rfl

def raw10128 : Matrix (Fin 3) (Fin 4) ℤ := ![![1, -1, 1, -1], ![-1, -1, 3, -1], ![0, 2, -4, 2]]

def raw10128step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -1, 0], ![-1, -1, 2], ![1, 3, -4], ![-1, -1, 2]]

def raw10128step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![1, 1, -2], ![-1, -3, 4], ![1, 1, -2]]

def raw10128step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 1, 0], ![1, 1, -2], ![1, 1, -2]]

theorem canonical10128 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw10128 = injectiveMoment H node244 := by
  calc
    injectiveMoment H raw10128 = injectiveMoment H raw10128step0 := by
      have heq : raw10128step0 = raw10128.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw10128).symm
    injectiveMoment H raw10128step0 = injectiveMoment H raw10128step1 := by
      have heq : raw10128step1 = -raw10128step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw10128step0).symm
    injectiveMoment H raw10128step1 = injectiveMoment H raw10128step2 := by
      have heq : raw10128step2 = (fun i j => raw10128step1 (permutation21 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw10128step1 permutation21 permutation3
    _ = injectiveMoment H node244 := by rfl

def raw10129 : Matrix (Fin 3) (Fin 4) ℤ := ![![1, -1, 1, -1], ![0, -2, 2, 0], ![-1, 3, -3, 1]]

def raw10129step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![-1, -2, 3], ![1, 2, -3], ![-1, 0, 1]]

def raw10129step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![2, 1, -3]]

theorem canonical10129 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw10129 = injectiveMoment H node168 := by
  calc
    injectiveMoment H raw10129 = injectiveMoment H raw10129step0 := by
      have heq : raw10129step0 = raw10129.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw10129).symm
    injectiveMoment H raw10129step0 = injectiveMoment H raw10129step1 := by
      have heq : raw10129step1 = (fun i j => raw10129step0 (permutation19 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw10129step0 permutation19 permutation5
    _ = injectiveMoment H node168 := by rfl

def raw10130 : Matrix (Fin 3) (Fin 4) ℤ := ![![1, -1, 1, -1], ![0, -1, 1, 0], ![-1, 2, -2, 1]]

def raw10130step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![-1, -1, 2], ![1, 1, -2], ![-1, 0, 1]]

def raw10130step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2]]

theorem canonical10130 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw10130 = injectiveMoment H node283 := by
  calc
    injectiveMoment H raw10130 = injectiveMoment H raw10130step0 := by
      have heq : raw10130step0 = raw10130.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw10130).symm
    injectiveMoment H raw10130step0 = injectiveMoment H raw10130step1 := by
      have heq : raw10130step1 = (fun i j => raw10130step0 (permutation19 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw10130step0 permutation19 permutation5
    _ = injectiveMoment H node283 := by rfl

def raw10131 : Matrix (Fin 3) (Fin 4) ℤ := ![![1, -1, 1, -1], ![0, -1, 2, -1], ![-1, 2, -3, 2]]

def raw10131step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![-1, -1, 2], ![1, 2, -3], ![-1, -1, 2]]

def raw10131step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![1, 1, -2], ![-1, -2, 3], ![1, 1, -2]]

def raw10131step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![1, 1, -2], ![1, 1, -2]]

theorem canonical10131 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw10131 = injectiveMoment H node175 := by
  calc
    injectiveMoment H raw10131 = injectiveMoment H raw10131step0 := by
      have heq : raw10131step0 = raw10131.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw10131).symm
    injectiveMoment H raw10131step0 = injectiveMoment H raw10131step1 := by
      have heq : raw10131step1 = -raw10131step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw10131step0).symm
    injectiveMoment H raw10131step1 = injectiveMoment H raw10131step2 := by
      have heq : raw10131step2 = (fun i j => raw10131step1 (permutation21 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw10131step1 permutation21 permutation5
    _ = injectiveMoment H node175 := by rfl

def raw10132 : Matrix (Fin 3) (Fin 4) ℤ := ![![1, -1, 1, -1], ![1, -2, 2, -1], ![-2, 3, -3, 2]]

def raw10132step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![-1, -2, 3], ![1, 2, -3], ![-1, -1, 2]]

def raw10132step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, -1, 2], ![1, 1, -2], ![1, 2, -3]]

theorem canonical10132 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw10132 = injectiveMoment H node258 := by
  calc
    injectiveMoment H raw10132 = injectiveMoment H raw10132step0 := by
      have heq : raw10132step0 = raw10132.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw10132).symm
    injectiveMoment H raw10132step0 = injectiveMoment H raw10132step1 := by
      have heq : raw10132step1 = (fun i j => raw10132step0 (permutation19 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw10132step0 permutation19 permutation3
    _ = injectiveMoment H node258 := by rfl

def raw10133 : Matrix (Fin 3) (Fin 4) ℤ := ![![1, -1, 1, -1], ![1, -1, 1, -1], ![-2, 2, -2, 2]]

def raw10133step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![-1, -1, 2], ![1, 1, -2], ![-1, -1, 2]]

def raw10133step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![1, 1, -2], ![1, 1, -2]]

theorem canonical10133 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw10133 = injectiveMoment H node275 := by
  calc
    injectiveMoment H raw10133 = injectiveMoment H raw10133step0 := by
      have heq : raw10133step0 = raw10133.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw10133).symm
    injectiveMoment H raw10133step0 = injectiveMoment H raw10133step1 := by
      have heq : raw10133step1 = (fun i j => raw10133step0 (permutation19 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw10133step0 permutation19 permutation3
    _ = injectiveMoment H node275 := by rfl

def raw10134 : Matrix (Fin 3) (Fin 4) ℤ := ![![1, -1, 1, -1], ![1, -1, 2, -2], ![-2, 2, -3, 3]]

def raw10134step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![-1, -1, 2], ![1, 2, -3], ![-1, -2, 3]]

def raw10134step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, -1, 2], ![1, 1, -2], ![1, 2, -3]]

theorem canonical10134 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw10134 = injectiveMoment H node258 := by
  calc
    injectiveMoment H raw10134 = injectiveMoment H raw10134step0 := by
      have heq : raw10134step0 = raw10134.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw10134).symm
    injectiveMoment H raw10134step0 = injectiveMoment H raw10134step1 := by
      have heq : raw10134step1 = (fun i j => raw10134step0 (permutation29 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw10134step0 permutation29 permutation3
    _ = injectiveMoment H node258 := by rfl

def raw10135 : Matrix (Fin 3) (Fin 4) ℤ := ![![1, -1, 1, -1], ![2, -1, 1, -2], ![-3, 2, -2, 3]]

def raw10135step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![-1, -1, 2], ![1, 1, -2], ![-1, -2, 3]]

def raw10135step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, -1, 2], ![1, 1, -2], ![1, 2, -3]]

theorem canonical10135 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw10135 = injectiveMoment H node258 := by
  calc
    injectiveMoment H raw10135 = injectiveMoment H raw10135step0 := by
      have heq : raw10135step0 = raw10135.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw10135).symm
    injectiveMoment H raw10135step0 = injectiveMoment H raw10135step1 := by
      have heq : raw10135step1 = (fun i j => raw10135step0 (permutation30 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw10135step0 permutation30 permutation3
    _ = injectiveMoment H node258 := by rfl

def raw10136 : Matrix (Fin 3) (Fin 4) ℤ := ![![1, -1, 2, -2], ![0, 2, 0, -2], ![-1, -1, -2, 4]]

def raw10136step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![-1, 2, -1], ![2, 0, -2], ![-2, -2, 4]]

def raw10136step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 2, -2], ![2, -1, -1]]

theorem canonical10136 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw10136 = injectiveMoment H node146 := by
  calc
    injectiveMoment H raw10136 = injectiveMoment H raw10136step0 := by
      have heq : raw10136step0 = raw10136.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw10136).symm
    injectiveMoment H raw10136step0 = injectiveMoment H raw10136step1 := by
      have heq : raw10136step1 = (fun i j => raw10136step0 (permutation28 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw10136step0 permutation28 permutation5
    _ = injectiveMoment H node146 := by rfl

def raw10137 : Matrix (Fin 3) (Fin 4) ℤ := ![![1, -1, 2, -2], ![1, 2, 0, -3], ![-2, -1, -2, 5]]

def raw10137step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![2, 0, -2], ![-2, -3, 5]]

def raw10137step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]

theorem canonical10137 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw10137 = injectiveMoment H node74 := by
  calc
    injectiveMoment H raw10137 = injectiveMoment H raw10137step0 := by
      have heq : raw10137step0 = raw10137.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw10137).symm
    injectiveMoment H raw10137step0 = injectiveMoment H raw10137step1 := by
      have heq : raw10137step1 = (fun i j => raw10137step0 (permutation31 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw10137step0 permutation31 permutation5
    _ = injectiveMoment H node74 := by rfl

def raw10138 : Matrix (Fin 3) (Fin 4) ℤ := ![![1, 0, 0, -1], ![-2, -2, 2, 2], ![1, 2, -2, -1]]

def raw10138step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -2, 1], ![0, -2, 2], ![0, 2, -2], ![-1, 2, -1]]

def raw10138step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 1, -2]]

theorem canonical10138 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw10138 = injectiveMoment H node279 := by
  calc
    injectiveMoment H raw10138 = injectiveMoment H raw10138step0 := by
      have heq : raw10138step0 = raw10138.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw10138).symm
    injectiveMoment H raw10138step0 = injectiveMoment H raw10138step1 := by
      have heq : raw10138step1 = (fun i j => raw10138step0 (permutation32 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw10138step0 permutation32 permutation4
    _ = injectiveMoment H node279 := by rfl

def raw10139 : Matrix (Fin 3) (Fin 4) ℤ := ![![1, 0, 0, -1], ![-1, -3, 4, 0], ![0, 3, -4, 1]]

def raw10139step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -1, 0], ![0, -3, 3], ![0, 4, -4], ![-1, 0, 1]]

def raw10139step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -3, 3], ![0, 4, -4], ![1, -1, 0]]

theorem canonical10139 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw10139 = injectiveMoment H node290 := by
  calc
    injectiveMoment H raw10139 = injectiveMoment H raw10139step0 := by
      have heq : raw10139step0 = raw10139.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw10139).symm
    injectiveMoment H raw10139step0 = injectiveMoment H raw10139step1 := by
      have heq : raw10139step1 = (fun i j => raw10139step0 (permutation30 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw10139step0 permutation30 permutation3
    _ = injectiveMoment H node290 := by rfl

def raw10140 : Matrix (Fin 3) (Fin 4) ℤ := ![![1, 0, 0, -1], ![-1, -2, 2, 1], ![0, 2, -2, 0]]

def raw10140step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -1, 0], ![0, -2, 2], ![0, 2, -2], ![-1, 1, 0]]

def raw10140step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1]]

theorem canonical10140 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw10140 = injectiveMoment H node291 := by
  calc
    injectiveMoment H raw10140 = injectiveMoment H raw10140step0 := by
      have heq : raw10140step0 = raw10140.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw10140).symm
    injectiveMoment H raw10140step0 = injectiveMoment H raw10140step1 := by
      have heq : raw10140step1 = (fun i j => raw10140step0 (permutation32 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw10140step0 permutation32 permutation4
    _ = injectiveMoment H node291 := by rfl

def raw10141 : Matrix (Fin 3) (Fin 4) ℤ := ![![1, 0, 0, -1], ![-1, -2, 3, 0], ![0, 2, -3, 1]]

def raw10141step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -1, 0], ![0, -2, 2], ![0, 3, -3], ![-1, 0, 1]]

def raw10141step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -2, 2], ![0, 3, -3], ![1, -1, 0]]

theorem canonical10141 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw10141 = injectiveMoment H node292 := by
  calc
    injectiveMoment H raw10141 = injectiveMoment H raw10141step0 := by
      have heq : raw10141step0 = raw10141.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw10141).symm
    injectiveMoment H raw10141step0 = injectiveMoment H raw10141step1 := by
      have heq : raw10141step1 = (fun i j => raw10141step0 (permutation30 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw10141step0 permutation30 permutation3
    _ = injectiveMoment H node292 := by rfl

def raw10142 : Matrix (Fin 3) (Fin 4) ℤ := ![![1, 0, 0, -1], ![0, -3, 3, 0], ![-1, 3, -3, 1]]

def raw10142step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![0, -3, 3], ![0, 3, -3], ![-1, 0, 1]]

def raw10142step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -3, 3], ![0, 3, -3], ![1, 0, -1]]

theorem canonical10142 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw10142 = injectiveMoment H node289 := by
  calc
    injectiveMoment H raw10142 = injectiveMoment H raw10142step0 := by
      have heq : raw10142step0 = raw10142.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw10142).symm
    injectiveMoment H raw10142step0 = injectiveMoment H raw10142step1 := by
      have heq : raw10142step1 = (fun i j => raw10142step0 (permutation30 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw10142step0 permutation30 permutation3
    _ = injectiveMoment H node289 := by rfl

def raw10143 : Matrix (Fin 3) (Fin 4) ℤ := ![![1, 0, 0, -1], ![0, -2, 3, -1], ![-1, 2, -3, 2]]

def raw10143step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![0, -2, 2], ![0, 3, -3], ![-1, -1, 2]]

def raw10143step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -2, 2], ![0, 3, -3], ![1, 0, -1]]

theorem canonical10143 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw10143 = injectiveMoment H node280 := by
  calc
    injectiveMoment H raw10143 = injectiveMoment H raw10143step0 := by
      have heq : raw10143step0 = raw10143.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw10143).symm
    injectiveMoment H raw10143step0 = injectiveMoment H raw10143step1 := by
      have heq : raw10143step1 = (fun i j => raw10143step0 (permutation30 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw10143step0 permutation30 permutation3
    _ = injectiveMoment H node280 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
