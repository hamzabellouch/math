import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes0
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes1
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes2
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes3
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes4
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes10
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes11
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes29
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes36

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw6880 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -1, 2], ![1, -2, 1], ![0, 3, -3]]

def raw6880step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 3, -3], ![1, -2, 1]]

theorem canonical6880 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6880 = injectiveMoment H node63 := by
  calc
    injectiveMoment H raw6880 = injectiveMoment H raw6880step0 := by
      have heq : raw6880step0 = (fun i j => raw6880 (permutation4 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6880 permutation4 permutation3
    _ = injectiveMoment H node63 := by rfl

def raw6881 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0], ![3, -1, -2]]

def raw6881step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]

theorem canonical6881 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6881 = injectiveMoment H node1880 := by
  calc
    injectiveMoment H raw6881 = injectiveMoment H raw6881step0 := by
      have heq : raw6881step0 = (fun i j => raw6881 (permutation340 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6881 permutation340 permutation8
    _ = injectiveMoment H node1880 := by rfl

def raw6882 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![1, -1, 0], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1]]

def raw6882step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1]]

def raw6882step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

theorem canonical6882 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6882 = injectiveMoment H node711 := by
  calc
    injectiveMoment H raw6882 = injectiveMoment H raw6882step0 := by
      have heq : raw6882step0 = -raw6882 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6882).symm
    injectiveMoment H raw6882step0 = injectiveMoment H raw6882step1 := by
      have heq : raw6882step1 = (fun i j => raw6882step0 (permutation34 i) (permutation7 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6882step0 permutation34 permutation7
    _ = injectiveMoment H node711 := by rfl

def raw6883 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1]]

def raw6883step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1]]

def raw6883step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0]]

theorem canonical6883 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6883 = injectiveMoment H node287 := by
  calc
    injectiveMoment H raw6883 = injectiveMoment H raw6883step0 := by
      have hz : ∀ j, raw6883 (permutation80 0) j = 0 := by decide +kernel
      have heq : raw6883step0 = (fun i j => raw6883 (permutation80 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw6883 permutation80 hz
    injectiveMoment H raw6883step0 = injectiveMoment H raw6883step1 := by
      have heq : raw6883step1 = (fun i j => raw6883step0 (permutation12 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6883step0 permutation12 permutation3
    _ = injectiveMoment H node287 := by rfl

def raw6884 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![1, 1, -2]]

def raw6884step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]

theorem canonical6884 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6884 = injectiveMoment H node2304 := by
  calc
    injectiveMoment H raw6884 = injectiveMoment H raw6884step0 := by
      have heq : raw6884step0 = (fun i j => raw6884 (permutation392 i) (permutation7 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6884 permutation392 permutation7
    _ = injectiveMoment H node2304 := by rfl

def raw6885 : Matrix (Fin 2) (Fin 3) ℤ := ![![-1, -1, 2], ![1, 1, -2]]

def raw6885step0 : Matrix (Fin 3) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![2, -2]]

def raw6885step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]

theorem canonical6885 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6885 = injectiveMoment H node11 := by
  calc
    injectiveMoment H raw6885 = injectiveMoment H raw6885step0 := by
      have heq : raw6885step0 = raw6885.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6885).symm
    injectiveMoment H raw6885step0 = injectiveMoment H raw6885step1 := by
      have heq : raw6885step1 = (fun i j => raw6885step0 (permutation7 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6885step0 permutation7 permutation2
    _ = injectiveMoment H node11 := by rfl

def raw6886 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![2, -2, 0], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1]]

def raw6886step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![-2, 2, 0], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1]]

def raw6886step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]

theorem canonical6886 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6886 = injectiveMoment H node667 := by
  calc
    injectiveMoment H raw6886 = injectiveMoment H raw6886step0 := by
      have heq : raw6886step0 = -raw6886 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6886).symm
    injectiveMoment H raw6886step0 = injectiveMoment H raw6886step1 := by
      have heq : raw6886step1 = (fun i j => raw6886step0 (permutation72 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6886step0 permutation72 permutation4
    _ = injectiveMoment H node667 := by rfl

def raw6887 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![-4, 2, 0, 2], ![5, -1, -2, -2]]

def raw6887step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -4, 5], ![-1, 2, -1], ![2, 0, -2], ![0, 2, -2]]

def raw6887step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 4, -5], ![1, -2, 1], ![-2, 0, 2], ![0, -2, 2]]

def raw6887step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![1, -2, 1], ![1, 4, -5]]

theorem canonical6887 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6887 = injectiveMoment H node200 := by
  calc
    injectiveMoment H raw6887 = injectiveMoment H raw6887step0 := by
      have heq : raw6887step0 = raw6887.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6887).symm
    injectiveMoment H raw6887step0 = injectiveMoment H raw6887step1 := by
      have heq : raw6887step1 = -raw6887step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6887step0).symm
    injectiveMoment H raw6887step1 = injectiveMoment H raw6887step2 := by
      have heq : raw6887step2 = (fun i j => raw6887step1 (permutation26 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6887step1 permutation26 permutation3
    _ = injectiveMoment H node200 := by rfl

def raw6888 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![-3, 2, -2, 3], ![4, -1, 0, -3]]

def raw6888step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 2, -1], ![2, -2, 0], ![0, 3, -3]]

def raw6888step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -2, 1], ![-2, 2, 0], ![0, -3, 3]]

def raw6888step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![1, -4, 3], ![1, 1, -2]]

theorem canonical6888 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6888 = injectiveMoment H node213 := by
  calc
    injectiveMoment H raw6888 = injectiveMoment H raw6888step0 := by
      have heq : raw6888step0 = raw6888.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6888).symm
    injectiveMoment H raw6888step0 = injectiveMoment H raw6888step1 := by
      have heq : raw6888step1 = -raw6888step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6888step0).symm
    injectiveMoment H raw6888step1 = injectiveMoment H raw6888step2 := by
      have heq : raw6888step2 = (fun i j => raw6888step1 (permutation25 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6888step1 permutation25 permutation4
    _ = injectiveMoment H node213 := by rfl

def raw6889 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![-3, 2, -1, 2], ![4, -1, -1, -2]]

def raw6889step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 2, -1], ![2, -1, -1], ![0, 2, -2]]

def raw6889step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -2, 1], ![-2, 1, 1], ![0, -2, 2]]

def raw6889step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![1, -2, 1], ![1, 3, -4]]

theorem canonical6889 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6889 = injectiveMoment H node225 := by
  calc
    injectiveMoment H raw6889 = injectiveMoment H raw6889step0 := by
      have heq : raw6889step0 = raw6889.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6889).symm
    injectiveMoment H raw6889step0 = injectiveMoment H raw6889step1 := by
      have heq : raw6889step1 = -raw6889step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6889step0).symm
    injectiveMoment H raw6889step1 = injectiveMoment H raw6889step2 := by
      have heq : raw6889step2 = (fun i j => raw6889step1 (permutation26 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6889step1 permutation26 permutation3
    _ = injectiveMoment H node225 := by rfl

def raw6890 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![-3, 2, 0, 1], ![4, -1, -2, -1]]

def raw6890step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 2, -1], ![2, 0, -2], ![0, 1, -1]]

def raw6890step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -2, 1], ![-2, 0, 2], ![0, -1, 1]]

def raw6890step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![1, -2, 1], ![1, 3, -4]]

theorem canonical6890 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6890 = injectiveMoment H node206 := by
  calc
    injectiveMoment H raw6890 = injectiveMoment H raw6890step0 := by
      have heq : raw6890step0 = raw6890.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6890).symm
    injectiveMoment H raw6890step0 = injectiveMoment H raw6890step1 := by
      have heq : raw6890step1 = -raw6890step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6890step0).symm
    injectiveMoment H raw6890step1 = injectiveMoment H raw6890step2 := by
      have heq : raw6890step2 = (fun i j => raw6890step1 (permutation26 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6890step1 permutation26 permutation3
    _ = injectiveMoment H node206 := by rfl

def raw6891 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![-3, 3, -2, 2], ![4, -2, 0, -2]]

def raw6891step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 3, -2], ![2, -2, 0], ![0, 2, -2]]

def raw6891step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -3, 2], ![-2, 2, 0], ![0, -2, 2]]

def raw6891step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![1, -4, 3], ![1, 2, -3]]

theorem canonical6891 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6891 = injectiveMoment H node211 := by
  calc
    injectiveMoment H raw6891 = injectiveMoment H raw6891step0 := by
      have heq : raw6891step0 = raw6891.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6891).symm
    injectiveMoment H raw6891step0 = injectiveMoment H raw6891step1 := by
      have heq : raw6891step1 = -raw6891step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6891step0).symm
    injectiveMoment H raw6891step1 = injectiveMoment H raw6891step2 := by
      have heq : raw6891step2 = (fun i j => raw6891step1 (permutation25 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6891step1 permutation25 permutation4
    _ = injectiveMoment H node211 := by rfl

def raw6892 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![-2, -1, -1, 4], ![3, 2, -1, -4]]

def raw6892step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, -1, 2], ![2, -1, -1], ![0, 4, -4]]

def raw6892step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, 1, -2], ![-2, 1, 1], ![0, -4, 4]]

def raw6892step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -4, 4], ![1, 1, -2], ![1, 2, -3]]

theorem canonical6892 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6892 = injectiveMoment H node219 := by
  calc
    injectiveMoment H raw6892 = injectiveMoment H raw6892step0 := by
      have heq : raw6892step0 = raw6892.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6892).symm
    injectiveMoment H raw6892step0 = injectiveMoment H raw6892step1 := by
      have heq : raw6892step1 = -raw6892step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6892step0).symm
    injectiveMoment H raw6892step1 = injectiveMoment H raw6892step2 := by
      have heq : raw6892step2 = (fun i j => raw6892step1 (permutation26 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6892step1 permutation26 permutation3
    _ = injectiveMoment H node219 := by rfl

def raw6893 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![-2, -1, 0, 3], ![3, 2, -2, -3]]

def raw6893step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, -1, 2], ![2, 0, -2], ![0, 3, -3]]

def raw6893step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, 1, -2], ![-2, 0, 2], ![0, -3, 3]]

def raw6893step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![1, 1, -2], ![1, 2, -3]]

theorem canonical6893 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6893 = injectiveMoment H node196 := by
  calc
    injectiveMoment H raw6893 = injectiveMoment H raw6893step0 := by
      have heq : raw6893step0 = raw6893.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6893).symm
    injectiveMoment H raw6893step0 = injectiveMoment H raw6893step1 := by
      have heq : raw6893step1 = -raw6893step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6893step0).symm
    injectiveMoment H raw6893step1 = injectiveMoment H raw6893step2 := by
      have heq : raw6893step2 = (fun i j => raw6893step1 (permutation26 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6893step1 permutation26 permutation3
    _ = injectiveMoment H node196 := by rfl

def raw6894 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![-2, 2, -2, 2], ![3, -1, 0, -2]]

def raw6894step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 2, -1], ![2, -2, 0], ![0, 2, -2]]

def raw6894step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -2, 1], ![-2, 2, 0], ![0, -2, 2]]

def raw6894step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![1, -3, 2], ![1, 1, -2]]

theorem canonical6894 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6894 = injectiveMoment H node212 := by
  calc
    injectiveMoment H raw6894 = injectiveMoment H raw6894step0 := by
      have heq : raw6894step0 = raw6894.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6894).symm
    injectiveMoment H raw6894step0 = injectiveMoment H raw6894step1 := by
      have heq : raw6894step1 = -raw6894step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6894step0).symm
    injectiveMoment H raw6894step1 = injectiveMoment H raw6894step2 := by
      have heq : raw6894step2 = (fun i j => raw6894step1 (permutation25 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6894step1 permutation25 permutation4
    _ = injectiveMoment H node212 := by rfl

def raw6895 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![-2, 2, -1, 1], ![3, -1, -1, -1]]

def raw6895step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 2, -1], ![2, -1, -1], ![0, 1, -1]]

def raw6895step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -2, 1], ![-2, 1, 1], ![0, -1, 1]]

def raw6895step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -2, 1], ![1, 2, -3]]

theorem canonical6895 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6895 = injectiveMoment H node229 := by
  calc
    injectiveMoment H raw6895 = injectiveMoment H raw6895step0 := by
      have heq : raw6895step0 = raw6895.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6895).symm
    injectiveMoment H raw6895step0 = injectiveMoment H raw6895step1 := by
      have heq : raw6895step1 = -raw6895step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6895step0).symm
    injectiveMoment H raw6895step1 = injectiveMoment H raw6895step2 := by
      have heq : raw6895step2 = (fun i j => raw6895step1 (permutation26 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6895step1 permutation26 permutation3
    _ = injectiveMoment H node229 := by rfl

def raw6896 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![-2, 2, 1, -1], ![3, -1, -3, 1]]

def raw6896step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 2, -1], ![2, 1, -3], ![0, -1, 1]]

def raw6896step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -2, 1], ![-2, -1, 3], ![0, 1, -1]]

def raw6896step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 2, -3]]

theorem canonical6896 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6896 = injectiveMoment H node180 := by
  calc
    injectiveMoment H raw6896 = injectiveMoment H raw6896step0 := by
      have heq : raw6896step0 = raw6896.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6896).symm
    injectiveMoment H raw6896step0 = injectiveMoment H raw6896step1 := by
      have heq : raw6896step1 = -raw6896step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6896step0).symm
    injectiveMoment H raw6896step1 = injectiveMoment H raw6896step2 := by
      have heq : raw6896step2 = (fun i j => raw6896step1 (permutation26 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6896step1 permutation26 permutation3
    _ = injectiveMoment H node180 := by rfl

def raw6897 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![-2, 3, -2, 1], ![3, -2, 0, -1]]

def raw6897step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 3, -2], ![2, -2, 0], ![0, 1, -1]]

def raw6897step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -3, 2], ![-2, 2, 0], ![0, -1, 1]]

def raw6897step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -3, 2], ![1, 2, -3]]

theorem canonical6897 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6897 = injectiveMoment H node209 := by
  calc
    injectiveMoment H raw6897 = injectiveMoment H raw6897step0 := by
      have heq : raw6897step0 = raw6897.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6897).symm
    injectiveMoment H raw6897step0 = injectiveMoment H raw6897step1 := by
      have heq : raw6897step1 = -raw6897step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6897step0).symm
    injectiveMoment H raw6897step1 = injectiveMoment H raw6897step2 := by
      have heq : raw6897step2 = (fun i j => raw6897step1 (permutation25 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6897step1 permutation25 permutation4
    _ = injectiveMoment H node209 := by rfl

def raw6898 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![-2, 3, 0, -1], ![3, -2, -2, 1]]

def raw6898step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 3, -2], ![2, 0, -2], ![0, -1, 1]]

def raw6898step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -3, 2], ![-2, 0, 2], ![0, 1, -1]]

def raw6898step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -3, 2], ![1, 2, -3]]

theorem canonical6898 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6898 = injectiveMoment H node209 := by
  calc
    injectiveMoment H raw6898 = injectiveMoment H raw6898step0 := by
      have heq : raw6898step0 = raw6898.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6898).symm
    injectiveMoment H raw6898step0 = injectiveMoment H raw6898step1 := by
      have heq : raw6898step1 = -raw6898step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6898step0).symm
    injectiveMoment H raw6898step1 = injectiveMoment H raw6898step2 := by
      have heq : raw6898step2 = (fun i j => raw6898step1 (permutation26 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6898step1 permutation26 permutation3
    _ = injectiveMoment H node209 := by rfl

def raw6899 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![-2, 4, -1, -1], ![3, -3, -1, 1]]

def raw6899step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 4, -3], ![2, -1, -1], ![0, -1, 1]]

def raw6899step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -4, 3], ![-2, 1, 1], ![0, 1, -1]]

def raw6899step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -3, 2], ![1, 3, -4]]

theorem canonical6899 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6899 = injectiveMoment H node228 := by
  calc
    injectiveMoment H raw6899 = injectiveMoment H raw6899step0 := by
      have heq : raw6899step0 = raw6899.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6899).symm
    injectiveMoment H raw6899step0 = injectiveMoment H raw6899step1 := by
      have heq : raw6899step1 = -raw6899step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6899step0).symm
    injectiveMoment H raw6899step1 = injectiveMoment H raw6899step2 := by
      have heq : raw6899step2 = (fun i j => raw6899step1 (permutation25 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6899step1 permutation25 permutation4
    _ = injectiveMoment H node228 := by rfl

def raw6900 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![-1, -2, 1, 2], ![2, 3, -3, -2]]

def raw6900step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -2, 3], ![2, 1, -3], ![0, 2, -2]]

def raw6900step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![1, 2, -3], ![-2, -1, 3], ![0, -2, 2]]

def raw6900step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![1, 1, -2], ![1, 2, -3]]

theorem canonical6900 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6900 = injectiveMoment H node167 := by
  calc
    injectiveMoment H raw6900 = injectiveMoment H raw6900step0 := by
      have heq : raw6900step0 = raw6900.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6900).symm
    injectiveMoment H raw6900step0 = injectiveMoment H raw6900step1 := by
      have heq : raw6900step1 = -raw6900step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6900step0).symm
    injectiveMoment H raw6900step1 = injectiveMoment H raw6900step2 := by
      have heq : raw6900step2 = (fun i j => raw6900step1 (permutation25 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6900step1 permutation25 permutation3
    _ = injectiveMoment H node167 := by rfl

def raw6901 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![-1, -2, 2, 1], ![2, 3, -4, -1]]

def raw6901step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -2, 3], ![2, 2, -4], ![0, 1, -1]]

def raw6901step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![1, 2, -3], ![-2, -2, 4], ![0, -1, 1]]

def raw6901step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, -1, 1], ![1, 1, -2], ![1, 2, -3]]

theorem canonical6901 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6901 = injectiveMoment H node144 := by
  calc
    injectiveMoment H raw6901 = injectiveMoment H raw6901step0 := by
      have heq : raw6901step0 = raw6901.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6901).symm
    injectiveMoment H raw6901step0 = injectiveMoment H raw6901step1 := by
      have heq : raw6901step1 = -raw6901step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6901step0).symm
    injectiveMoment H raw6901step1 = injectiveMoment H raw6901step2 := by
      have heq : raw6901step2 = (fun i j => raw6901step1 (permutation25 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6901step1 permutation25 permutation3
    _ = injectiveMoment H node144 := by rfl

def raw6902 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![-1, -1, -2, 4], ![2, 2, 0, -4]]

def raw6902step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![2, -2, 0], ![0, 4, -4]]

def raw6902step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![1, 1, -2], ![-2, 2, 0], ![0, -4, 4]]

def raw6902step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 4, -4], ![1, -2, 1], ![1, -2, 1]]

theorem canonical6902 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6902 = injectiveMoment H node218 := by
  calc
    injectiveMoment H raw6902 = injectiveMoment H raw6902step0 := by
      have heq : raw6902step0 = raw6902.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6902).symm
    injectiveMoment H raw6902step0 = injectiveMoment H raw6902step1 := by
      have heq : raw6902step1 = -raw6902step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6902step0).symm
    injectiveMoment H raw6902step1 = injectiveMoment H raw6902step2 := by
      have heq : raw6902step2 = (fun i j => raw6902step1 (permutation25 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6902step1 permutation25 permutation4
    _ = injectiveMoment H node218 := by rfl

def raw6903 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![-1, -1, -1, 3], ![2, 2, -1, -3]]

def raw6903step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![2, -1, -1], ![0, 3, -3]]

def raw6903step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![1, 1, -2], ![-2, 1, 1], ![0, -3, 3]]

def raw6903step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -3, 3], ![1, 1, -2], ![1, 1, -2]]

theorem canonical6903 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6903 = injectiveMoment H node223 := by
  calc
    injectiveMoment H raw6903 = injectiveMoment H raw6903step0 := by
      have heq : raw6903step0 = raw6903.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6903).symm
    injectiveMoment H raw6903step0 = injectiveMoment H raw6903step1 := by
      have heq : raw6903step1 = -raw6903step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6903step0).symm
    injectiveMoment H raw6903step1 = injectiveMoment H raw6903step2 := by
      have heq : raw6903step2 = (fun i j => raw6903step1 (permutation25 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6903step1 permutation25 permutation3
    _ = injectiveMoment H node223 := by rfl

def raw6904 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![-1, -1, 3, -1], ![2, 2, -5, 1]]

def raw6904step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![2, 3, -5], ![0, -1, 1]]

def raw6904step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![1, 1, -2], ![-2, -3, 5], ![0, 1, -1]]

def raw6904step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 1, -1], ![1, 1, -2], ![1, 1, -2]]

theorem canonical6904 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6904 = injectiveMoment H node124 := by
  calc
    injectiveMoment H raw6904 = injectiveMoment H raw6904step0 := by
      have heq : raw6904step0 = raw6904.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6904).symm
    injectiveMoment H raw6904step0 = injectiveMoment H raw6904step1 := by
      have heq : raw6904step1 = -raw6904step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6904step0).symm
    injectiveMoment H raw6904step1 = injectiveMoment H raw6904step2 := by
      have heq : raw6904step2 = (fun i j => raw6904step1 (permutation25 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6904step1 permutation25 permutation3
    _ = injectiveMoment H node124 := by rfl

def raw6905 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![-1, 2, -3, 2], ![2, -1, 1, -2]]

def raw6905step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![2, -3, 1], ![0, 2, -2]]

def raw6905step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![1, -2, 1], ![-2, 3, -1], ![0, -2, 2]]

def raw6905step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, -2, 1], ![1, 1, -2]]

theorem canonical6905 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6905 = injectiveMoment H node184 := by
  calc
    injectiveMoment H raw6905 = injectiveMoment H raw6905step0 := by
      have heq : raw6905step0 = raw6905.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6905).symm
    injectiveMoment H raw6905step0 = injectiveMoment H raw6905step1 := by
      have heq : raw6905step1 = -raw6905step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6905step0).symm
    injectiveMoment H raw6905step1 = injectiveMoment H raw6905step2 := by
      have heq : raw6905step2 = (fun i j => raw6905step1 (permutation25 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6905step1 permutation25 permutation4
    _ = injectiveMoment H node184 := by rfl

def raw6906 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![-1, 2, -2, 1], ![2, -1, 0, -1]]

def raw6906step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![2, -2, 0], ![0, 1, -1]]

def raw6906step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![1, -2, 1], ![-2, 2, 0], ![0, -1, 1]]

def raw6906step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]

theorem canonical6906 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6906 = injectiveMoment H node210 := by
  calc
    injectiveMoment H raw6906 = injectiveMoment H raw6906step0 := by
      have heq : raw6906step0 = raw6906.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6906).symm
    injectiveMoment H raw6906step0 = injectiveMoment H raw6906step1 := by
      have heq : raw6906step1 = -raw6906step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6906step0).symm
    injectiveMoment H raw6906step1 = injectiveMoment H raw6906step2 := by
      have heq : raw6906step2 = (fun i j => raw6906step1 (permutation25 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6906step1 permutation25 permutation4
    _ = injectiveMoment H node210 := by rfl

def raw6907 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![-1, 2, 0, -1], ![2, -1, -2, 1]]

def raw6907step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![2, 0, -2], ![0, -1, 1]]

def raw6907step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![1, -2, 1], ![-2, 0, 2], ![0, 1, -1]]

def raw6907step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]

theorem canonical6907 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6907 = injectiveMoment H node210 := by
  calc
    injectiveMoment H raw6907 = injectiveMoment H raw6907step0 := by
      have heq : raw6907step0 = raw6907.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6907).symm
    injectiveMoment H raw6907step0 = injectiveMoment H raw6907step1 := by
      have heq : raw6907step1 = -raw6907step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6907step0).symm
    injectiveMoment H raw6907step1 = injectiveMoment H raw6907step2 := by
      have heq : raw6907step2 = (fun i j => raw6907step1 (permutation26 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6907step1 permutation26 permutation3
    _ = injectiveMoment H node210 := by rfl

def raw6908 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![-1, 2, 1, -2], ![2, -1, -3, 2]]

def raw6908step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![2, 1, -3], ![0, -2, 2]]

def raw6908step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![1, -2, 1], ![-2, -1, 3], ![0, 2, -2]]

def raw6908step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, -2, 1], ![1, 1, -2]]

theorem canonical6908 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6908 = injectiveMoment H node184 := by
  calc
    injectiveMoment H raw6908 = injectiveMoment H raw6908step0 := by
      have heq : raw6908step0 = raw6908.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6908).symm
    injectiveMoment H raw6908step0 = injectiveMoment H raw6908step1 := by
      have heq : raw6908step1 = -raw6908step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6908step0).symm
    injectiveMoment H raw6908step1 = injectiveMoment H raw6908step2 := by
      have heq : raw6908step2 = (fun i j => raw6908step1 (permutation26 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6908step1 permutation26 permutation3
    _ = injectiveMoment H node184 := by rfl

def raw6909 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![-1, 3, -4, 2], ![2, -2, 2, -2]]

def raw6909step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 3, -2], ![2, -4, 2], ![0, 2, -2]]

def raw6909step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![1, -3, 2], ![-2, 4, -2], ![0, -2, 2]]

def raw6909step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![1, -2, 1], ![1, 2, -3]]

theorem canonical6909 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6909 = injectiveMoment H node152 := by
  calc
    injectiveMoment H raw6909 = injectiveMoment H raw6909step0 := by
      have heq : raw6909step0 = raw6909.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6909).symm
    injectiveMoment H raw6909step0 = injectiveMoment H raw6909step1 := by
      have heq : raw6909step1 = -raw6909step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6909step0).symm
    injectiveMoment H raw6909step1 = injectiveMoment H raw6909step2 := by
      have heq : raw6909step2 = (fun i j => raw6909step1 (permutation25 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6909step1 permutation25 permutation4
    _ = injectiveMoment H node152 := by rfl

def raw6910 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![-1, 3, -1, -1], ![2, -2, -1, 1]]

def raw6910step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 3, -2], ![2, -1, -1], ![0, -1, 1]]

def raw6910step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![1, -3, 2], ![-2, 1, 1], ![0, 1, -1]]

def raw6910step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -2, 1], ![1, 2, -3]]

theorem canonical6910 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6910 = injectiveMoment H node229 := by
  calc
    injectiveMoment H raw6910 = injectiveMoment H raw6910step0 := by
      have heq : raw6910step0 = raw6910.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6910).symm
    injectiveMoment H raw6910step0 = injectiveMoment H raw6910step1 := by
      have heq : raw6910step1 = -raw6910step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6910step0).symm
    injectiveMoment H raw6910step1 = injectiveMoment H raw6910step2 := by
      have heq : raw6910step2 = (fun i j => raw6910step1 (permutation25 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6910step1 permutation25 permutation4
    _ = injectiveMoment H node229 := by rfl

def raw6911 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![-1, 3, 0, -2], ![2, -2, -2, 2]]

def raw6911step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 3, -2], ![2, 0, -2], ![0, -2, 2]]

def raw6911step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![1, -3, 2], ![-2, 0, 2], ![0, 2, -2]]

def raw6911step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![1, -3, 2], ![1, 1, -2]]

theorem canonical6911 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6911 = injectiveMoment H node212 := by
  calc
    injectiveMoment H raw6911 = injectiveMoment H raw6911step0 := by
      have heq : raw6911step0 = raw6911.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6911).symm
    injectiveMoment H raw6911step0 = injectiveMoment H raw6911step1 := by
      have heq : raw6911step1 = -raw6911step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6911step0).symm
    injectiveMoment H raw6911step1 = injectiveMoment H raw6911step2 := by
      have heq : raw6911step2 = (fun i j => raw6911step1 (permutation26 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6911step1 permutation26 permutation3
    _ = injectiveMoment H node212 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
