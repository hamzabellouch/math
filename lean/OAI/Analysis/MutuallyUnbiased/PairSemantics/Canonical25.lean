import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes0
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes1
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes2
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes3
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes4
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes5

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw800 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -3, 2], ![1, 1, -2], ![1, 1, -2]]

theorem canonical800 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw800 = injectiveMoment H node114 := by
  rfl

def raw801 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -3, 2], ![2, 2, -4]]

theorem canonical801 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw801 = injectiveMoment H node20 := by
  rfl

def raw802 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 2, -2], ![2, -1, -1]]

def raw802step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]

theorem canonical802 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw802 = injectiveMoment H node111 := by
  calc
    injectiveMoment H raw802 = injectiveMoment H raw802step0 := by
      have heq : raw802step0 = (fun i j => raw802 (permutation11 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw802 permutation11 permutation3
    _ = injectiveMoment H node111 := by rfl

def raw803 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, -2, 1], ![1, 3, -4]]

theorem canonical803 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw803 = injectiveMoment H node115 := by
  rfl

def raw804 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]

def raw804step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]

theorem canonical804 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw804 = injectiveMoment H node109 := by
  calc
    injectiveMoment H raw804 = injectiveMoment H raw804step0 := by
      have heq : raw804step0 = (fun i j => raw804 (permutation32 i) (permutation7 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw804 permutation32 permutation7
    _ = injectiveMoment H node109 := by rfl

def raw805 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]

def raw805step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -2, 1], ![1, 2, -3]]

theorem canonical805 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw805 = injectiveMoment H node229 := by
  calc
    injectiveMoment H raw805 = injectiveMoment H raw805step0 := by
      have heq : raw805step0 = (fun i j => raw805 (permutation18 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw805 permutation18 permutation6
    _ = injectiveMoment H node229 := by rfl

def raw806 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![2, 1, -3]]

def raw806step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -3, 2], ![1, 2, -3]]

theorem canonical806 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw806 = injectiveMoment H node43 := by
  calc
    injectiveMoment H raw806 = injectiveMoment H raw806step0 := by
      have heq : raw806step0 = (fun i j => raw806 (permutation5 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw806 permutation5 permutation5
    _ = injectiveMoment H node43 := by rfl

def raw807 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, -2, 1], ![1, 2, -3]]

def raw807step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]

theorem canonical807 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw807 = injectiveMoment H node109 := by
  calc
    injectiveMoment H raw807 = injectiveMoment H raw807step0 := by
      have heq : raw807step0 = (fun i j => raw807 (permutation30 i) (permutation7 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw807 permutation30 permutation7
    _ = injectiveMoment H node109 := by rfl

def raw808 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]

def raw808step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]

def raw808step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]

theorem canonical808 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw808 = injectiveMoment H node176 := by
  calc
    injectiveMoment H raw808 = injectiveMoment H raw808step0 := by
      have heq : raw808step0 = -raw808 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw808).symm
    injectiveMoment H raw808step0 = injectiveMoment H raw808step1 := by
      have heq : raw808step1 = (fun i j => raw808step0 (permutation9 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw808step0 permutation9 permutation8
    _ = injectiveMoment H node176 := by rfl

def raw809 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]

def raw809step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]

def raw809step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1]]

theorem canonical809 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw809 = injectiveMoment H node271 := by
  calc
    injectiveMoment H raw809 = injectiveMoment H raw809step0 := by
      have heq : raw809step0 = -raw809 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw809).symm
    injectiveMoment H raw809step0 = injectiveMoment H raw809step1 := by
      have heq : raw809step1 = (fun i j => raw809step0 (permutation12 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw809step0 permutation12 permutation6
    _ = injectiveMoment H node271 := by rfl

def raw810 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![2, 0, -2]]

def raw810step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, -1, -2], ![-1, 1, 0], ![-2, 0, 2]]

def raw810step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 2, -2], ![1, 0, -1]]

theorem canonical810 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw810 = injectiveMoment H node57 := by
  calc
    injectiveMoment H raw810 = injectiveMoment H raw810step0 := by
      have heq : raw810step0 = -raw810 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw810).symm
    injectiveMoment H raw810step0 = injectiveMoment H raw810step1 := by
      have heq : raw810step1 = (fun i j => raw810step0 (permutation4 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw810step0 permutation4 permutation6
    _ = injectiveMoment H node57 := by rfl

def raw811 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![2, -1, -1]]

def raw811step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, -1, -2], ![-1, 0, 1], ![-2, 1, 1]]

def raw811step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 1, -1], ![1, 1, -2]]

theorem canonical811 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw811 = injectiveMoment H node56 := by
  calc
    injectiveMoment H raw811 = injectiveMoment H raw811step0 := by
      have heq : raw811step0 = -raw811 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw811).symm
    injectiveMoment H raw811step0 = injectiveMoment H raw811step1 := by
      have heq : raw811step1 = (fun i j => raw811step0 (permutation3 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw811step0 permutation3 permutation6
    _ = injectiveMoment H node56 := by rfl

def raw812 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 1, -2], ![1, -2, 1], ![1, 0, -1]]

def raw812step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -2, 1], ![1, 2, -3]]

theorem canonical812 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw812 = injectiveMoment H node229 := by
  calc
    injectiveMoment H raw812 = injectiveMoment H raw812step0 := by
      have heq : raw812step0 = (fun i j => raw812 (permutation26 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw812 permutation26 permutation6
    _ = injectiveMoment H node229 := by rfl

def raw813 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 1, -2], ![2, -2, 0]]

def raw813step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, -1, -2], ![-1, -1, 2], ![-2, 2, 0]]

def raw813step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![2, -1, -1]]

theorem canonical813 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw813 = injectiveMoment H node36 := by
  calc
    injectiveMoment H raw813 = injectiveMoment H raw813step0 := by
      have heq : raw813step0 = -raw813 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw813).symm
    injectiveMoment H raw813step0 = injectiveMoment H raw813step1 := by
      have heq : raw813step1 = (fun i j => raw813step0 (permutation4 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw813step0 permutation4 permutation8
    _ = injectiveMoment H node36 := by rfl

def raw814 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 2, -3], ![2, -3, 1]]

theorem canonical814 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw814 = injectiveMoment H node21 := by
  rfl

def raw815 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![2, -4, 2], ![1, 3, -4]]

def raw815step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 3, -4], ![2, -4, 2]]

theorem canonical815 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw815 = injectiveMoment H node22 := by
  calc
    injectiveMoment H raw815 = injectiveMoment H raw815step0 := by
      have heq : raw815step0 = (fun i j => raw815 (permutation4 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw815 permutation4 permutation3
    _ = injectiveMoment H node22 := by rfl

def raw816 : Matrix (Fin 2) (Fin 3) ℤ := ![![-3, 1, 2], ![3, -1, -2]]

def raw816step0 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]

theorem canonical816 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw816 = injectiveMoment H node10 := by
  calc
    injectiveMoment H raw816 = injectiveMoment H raw816step0 := by
      have heq : raw816step0 = raw816.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw816).symm
    _ = injectiveMoment H node10 := by rfl

def raw817 : Matrix (Fin 3) (Fin 4) ℤ := ![![-3, 1, 2, 0], ![1, -2, -1, 2], ![2, 1, -1, -2]]

def raw817step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![2, -1, -1], ![0, 2, -2]]

def raw817step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]

theorem canonical817 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw817 = injectiveMoment H node111 := by
  calc
    injectiveMoment H raw817 = injectiveMoment H raw817step0 := by
      have heq : raw817step0 = raw817.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw817).symm
    injectiveMoment H raw817step0 = injectiveMoment H raw817step1 := by
      have heq : raw817step1 = (fun i j => raw817step0 (permutation13 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw817step0 permutation13 permutation3
    _ = injectiveMoment H node111 := by rfl

def raw818 : Matrix (Fin 3) (Fin 4) ℤ := ![![-3, 1, 2, 0], ![1, -2, 2, -1], ![2, 1, -4, 1]]

def raw818step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![2, 2, -4], ![0, -1, 1]]

def raw818step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![2, 2, -4]]

theorem canonical818 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw818 = injectiveMoment H node106 := by
  calc
    injectiveMoment H raw818 = injectiveMoment H raw818step0 := by
      have heq : raw818step0 = raw818.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw818).symm
    injectiveMoment H raw818step0 = injectiveMoment H raw818step1 := by
      have heq : raw818step1 = (fun i j => raw818step0 (permutation13 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw818step0 permutation13 permutation3
    _ = injectiveMoment H node106 := by rfl

def raw819 : Matrix (Fin 3) (Fin 4) ℤ := ![![-3, 1, 2, 0], ![1, 1, -3, 1], ![2, -2, 1, -1]]

def raw819step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 1, -2], ![2, -3, 1], ![0, 1, -1]]

def raw819step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]

theorem canonical819 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw819 = injectiveMoment H node109 := by
  calc
    injectiveMoment H raw819 = injectiveMoment H raw819step0 := by
      have heq : raw819step0 = raw819.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw819).symm
    injectiveMoment H raw819step0 = injectiveMoment H raw819step1 := by
      have heq : raw819step1 = (fun i j => raw819step0 (permutation13 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw819step0 permutation13 permutation3
    _ = injectiveMoment H node109 := by rfl

def raw820 : Matrix (Fin 3) (Fin 4) ℤ := ![![-3, 1, 2, 0], ![1, 2, -2, -1], ![2, -3, 0, 1]]

def raw820step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 2, -3], ![2, -2, 0], ![0, -1, 1]]

def raw820step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]

theorem canonical820 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw820 = injectiveMoment H node107 := by
  calc
    injectiveMoment H raw820 = injectiveMoment H raw820step0 := by
      have heq : raw820step0 = raw820.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw820).symm
    injectiveMoment H raw820step0 = injectiveMoment H raw820step1 := by
      have heq : raw820step1 = (fun i j => raw820step0 (permutation13 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw820step0 permutation13 permutation3
    _ = injectiveMoment H node107 := by rfl

def raw821 : Matrix (Fin 3) (Fin 4) ℤ := ![![-3, 1, 2, 0], ![2, -2, -1, 1], ![1, 1, -1, -1]]

def raw821step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![2, -1, -1], ![0, 1, -1]]

def raw821step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -2, -1], ![-1, 2, -1], ![-2, 1, 1], ![0, -1, 1]]

def raw821step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2]]

theorem canonical821 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw821 = injectiveMoment H node261 := by
  calc
    injectiveMoment H raw821 = injectiveMoment H raw821step0 := by
      have heq : raw821step0 = raw821.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw821).symm
    injectiveMoment H raw821step0 = injectiveMoment H raw821step1 := by
      have heq : raw821step1 = -raw821step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw821step0).symm
    injectiveMoment H raw821step1 = injectiveMoment H raw821step2 := by
      have heq : raw821step2 = (fun i j => raw821step1 (permutation10 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw821step1 permutation10 permutation8
    _ = injectiveMoment H node261 := by rfl

def raw822 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -3, 3], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]

def raw822step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -3, 1]]

theorem canonical822 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw822 = injectiveMoment H node347 := by
  calc
    injectiveMoment H raw822 = injectiveMoment H raw822step0 := by
      have heq : raw822step0 = (fun i j => raw822 (permutation73 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw822 permutation73 permutation5
    _ = injectiveMoment H node347 := by rfl

def raw823 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -3, 3], ![1, 0, -1], ![2, 1, -3]]

def raw823step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 2, -3], ![2, -3, 1]]

theorem canonical823 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw823 = injectiveMoment H node95 := by
  calc
    injectiveMoment H raw823 = injectiveMoment H raw823step0 := by
      have heq : raw823step0 = (fun i j => raw823 (permutation18 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw823 permutation18 permutation5
    _ = injectiveMoment H node95 := by rfl

def raw824 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -3, 3], ![1, 1, -2], ![2, 0, -2]]

def raw824step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 1, -2], ![2, -3, 1]]

theorem canonical824 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw824 = injectiveMoment H node97 := by
  calc
    injectiveMoment H raw824 = injectiveMoment H raw824step0 := by
      have heq : raw824step0 = (fun i j => raw824 (permutation20 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw824 permutation20 permutation5
    _ = injectiveMoment H node97 := by rfl

def raw825 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 0, 0], ![1, 0, -1], ![2, 0, -2]]

def raw825step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, 2, -2], ![0, 0, 0], ![-1, 0, 1], ![-2, 0, 2]]

def raw825step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -2, -1], ![0, 2, -2], ![-1, 0, 1], ![-2, 0, 2]]

def raw825step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]

theorem canonical825 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw825 = injectiveMoment H node177 := by
  calc
    injectiveMoment H raw825 = injectiveMoment H raw825step0 := by
      have heq : raw825step0 = -raw825 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw825).symm
    injectiveMoment H raw825step0 = injectiveMoment H raw825step1 := by
      have hz : ∀ j, raw825step0 (permutation80 0) j = 0 := by decide +kernel
      have heq : raw825step1 = (fun i j => raw825step0 (permutation80 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw825step0 permutation80 hz
    injectiveMoment H raw825step1 = injectiveMoment H raw825step2 := by
      have heq : raw825step2 = (fun i j => raw825step1 (permutation12 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw825step1 permutation12 permutation6
    _ = injectiveMoment H node177 := by rfl

def raw826 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]

def raw826step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]

theorem canonical826 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw826 = injectiveMoment H node369 := by
  calc
    injectiveMoment H raw826 = injectiveMoment H raw826step0 := by
      have heq : raw826step0 = (fun i j => raw826 (permutation39 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw826 permutation39 permutation4
    _ = injectiveMoment H node369 := by rfl

def raw827 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]

def raw827step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]

theorem canonical827 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw827 = injectiveMoment H node368 := by
  calc
    injectiveMoment H raw827 = injectiveMoment H raw827step0 := by
      have heq : raw827step0 = (fun i j => raw827 (permutation39 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw827 permutation39 permutation4
    _ = injectiveMoment H node368 := by rfl

def raw828 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![3, -1, -2]]

def raw828step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![3, -2, -1]]

theorem canonical828 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw828 = injectiveMoment H node105 := by
  calc
    injectiveMoment H raw828 = injectiveMoment H raw828step0 := by
      have heq : raw828step0 = (fun i j => raw828 (permutation11 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw828 permutation11 permutation4
    _ = injectiveMoment H node105 := by rfl

def raw829 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]

def raw829step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]

theorem canonical829 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw829 = injectiveMoment H node377 := by
  calc
    injectiveMoment H raw829 = injectiveMoment H raw829step0 := by
      have heq : raw829step0 = (fun i j => raw829 (permutation38 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw829 permutation38 permutation4
    _ = injectiveMoment H node377 := by rfl

def raw830 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, -1, 0], ![2, 1, -3]]

def raw830step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]

theorem canonical830 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw830 = injectiveMoment H node107 := by
  calc
    injectiveMoment H raw830 = injectiveMoment H raw830step0 := by
      have heq : raw830step0 = (fun i j => raw830 (permutation31 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw830 permutation31 permutation8
    _ = injectiveMoment H node107 := by rfl

def raw831 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]

def raw831step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -2, -1], ![0, 2, -2], ![-1, 0, 1], ![-2, 0, 2]]

def raw831step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]

theorem canonical831 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw831 = injectiveMoment H node177 := by
  calc
    injectiveMoment H raw831 = injectiveMoment H raw831step0 := by
      have heq : raw831step0 = -raw831 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw831).symm
    injectiveMoment H raw831step0 = injectiveMoment H raw831step1 := by
      have heq : raw831step1 = (fun i j => raw831step0 (permutation12 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw831step0 permutation12 permutation6
    _ = injectiveMoment H node177 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
