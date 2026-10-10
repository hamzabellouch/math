import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes0
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes1
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes3
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes4
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes5
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes13

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw832 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]

def raw832step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]

theorem canonical832 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw832 = injectiveMoment H node111 := by
  calc
    injectiveMoment H raw832 = injectiveMoment H raw832step0 := by
      have heq : raw832step0 = (fun i j => raw832 (permutation9 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw832 permutation9 permutation4
    _ = injectiveMoment H node111 := by rfl

def raw833 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1]]

def raw833step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]

theorem canonical833 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw833 = injectiveMoment H node372 := by
  calc
    injectiveMoment H raw833 = injectiveMoment H raw833step0 := by
      have heq : raw833step0 = (fun i j => raw833 (permutation36 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw833 permutation36 permutation4
    _ = injectiveMoment H node372 := by rfl

def raw834 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -3, 2], ![2, 0, -2]]

def raw834step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]

theorem canonical834 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw834 = injectiveMoment H node107 := by
  calc
    injectiveMoment H raw834 = injectiveMoment H raw834step0 := by
      have heq : raw834step0 = (fun i j => raw834 (permutation9 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw834 permutation9 permutation4
    _ = injectiveMoment H node107 := by rfl

def raw835 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]

def raw835step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]

def raw835step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

theorem canonical835 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw835 = injectiveMoment H node872 := by
  calc
    injectiveMoment H raw835 = injectiveMoment H raw835step0 := by
      have heq : raw835step0 = -raw835 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw835).symm
    injectiveMoment H raw835step0 = injectiveMoment H raw835step1 := by
      have heq : raw835step1 = (fun i j => raw835step0 (permutation41 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw835step0 permutation41 permutation8
    _ = injectiveMoment H node872 := by rfl

def raw836 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]

def raw836step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -2, -1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]

def raw836step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2]]

theorem canonical836 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw836 = injectiveMoment H node261 := by
  calc
    injectiveMoment H raw836 = injectiveMoment H raw836step0 := by
      have heq : raw836step0 = -raw836 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw836).symm
    injectiveMoment H raw836step0 = injectiveMoment H raw836step1 := by
      have heq : raw836step1 = (fun i j => raw836step0 (permutation11 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw836step0 permutation11 permutation8
    _ = injectiveMoment H node261 := by rfl

def raw837 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -3, 2], ![1, 0, -1], ![1, 1, -2]]

def raw837step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]

theorem canonical837 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw837 = injectiveMoment H node109 := by
  calc
    injectiveMoment H raw837 = injectiveMoment H raw837step0 := by
      have heq : raw837step0 = (fun i j => raw837 (permutation18 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw837 permutation18 permutation5
    _ = injectiveMoment H node109 := by rfl

def raw838 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -3, 2], ![2, 1, -3]]

def raw838step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 2, -3], ![2, -3, 1]]

theorem canonical838 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw838 = injectiveMoment H node21 := by
  calc
    injectiveMoment H raw838 = injectiveMoment H raw838step0 := by
      have heq : raw838step0 = (fun i j => raw838 (permutation3 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw838 permutation3 permutation4
    _ = injectiveMoment H node21 := by rfl

def raw839 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]

def raw839step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -2, 1], ![1, 2, -3]]

theorem canonical839 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw839 = injectiveMoment H node229 := by
  calc
    injectiveMoment H raw839 = injectiveMoment H raw839step0 := by
      have heq : raw839step0 = (fun i j => raw839 (permutation32 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw839 permutation32 permutation8
    _ = injectiveMoment H node229 := by rfl

def raw840 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 1, -2], ![2, -3, 1]]

def raw840step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -3, 2], ![1, 2, -3]]

theorem canonical840 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw840 = injectiveMoment H node43 := by
  calc
    injectiveMoment H raw840 = injectiveMoment H raw840step0 := by
      have heq : raw840step0 = (fun i j => raw840 (permutation5 i) (permutation7 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw840 permutation5 permutation7
    _ = injectiveMoment H node43 := by rfl

def raw841 : Matrix (Fin 2) (Fin 3) ℤ := ![![-3, 2, 1], ![3, -2, -1]]

def raw841step0 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![2, -2], ![1, -1]]

def raw841step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]

theorem canonical841 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw841 = injectiveMoment H node10 := by
  calc
    injectiveMoment H raw841 = injectiveMoment H raw841step0 := by
      have heq : raw841step0 = raw841.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw841).symm
    injectiveMoment H raw841step0 = injectiveMoment H raw841step1 := by
      have heq : raw841step1 = (fun i j => raw841step0 (permutation4 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw841step0 permutation4 permutation1
    _ = injectiveMoment H node10 := by rfl

def raw842 : Matrix (Fin 2) (Fin 4) ℤ := ![![-3, 2, 2, -1], ![3, -2, -2, 1]]

def raw842step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![2, -2], ![2, -2], ![-1, 1]]

def raw842step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![2, -2], ![2, -2]]

theorem canonical842 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw842 = injectiveMoment H node25 := by
  calc
    injectiveMoment H raw842 = injectiveMoment H raw842step0 := by
      have heq : raw842step0 = raw842.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw842).symm
    injectiveMoment H raw842step0 = injectiveMoment H raw842step1 := by
      have heq : raw842step1 = (fun i j => raw842step0 (permutation13 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw842step0 permutation13 permutation1
    _ = injectiveMoment H node25 := by rfl

def raw843 : Matrix (Fin 2) (Fin 4) ℤ := ![![-3, 2, 3, -2], ![3, -2, -3, 2]]

def raw843step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![2, -2], ![3, -3], ![-2, 2]]

def raw843step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-2, 2], ![2, -2], ![3, -3]]

theorem canonical843 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw843 = injectiveMoment H node23 := by
  calc
    injectiveMoment H raw843 = injectiveMoment H raw843step0 := by
      have heq : raw843step0 = raw843.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw843).symm
    injectiveMoment H raw843step0 = injectiveMoment H raw843step1 := by
      have heq : raw843step1 = (fun i j => raw843step0 (permutation13 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw843step0 permutation13 permutation1
    _ = injectiveMoment H node23 := by rfl

def raw844 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![-2, 2], ![0, 0], ![1, -1], ![1, -1], ![3, -3]]

def raw844step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-2, 2], ![1, -1], ![1, -1], ![3, -3]]

theorem canonical844 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw844 = injectiveMoment H node116 := by
  calc
    injectiveMoment H raw844 = injectiveMoment H raw844step0 := by
      have hz : ∀ j, raw844 (permutation221 0) j = 0 := by decide +kernel
      have heq : raw844step0 = (fun i j => raw844 (permutation221 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw844 permutation221 hz
    _ = injectiveMoment H node116 := by rfl

def raw845 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![-2, 2], ![0, 0], ![1, -1], ![2, -2], ![2, -2]]

def raw845step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-2, 2], ![1, -1], ![2, -2], ![2, -2]]

theorem canonical845 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw845 = injectiveMoment H node117 := by
  calc
    injectiveMoment H raw845 = injectiveMoment H raw845step0 := by
      have hz : ∀ j, raw845 (permutation221 0) j = 0 := by decide +kernel
      have heq : raw845step0 = (fun i j => raw845 (permutation221 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw845 permutation221 hz
    _ = injectiveMoment H node117 := by rfl

def raw846 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-2, 2], ![0, 0], ![2, -2], ![3, -3]]

def raw846step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-2, 2], ![2, -2], ![3, -3]]

theorem canonical846 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw846 = injectiveMoment H node23 := by
  calc
    injectiveMoment H raw846 = injectiveMoment H raw846step0 := by
      have hz : ∀ j, raw846 (permutation80 0) j = 0 := by decide +kernel
      have heq : raw846step0 = (fun i j => raw846 (permutation80 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw846 permutation80 hz
    _ = injectiveMoment H node23 := by rfl

def raw847 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![-2, 2], ![1, -1], ![1, -1], ![1, -1], ![2, -2]]

theorem canonical847 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw847 = injectiveMoment H node380 := by
  rfl

def raw848 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-2, 2], ![1, -1], ![1, -1], ![3, -3]]

theorem canonical848 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw848 = injectiveMoment H node116 := by
  rfl

def raw849 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-2, 2], ![1, -1], ![2, -2], ![2, -2]]

theorem canonical849 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw849 = injectiveMoment H node117 := by
  rfl

def raw850 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-2, 2], ![1, -1], ![4, -4]]

def raw850step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![-1, 1], ![2, -2], ![3, -3]]

theorem canonical850 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw850 = injectiveMoment H node15 := by
  calc
    injectiveMoment H raw850 = injectiveMoment H raw850step0 := by
      have heq : raw850step0 = (fun i j => raw850 (permutation32 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw850 permutation32 permutation2
    _ = injectiveMoment H node15 := by rfl

def raw851 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-2, 2], ![2, -2], ![1, -1], ![2, -2]]

def raw851step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-2, 2], ![1, -1], ![2, -2], ![2, -2]]

theorem canonical851 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw851 = injectiveMoment H node117 := by
  calc
    injectiveMoment H raw851 = injectiveMoment H raw851step0 := by
      have heq : raw851step0 = (fun i j => raw851 (permutation35 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw851 permutation35 permutation1
    _ = injectiveMoment H node117 := by rfl

def raw852 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-2, 2], ![2, -2], ![3, -3]]

theorem canonical852 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw852 = injectiveMoment H node23 := by
  rfl

def raw853 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-2, 2], ![3, -3], ![2, -2]]

def raw853step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-2, 2], ![2, -2], ![3, -3]]

theorem canonical853 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw853 = injectiveMoment H node23 := by
  calc
    injectiveMoment H raw853 = injectiveMoment H raw853step0 := by
      have heq : raw853step0 = (fun i j => raw853 (permutation10 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw853 permutation10 permutation1
    _ = injectiveMoment H node23 := by rfl

def raw854 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![-1, 1], ![1, -1], ![1, -1], ![3, -3]]

theorem canonical854 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw854 = injectiveMoment H node381 := by
  rfl

def raw855 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![-1, 1], ![1, -1], ![2, -2], ![2, -2]]

theorem canonical855 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw855 = injectiveMoment H node382 := by
  rfl

def raw856 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![-1, 1], ![2, -2], ![3, -3]]

def raw856step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-2, 2], ![1, -1], ![1, -1], ![3, -3]]

theorem canonical856 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw856 = injectiveMoment H node116 := by
  calc
    injectiveMoment H raw856 = injectiveMoment H raw856step0 := by
      have heq : raw856step0 = (fun i j => raw856 (permutation148 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw856 permutation148 permutation2
    _ = injectiveMoment H node116 := by rfl

def raw857 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![0, 0], ![0, 0], ![1, -1], ![3, -3]]

def raw857step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![0, 0], ![1, -1], ![3, -3]]

def raw857step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![3, -3]]

theorem canonical857 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw857 = injectiveMoment H node24 := by
  calc
    injectiveMoment H raw857 = injectiveMoment H raw857step0 := by
      have hz : ∀ j, raw857 (permutation241 0) j = 0 := by decide +kernel
      have heq : raw857step0 = (fun i j => raw857 (permutation241 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw857 permutation241 hz
    injectiveMoment H raw857step0 = injectiveMoment H raw857step1 := by
      have hz : ∀ j, raw857step0 (permutation80 0) j = 0 := by decide +kernel
      have heq : raw857step1 = (fun i j => raw857step0 (permutation80 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw857step0 permutation80 hz
    _ = injectiveMoment H node24 := by rfl

def raw858 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![0, 0], ![0, 0], ![2, -2], ![2, -2]]

def raw858step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![0, 0], ![2, -2], ![2, -2]]

def raw858step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![2, -2], ![2, -2]]

theorem canonical858 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw858 = injectiveMoment H node25 := by
  calc
    injectiveMoment H raw858 = injectiveMoment H raw858step0 := by
      have hz : ∀ j, raw858 (permutation241 0) j = 0 := by decide +kernel
      have heq : raw858step0 = (fun i j => raw858 (permutation241 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw858 permutation241 hz
    injectiveMoment H raw858step0 = injectiveMoment H raw858step1 := by
      have hz : ∀ j, raw858step0 (permutation80 0) j = 0 := by decide +kernel
      have heq : raw858step1 = (fun i j => raw858step0 (permutation80 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw858step0 permutation80 hz
    _ = injectiveMoment H node25 := by rfl

def raw859 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![0, 0], ![1, -1], ![1, -1], ![2, -2]]

def raw859step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]

theorem canonical859 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw859 = injectiveMoment H node118 := by
  calc
    injectiveMoment H raw859 = injectiveMoment H raw859step0 := by
      have hz : ∀ j, raw859 (permutation221 0) j = 0 := by decide +kernel
      have heq : raw859step0 = (fun i j => raw859 (permutation221 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw859 permutation221 hz
    _ = injectiveMoment H node118 := by rfl

def raw860 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![0, 0], ![1, -1], ![3, -3]]

def raw860step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![3, -3]]

theorem canonical860 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw860 = injectiveMoment H node24 := by
  calc
    injectiveMoment H raw860 = injectiveMoment H raw860step0 := by
      have hz : ∀ j, raw860 (permutation80 0) j = 0 := by decide +kernel
      have heq : raw860step0 = (fun i j => raw860 (permutation80 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw860 permutation80 hz
    _ = injectiveMoment H node24 := by rfl

def raw861 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![0, 0], ![2, -2], ![2, -2]]

def raw861step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![2, -2], ![2, -2]]

theorem canonical861 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw861 = injectiveMoment H node25 := by
  calc
    injectiveMoment H raw861 = injectiveMoment H raw861step0 := by
      have hz : ∀ j, raw861 (permutation80 0) j = 0 := by decide +kernel
      have heq : raw861step0 = (fun i j => raw861 (permutation80 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw861 permutation80 hz
    _ = injectiveMoment H node25 := by rfl

def raw862 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![0, 0], ![4, -4]]

def raw862step0 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![4, -4]]

def raw862step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![3, -3]]

theorem canonical862 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw862 = injectiveMoment H node8 := by
  calc
    injectiveMoment H raw862 = injectiveMoment H raw862step0 := by
      have hz : ∀ j, raw862 (permutation21 0) j = 0 := by decide +kernel
      have heq : raw862step0 = (fun i j => raw862 (permutation21 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw862 permutation21 hz
    injectiveMoment H raw862step0 = injectiveMoment H raw862step1 := by
      have heq : raw862step1 = (fun i j => raw862step0 (permutation8 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw862step0 permutation8 permutation2
    _ = injectiveMoment H node8 := by rfl

def raw863 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![0, 0], ![1, -1], ![2, -2]]

def raw863step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]

theorem canonical863 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw863 = injectiveMoment H node118 := by
  calc
    injectiveMoment H raw863 = injectiveMoment H raw863step0 := by
      have hz : ∀ j, raw863 (permutation241 0) j = 0 := by decide +kernel
      have heq : raw863step0 = (fun i j => raw863 (permutation241 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw863 permutation241 hz
    _ = injectiveMoment H node118 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
