import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes4
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes12
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes15
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes17
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes18
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes19
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes23
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes25
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes26
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes37

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw1856 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, -1, 1], ![0, 2, 1, -3], ![2, -1, 0, -1]]

def raw1856step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 1, 0, -3], ![0, 0, 1, -1], ![0, -2, -1, 3], ![-2, 1, 0, 1]]

def raw1856step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 1, -2, 1], ![0, 1, 2, -3], ![1, 0, 0, -1]]

theorem canonical1856 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw1856 = injectiveMoment H node816 := by
  calc
    injectiveMoment H raw1856 = injectiveMoment H raw1856step0 := by
      have heq : raw1856step0 = -raw1856 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw1856).symm
    injectiveMoment H raw1856step0 = injectiveMoment H raw1856step1 := by
      have heq : raw1856step1 = (fun i j => raw1856step0 (permutation25 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1856step0 permutation25 permutation23
    _ = injectiveMoment H node816 := by rfl

def raw1857 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def raw1857step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 1, 0, -3], ![0, 0, 1, -1], ![0, -2, -2, 4], ![-1, 1, 0, 0], ![-1, 0, 1, 0]]

def raw1857step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 2, -3]]

theorem canonical1857 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw1857 = injectiveMoment H node1486 := by
  calc
    injectiveMoment H raw1857 = injectiveMoment H raw1857step0 := by
      have heq : raw1857step0 = -raw1857 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw1857).symm
    injectiveMoment H raw1857step0 = injectiveMoment H raw1857step1 := by
      have heq : raw1857step1 = (fun i j => raw1857step0 (permutation101 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1857step0 permutation101 permutation17
    _ = injectiveMoment H node1486 := by rfl

def raw1858 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, 0, -1, 0], ![1, -1, 0, 0]]

def raw1858step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 1, 0, -3], ![0, 0, 1, -1], ![0, -2, -2, 4], ![-1, 0, 1, 0], ![-1, 1, 0, 0]]

def raw1858step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 2, -3]]

theorem canonical1858 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw1858 = injectiveMoment H node1486 := by
  calc
    injectiveMoment H raw1858 = injectiveMoment H raw1858step0 := by
      have heq : raw1858step0 = -raw1858 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw1858).symm
    injectiveMoment H raw1858step0 = injectiveMoment H raw1858step1 := by
      have heq : raw1858step1 = (fun i j => raw1858step0 (permutation95 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1858step0 permutation95 permutation17
    _ = injectiveMoment H node1486 := by rfl

def raw1859 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, -1, 1], ![1, -1, 1, -1], ![1, 2, 0, -3]]

def raw1859step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 1, 0, -3], ![0, 0, 1, -1], ![-1, 1, -1, 1], ![-1, -2, 0, 3]]

def raw1859step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, -2, 3], ![0, 2, 1, -3], ![1, 0, 0, -1]]

theorem canonical1859 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw1859 = injectiveMoment H node1094 := by
  calc
    injectiveMoment H raw1859 = injectiveMoment H raw1859step0 := by
      have heq : raw1859step0 = -raw1859 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw1859).symm
    injectiveMoment H raw1859step0 = injectiveMoment H raw1859step1 := by
      have heq : raw1859step1 = (fun i j => raw1859step0 (permutation25 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1859step0 permutation25 permutation21
    _ = injectiveMoment H node1094 := by rfl

def raw1860 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, -1, 1], ![1, 0, 2, -3], ![1, 1, -1, -1]]

def raw1860step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, -1, 1], ![0, 1, 2, -3], ![1, 1, -1, -1]]

theorem canonical1860 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1860 = injectiveMoment H node797 := by
  calc
    injectiveMoment H raw1860 = injectiveMoment H raw1860step0 := by
      have heq : raw1860step0 = (fun i j => raw1860 (permutation9 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1860 permutation9 permutation15
    _ = injectiveMoment H node797 := by rfl

def raw1861 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 0, 0], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 2, -1, -2]]

def raw1861step0 : Matrix (Fin 4) (Fin 5) ℤ := ![![-2, 0, 0, 1, 1], ![-1, 0, 0, -1, 2], ![0, 0, 1, 0, -1], ![3, 0, -1, 0, -2]]

def raw1861step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 0, -1, 2], ![0, 1, 0, -1], ![3, -1, 0, -2]]

def raw1861step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 2, -1], ![0, 1, 1, -2], ![1, 0, -1, 0]]

theorem canonical1861 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1861 = injectiveMoment H node1207 := by
  calc
    injectiveMoment H raw1861 = injectiveMoment H raw1861step0 := by
      have heq : raw1861step0 = raw1861.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1861).symm
    injectiveMoment H raw1861step0 = injectiveMoment H raw1861step1 := by
      have hz : ∀ i, raw1861step0 i (permutation57 0) = 0 := by decide +kernel
      have heq : raw1861step1 = (fun i j => raw1861step0 i (permutation57 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw1861step0 permutation57 hz
    injectiveMoment H raw1861step1 = injectiveMoment H raw1861step2 := by
      have heq : raw1861step2 = (fun i j => raw1861step1 (permutation29 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1861step1 permutation29 permutation18
    _ = injectiveMoment H node1207 := by rfl

def raw1862 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 0, 0], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, -1, 1, -2]]

def raw1862step0 : Matrix (Fin 4) (Fin 5) ℤ := ![![-2, 0, 0, 0, 2], ![-1, 0, 1, 1, -1], ![0, 0, -1, 0, 1], ![3, 0, 0, -1, -2]]

def raw1862step1 : Matrix (Fin 4) (Fin 5) ℤ := ![![2, 0, 0, 0, -2], ![1, 0, -1, -1, 1], ![0, 0, 1, 0, -1], ![-3, 0, 0, 1, 2]]

def raw1862step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![1, -1, -1, 1], ![0, 1, 0, -1], ![-3, 0, 1, 2]]

def raw1862step3 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -2, 2], ![0, 1, -1, 0], ![1, 0, 2, -3]]

theorem canonical1862 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw1862 = injectiveMoment H node1109 := by
  calc
    injectiveMoment H raw1862 = injectiveMoment H raw1862step0 := by
      have heq : raw1862step0 = raw1862.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1862).symm
    injectiveMoment H raw1862step0 = injectiveMoment H raw1862step1 := by
      have heq : raw1862step1 = -raw1862step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw1862step0).symm
    injectiveMoment H raw1862step1 = injectiveMoment H raw1862step2 := by
      have hz : ∀ i, raw1862step1 i (permutation57 0) = 0 := by decide +kernel
      have heq : raw1862step2 = (fun i j => raw1862step1 i (permutation57 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw1862step1 permutation57 hz
    injectiveMoment H raw1862step2 = injectiveMoment H raw1862step3 := by
      have heq : raw1862step3 = (fun i j => raw1862step2 (permutation15 i) (permutation24 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1862step2 permutation15 permutation24
    _ = injectiveMoment H node1109 := by rfl

def raw1863 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 0, 0], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 1, 1, -3]]

def raw1863step0 : Matrix (Fin 4) (Fin 5) ℤ := ![![-2, 0, 0, 1, 1], ![-1, 0, 1, -1, 1], ![0, 0, -1, 0, 1], ![3, 0, 0, 0, -3]]

def raw1863step1 : Matrix (Fin 4) (Fin 5) ℤ := ![![2, 0, 0, -1, -1], ![1, 0, -1, 1, -1], ![0, 0, 1, 0, -1], ![-3, 0, 0, 0, 3]]

def raw1863step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![1, -1, 1, -1], ![0, 1, 0, -1], ![-3, 0, 0, 3]]

def raw1863step3 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, 3, -3], ![0, 1, -1, 0], ![1, -1, -1, 1]]

theorem canonical1863 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw1863 = injectiveMoment H node1268 := by
  calc
    injectiveMoment H raw1863 = injectiveMoment H raw1863step0 := by
      have heq : raw1863step0 = raw1863.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1863).symm
    injectiveMoment H raw1863step0 = injectiveMoment H raw1863step1 := by
      have heq : raw1863step1 = -raw1863step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw1863step0).symm
    injectiveMoment H raw1863step1 = injectiveMoment H raw1863step2 := by
      have hz : ∀ i, raw1863step1 i (permutation57 0) = 0 := by decide +kernel
      have heq : raw1863step2 = (fun i j => raw1863step1 i (permutation57 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw1863step1 permutation57 hz
    injectiveMoment H raw1863step2 = injectiveMoment H raw1863step3 := by
      have heq : raw1863step3 = (fun i j => raw1863step2 (permutation14 i) (permutation24 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1863step2 permutation14 permutation24
    _ = injectiveMoment H node1268 := by rfl

def raw1864 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 0, 0], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 0, 1, -2]]

def raw1864step0 : Matrix (Fin 4) (Fin 5) ℤ := ![![-2, 0, 0, 1, 1], ![-1, 0, 1, 0, 0], ![0, 0, -1, 0, 1], ![3, 0, 0, -1, -2]]

def raw1864step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 1, 0, 0], ![0, -1, 0, 1], ![3, 0, -1, -2]]

def raw1864step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 1, 0], ![0, 1, 0, -1], ![1, 0, 1, -2]]

theorem canonical1864 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1864 = injectiveMoment H node1202 := by
  calc
    injectiveMoment H raw1864 = injectiveMoment H raw1864step0 := by
      have heq : raw1864step0 = raw1864.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1864).symm
    injectiveMoment H raw1864step0 = injectiveMoment H raw1864step1 := by
      have hz : ∀ i, raw1864step0 i (permutation57 0) = 0 := by decide +kernel
      have heq : raw1864step1 = (fun i j => raw1864step0 i (permutation57 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw1864step0 permutation57 hz
    injectiveMoment H raw1864step1 = injectiveMoment H raw1864step2 := by
      have heq : raw1864step2 = (fun i j => raw1864step1 (permutation32 i) (permutation24 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1864step1 permutation32 permutation24
    _ = injectiveMoment H node1202 := by rfl

def raw1865 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 0, 0], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 1, -2]]

def raw1865step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 1, -2]]

def raw1865step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 1, 0], ![0, 1, 1, -2], ![1, 0, 0, -1]]

theorem canonical1865 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1865 = injectiveMoment H node1203 := by
  calc
    injectiveMoment H raw1865 = injectiveMoment H raw1865step0 := by
      have hz : ∀ j, raw1865 (permutation57 0) j = 0 := by decide +kernel
      have heq : raw1865step0 = (fun i j => raw1865 (permutation57 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw1865 permutation57 hz
    injectiveMoment H raw1865step0 = injectiveMoment H raw1865step1 := by
      have heq : raw1865step1 = (fun i j => raw1865step0 (permutation12 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1865step0 permutation12 permutation17
    _ = injectiveMoment H node1203 := by rfl

def raw1866 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 0, 0], ![0, 1, 1, -2], ![1, 0, -1, 0], ![1, 0, 0, -1]]

def raw1866step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 1, 0, -3], ![0, 0, 0, 0], ![0, -1, -1, 2], ![-1, 0, 1, 0], ![-1, 0, 0, 1]]

def raw1866step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 1, 0, -3], ![0, -1, -1, 2], ![-1, 0, 1, 0], ![-1, 0, 0, 1]]

def raw1866step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, 0, 2, -3]]

theorem canonical1866 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw1866 = injectiveMoment H node1043 := by
  calc
    injectiveMoment H raw1866 = injectiveMoment H raw1866step0 := by
      have heq : raw1866step0 = -raw1866 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw1866).symm
    injectiveMoment H raw1866step0 = injectiveMoment H raw1866step1 := by
      have hz : ∀ j, raw1866step0 (permutation57 0) j = 0 := by decide +kernel
      have heq : raw1866step1 = (fun i j => raw1866step0 (permutation57 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw1866step0 permutation57 hz
    injectiveMoment H raw1866step1 = injectiveMoment H raw1866step2 := by
      have heq : raw1866step2 = (fun i j => raw1866step1 (permutation20 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1866step1 permutation20 permutation17
    _ = injectiveMoment H node1043 := by rfl

def raw1867 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 0, 0], ![0, 1, 2, -3], ![1, 0, -1, 0], ![1, 0, -1, 0]]

def raw1867step0 : Matrix (Fin 4) (Fin 5) ℤ := ![![-2, 0, 0, 1, 1], ![-1, 0, 1, 0, 0], ![0, 0, 2, -1, -1], ![3, 0, -3, 0, 0]]

def raw1867step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 1, 0, 0], ![0, 2, -1, -1], ![3, -3, 0, 0]]

def raw1867step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 0, 3, -3], ![1, 1, -2, 0]]

theorem canonical1867 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1867 = injectiveMoment H node1041 := by
  calc
    injectiveMoment H raw1867 = injectiveMoment H raw1867step0 := by
      have heq : raw1867step0 = raw1867.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1867).symm
    injectiveMoment H raw1867step0 = injectiveMoment H raw1867step1 := by
      have hz : ∀ i, raw1867step0 i (permutation57 0) = 0 := by decide +kernel
      have heq : raw1867step1 = (fun i j => raw1867step0 i (permutation57 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw1867step0 permutation57 hz
    injectiveMoment H raw1867step1 = injectiveMoment H raw1867step2 := by
      have heq : raw1867step2 = (fun i j => raw1867step1 (permutation24 i) (permutation25 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1867step1 permutation24 permutation25
    _ = injectiveMoment H node1041 := by rfl

def raw1868 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 0, 0], ![1, -1, 1, -1], ![1, 2, -1, -2]]

def raw1868step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 0, -1, 2], ![0, 0, 1, -1], ![3, 0, -1, -2]]

def raw1868step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![3, -1, -2]]

def raw1868step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2]]

theorem canonical1868 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1868 = injectiveMoment H node261 := by
  calc
    injectiveMoment H raw1868 = injectiveMoment H raw1868step0 := by
      have heq : raw1868step0 = raw1868.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1868).symm
    injectiveMoment H raw1868step0 = injectiveMoment H raw1868step1 := by
      have hz : ∀ i, raw1868step0 i (permutation15 0) = 0 := by decide +kernel
      have heq : raw1868step1 = (fun i j => raw1868step0 i (permutation15 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw1868step0 permutation15 hz
    injectiveMoment H raw1868step1 = injectiveMoment H raw1868step2 := by
      have heq : raw1868step2 = (fun i j => raw1868step1 (permutation30 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1868step1 permutation30 permutation6
    _ = injectiveMoment H node261 := by rfl

def raw1869 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 0, 0], ![1, 0, -1, 0], ![1, 1, 1, -3]]

def raw1869step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 0, 0, 1], ![0, 0, -1, 1], ![3, 0, 0, -3]]

def raw1869step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![1, 0, 0, -1], ![0, 0, 1, -1], ![-3, 0, 0, 3]]

def raw1869step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, 1, -1], ![-3, 0, 3]]

def raw1869step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0]]

theorem canonical1869 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw1869 = injectiveMoment H node285 := by
  calc
    injectiveMoment H raw1869 = injectiveMoment H raw1869step0 := by
      have heq : raw1869step0 = raw1869.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1869).symm
    injectiveMoment H raw1869step0 = injectiveMoment H raw1869step1 := by
      have heq : raw1869step1 = -raw1869step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw1869step0).symm
    injectiveMoment H raw1869step1 = injectiveMoment H raw1869step2 := by
      have hz : ∀ i, raw1869step1 i (permutation15 0) = 0 := by decide +kernel
      have heq : raw1869step2 = (fun i j => raw1869step1 i (permutation15 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw1869step1 permutation15 hz
    injectiveMoment H raw1869step2 = injectiveMoment H raw1869step3 := by
      have heq : raw1869step3 = (fun i j => raw1869step2 (permutation10 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1869step2 permutation10 permutation6
    _ = injectiveMoment H node285 := by rfl

def raw1870 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, -1, 1, 0], ![0, 1, -1, 0], ![2, 1, -1, -2]]

def raw1870step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, -1, 0], ![2, 1, -1, -2]]

theorem canonical1870 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1870 = injectiveMoment H node1630 := by
  calc
    injectiveMoment H raw1870 = injectiveMoment H raw1870step0 := by
      have heq : raw1870step0 = (fun i j => raw1870 (permutation39 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1870 permutation39 permutation9
    _ = injectiveMoment H node1630 := by rfl

def raw1871 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, -1, 1, 0], ![0, 1, 0, -1], ![2, 1, -2, -1]]

def raw1871step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, 1, -2, -1]]

theorem canonical1871 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1871 = injectiveMoment H node1631 := by
  calc
    injectiveMoment H raw1871 = injectiveMoment H raw1871step0 := by
      have heq : raw1871step0 = (fun i j => raw1871 (permutation39 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1871 permutation39 permutation9
    _ = injectiveMoment H node1631 := by rfl

def raw1872 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, -1, 1, 0], ![1, 0, -1, 0], ![1, 2, -1, -2]]

def raw1872step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![1, 0, -1, 0], ![1, 2, -1, -2]]

theorem canonical1872 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1872 = injectiveMoment H node1634 := by
  calc
    injectiveMoment H raw1872 = injectiveMoment H raw1872step0 := by
      have heq : raw1872step0 = (fun i j => raw1872 (permutation39 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1872 permutation39 permutation9
    _ = injectiveMoment H node1634 := by rfl

def raw1873 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 0, -1, 1], ![2, 1, 0, -3]]

def raw1873step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 0, 1], ![0, 1, 0, -1], ![1, 0, 2, -3]]

theorem canonical1873 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1873 = injectiveMoment H node1197 := by
  calc
    injectiveMoment H raw1873 = injectiveMoment H raw1873step0 := by
      have heq : raw1873step0 = (fun i j => raw1873 (permutation11 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1873 permutation11 permutation17
    _ = injectiveMoment H node1197 := by rfl

def raw1874 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 0, 0, 0], ![0, 1, -1, 0], ![2, 0, 0, -2]]

def raw1874step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![2, 0, 0, -2]]

def raw1874step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, -1, 0, 0]]

theorem canonical1874 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1874 = injectiveMoment H node1221 := by
  calc
    injectiveMoment H raw1874 = injectiveMoment H raw1874step0 := by
      have hz : ∀ j, raw1874 (permutation80 0) j = 0 := by decide +kernel
      have heq : raw1874step0 = (fun i j => raw1874 (permutation80 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw1874 permutation80 hz
    injectiveMoment H raw1874step0 = injectiveMoment H raw1874step1 := by
      have heq : raw1874step1 = (fun i j => raw1874step0 (permutation13 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1874step0 permutation13 permutation17
    _ = injectiveMoment H node1221 := by rfl

def raw1875 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 0, 0, 0], ![1, -1, 0, 0], ![1, 2, -1, -2]]

def raw1875step0 : Matrix (Fin 4) (Fin 5) ℤ := ![![-2, 0, 0, 1, 1], ![-1, 0, 0, -1, 2], ![0, 1, 0, 0, -1], ![3, -1, 0, 0, -2]]

def raw1875step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 0, -1, 2], ![0, 1, 0, -1], ![3, -1, 0, -2]]

def raw1875step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 2, -1], ![0, 1, 1, -2], ![1, 0, -1, 0]]

theorem canonical1875 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1875 = injectiveMoment H node1207 := by
  calc
    injectiveMoment H raw1875 = injectiveMoment H raw1875step0 := by
      have heq : raw1875step0 = raw1875.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1875).symm
    injectiveMoment H raw1875step0 = injectiveMoment H raw1875step1 := by
      have hz : ∀ i, raw1875step0 i (permutation80 0) = 0 := by decide +kernel
      have heq : raw1875step1 = (fun i j => raw1875step0 i (permutation80 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw1875step0 permutation80 hz
    injectiveMoment H raw1875step1 = injectiveMoment H raw1875step2 := by
      have heq : raw1875step2 = (fun i j => raw1875step1 (permutation29 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1875step1 permutation29 permutation18
    _ = injectiveMoment H node1207 := by rfl

def raw1876 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 0, 0, 0], ![1, 0, 0, -1], ![1, 1, -1, -1]]

def raw1876step0 : Matrix (Fin 4) (Fin 5) ℤ := ![![-2, 0, 0, 1, 1], ![-1, 0, 0, 0, 1], ![0, 1, 0, 0, -1], ![3, -1, 0, -1, -1]]

def raw1876step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 0, 0, 1], ![0, 1, 0, -1], ![3, -1, -1, -1]]

def raw1876step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 0, 1, -2]]

theorem canonical1876 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1876 = injectiveMoment H node969 := by
  calc
    injectiveMoment H raw1876 = injectiveMoment H raw1876step0 := by
      have heq : raw1876step0 = raw1876.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1876).symm
    injectiveMoment H raw1876step0 = injectiveMoment H raw1876step1 := by
      have hz : ∀ i, raw1876step0 i (permutation80 0) = 0 := by decide +kernel
      have heq : raw1876step1 = (fun i j => raw1876step0 i (permutation80 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw1876step0 permutation80 hz
    injectiveMoment H raw1876step1 = injectiveMoment H raw1876step2 := by
      have heq : raw1876step2 = (fun i j => raw1876step1 (permutation30 i) (permutation24 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1876step1 permutation30 permutation24
    _ = injectiveMoment H node969 := by rfl

def raw1877 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 0, 0, 0], ![2, 1, -1, -2]]

def raw1877step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-1, 0, 0, 1], ![0, 1, 0, -1], ![3, -1, 0, -2]]

def raw1877step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![3, -1, -2]]

def raw1877step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0]]

theorem canonical1877 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1877 = injectiveMoment H node272 := by
  calc
    injectiveMoment H raw1877 = injectiveMoment H raw1877step0 := by
      have heq : raw1877step0 = raw1877.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1877).symm
    injectiveMoment H raw1877step0 = injectiveMoment H raw1877step1 := by
      have hz : ∀ i, raw1877step0 i (permutation21 0) = 0 := by decide +kernel
      have heq : raw1877step1 = (fun i j => raw1877step0 i (permutation21 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw1877step0 permutation21 hz
    injectiveMoment H raw1877step1 = injectiveMoment H raw1877step2 := by
      have heq : raw1877step2 = (fun i j => raw1877step1 (permutation29 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1877step1 permutation29 permutation6
    _ = injectiveMoment H node272 := by rfl

def raw1878 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 0, -1, 1], ![2, 1, -1, -2]]

def raw1878step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, 2, -1, -2]]

theorem canonical1878 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1878 = injectiveMoment H node2407 := by
  calc
    injectiveMoment H raw1878 = injectiveMoment H raw1878step0 := by
      have heq : raw1878step0 = (fun i j => raw1878 (permutation45 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1878 permutation45 permutation15
    _ = injectiveMoment H node2407 := by rfl

def raw1879 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 0, 0, 0], ![2, 1, -2, -1]]

def raw1879step0 : Matrix (Fin 4) (Fin 5) ℤ := ![![-2, 0, 0, 0, 2], ![-1, 0, 0, 0, 1], ![0, 1, 1, 0, -2], ![3, -1, -1, 0, -1]]

def raw1879step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-1, 0, 0, 1], ![0, 1, 1, -2], ![3, -1, -1, -1]]

def raw1879step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 1, -1], ![0, 0, 2, -2], ![1, 1, -2, 0]]

theorem canonical1879 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1879 = injectiveMoment H node967 := by
  calc
    injectiveMoment H raw1879 = injectiveMoment H raw1879step0 := by
      have heq : raw1879step0 = raw1879.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1879).symm
    injectiveMoment H raw1879step0 = injectiveMoment H raw1879step1 := by
      have hz : ∀ i, raw1879step0 i (permutation104 0) = 0 := by decide +kernel
      have heq : raw1879step1 = (fun i j => raw1879step0 i (permutation104 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw1879step0 permutation104 hz
    injectiveMoment H raw1879step1 = injectiveMoment H raw1879step2 := by
      have heq : raw1879step2 = (fun i j => raw1879step1 (permutation29 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1879step1 permutation29 permutation18
    _ = injectiveMoment H node967 := by rfl

def raw1880 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![2, 0, -1, -1]]

def raw1880step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, 0, -1, 0]]

theorem canonical1880 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1880 = injectiveMoment H node2422 := by
  calc
    injectiveMoment H raw1880 = injectiveMoment H raw1880step0 := by
      have heq : raw1880step0 = (fun i j => raw1880 (permutation34 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1880 permutation34 permutation15
    _ = injectiveMoment H node2422 := by rfl

def raw1881 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, 0, -2, 0]]

def raw1881step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, 0, 0, -1]]

theorem canonical1881 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1881 = injectiveMoment H node2421 := by
  calc
    injectiveMoment H raw1881 = injectiveMoment H raw1881step0 := by
      have heq : raw1881step0 = (fun i j => raw1881 (permutation34 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1881 permutation34 permutation15
    _ = injectiveMoment H node2421 := by rfl

def raw1882 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -2, 0], ![2, -1, 0, -1]]

theorem canonical1882 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1882 = injectiveMoment H node1672 := by
  rfl

def raw1883 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, -1, 1], ![1, 2, -1, -2]]

theorem canonical1883 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1883 = injectiveMoment H node1673 := by
  rfl

def raw1884 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 2, -2, -1]]

theorem canonical1884 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1884 = injectiveMoment H node1674 := by
  rfl

def raw1885 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, 0, -1, 0], ![1, 1, -1, -1]]

def raw1885step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 1, -1, -1]]

theorem canonical1885 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1885 = injectiveMoment H node2419 := by
  calc
    injectiveMoment H raw1885 = injectiveMoment H raw1885step0 := by
      have heq : raw1885step0 = (fun i j => raw1885 (permutation33 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1885 permutation33 permutation15
    _ = injectiveMoment H node2419 := by rfl

def raw1886 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, 0, 0, -1], ![1, 1, -2, 0]]

def raw1886step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 1, -2, 0]]

theorem canonical1886 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1886 = injectiveMoment H node2420 := by
  calc
    injectiveMoment H raw1886 = injectiveMoment H raw1886step0 := by
      have heq : raw1886step0 = (fun i j => raw1886 (permutation33 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1886 permutation33 permutation15
    _ = injectiveMoment H node2420 := by rfl

def raw1887 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![2, 1, -2, -1]]

def raw1887step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-1, 0, 0, 1], ![0, 1, 1, -2], ![3, -1, -1, -1]]

def raw1887step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 1, -1], ![0, 0, 2, -2], ![1, 1, -2, 0]]

theorem canonical1887 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1887 = injectiveMoment H node967 := by
  calc
    injectiveMoment H raw1887 = injectiveMoment H raw1887step0 := by
      have heq : raw1887step0 = raw1887.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1887).symm
    injectiveMoment H raw1887step0 = injectiveMoment H raw1887step1 := by
      have heq : raw1887step1 = (fun i j => raw1887step0 (permutation29 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1887step0 permutation29 permutation18
    _ = injectiveMoment H node967 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
