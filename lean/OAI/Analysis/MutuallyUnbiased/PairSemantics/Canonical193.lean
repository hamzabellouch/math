import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes9
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes10
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes14
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes15
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes17
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes18
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes19
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes21
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes27
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes39

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw6176 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 1, 0, 0], ![1, -1, 1, -1], ![1, 1, 0, -2]]

def raw6176step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 1, 0], ![0, 1, 1, -2], ![1, 1, -1, -1]]

theorem canonical6176 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6176 = injectiveMoment H node936 := by
  calc
    injectiveMoment H raw6176 = injectiveMoment H raw6176step0 := by
      have heq : raw6176step0 = (fun i j => raw6176 (permutation10 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6176 permutation10 permutation21
    _ = injectiveMoment H node936 := by rfl

def raw6177 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 1, 1, -1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 1, -2]]

def raw6177step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 0, 1, 0], ![0, 1, -1, 0], ![1, -1, 1, -1], ![1, 1, 0, -2]]

theorem canonical6177 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6177 = injectiveMoment H node2511 := by
  calc
    injectiveMoment H raw6177 = injectiveMoment H raw6177step0 := by
      have heq : raw6177step0 = (fun i j => raw6177 (permutation41 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6177 permutation41 permutation21
    _ = injectiveMoment H node2511 := by rfl

def raw6178 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 1, 1, -1], ![0, 1, -1, 0], ![1, -1, 1, -1], ![1, 0, 0, -1]]

def raw6178step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 0, 1, 0], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 1, -1, -1]]

theorem canonical6178 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6178 = injectiveMoment H node2512 := by
  calc
    injectiveMoment H raw6178 = injectiveMoment H raw6178step0 := by
      have heq : raw6178step0 = (fun i j => raw6178 (permutation43 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6178 permutation43 permutation21
    _ = injectiveMoment H node2512 := by rfl

def raw6179 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 1, 1, -1], ![0, 1, -1, 0], ![1, -1, 2, -2], ![1, 0, -1, 0]]

theorem canonical6179 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6179 = injectiveMoment H node2527 := by
  rfl

def raw6180 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 1, 1, -1], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 0, -1, 0]]

def raw6180step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 0, 1, 0], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 1, -1, -1]]

theorem canonical6180 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6180 = injectiveMoment H node2512 := by
  calc
    injectiveMoment H raw6180 = injectiveMoment H raw6180step0 := by
      have heq : raw6180step0 = (fun i j => raw6180 (permutation54 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6180 permutation54 permutation23
    _ = injectiveMoment H node2512 := by rfl

def raw6181 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 1, 1, -1], ![0, 1, 0, -1], ![1, -1, 2, -2], ![1, 0, -2, 1]]

theorem canonical6181 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6181 = injectiveMoment H node2528 := by
  rfl

def raw6182 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 1, 1, -1], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def raw6182step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 0, 1, 0], ![0, -1, 1, 0], ![1, 1, -1, -1], ![1, 1, 0, -2]]

theorem canonical6182 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6182 = injectiveMoment H node2510 := by
  calc
    injectiveMoment H raw6182 = injectiveMoment H raw6182step0 := by
      have heq : raw6182step0 = (fun i j => raw6182 (permutation49 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6182 permutation49 permutation17
    _ = injectiveMoment H node2510 := by rfl

def raw6183 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 1, 1, -1], ![1, -1, 1, -1], ![1, 1, -1, -1]]

theorem canonical6183 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6183 = injectiveMoment H node926 := by
  rfl

def raw6184 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 1, 1, -1], ![1, -1, 2, -2], ![1, 1, -2, 0]]

def raw6184step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![-1, 1, -1, 1], ![-1, 1, 2, -2], ![3, -1, -2, 0]]

def raw6184step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -1, 3, -2], ![1, -1, -1, 1], ![1, 1, -1, -1]]

theorem canonical6184 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6184 = injectiveMoment H node680 := by
  calc
    injectiveMoment H raw6184 = injectiveMoment H raw6184step0 := by
      have heq : raw6184step0 = raw6184.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6184).symm
    injectiveMoment H raw6184step0 = injectiveMoment H raw6184step1 := by
      have heq : raw6184step1 = (fun i j => raw6184step0 (permutation25 i) (permutation29 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6184step0 permutation25 permutation29
    _ = injectiveMoment H node680 := by rfl

def raw6185 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 1, 1, -1], ![1, 0, 1, -2], ![1, 0, -1, 0]]

def raw6185step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 1, 0], ![0, 1, 1, -2], ![1, 1, -1, -1]]

theorem canonical6185 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6185 = injectiveMoment H node936 := by
  calc
    injectiveMoment H raw6185 = injectiveMoment H raw6185step0 := by
      have heq : raw6185step0 = (fun i j => raw6185 (permutation14 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6185 permutation14 permutation17
    _ = injectiveMoment H node936 := by rfl

def raw6186 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 1, 1, -1], ![1, 0, 2, -3], ![1, 0, -2, 1]]

def raw6186step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 1, -2, 1], ![0, 1, 2, -3], ![1, -1, 1, -1]]

theorem canonical6186 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6186 = injectiveMoment H node984 := by
  calc
    injectiveMoment H raw6186 = injectiveMoment H raw6186step0 := by
      have heq : raw6186step0 = (fun i j => raw6186 (permutation14 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6186 permutation14 permutation15
    _ = injectiveMoment H node984 := by rfl

def raw6187 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 1, 2, -2], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw6187step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 1, 1, -3], ![1, -1, -2, 2], ![0, -1, 1, 0], ![-1, 1, 0, 0], ![-1, 0, 0, 1]]

def raw6187step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 1, 1, -3]]

theorem canonical6187 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6187 = injectiveMoment H node1768 := by
  calc
    injectiveMoment H raw6187 = injectiveMoment H raw6187step0 := by
      have heq : raw6187step0 = -raw6187 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6187).symm
    injectiveMoment H raw6187step0 = injectiveMoment H raw6187step1 := by
      have heq : raw6187step1 = (fun i j => raw6187step0 (permutation79 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6187step0 permutation79 permutation23
    _ = injectiveMoment H node1768 := by rfl

def raw6188 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 1, 2, -2], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 0, 0, -1]]

def raw6188step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 1, 1, -3], ![1, -1, -2, 2], ![0, -1, 0, 1], ![-1, 1, 1, -1], ![-1, 0, 0, 1]]

def raw6188step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 0, 1], ![0, 0, -1, 1], ![1, 1, -1, -1], ![1, 1, 1, -3]]

theorem canonical6188 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6188 = injectiveMoment H node1736 := by
  calc
    injectiveMoment H raw6188 = injectiveMoment H raw6188step0 := by
      have heq : raw6188step0 = -raw6188 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6188).symm
    injectiveMoment H raw6188step0 = injectiveMoment H raw6188step1 := by
      have heq : raw6188step1 = (fun i j => raw6188step0 (permutation67 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6188step0 permutation67 permutation23
    _ = injectiveMoment H node1736 := by rfl

def raw6189 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 1, 2, -2], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def raw6189step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 1, 1, -3], ![1, -1, -2, 2], ![0, -1, 0, 1], ![-1, 1, 0, 0], ![-1, 0, 1, 0]]

def raw6189step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 0, 1], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 1, 1, -3]]

theorem canonical6189 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6189 = injectiveMoment H node1739 := by
  calc
    injectiveMoment H raw6189 = injectiveMoment H raw6189step0 := by
      have heq : raw6189step0 = -raw6189 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6189).symm
    injectiveMoment H raw6189step0 = injectiveMoment H raw6189step1 := by
      have heq : raw6189step1 = (fun i j => raw6189step0 (permutation65 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6189step0 permutation65 permutation23
    _ = injectiveMoment H node1739 := by rfl

def raw6190 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 1, 2, -2], ![1, -1, 0, 0], ![1, 1, -1, -1]]

def raw6190step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![-1, 1, -1, 1], ![-1, 2, 0, -1], ![3, -2, 0, -1]]

def raw6190step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 1, -1, -1], ![1, -1, 1, -1], ![1, -2, 0, 1], ![-3, 2, 0, 1]]

def raw6190step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 1, -3, 2], ![0, 1, 1, -2], ![1, -1, 1, -1]]

theorem canonical6190 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6190 = injectiveMoment H node1123 := by
  calc
    injectiveMoment H raw6190 = injectiveMoment H raw6190step0 := by
      have heq : raw6190step0 = raw6190.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6190).symm
    injectiveMoment H raw6190step0 = injectiveMoment H raw6190step1 := by
      have heq : raw6190step1 = -raw6190step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6190step0).symm
    injectiveMoment H raw6190step1 = injectiveMoment H raw6190step2 := by
      have heq : raw6190step2 = (fun i j => raw6190step1 (permutation14 i) (permutation25 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6190step1 permutation14 permutation25
    _ = injectiveMoment H node1123 := by rfl

def raw6191 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 1, 2, -2], ![1, -1, 1, -1], ![1, 1, -2, 0]]

def raw6191step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![-1, 1, -1, 1], ![-1, 2, 1, -2], ![3, -2, -1, 0]]

def raw6191step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -1, 3, -2], ![1, -1, -1, 1], ![1, 1, -1, -1]]

theorem canonical6191 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6191 = injectiveMoment H node680 := by
  calc
    injectiveMoment H raw6191 = injectiveMoment H raw6191step0 := by
      have heq : raw6191step0 = raw6191.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6191).symm
    injectiveMoment H raw6191step0 = injectiveMoment H raw6191step1 := by
      have heq : raw6191step1 = (fun i j => raw6191step0 (permutation26 i) (permutation31 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6191step0 permutation26 permutation31
    _ = injectiveMoment H node680 := by rfl

def raw6192 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 1, 3, -3], ![0, 1, -2, 1], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw6192step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 1, 0, 0], ![0, 1, 0, -1], ![1, -1, 3, -3], ![1, 0, -2, 1]]

theorem canonical6192 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6192 = injectiveMoment H node2526 := by
  calc
    injectiveMoment H raw6192 = injectiveMoment H raw6192step0 := by
      have heq : raw6192step0 = (fun i j => raw6192 (permutation49 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6192 permutation49 permutation15
    _ = injectiveMoment H node2526 := by rfl

def raw6193 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 1, 3, -3], ![1, -1, -1, 1], ![1, 1, -1, -1]]

def raw6193step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 1, -1, 1], ![1, -1, 3, -3], ![1, 1, -1, -1]]

theorem canonical6193 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6193 = injectiveMoment H node925 := by
  calc
    injectiveMoment H raw6193 = injectiveMoment H raw6193step0 := by
      have heq : raw6193step0 = (fun i j => raw6193 (permutation11 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6193 permutation11 permutation15
    _ = injectiveMoment H node925 := by rfl

def raw6194 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 1, 3, -3], ![1, -1, 0, 0], ![1, 1, -2, 0]]

def raw6194step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![-1, 1, -1, 1], ![-1, 3, 0, -2], ![3, -3, 0, 0]]

def raw6194step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 1, -1, -1], ![1, -1, 1, -1], ![1, -3, 0, 2], ![-3, 3, 0, 0]]

def raw6194step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -3, 3], ![0, 2, 1, -3], ![1, -1, 1, -1]]

theorem canonical6194 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6194 = injectiveMoment H node1105 := by
  calc
    injectiveMoment H raw6194 = injectiveMoment H raw6194step0 := by
      have heq : raw6194step0 = raw6194.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6194).symm
    injectiveMoment H raw6194step0 = injectiveMoment H raw6194step1 := by
      have heq : raw6194step1 = -raw6194step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6194step0).symm
    injectiveMoment H raw6194step1 = injectiveMoment H raw6194step2 := by
      have heq : raw6194step2 = (fun i j => raw6194step1 (permutation14 i) (permutation25 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6194step1 permutation14 permutation25
    _ = injectiveMoment H node1105 := by rfl

def raw6195 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 2, -2, 1], ![1, -1, 0, 0], ![1, 0, 3, -4]]

def raw6195step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![-1, 2, -1, 0], ![-1, -2, 0, 3], ![3, 1, 0, -4]]

def raw6195step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![0, -1, -2, 3], ![0, 3, 1, -4], ![1, -1, -1, 1]]

theorem canonical6195 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6195 = injectiveMoment H node1157 := by
  calc
    injectiveMoment H raw6195 = injectiveMoment H raw6195step0 := by
      have heq : raw6195step0 = raw6195.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6195).symm
    injectiveMoment H raw6195step0 = injectiveMoment H raw6195step1 := by
      have heq : raw6195step1 = (fun i j => raw6195step0 (permutation18 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6195step0 permutation18 permutation21
    _ = injectiveMoment H node1157 := by rfl

def raw6196 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 2, -2, 1], ![1, -1, 3, -3], ![1, 0, 0, -1]]

def raw6196step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![-1, 2, -1, 0], ![-1, -2, 3, 0], ![3, 1, -3, -1]]

def raw6196step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 1, -1, -1], ![1, -2, 1, 0], ![1, 2, -3, 0], ![-3, -1, 3, 1]]

def raw6196step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, 1, -1], ![0, -2, 1, 1], ![0, 2, 1, -3], ![1, -1, -3, 3]]

theorem canonical6196 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6196 = injectiveMoment H node1358 := by
  calc
    injectiveMoment H raw6196 = injectiveMoment H raw6196step0 := by
      have heq : raw6196step0 = raw6196.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6196).symm
    injectiveMoment H raw6196step0 = injectiveMoment H raw6196step1 := by
      have heq : raw6196step1 = -raw6196step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6196step0).symm
    injectiveMoment H raw6196step1 = injectiveMoment H raw6196step2 := by
      have heq : raw6196step2 = (fun i j => raw6196step1 (permutation9 i) (permutation29 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6196step1 permutation9 permutation29
    _ = injectiveMoment H node1358 := by rfl

def raw6197 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 2, -1, 0], ![1, -1, 3, -3], ![1, 0, -1, 0]]

def raw6197step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![-1, 2, -1, 0], ![-1, -1, 3, -1], ![3, 0, -3, 0]]

def raw6197step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 3, -3], ![0, 2, -1, -1], ![1, -1, -1, 1]]

theorem canonical6197 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6197 = injectiveMoment H node980 := by
  calc
    injectiveMoment H raw6197 = injectiveMoment H raw6197step0 := by
      have heq : raw6197step0 = raw6197.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6197).symm
    injectiveMoment H raw6197step0 = injectiveMoment H raw6197step1 := by
      have heq : raw6197step1 = (fun i j => raw6197step0 (permutation26 i) (permutation29 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6197step0 permutation26 permutation29
    _ = injectiveMoment H node980 := by rfl

def raw6198 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 2, 0, -1], ![1, -1, 2, -2], ![1, 0, -1, 0]]

def raw6198step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![-1, 2, -1, 0], ![-1, 0, 2, -1], ![3, -1, -2, 0]]

def raw6198step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 3, -2], ![0, 2, -1, -1], ![1, -1, -1, 1]]

theorem canonical6198 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6198 = injectiveMoment H node1249 := by
  calc
    injectiveMoment H raw6198 = injectiveMoment H raw6198step0 := by
      have heq : raw6198step0 = raw6198.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6198).symm
    injectiveMoment H raw6198step0 = injectiveMoment H raw6198step1 := by
      have heq : raw6198step1 = (fun i j => raw6198step0 (permutation26 i) (permutation29 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6198step0 permutation26 permutation29
    _ = injectiveMoment H node1249 := by rfl

def raw6199 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 2, 0, -1], ![1, -1, 3, -3], ![1, 0, -2, 1]]

def raw6199step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![-1, 2, -1, 0], ![-1, 0, 3, -2], ![3, -1, -3, 1]]

def raw6199step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 2, -1, -1], ![1, -1, -1, 1], ![1, -1, 3, -3]]

theorem canonical6199 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6199 = injectiveMoment H node604 := by
  calc
    injectiveMoment H raw6199 = injectiveMoment H raw6199step0 := by
      have heq : raw6199step0 = raw6199.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6199).symm
    injectiveMoment H raw6199step0 = injectiveMoment H raw6199step1 := by
      have heq : raw6199step1 = (fun i j => raw6199step0 (permutation23 i) (permutation29 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6199step0 permutation23 permutation29
    _ = injectiveMoment H node604 := by rfl

def raw6200 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 2, 1, -2], ![1, -1, 2, -2], ![1, 0, -2, 1]]

def raw6200step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 1, 1, -3], ![1, -2, -1, 2], ![-1, 1, -2, 2], ![-1, 0, 2, -1]]

def raw6200step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -1, 2, -1], ![1, -1, -2, 2], ![1, 1, 1, -3]]

theorem canonical6200 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6200 = injectiveMoment H node679 := by
  calc
    injectiveMoment H raw6200 = injectiveMoment H raw6200step0 := by
      have heq : raw6200step0 = -raw6200 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6200).symm
    injectiveMoment H raw6200step0 = injectiveMoment H raw6200step1 := by
      have heq : raw6200step1 = (fun i j => raw6200step0 (permutation20 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6200step0 permutation20 permutation15
    _ = injectiveMoment H node679 := by rfl

def raw6201 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 0, 1], ![0, 2, 2, -4], ![1, 0, -1, 0]]

def raw6201step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, -1, 2, 0], ![-1, 0, 2, -1], ![3, 1, -4, 0]]

def raw6201step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 0, -1], ![1, 1, -2, 0], ![1, 0, -2, 1], ![-3, -1, 4, 0]]

def raw6201step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, -1, 1, 0], ![0, 1, 1, -2], ![1, 0, 1, -2]]

theorem canonical6201 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6201 = injectiveMoment H node1168 := by
  calc
    injectiveMoment H raw6201 = injectiveMoment H raw6201step0 := by
      have heq : raw6201step0 = raw6201.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6201).symm
    injectiveMoment H raw6201step0 = injectiveMoment H raw6201step1 := by
      have heq : raw6201step1 = -raw6201step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6201step0).symm
    injectiveMoment H raw6201step1 = injectiveMoment H raw6201step2 := by
      have heq : raw6201step2 = (fun i j => raw6201step1 (permutation28 i) (permutation19 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6201step1 permutation28 permutation19
    _ = injectiveMoment H node1168 := by rfl

def raw6202 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 1, 0], ![-1, 1, 0, 0], ![1, 0, 0, -1], ![1, 1, 0, -2]]

def raw6202step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 1, 0], ![0, 1, 0, -1], ![0, 1, 1, -2], ![1, 0, -1, 0]]

theorem canonical6202 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6202 = injectiveMoment H node2536 := by
  calc
    injectiveMoment H raw6202 = injectiveMoment H raw6202step0 := by
      have heq : raw6202step0 = (fun i j => raw6202 (permutation42 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6202 permutation42 permutation21
    _ = injectiveMoment H node2536 := by rfl

def raw6203 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 1, 0], ![-1, 1, 1, -1], ![1, 0, 0, -1], ![1, 1, -1, -1]]

def raw6203step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 0, 1, 0], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 1, -1, -1]]

theorem canonical6203 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6203 = injectiveMoment H node2512 := by
  calc
    injectiveMoment H raw6203 = injectiveMoment H raw6203step0 := by
      have heq : raw6203step0 = (fun i j => raw6203 (permutation35 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6203 permutation35 permutation15
    _ = injectiveMoment H node2512 := by rfl

def raw6204 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, 0, 0, -1]]

theorem canonical6204 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6204 = injectiveMoment H node2532 := by
  rfl

def raw6205 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, 0, -1, 0]]

theorem canonical6205 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6205 = injectiveMoment H node2533 := by
  rfl

def raw6206 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 1, 0], ![0, 1, -1, 0], ![0, 0, 1, -1], ![1, 1, 0, -2]]

def raw6206step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 1, 0, -2]]

theorem canonical6206 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6206 = injectiveMoment H node2530 := by
  calc
    injectiveMoment H raw6206 = injectiveMoment H raw6206step0 := by
      have heq : raw6206step0 = (fun i j => raw6206 (permutation35 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6206 permutation35 permutation9
    _ = injectiveMoment H node2530 := by rfl

def raw6207 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 1, 0], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, 0, -1, 0]]

theorem canonical6207 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6207 = injectiveMoment H node2535 := by
  rfl

end MUB6.Certificate.PairSemantics

end OAI
