import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes12
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes15
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes17
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes19
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes25
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes26
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes40
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes41

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw2016 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, 0, 3, -4]]

theorem canonical2016 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2016 = injectiveMoment H node1714 := by
  rfl

def raw2017 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 2, -3]]

def raw2017step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 1, 0, -3], ![0, -1, 1, 0], ![0, -1, 1, 0], ![-1, 1, 0, 0], ![-1, 0, -2, 3]]

def raw2017step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 2, 1, -3], ![1, 0, -1, 0], ![1, 0, -1, 0]]

theorem canonical2017 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2017 = injectiveMoment H node1644 := by
  calc
    injectiveMoment H raw2017 = injectiveMoment H raw2017step0 := by
      have heq : raw2017step0 = -raw2017 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2017).symm
    injectiveMoment H raw2017step0 = injectiveMoment H raw2017step1 := by
      have heq : raw2017step1 = (fun i j => raw2017step0 (permutation145 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2017step0 permutation145 permutation21
    _ = injectiveMoment H node1644 := by rfl

def raw2018 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 1, -1], ![1, 0, 1, -2]]

theorem canonical2018 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2018 = injectiveMoment H node1715 := by
  rfl

def raw2019 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 2, -2], ![1, 0, 0, -1]]

theorem canonical2019 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2019 = injectiveMoment H node1716 := by
  rfl

def raw2020 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 3, -3], ![1, 0, -1, 0]]

theorem canonical2020 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2020 = injectiveMoment H node1717 := by
  rfl

def raw2021 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, -1, 3, -3]]

def raw2021step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 3, -3], ![1, 0, -1, 0]]

theorem canonical2021 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2021 = injectiveMoment H node1717 := by
  calc
    injectiveMoment H raw2021 = injectiveMoment H raw2021step0 := by
      have heq : raw2021step0 = (fun i j => raw2021 (permutation34 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2021 permutation34 permutation9
    _ = injectiveMoment H node1717 := by rfl

def raw2022 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, -1, 2, -2]]

def raw2022step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 2, -2], ![1, 0, 0, -1]]

theorem canonical2022 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2022 = injectiveMoment H node1716 := by
  calc
    injectiveMoment H raw2022 = injectiveMoment H raw2022step0 := by
      have heq : raw2022step0 = (fun i j => raw2022 (permutation34 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2022 permutation34 permutation9
    _ = injectiveMoment H node1716 := by rfl

def raw2023 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, -1, 2, -3]]

def raw2023step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-1, 1, 1, -1], ![0, -1, -1, 2], ![3, 0, 0, -3]]

def raw2023step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 0, 3, -3], ![1, 1, -1, -1]]

theorem canonical2023 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2023 = injectiveMoment H node1028 := by
  calc
    injectiveMoment H raw2023 = injectiveMoment H raw2023step0 := by
      have heq : raw2023step0 = raw2023.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2023).symm
    injectiveMoment H raw2023step0 = injectiveMoment H raw2023step1 := by
      have heq : raw2023step1 = (fun i j => raw2023step0 (permutation22 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2023step0 permutation22 permutation17
    _ = injectiveMoment H node1028 := by rfl

def raw2024 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 0, 2, -3]]

def raw2024step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 1, 0, -3], ![0, -1, 1, 0], ![0, -1, 0, 1], ![-1, 1, 1, -1], ![-1, 0, -2, 3]]

def raw2024step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, -1, 1, -1], ![1, 0, -1, 0]]

theorem canonical2024 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2024 = injectiveMoment H node1671 := by
  calc
    injectiveMoment H raw2024 = injectiveMoment H raw2024step0 := by
      have heq : raw2024step0 = -raw2024 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2024).symm
    injectiveMoment H raw2024step0 = injectiveMoment H raw2024step1 := by
      have heq : raw2024step1 = (fun i j => raw2024step0 (permutation140 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2024step0 permutation140 permutation21
    _ = injectiveMoment H node1671 := by rfl

def raw2025 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 1, -2]]

def raw2025step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 1, 0, -3], ![0, -1, 1, 0], ![0, -1, 0, 1], ![-1, 1, 0, 0], ![-1, 0, -1, 2]]

def raw2025step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, 0, -1, 0]]

theorem canonical2025 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2025 = injectiveMoment H node2580 := by
  calc
    injectiveMoment H raw2025 = injectiveMoment H raw2025step0 := by
      have heq : raw2025step0 = -raw2025 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2025).symm
    injectiveMoment H raw2025step0 = injectiveMoment H raw2025step1 := by
      have heq : raw2025step1 = (fun i j => raw2025step0 (permutation149 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2025step0 permutation149 permutation21
    _ = injectiveMoment H node2580 := by rfl

def raw2026 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 0, 0, -1]]

def raw2026step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 1, 0, -3], ![0, -1, 1, 0], ![0, -1, 0, 1], ![-1, 1, -1, 1], ![-1, 0, 0, 1]]

def raw2026step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, 0, -1, 0]]

theorem canonical2026 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2026 = injectiveMoment H node2627 := by
  calc
    injectiveMoment H raw2026 = injectiveMoment H raw2026step0 := by
      have heq : raw2026step0 = -raw2026 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2026).symm
    injectiveMoment H raw2026step0 = injectiveMoment H raw2026step1 := by
      have heq : raw2026step1 = (fun i j => raw2026step0 (permutation126 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2026step0 permutation126 permutation21
    _ = injectiveMoment H node2627 := by rfl

def raw2027 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 2, -2], ![1, 0, -1, 0]]

theorem canonical2027 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2027 = injectiveMoment H node1718 := by
  rfl

def raw2028 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, -1, 2, -2]]

def raw2028step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 2, -2], ![1, 0, -1, 0]]

theorem canonical2028 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2028 = injectiveMoment H node1718 := by
  calc
    injectiveMoment H raw2028 = injectiveMoment H raw2028step0 := by
      have heq : raw2028step0 = (fun i j => raw2028 (permutation34 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2028 permutation34 permutation9
    _ = injectiveMoment H node1718 := by rfl

def raw2029 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, -1, 1, -2]]

def raw2029step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-1, 1, 1, -1], ![0, -1, 0, 1], ![3, 0, -1, -2]]

def raw2029step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![1, -1, -1, 1], ![0, 1, 0, -1], ![-3, 0, 1, 2]]

def raw2029step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -2, 2], ![0, 1, -1, 0], ![1, 0, 2, -3]]

theorem canonical2029 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2029 = injectiveMoment H node1109 := by
  calc
    injectiveMoment H raw2029 = injectiveMoment H raw2029step0 := by
      have heq : raw2029step0 = raw2029.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2029).symm
    injectiveMoment H raw2029step0 = injectiveMoment H raw2029step1 := by
      have heq : raw2029step1 = -raw2029step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2029step0).symm
    injectiveMoment H raw2029step1 = injectiveMoment H raw2029step2 := by
      have heq : raw2029step2 = (fun i j => raw2029step1 (permutation15 i) (permutation24 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2029step1 permutation15 permutation24
    _ = injectiveMoment H node1109 := by rfl

def raw2030 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw2030step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 1, 0, -3], ![0, -1, 1, 0], ![0, -1, -1, 2], ![-1, 1, 0, 0], ![-1, 0, 0, 1]]

def raw2030step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, -1, 0, 0]]

theorem canonical2030 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2030 = injectiveMoment H node2605 := by
  calc
    injectiveMoment H raw2030 = injectiveMoment H raw2030step0 := by
      have heq : raw2030step0 = -raw2030 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2030).symm
    injectiveMoment H raw2030step0 = injectiveMoment H raw2030step1 := by
      have heq : raw2030step1 = (fun i j => raw2030step0 (permutation102 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2030step0 permutation102 permutation23
    _ = injectiveMoment H node2605 := by rfl

def raw2031 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, -1, 1, -1], ![1, 0, -1, 0]]

theorem canonical2031 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2031 = injectiveMoment H node1719 := by
  rfl

def raw2032 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, 0, -1, 0], ![1, -1, 1, -1]]

def raw2032step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, -1, 1, -1], ![1, 0, -1, 0]]

theorem canonical2032 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2032 = injectiveMoment H node1719 := by
  calc
    injectiveMoment H raw2032 = injectiveMoment H raw2032step0 := by
      have heq : raw2032step0 = (fun i j => raw2032 (permutation34 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2032 permutation34 permutation9
    _ = injectiveMoment H node1719 := by rfl

def raw2033 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -1, 0], ![0, 1, 1, -2], ![2, -1, 0, -1]]

def raw2033step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 1, 0, -3], ![0, -1, 1, 0], ![0, -1, -1, 2], ![-2, 1, 0, 1]]

def raw2033step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, -2, 1], ![0, 1, 2, -3], ![1, -1, 0, 0]]

theorem canonical2033 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2033 = injectiveMoment H node1079 := by
  calc
    injectiveMoment H raw2033 = injectiveMoment H raw2033step0 := by
      have heq : raw2033step0 = -raw2033 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2033).symm
    injectiveMoment H raw2033step0 = injectiveMoment H raw2033step1 := by
      have heq : raw2033step1 = (fun i j => raw2033step0 (permutation25 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2033step0 permutation25 permutation23
    _ = injectiveMoment H node1079 := by rfl

def raw2034 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, -1, -1, 1], ![1, 0, 0, -1]]

def raw2034step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 1, 0, -3], ![0, -1, 1, 0], ![0, -1, -2, 3], ![-1, 1, 1, -1], ![-1, 0, 0, 1]]

def raw2034step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, -1, 1], ![0, 1, 2, -3], ![1, -1, 0, 0], ![1, 1, -1, -1]]

theorem canonical2034 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2034 = injectiveMoment H node1669 := by
  calc
    injectiveMoment H raw2034 = injectiveMoment H raw2034step0 := by
      have heq : raw2034step0 = -raw2034 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2034).symm
    injectiveMoment H raw2034step0 = injectiveMoment H raw2034step1 := by
      have heq : raw2034step1 = (fun i j => raw2034step0 (permutation98 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2034step0 permutation98 permutation23
    _ = injectiveMoment H node1669 := by rfl

def raw2035 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, -1, 0, 0], ![1, 0, -1, 0]]

theorem canonical2035 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2035 = injectiveMoment H node1720 := by
  rfl

def raw2036 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, -1, 1, -1], ![1, 0, -2, 1]]

theorem canonical2036 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2036 = injectiveMoment H node1721 := by
  rfl

def raw2037 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, 0, -1, 0], ![1, -1, 0, 0]]

def raw2037step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, -1, 0, 0], ![1, 0, -1, 0]]

theorem canonical2037 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2037 = injectiveMoment H node1720 := by
  calc
    injectiveMoment H raw2037 = injectiveMoment H raw2037step0 := by
      have heq : raw2037step0 = (fun i j => raw2037 (permutation34 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2037 permutation34 permutation9
    _ = injectiveMoment H node1720 := by rfl

def raw2038 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -1, 0], ![0, 1, 2, -3], ![2, -1, -1, 0]]

def raw2038step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-1, 1, 1, -1], ![0, -1, 2, -1], ![3, 0, -3, 0]]

def raw2038step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 3, -3], ![0, 2, -2, 0], ![1, -1, -1, 1]]

theorem canonical2038 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2038 = injectiveMoment H node1066 := by
  calc
    injectiveMoment H raw2038 = injectiveMoment H raw2038step0 := by
      have heq : raw2038step0 = raw2038.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2038).symm
    injectiveMoment H raw2038step0 = injectiveMoment H raw2038step1 := by
      have heq : raw2038step1 = (fun i j => raw2038step0 (permutation25 i) (permutation19 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2038step0 permutation25 permutation19
    _ = injectiveMoment H node1066 := by rfl

def raw2039 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, -1, -1, 1], ![1, 0, -1, 0]]

theorem canonical2039 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2039 = injectiveMoment H node1722 := by
  rfl

def raw2040 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, -1, 0, 0], ![1, 0, -2, 1]]

theorem canonical2040 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2040 = injectiveMoment H node1723 := by
  rfl

def raw2041 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, 0, -1, 0], ![1, -1, -1, 1]]

def raw2041step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, -1, -1, 1], ![1, 0, -1, 0]]

theorem canonical2041 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2041 = injectiveMoment H node1722 := by
  calc
    injectiveMoment H raw2041 = injectiveMoment H raw2041step0 := by
      have heq : raw2041step0 = (fun i j => raw2041 (permutation34 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2041 permutation34 permutation9
    _ = injectiveMoment H node1722 := by rfl

def raw2042 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, 1, 2, -4]]

def raw2042step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 1, -1, 1], ![0, -1, -1, 2], ![3, 0, 1, -4]]

def raw2042step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, -2, 1], ![0, 1, 3, -4], ![1, -1, -1, 1]]

theorem canonical2042 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2042 = injectiveMoment H node1080 := by
  calc
    injectiveMoment H raw2042 = injectiveMoment H raw2042step0 := by
      have heq : raw2042step0 = raw2042.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2042).symm
    injectiveMoment H raw2042step0 = injectiveMoment H raw2042step1 := by
      have heq : raw2042step1 = (fun i j => raw2042step0 (permutation22 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2042step0 permutation22 permutation17
    _ = injectiveMoment H node1080 := by rfl

def raw2043 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 1, 1, -3]]

def raw2043step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 1, -1, 1], ![0, -1, 0, 1], ![3, 0, 0, -3]]

def raw2043step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![1, -1, 1, -1], ![0, 1, 0, -1], ![-3, 0, 0, 3]]

def raw2043step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, 3, -3], ![0, 1, -1, 0], ![1, -1, -1, 1]]

theorem canonical2043 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2043 = injectiveMoment H node1268 := by
  calc
    injectiveMoment H raw2043 = injectiveMoment H raw2043step0 := by
      have heq : raw2043step0 = raw2043.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2043).symm
    injectiveMoment H raw2043step0 = injectiveMoment H raw2043step1 := by
      have heq : raw2043step1 = -raw2043step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2043step0).symm
    injectiveMoment H raw2043step1 = injectiveMoment H raw2043step2 := by
      have heq : raw2043step2 = (fun i j => raw2043step1 (permutation14 i) (permutation24 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2043step1 permutation14 permutation24
    _ = injectiveMoment H node1268 := by rfl

def raw2044 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -1, 0], ![1, -1, 1, -1], ![1, 1, 0, -2]]

def raw2044step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 1, 0, -3], ![0, -1, 1, 0], ![-1, 1, -1, 1], ![-1, -1, 0, 2]]

def raw2044step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, -1, 2], ![0, 2, 1, -3], ![1, 0, -1, 0]]

theorem canonical2044 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2044 = injectiveMoment H node1099 := by
  calc
    injectiveMoment H raw2044 = injectiveMoment H raw2044step0 := by
      have heq : raw2044step0 = -raw2044 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2044).symm
    injectiveMoment H raw2044step0 = injectiveMoment H raw2044step1 := by
      have heq : raw2044step1 = (fun i j => raw2044step0 (permutation25 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2044step0 permutation25 permutation21
    _ = injectiveMoment H node1099 := by rfl

def raw2045 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -1, 0], ![1, -1, 2, -2], ![1, 1, -1, -1]]

def raw2045step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 1, -1, 1], ![0, -1, 2, -1], ![3, 0, -2, -1]]

def raw2045step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 3, -2], ![0, 1, -2, 1], ![1, 1, -1, -1]]

theorem canonical2045 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2045 = injectiveMoment H node1013 := by
  calc
    injectiveMoment H raw2045 = injectiveMoment H raw2045step0 := by
      have heq : raw2045step0 = raw2045.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2045).symm
    injectiveMoment H raw2045step0 = injectiveMoment H raw2045step1 := by
      have heq : raw2045step1 = (fun i j => raw2045step0 (permutation25 i) (permutation19 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2045step0 permutation25 permutation19
    _ = injectiveMoment H node1013 := by rfl

def raw2046 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -1, 0], ![1, -1, 3, -3], ![1, 1, -2, 0]]

def raw2046step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 1, -1, 1], ![0, -1, 3, -2], ![3, 0, -3, 0]]

def raw2046step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 3, -3], ![0, 1, -2, 1], ![1, 1, -1, -1]]

theorem canonical2046 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2046 = injectiveMoment H node809 := by
  calc
    injectiveMoment H raw2046 = injectiveMoment H raw2046step0 := by
      have heq : raw2046step0 = raw2046.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2046).symm
    injectiveMoment H raw2046step0 = injectiveMoment H raw2046step1 := by
      have heq : raw2046step1 = (fun i j => raw2046step0 (permutation25 i) (permutation19 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2046step0 permutation25 permutation19
    _ = injectiveMoment H node809 := by rfl

def raw2047 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -1, 0], ![1, 0, -2, 1], ![1, 0, 3, -4]]

def raw2047step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 1, -2, 1], ![0, 1, 3, -4], ![1, 0, -1, 0]]

theorem canonical2047 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2047 = injectiveMoment H node817 := by
  calc
    injectiveMoment H raw2047 = injectiveMoment H raw2047step0 := by
      have heq : raw2047step0 = (fun i j => raw2047 (permutation12 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2047 permutation12 permutation15
    _ = injectiveMoment H node817 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
