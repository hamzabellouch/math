import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes0
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes1
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes2
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes3
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes4
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes11
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes12
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes14
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes18
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes41
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes42

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw7008 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, 0, 1, -1], ![0, 0, 2, -2], ![1, 0, 0, -1]]

def raw7008step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1]]

theorem canonical7008 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7008 = injectiveMoment H node254 := by
  calc
    injectiveMoment H raw7008 = injectiveMoment H raw7008step0 := by
      have hz : ∀ i, raw7008 i (permutation15 0) = 0 := by decide +kernel
      have heq : raw7008step0 = (fun i j => raw7008 i (permutation15 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw7008 permutation15 hz
    _ = injectiveMoment H node254 := by rfl

def raw7009 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -2, 2, -1]]

theorem canonical7009 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7009 = injectiveMoment H node2692 := by
  rfl

def raw7010 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 1, -2], ![1, -2, 1, 0]]

theorem canonical7010 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7010 = injectiveMoment H node2693 := by
  rfl

def raw7011 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, 0, 1, -1], ![0, 1, 1, -2], ![0, 1, 0, -1], ![1, -2, 1, 0]]

def raw7011step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 1, -2], ![1, -2, 1, 0]]

theorem canonical7011 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7011 = injectiveMoment H node2693 := by
  calc
    injectiveMoment H raw7011 = injectiveMoment H raw7011step0 := by
      have heq : raw7011step0 = (fun i j => raw7011 (permutation35 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7011 permutation35 permutation9
    _ = injectiveMoment H node2693 := by rfl

def raw7012 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, -1, 1, -1]]

theorem canonical7012 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7012 = injectiveMoment H node1176 := by
  rfl

def raw7013 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, 0, 1, -1], ![0, 1, 2, -3], ![1, -1, 0, 0]]

def raw7013step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, 1, -1], ![-3, 1, 2, 0], ![4, -1, -3, 0]]

def raw7013step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, -1, 1, 0], ![0, 1, 0, -1], ![1, 0, 2, -3]]

theorem canonical7013 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7013 = injectiveMoment H node1167 := by
  calc
    injectiveMoment H raw7013 = injectiveMoment H raw7013step0 := by
      have heq : raw7013step0 = raw7013.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7013).symm
    injectiveMoment H raw7013step0 = injectiveMoment H raw7013step1 := by
      have heq : raw7013step1 = (fun i j => raw7013step0 (permutation29 i) (permutation20 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7013step0 permutation29 permutation20
    _ = injectiveMoment H node1167 := by rfl

def raw7014 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -2, 2, -1]]

def raw7014step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, 2, -2], ![-3, 1, 0, 2], ![4, -1, -2, -1]]

def raw7014step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, 0, 2, -3]]

theorem canonical7014 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7014 = injectiveMoment H node768 := by
  calc
    injectiveMoment H raw7014 = injectiveMoment H raw7014step0 := by
      have heq : raw7014step0 = raw7014.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7014).symm
    injectiveMoment H raw7014step0 = injectiveMoment H raw7014step1 := by
      have heq : raw7014step1 = (fun i j => raw7014step0 (permutation27 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7014step0 permutation27 permutation18
    _ = injectiveMoment H node768 := by rfl

def raw7015 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, 0, 1, -1], ![0, 2, 1, -3], ![1, -2, 1, 0]]

def raw7015step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, 2, -2], ![-3, 1, 1, 1], ![4, -1, -3, 0]]

def raw7015step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 0, -1], ![0, 0, -2, 2], ![3, -1, -1, -1], ![-4, 1, 3, 0]]

def raw7015step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 0, 1], ![0, 2, -2, 0], ![1, 0, 3, -4]]

theorem canonical7015 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7015 = injectiveMoment H node935 := by
  calc
    injectiveMoment H raw7015 = injectiveMoment H raw7015step0 := by
      have heq : raw7015step0 = raw7015.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7015).symm
    injectiveMoment H raw7015step0 = injectiveMoment H raw7015step1 := by
      have heq : raw7015step1 = -raw7015step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7015step0).symm
    injectiveMoment H raw7015step1 = injectiveMoment H raw7015step2 := by
      have heq : raw7015step2 = (fun i j => raw7015step1 (permutation21 i) (permutation20 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7015step1 permutation21 permutation20
    _ = injectiveMoment H node935 := by rfl

def raw7016 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, 0, 1, -1], ![1, 0, 2, -3]]

def raw7016step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 1, -1], ![1, 2, -3]]

theorem canonical7016 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7016 = injectiveMoment H node51 := by
  calc
    injectiveMoment H raw7016 = injectiveMoment H raw7016step0 := by
      have hz : ∀ i, raw7016 i (permutation15 0) = 0 := by decide +kernel
      have heq : raw7016step0 = (fun i j => raw7016 i (permutation15 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw7016 permutation15 hz
    _ = injectiveMoment H node51 := by rfl

def raw7017 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, 0, 2, -2], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -2, 1, 0]]

theorem canonical7017 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7017 = injectiveMoment H node2694 := by
  rfl

def raw7018 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, -1, 1, -1]]

theorem canonical7018 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7018 = injectiveMoment H node1177 := by
  rfl

def raw7019 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, 0, 2, -2], ![0, 1, 1, -2], ![1, -1, 0, 0]]

theorem canonical7019 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7019 = injectiveMoment H node1178 := by
  rfl

def raw7020 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, 0, 2, -2], ![0, 2, 0, -2], ![1, -2, 1, 0]]

theorem canonical7020 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7020 = injectiveMoment H node1180 := by
  rfl

def raw7021 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, 0, 2, -2], ![1, 0, 1, -2]]

def raw7021step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 2, -2], ![1, 1, -2]]

theorem canonical7021 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7021 = injectiveMoment H node52 := by
  calc
    injectiveMoment H raw7021 = injectiveMoment H raw7021step0 := by
      have hz : ∀ i, raw7021 i (permutation15 0) = 0 := by decide +kernel
      have heq : raw7021step0 = (fun i j => raw7021 i (permutation15 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw7021 permutation15 hz
    _ = injectiveMoment H node52 := by rfl

def raw7022 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, 0, 3, -3], ![1, 0, 0, -1]]

def raw7022step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 3, -3], ![1, 0, -1]]

theorem canonical7022 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7022 = injectiveMoment H node53 := by
  calc
    injectiveMoment H raw7022 = injectiveMoment H raw7022step0 := by
      have hz : ∀ i, raw7022 i (permutation15 0) = 0 := by decide +kernel
      have heq : raw7022step0 = (fun i j => raw7022 i (permutation15 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw7022 permutation15 hz
    _ = injectiveMoment H node53 := by rfl

def raw7023 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -2, 3, -2]]

def raw7023step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 1, 1, -2], ![-3, 0, 0, 3], ![4, -1, -1, -2]]

def raw7023step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 1, -1], ![0, 0, 3, -3], ![1, 1, -2, 0]]

theorem canonical7023 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7023 = injectiveMoment H node908 := by
  calc
    injectiveMoment H raw7023 = injectiveMoment H raw7023step0 := by
      have heq : raw7023step0 = raw7023.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7023).symm
    injectiveMoment H raw7023step0 = injectiveMoment H raw7023step1 := by
      have heq : raw7023step1 = (fun i j => raw7023step0 (permutation28 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7023step0 permutation28 permutation18
    _ = injectiveMoment H node908 := by rfl

def raw7024 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, 1, 0, -1], ![0, 1, 1, -2], ![1, -2, 2, -1]]

def raw7024step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 1, 1, -2], ![-3, 0, 1, 2], ![4, -1, -2, -1]]

def raw7024step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 1, -1], ![0, 1, 2, -3], ![1, 1, -2, 0]]

theorem canonical7024 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7024 = injectiveMoment H node767 := by
  calc
    injectiveMoment H raw7024 = injectiveMoment H raw7024step0 := by
      have heq : raw7024step0 = raw7024.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7024).symm
    injectiveMoment H raw7024step0 = injectiveMoment H raw7024step1 := by
      have heq : raw7024step1 = (fun i j => raw7024step0 (permutation28 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7024step0 permutation28 permutation18
    _ = injectiveMoment H node767 := by rfl

def raw7025 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, 1, 0, -1], ![0, 1, 2, -3], ![1, -2, 1, 0]]

theorem canonical7025 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7025 = injectiveMoment H node1185 := by
  rfl

def raw7026 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, 1, 0, -1], ![1, -1, 3, -3]]

def raw7026step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 1, -1], ![-3, 0, 3], ![4, -1, -3]]

def raw7026step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 1, -1], ![0, 3, -3], ![1, -1, 0]]

theorem canonical7026 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7026 = injectiveMoment H node255 := by
  calc
    injectiveMoment H raw7026 = injectiveMoment H raw7026step0 := by
      have heq : raw7026step0 = raw7026.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7026).symm
    injectiveMoment H raw7026step0 = injectiveMoment H raw7026step1 := by
      have heq : raw7026step1 = (fun i j => raw7026step0 (permutation28 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7026step0 permutation28 permutation6
    _ = injectiveMoment H node255 := by rfl

def raw7027 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, 1, 1, -2], ![-1, 1, 2, -2], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def raw7027step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![-1, 1, 2, -2], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, -1, 0, 0]]

theorem canonical7027 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7027 = injectiveMoment H node2680 := by
  calc
    injectiveMoment H raw7027 = injectiveMoment H raw7027step0 := by
      have heq : raw7027step0 = (fun i j => raw7027 (permutation39 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7027 permutation39 permutation9
    _ = injectiveMoment H node2680 := by rfl

def raw7028 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, 1, 1, -2], ![0, 0, 2, -2], ![1, -1, 0, 0]]

def raw7028step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, 0, 2, -2], ![0, 1, 1, -2], ![1, -1, 0, 0]]

theorem canonical7028 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7028 = injectiveMoment H node1178 := by
  calc
    injectiveMoment H raw7028 = injectiveMoment H raw7028step0 := by
      have heq : raw7028step0 = (fun i j => raw7028 (permutation11 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7028 permutation11 permutation9
    _ = injectiveMoment H node1178 := by rfl

def raw7029 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, 1, 1, -2], ![0, 1, 0, -1], ![1, -2, 2, -1]]

def raw7029step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 1, 1, -2], ![-3, 1, 0, 2], ![4, -2, -1, -1]]

def raw7029step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 1, -1], ![0, 1, 2, -3], ![1, 1, -2, 0]]

theorem canonical7029 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7029 = injectiveMoment H node767 := by
  calc
    injectiveMoment H raw7029 = injectiveMoment H raw7029step0 := by
      have heq : raw7029step0 = raw7029.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7029).symm
    injectiveMoment H raw7029step0 = injectiveMoment H raw7029step1 := by
      have heq : raw7029step1 = (fun i j => raw7029step0 (permutation28 i) (permutation24 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7029step0 permutation28 permutation24
    _ = injectiveMoment H node767 := by rfl

def raw7030 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, 1, 1, -2], ![0, 1, 1, -2], ![0, -1, 1, 0], ![1, -1, 0, 0]]

def raw7030step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, -1, 1, 0], ![0, 1, 1, -2], ![0, 1, 1, -2], ![1, -1, 0, 0]]

theorem canonical7030 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7030 = injectiveMoment H node2688 := by
  calc
    injectiveMoment H raw7030 = injectiveMoment H raw7030step0 := by
      have heq : raw7030step0 = (fun i j => raw7030 (permutation45 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7030 permutation45 permutation9
    _ = injectiveMoment H node2688 := by rfl

def raw7031 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, 1, 1, -2], ![0, 1, 1, -2], ![1, -2, 1, 0]]

theorem canonical7031 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7031 = injectiveMoment H node1186 := by
  rfl

def raw7032 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, 1, 1, -2], ![0, 1, 1, -2], ![1, -1, 0, 0], ![0, -1, 1, 0]]

def raw7032step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, -1, 1, 0], ![0, 1, 1, -2], ![0, 1, 1, -2], ![1, -1, 0, 0]]

theorem canonical7032 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7032 = injectiveMoment H node2688 := by
  calc
    injectiveMoment H raw7032 = injectiveMoment H raw7032step0 := by
      have heq : raw7032step0 = (fun i j => raw7032 (permutation51 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7032 permutation51 permutation9
    _ = injectiveMoment H node2688 := by rfl

def raw7033 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, 1, 1, -2], ![1, -1, 2, -2]]

def raw7033step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 1, -1], ![-3, 1, 2], ![4, -2, -2]]

def raw7033step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![1, -1, 0], ![1, 2, -3]]

theorem canonical7033 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7033 = injectiveMoment H node149 := by
  calc
    injectiveMoment H raw7033 = injectiveMoment H raw7033step0 := by
      have heq : raw7033step0 = raw7033.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7033).symm
    injectiveMoment H raw7033step0 = injectiveMoment H raw7033step1 := by
      have heq : raw7033step1 = (fun i j => raw7033step0 (permutation27 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7033step0 permutation27 permutation6
    _ = injectiveMoment H node149 := by rfl

def raw7034 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, 1, 2, -3], ![0, 1, 0, -1], ![1, -2, 1, 0]]

def raw7034step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, 1, 0, -1], ![0, 1, 2, -3], ![1, -2, 1, 0]]

theorem canonical7034 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7034 = injectiveMoment H node1185 := by
  calc
    injectiveMoment H raw7034 = injectiveMoment H raw7034step0 := by
      have heq : raw7034step0 = (fun i j => raw7034 (permutation11 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7034 permutation11 permutation9
    _ = injectiveMoment H node1185 := by rfl

def raw7035 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, 1, 2, -3], ![1, -1, 1, -1]]

def raw7035step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 1, -1], ![-3, 2, 1], ![4, -3, -1]]

def raw7035step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 1, 0], ![1, 0, -1], ![1, 2, -3]]

theorem canonical7035 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7035 = injectiveMoment H node243 := by
  calc
    injectiveMoment H raw7035 = injectiveMoment H raw7035step0 := by
      have heq : raw7035step0 = raw7035.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7035).symm
    injectiveMoment H raw7035step0 = injectiveMoment H raw7035step1 := by
      have heq : raw7035step1 = (fun i j => raw7035step0 (permutation29 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7035step0 permutation29 permutation8
    _ = injectiveMoment H node243 := by rfl

def raw7036 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, 1, 3, -4], ![1, -1, 0, 0]]

def raw7036step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 1, -1], ![-3, 3, 0], ![4, -4, 0]]

def raw7036step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -3, 3], ![0, 4, -4], ![1, -1, 0]]

theorem canonical7036 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7036 = injectiveMoment H node290 := by
  calc
    injectiveMoment H raw7036 = injectiveMoment H raw7036step0 := by
      have heq : raw7036step0 = raw7036.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7036).symm
    injectiveMoment H raw7036step0 = injectiveMoment H raw7036step1 := by
      have heq : raw7036step1 = (fun i j => raw7036step0 (permutation18 i) (permutation7 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7036step0 permutation18 permutation7
    _ = injectiveMoment H node290 := by rfl

def raw7037 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, 2, 0, -2], ![1, -2, 3, -2]]

def raw7037step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 2, -2], ![-3, 0, 3], ![4, -2, -2]]

def raw7037step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 3, -3], ![2, -2, 0]]

theorem canonical7037 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7037 = injectiveMoment H node147 := by
  calc
    injectiveMoment H raw7037 = injectiveMoment H raw7037step0 := by
      have heq : raw7037step0 = raw7037.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7037).symm
    injectiveMoment H raw7037step0 = injectiveMoment H raw7037step1 := by
      have heq : raw7037step1 = (fun i j => raw7037step0 (permutation28 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7037step0 permutation28 permutation6
    _ = injectiveMoment H node147 := by rfl

def raw7038 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, 2, 2, -4], ![1, -2, 1, 0]]

def raw7038step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 2, -2], ![-3, 2, 1], ![4, -4, 0]]

def raw7038step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 4, -4], ![1, -3, 2], ![1, -1, 0]]

theorem canonical7038 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7038 = injectiveMoment H node217 := by
  calc
    injectiveMoment H raw7038 = injectiveMoment H raw7038step0 := by
      have heq : raw7038step0 = raw7038.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7038).symm
    injectiveMoment H raw7038step0 = injectiveMoment H raw7038step1 := by
      have heq : raw7038step1 = (fun i j => raw7038step0 (permutation20 i) (permutation7 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7038step0 permutation20 permutation7
    _ = injectiveMoment H node217 := by rfl

def raw7039 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![1, -2, 2, -1], ![0, 2, 1, -3]]

def raw7039step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![0, -2, 2], ![-3, 2, 1], ![4, -1, -3]]

def raw7039step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 2, -3], ![2, -2, 0]]

theorem canonical7039 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7039 = injectiveMoment H node83 := by
  calc
    injectiveMoment H raw7039 = injectiveMoment H raw7039step0 := by
      have heq : raw7039step0 = raw7039.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7039).symm
    injectiveMoment H raw7039step0 = injectiveMoment H raw7039step1 := by
      have heq : raw7039step1 = (fun i j => raw7039step0 (permutation28 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7039step0 permutation28 permutation8
    _ = injectiveMoment H node83 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
