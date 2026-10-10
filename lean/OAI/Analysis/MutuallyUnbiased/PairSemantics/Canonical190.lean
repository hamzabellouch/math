import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes2
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes3
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes4
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes11
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes12
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes13
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes14
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes17
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes18
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes19
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes38
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes39

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw6080 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -1, 1, -1]]

def raw6080step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 0, 2, -1], ![-2, 1, 0, 1], ![4, -1, -2, -1]]

def raw6080step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, 0, 1, -2]]

theorem canonical6080 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6080 = injectiveMoment H node769 := by
  calc
    injectiveMoment H raw6080 = injectiveMoment H raw6080step0 := by
      have heq : raw6080step0 = raw6080.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6080).symm
    injectiveMoment H raw6080step0 = injectiveMoment H raw6080step1 := by
      have heq : raw6080step1 = (fun i j => raw6080step0 (permutation27 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6080step0 permutation27 permutation18
    _ = injectiveMoment H node769 := by rfl

def raw6081 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 1, -1], ![0, 2, 1, -3], ![1, -1, 0, 0]]

def raw6081step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 0, 2, -1], ![-2, 1, 1, 0], ![4, -1, -3, 0]]

def raw6081step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, -1, 2, -1], ![0, 1, 0, -1], ![1, 0, 1, -2]]

theorem canonical6081 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6081 = injectiveMoment H node1170 := by
  calc
    injectiveMoment H raw6081 = injectiveMoment H raw6081step0 := by
      have heq : raw6081step0 = raw6081.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6081).symm
    injectiveMoment H raw6081step0 = injectiveMoment H raw6081step1 := by
      have heq : raw6081step1 = (fun i j => raw6081step0 (permutation29 i) (permutation20 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6081step0 permutation29 permutation20
    _ = injectiveMoment H node1170 := by rfl

def raw6082 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 1, -1], ![1, -1, 2, -2], ![0, 2, -1, -1]]

def raw6082step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, -1, 2, -2]]

theorem canonical6082 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6082 = injectiveMoment H node911 := by
  calc
    injectiveMoment H raw6082 = injectiveMoment H raw6082step0 := by
      have heq : raw6082step0 = (fun i j => raw6082 (permutation10 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6082 permutation10 permutation9
    _ = injectiveMoment H node911 := by rfl

def raw6083 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 1, -1], ![1, 1, 1, -3]]

def raw6083step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1], ![4, -1, -3]]

def raw6083step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2]]

theorem canonical6083 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6083 = injectiveMoment H node253 := by
  calc
    injectiveMoment H raw6083 = injectiveMoment H raw6083step0 := by
      have heq : raw6083step0 = raw6083.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6083).symm
    injectiveMoment H raw6083step0 = injectiveMoment H raw6083step1 := by
      have heq : raw6083step1 = (fun i j => raw6083step0 (permutation27 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6083step0 permutation27 permutation6
    _ = injectiveMoment H node253 := by rfl

def raw6084 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 2, -2], ![0, 0, 0, 0], ![1, 1, 0, -2]]

def raw6084step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 0, 0, 1], ![-2, 2, 0, 0], ![4, -2, 0, -2]]

def raw6084step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0], ![4, -2, -2]]

def raw6084step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 1, -1], ![2, 0, -2]]

theorem canonical6084 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6084 = injectiveMoment H node145 := by
  calc
    injectiveMoment H raw6084 = injectiveMoment H raw6084step0 := by
      have heq : raw6084step0 = raw6084.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6084).symm
    injectiveMoment H raw6084step0 = injectiveMoment H raw6084step1 := by
      have hz : ∀ i, raw6084step0 i (permutation21 0) = 0 := by decide +kernel
      have heq : raw6084step1 = (fun i j => raw6084step0 i (permutation21 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw6084step0 permutation21 hz
    injectiveMoment H raw6084step1 = injectiveMoment H raw6084step2 := by
      have heq : raw6084step2 = (fun i j => raw6084step1 (permutation27 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6084step1 permutation27 permutation6
    _ = injectiveMoment H node145 := by rfl

def raw6085 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 2, -2], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, -1, 0, 0]]

def raw6085step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 1, -1], ![0, 0, 2, -2], ![0, 2, -1, -1], ![1, -1, 0, 0]]

theorem canonical6085 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6085 = injectiveMoment H node2506 := by
  calc
    injectiveMoment H raw6085 = injectiveMoment H raw6085step0 := by
      have heq : raw6085step0 = (fun i j => raw6085 (permutation39 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6085 permutation39 permutation9
    _ = injectiveMoment H node2506 := by rfl

def raw6086 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 2, -2], ![0, 0, 1, -1], ![1, 1, -1, -1]]

def raw6086step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 1, -1], ![0, 0, 2, -2], ![1, 1, -1, -1]]

theorem canonical6086 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6086 = injectiveMoment H node907 := by
  calc
    injectiveMoment H raw6086 = injectiveMoment H raw6086step0 := by
      have heq : raw6086step0 = (fun i j => raw6086 (permutation11 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6086 permutation11 permutation9
    _ = injectiveMoment H node907 := by rfl

def raw6087 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, 0, 1, -2]]

theorem canonical6087 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6087 = injectiveMoment H node914 := by
  rfl

def raw6088 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, 0, 0, -1]]

theorem canonical6088 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6088 = injectiveMoment H node915 := by
  rfl

def raw6089 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 2, -2], ![0, 2, -1, -1], ![1, -1, 1, -1]]

theorem canonical6089 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6089 = injectiveMoment H node917 := by
  rfl

def raw6090 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 2, -2], ![0, 2, 0, -2], ![1, -1, 0, 0]]

def raw6090step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 2, -2], ![0, 2, 0, -2], ![1, 0, -1, 0]]

theorem canonical6090 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6090 = injectiveMoment H node775 := by
  calc
    injectiveMoment H raw6090 = injectiveMoment H raw6090step0 := by
      have heq : raw6090step0 = (fun i j => raw6090 (permutation11 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6090 permutation11 permutation11
    _ = injectiveMoment H node775 := by rfl

def raw6091 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 2, -2], ![1, 1, 0, -2]]

def raw6091step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0], ![4, -2, -2]]

def raw6091step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 1, -1], ![2, 0, -2]]

theorem canonical6091 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6091 = injectiveMoment H node145 := by
  calc
    injectiveMoment H raw6091 = injectiveMoment H raw6091step0 := by
      have heq : raw6091step0 = raw6091.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6091).symm
    injectiveMoment H raw6091step0 = injectiveMoment H raw6091step1 := by
      have heq : raw6091step1 = (fun i j => raw6091step0 (permutation27 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6091step0 permutation27 permutation6
    _ = injectiveMoment H node145 := by rfl

def raw6092 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 3, -3], ![0, 1, -1, 0], ![1, 0, 0, -1]]

theorem canonical6092 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6092 = injectiveMoment H node919 := by
  rfl

def raw6093 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 3, -3], ![0, 2, -1, -1], ![1, -1, 0, 0]]

theorem canonical6093 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6093 = injectiveMoment H node920 := by
  rfl

def raw6094 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 3, -3], ![1, 1, -1, -1]]

def raw6094step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-2, 3, -1], ![4, -3, -1]]

def raw6094step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 3, -2], ![1, 0, -1], ![1, 0, -1]]

theorem canonical6094 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6094 = injectiveMoment H node248 := by
  calc
    injectiveMoment H raw6094 = injectiveMoment H raw6094step0 := by
      have heq : raw6094step0 = raw6094.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6094).symm
    injectiveMoment H raw6094step0 = injectiveMoment H raw6094step1 := by
      have heq : raw6094step1 = (fun i j => raw6094step0 (permutation31 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6094step0 permutation31 permutation8
    _ = injectiveMoment H node248 := by rfl

def raw6095 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 4, -4], ![1, 1, -2, 0]]

def raw6095step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-2, 4, -2], ![4, -4, 0]]

def raw6095step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 4, -4], ![1, -1, 0], ![1, -1, 0]]

theorem canonical6095 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6095 = injectiveMoment H node157 := by
  calc
    injectiveMoment H raw6095 = injectiveMoment H raw6095step0 := by
      have heq : raw6095step0 = raw6095.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6095).symm
    injectiveMoment H raw6095step0 = injectiveMoment H raw6095step1 := by
      have heq : raw6095step1 = (fun i j => raw6095step0 (permutation25 i) (permutation7 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6095step0 permutation25 permutation7
    _ = injectiveMoment H node157 := by rfl

def raw6096 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 1, -1, 0], ![-1, 1, 1, -1], ![1, -1, 1, -1], ![1, 0, 1, -2]]

def raw6096step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![-1, 1, 1, -1], ![0, 1, -1, 0], ![1, -1, 1, -1], ![1, 0, 1, -2]]

theorem canonical6096 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6096 = injectiveMoment H node2488 := by
  calc
    injectiveMoment H raw6096 = injectiveMoment H raw6096step0 := by
      have heq : raw6096step0 = (fun i j => raw6096 (permutation39 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6096 permutation39 permutation9
    _ = injectiveMoment H node2488 := by rfl

def raw6097 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 1, -1, 0], ![0, 0, 2, -2], ![1, 0, 1, -2]]

def raw6097step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, 0, 1, -2]]

theorem canonical6097 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6097 = injectiveMoment H node914 := by
  calc
    injectiveMoment H raw6097 = injectiveMoment H raw6097step0 := by
      have heq : raw6097step0 = (fun i j => raw6097 (permutation11 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6097 permutation11 permutation9
    _ = injectiveMoment H node914 := by rfl

def raw6098 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 1, -1, 0], ![0, 1, 0, -1], ![0, -1, 2, -1], ![1, 0, 1, -2]]

def raw6098step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, -1, 2, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, 1, -2]]

theorem canonical6098 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6098 = injectiveMoment H node2499 := by
  calc
    injectiveMoment H raw6098 = injectiveMoment H raw6098step0 := by
      have heq : raw6098step0 = (fun i j => raw6098 (permutation45 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6098 permutation45 permutation9
    _ = injectiveMoment H node2499 := by rfl

def raw6099 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 1, -1], ![0, 0, 2, -2]]

def raw6099step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 1, -1]]

theorem canonical6099 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6099 = injectiveMoment H node2508 := by
  calc
    injectiveMoment H raw6099 = injectiveMoment H raw6099step0 := by
      have heq : raw6099step0 = (fun i j => raw6099 (permutation51 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6099 permutation51 permutation9
    _ = injectiveMoment H node2508 := by rfl

def raw6100 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 3, -3]]

def raw6100step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 1, 1, -1], ![-2, -1, 0, 3], ![4, 0, -1, -3]]

def raw6100step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 0, -1], ![1, -1, -1, 1], ![2, 1, 0, -3], ![-4, 0, 1, 3]]

def raw6100step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -1, 1], ![0, 1, -3, 2], ![1, 0, 3, -4]]

theorem canonical6100 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6100 = injectiveMoment H node1115 := by
  calc
    injectiveMoment H raw6100 = injectiveMoment H raw6100step0 := by
      have heq : raw6100step0 = raw6100.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6100).symm
    injectiveMoment H raw6100step0 = injectiveMoment H raw6100step1 := by
      have heq : raw6100step1 = -raw6100step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6100step0).symm
    injectiveMoment H raw6100step1 = injectiveMoment H raw6100step2 := by
      have heq : raw6100step2 = (fun i j => raw6100step1 (permutation15 i) (permutation24 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6100step1 permutation15 permutation24
    _ = injectiveMoment H node1115 := by rfl

def raw6101 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, -1, 2, -2]]

theorem canonical6101 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6101 = injectiveMoment H node921 := by
  rfl

def raw6102 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, -1, 0, 0]]

def raw6102step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 1, 1, -1], ![-2, -1, 3, 0], ![4, 0, -4, 0]]

def raw6102step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 0, 4, -4], ![0, 1, -1, 0], ![1, -1, -1, 1]]

theorem canonical6102 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6102 = injectiveMoment H node1228 := by
  calc
    injectiveMoment H raw6102 = injectiveMoment H raw6102step0 := by
      have heq : raw6102step0 = raw6102.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6102).symm
    injectiveMoment H raw6102step0 = injectiveMoment H raw6102step1 := by
      have heq : raw6102step1 = (fun i j => raw6102step0 (permutation25 i) (permutation19 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6102step0 permutation25 permutation19
    _ = injectiveMoment H node1228 := by rfl

def raw6103 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 1, -1, 0], ![1, 0, 3, -4]]

def raw6103step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![-2, -1, 3], ![4, 0, -4]]

def raw6103step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -1, 1], ![0, 4, -4], ![1, -1, 0]]

theorem canonical6103 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6103 = injectiveMoment H node270 := by
  calc
    injectiveMoment H raw6103 = injectiveMoment H raw6103step0 := by
      have heq : raw6103step0 = raw6103.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6103).symm
    injectiveMoment H raw6103step0 = injectiveMoment H raw6103step1 := by
      have heq : raw6103step1 = (fun i j => raw6103step0 (permutation22 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6103step0 permutation22 permutation5
    _ = injectiveMoment H node270 := by rfl

def raw6104 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, 2, -2]]

def raw6104step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 1, 1, -1], ![-2, 0, 0, 2], ![4, -1, -1, -2]]

def raw6104step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 1, -1], ![0, 0, 2, -2], ![1, 1, -1, -1]]

theorem canonical6104 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6104 = injectiveMoment H node907 := by
  calc
    injectiveMoment H raw6104 = injectiveMoment H raw6104step0 := by
      have heq : raw6104step0 = raw6104.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6104).symm
    injectiveMoment H raw6104step0 = injectiveMoment H raw6104step1 := by
      have heq : raw6104step1 = (fun i j => raw6104step0 (permutation28 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6104step0 permutation28 permutation18
    _ = injectiveMoment H node907 := by rfl

def raw6105 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 1, 0, -1], ![1, 0, 2, -3]]

def raw6105step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![-2, 0, 2], ![4, -1, -3]]

def raw6105step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1]]

theorem canonical6105 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6105 = injectiveMoment H node254 := by
  calc
    injectiveMoment H raw6105 = injectiveMoment H raw6105step0 := by
      have heq : raw6105step0 = raw6105.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6105).symm
    injectiveMoment H raw6105step0 = injectiveMoment H raw6105step1 := by
      have heq : raw6105step1 = (fun i j => raw6105step0 (permutation28 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6105step0 permutation28 permutation6
    _ = injectiveMoment H node254 := by rfl

def raw6106 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 1, 1, -2], ![0, -1, 2, -1], ![1, 1, -1, -1]]

def raw6106step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, -1, 2, -1], ![0, 1, 1, -2], ![1, 1, -1, -1]]

theorem canonical6106 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6106 = injectiveMoment H node894 := by
  calc
    injectiveMoment H raw6106 = injectiveMoment H raw6106step0 := by
      have heq : raw6106step0 = (fun i j => raw6106 (permutation11 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6106 permutation11 permutation9
    _ = injectiveMoment H node894 := by rfl

def raw6107 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 1, 1, -2], ![0, 1, 0, -1], ![1, -1, 1, -1]]

def raw6107step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, 1, -1, -1]]

theorem canonical6107 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6107 = injectiveMoment H node766 := by
  calc
    injectiveMoment H raw6107 = injectiveMoment H raw6107step0 := by
      have heq : raw6107step0 = (fun i j => raw6107 (permutation11 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6107 permutation11 permutation11
    _ = injectiveMoment H node766 := by rfl

def raw6108 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 1, 1, -2], ![0, 1, 1, -2], ![1, -1, 0, 0]]

def raw6108step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 1, 1, -2], ![0, 1, 1, -2], ![1, 0, -1, 0]]

theorem canonical6108 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6108 = injectiveMoment H node787 := by
  calc
    injectiveMoment H raw6108 = injectiveMoment H raw6108step0 := by
      have heq : raw6108step0 = (fun i j => raw6108 (permutation9 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6108 permutation9 permutation11
    _ = injectiveMoment H node787 := by rfl

def raw6109 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 1, 1, -2], ![1, -1, 1, -1], ![0, 1, 0, -1]]

def raw6109step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, 1, -1, -1]]

theorem canonical6109 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6109 = injectiveMoment H node766 := by
  calc
    injectiveMoment H raw6109 = injectiveMoment H raw6109step0 := by
      have heq : raw6109step0 = (fun i j => raw6109 (permutation13 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6109 permutation13 permutation11
    _ = injectiveMoment H node766 := by rfl

def raw6110 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 1, 1, -2], ![1, 0, 1, -2]]

def raw6110step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![-2, 1, 1], ![4, -2, -2]]

def raw6110step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]

theorem canonical6110 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6110 = injectiveMoment H node150 := by
  calc
    injectiveMoment H raw6110 = injectiveMoment H raw6110step0 := by
      have heq : raw6110step0 = raw6110.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6110).symm
    injectiveMoment H raw6110step0 = injectiveMoment H raw6110step1 := by
      have heq : raw6110step1 = (fun i j => raw6110step0 (permutation27 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6110step0 permutation27 permutation6
    _ = injectiveMoment H node150 := by rfl

def raw6111 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 1, 2, -3], ![1, 0, 0, -1]]

def raw6111step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![-2, 2, 0], ![4, -3, -1]]

def raw6111step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1]]

theorem canonical6111 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6111 = injectiveMoment H node254 := by
  calc
    injectiveMoment H raw6111 = injectiveMoment H raw6111step0 := by
      have heq : raw6111step0 = raw6111.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6111).symm
    injectiveMoment H raw6111step0 = injectiveMoment H raw6111step1 := by
      have heq : raw6111step1 = (fun i j => raw6111step0 (permutation30 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6111step0 permutation30 permutation8
    _ = injectiveMoment H node254 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
